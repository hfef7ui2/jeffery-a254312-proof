# The One-Step Ascent Set of Jeffery's Collatz Map

This paper proves that OEIS A254312 lists each positive integer $m$ satisfying $S(m)>m$ exactly once. The Lean formalization verifies both the array bijection and the upward-antidiagonal reading specified by Jeffery. [OEIS conjecture](https://oeis.org/A254312) · [Definition of S](https://oeis.org/A257480)

- [Paper (PDF)](output/pdf/Jeffery-A254312-paper.pdf)
- [LaTeX source](paper/main.tex) and [BibTeX bibliography](paper/references.bib)
- [Lean main theorem](Jeffery.lean) and [verification log](output/lean-verification.txt)

To reproduce the build, install elan and run the following from the repository root. The toolchain and mathlib commit are pinned.

```sh
lake exe cache get
lake build
lake env lean Jeffery.lean
```

The logarithmic separation proof by Eric Merle is bundled with its original attribution and license. [Provenance and license](vendor/PROVENANCE.md)

## Jeffery 的 A254312 猜想 · Lean 4 形式化

对每个正整数 `m`，`S(m) > m` 当且仅当存在正整数 `n, k` 使 `A(n,k) = m`。每个出现的数恰好占一个位置，数组的所有项均为正整数。这给出了 A254312 所述排列猜想。原问题由 L. Edson Jeffery 于 2015 年提出。[数组与猜想原文](https://github.com/oeis/oeisdata/blob/main/seq/A254/A254312.seq) · [函数 S 的原始定义](https://github.com/oeis/oeisdata/blob/main/seq/A257/A257480.seq)

### 复验

安装带 Lake 的 Lean 工具链管理器 elan，在工程根目录运行以下命令。首次运行需要联网获取固定版本的依赖。

```sh
lake exe cache get
lake build
lake env lean Jeffery.lean
```

`lean-toolchain` 指定 Lean `4.34.0`，`lake-manifest.json` 将 mathlib 锁定到 `5ed2965256430c3649e86755f9576b54eca72435`。最后一条命令重新检查主文件，并打印主要定理的公理依赖。此工程中主定理的输出为 `[propext, Classical.choice, Quot.sound]`，即命题外延性、经典选择和商类型的标准公理。

`output/lean-verification.txt` 保存本次验证输出。若要对本工程及随附对数证明生成的 `.olean` 文件再逐模块重放，可运行 `lake env leanchecker -v Jeffery Logs23`。

### 定理和源码

| 文件 | 内容 |
| --- | --- |
| `Jeffery.lean` | `jeffery_conjecture` 给出上升与唯一数组位置的等价关系，`ascent_iff_occurs` 给出上升与至少出现一次的等价关系，`jeffery_sequence` 给出上升与唯一序列编号的等价关系。 |
| `Jeffery/Statement.lean` | `originalStep` 用有理数给出原始分式。`step_as_printed` 证明其值等于可计算的整数版本。 |
| `Jeffery/Normalization.lean` | 构造 2 进赋值与奇数部分，证明分解、整除性和上升判定所用的标准形。 |
| `Jeffery/Beatty.lean` | 对实数表达式 `n * log 3 / log (3 / 2)` 取下整，证明相应的严格幂比较。 |
| `Jeffery/Array.lean` | 从带符号的数组分子恢复精确的商，证明行内参数化和列唯一性。 |
| `Jeffery/Permutation.lean` | 用 `valuationTwo (3*m-2) + 1` 从数组值恢复行号，再证明全数组唯一性与上升判定。`oeisArray` 在这里给出 OEIS 的带符号公式。 |
| `Jeffery/Antidiagonal.lean` | 按 `(1,1), (2,1), (1,2), (3,1), …` 的次序读数组，证明正整数序号与正整数行列位置一一对应。 |
| `Jeffery/Gap.lean` 与 `vendor/Logs23/` | 对所有正整数 `n,v` 证明如下幂差引理，并在主文件中消去对对数下界的假设。 |

$$
3^v < 2^{n+v} \quad\Longrightarrow\quad 3^v+2^n\le 2^{n+v}+1.
$$

手稿在这一步引用 Ellison 的幂差估计。Lean 版本用另一条证明得到同一引理。当 `v ≤ 20000` 时，源码用有理数界和精确整数比较覆盖全部情况；当 `v > 20000` 时，使用 Eric Merle 的 `Logs23.lam_lower_thm`。后者及其专用依赖均随工程附上，由 Lake 从源码构建。其出处和改编范围见 [`vendor/PROVENANCE.md`](vendor/PROVENANCE.md)。[Merle 的上游 Lean 证明](https://github.com/ericmerle3789/one-obstruction-three-faces-lean/blob/cd92689908fabd161d06ffdb04b43bb83a5894e0/logs23/Logs23/TwoLog.lean)
