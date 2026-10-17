# Char2Theta — Lean 4 形式化

目标是形式化 *Dyadic Weil Representations, Clifford Groups, and Theta Correspondence*（2026-10-09 版）。已证明第一节式 (1.1) 的具体 Clifford 射影正合列，并建立 §1.3 的局部域算术、导子、格函数模型、Fourier 理论及完整 L² 上的基本酉算子。Gaussian 截断积分、单位模长的 Weil 指数、带准确标量的 Bruhat 关系及标准三次／四次关系也已证明。**具体 metaplectic 二重覆盖、规范提升、完整 Weil 表示及原文的 `τ_L` 尚未构造**；各项覆盖范围见下表。

原文保存在 [docs/Char2Theta.pdf](docs/Char2Theta.pdf)，第一节位于 PDF 第 2–3 页。原文件 SHA-256：`72b87df00a4f1026d83162ae55318ec7918fc45fd164556b5bdcb7086c8cfddc`。本轮是结构整理；未扩大已形式化的数学范围。

## 打开与编译

用 VS Code 打开 [Char2Theta.code-workspace](Char2Theta.code-workspace)，或直接打开本目录。推荐扩展为 `leanprover.lean4`；入口文件是 [Char2Theta.lean](Char2Theta.lean)。

工具链固定为 Lean `v4.32.0`，mathlib 固定为提交 `81a5d257c8e410db227a6665ed08f64fea08e997`（`v4.32.0` 标签）；传递依赖由 `lake-manifest.json` 锁定。

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

如果默认缓存目录不可写，可以使用项目内缓存：

```sh
MATHLIB_CACHE_DIR="$PWD/.lake/cache" lake exe cache get
```

## 模块组织与阅读顺序

第一节现为 **7 个主题模块**（整理前 17 个），加上总入口与公理审计文件共 **9 个 Lean 文件**。
每个模块开头都有中文导读，内部按依赖顺序保留原证明。总入口只导入 `Clifford` 与
`DyadicWeil` 两条链的终点；使用 `import Char2Theta` 无需修改。被合并的旧文件已删除，
没有另留只转发导入的文件。

| 模块 | 内容 | 原直接导入路径的迁移（省略 `Char2Theta.Section1.`） |
|---|---|---|
| [FiniteBasics.lean](Char2Theta/Section1/FiniteBasics.lean) | 中心扩张、有限坐标、复相位、公共特征延拓 | `FiniteBasics`；`extend_unit_character` 从 `SymplecticLifting` 移入 |
| [Clifford.lean](Char2Theta/Section1/Clifford.lean) | Pauli、Heisenberg、自同构、辛提升、正合列 (1.1) | `Pauli`、`Heisenberg`、`PauliAutomorphisms`、`SymplecticLifting`、`CliffordExactSequence` |
| [DyadicArithmetic.lean](Char2Theta/Section1/DyadicArithmetic.lean) | 整数环、剩余域、数值公式、Witt 及模四商比较 | `DyadicArithmetic`、`DyadicQuotients`；`Dyadic` 的算术约定 |
| [DyadicCharacter.lean](Char2Theta/Section1/DyadicCharacter.lean) | 局部域拓扑、导子、核障碍、光滑特征 | `DyadicCharacter`；`DyadicTopology` 的局部域部分、`Dyadic` 的特征约定 |
| [DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) | 格与表示约定、紧开坐标格、有限模型、delta 基及根算子 | `DyadicLatticeModel`、`DyadicWeilOperators`；`DyadicTopology` 的坐标格部分、`Dyadic` 的函数与表示约定 |
| [DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) | Haar 积分、有限限制、归一化、测试函数反演与 Plancherel | `DyadicLocalFourier`、`DyadicFourierNormalization`；`DyadicFourierAnalysis` 的测试函数部分 |
| [DyadicWeil.lean](Char2Theta/Section1/DyadicWeil.lean) | 完整 L² 酉算子、Gaussian 积分、Weil 指数与具体群关系 | `DyadicFourierAnalysis` 的 L² 部分、`DyadicGaussian` |

局部理论的依赖链为 `FiniteBasics → DyadicArithmetic → DyadicCharacter → DyadicLatticeModel → DyadicFourier → DyadicWeil`。
有限群理论为 `FiniteBasics → Clifford`。通用特征延拓已放回公共基础，局部特征不再导入辛提升或 Clifford 理论。

## 本次删除与兼容性

删除前检查了源码引用与已编译声明的类型／证明依赖。以下 8 项是未使用的包装或重复接口；
其余数学定义、定理和实例保留。终点定理即使没有下游调用，仍是形式化成果；不同空间上的
相容性公式也保留，不能仅因结果相似而删除。

| 删除的声明 | 保留内容或直接替代 |
|---|---|
| `BilinearExtension.labelHom` | 没有调用的标签投影包装；实际证明直接使用 `.label` |
| `μ` | 直接使用 mathlib `rootsOfUnity` |
| `Dyadic.ComplexRepresentation` | 直接使用 mathlib `Representation ℂ`；`SmoothRepresentation` 和 `Genuine` 保留 |
| `Dyadic.liftedSubgroup` | 直接使用 mathlib `Subgroup.comap` |
| `binary_field_card` | mathlib `Module.card_eq_pow_finrank`；实际剩余域公式 `residueCard_eq_two_pow` 保留 |
| `Dyadic.smoothConductorFourCharacter` | 保留 `conductorFourCharacter` 及光滑性、导子与存在性定理 |
| `Dyadic.LocalQuadraticDatum.dual` | 删除未调用的数据再包装；`dualForm` 及其极化、配平方定理保留 |
| `Dyadic.localWeilIndexUnit` | 保留 `localWeilIndex` 和带单位模长证明的 `localWeilScalar : unitary ℂ` |

直接引用这些名称或旧模块路径的外部代码需要按上表迁移。保留的公开声明经过类型比对；
差异限于宇宙参数和自动证明名、`ComplexRepresentation` 别名展开，以及定义相等的实例项。
合并后另删除 62 条传递冗余导入；每项均由 importGraph 检测，并以重新构建验证。
原文记号、Fourier 正负号、Haar 归一化、定理假设和已完成数学范围均未改变。

## 第一节覆盖情况

“定义”只表示对象或条件已经准确写出；“证明”表示存在经过 Lean 内核检查的证明。条件性结果的假设列在声明中，不能当作已从局部域假设推出的事实。

| 原文内容 | 当前状态与入口 |
|---|---|
| §1.1：`𝔽₂ᴺ`、`ℂ[𝔽₂ᴺ]`、delta 向量、`X_a`、`Z_b` | [FiniteBasics.lean](Char2Theta/Section1/FiniteBasics.lean)、[Clifford.lean](Char2Theta/Section1/Clifford.lean) 定义；证明 `X_delta`、`Z_delta`、`Z_mul_X`。有限标签上全体函数与有限支撑函数有相同数学含义，本项目使用全体函数。 |
| Pauli 群乘法、阶数、中心、酉表示 | 证明 `Pauli.card`、`matrix_mul`、`matrix_unitary`、`matrix_injective`、`matrix_delta`、`mem_center_iff`、`matrix_ofCenter`；[Clifford.lean](Char2Theta/Section1/Clifford.lean) 给出与实际算子子群的群同构和该子群的阶数；`pauliCenterEquiv` 的定义域是抽象群 `Pauli N` 的中心，给出它与加法 `ZMod 4` 的群同构。具体算子群的中心可经已有群同构传递；中心元素的算子恰按 `i^s I` 作用。 |
| 完整 Clifford 群 | 用 mathlib 的酉群和正规化子定义 `Clifford`；证明所有单位复标量均属于该群，并证明群无限。另证明 `dim ℋ_N = 2^N`。 |
| 式 (1.1)：有限射影商及其正合列 | **已证明**：[Clifford.lean](Char2Theta/Section1/Clifford.lean) 中 `equation_1_1` 汇总左箭头单射、中间 `Function.MulExact`、右箭头满射；`projectiveClifford_finite` 证明商群有限。中间项是实际酉正规化子除以全部单位标量，右端直接使用 mathlib 的 `Matrix.symplecticGroup (Fin N) F₂`。对任意 `N : ℕ`（包括 0）成立。 |
| §1.2：`H(B)`、`Q(v)=B(v,v)`、平方、交换子 | [FiniteBasics.lean](Char2Theta/Section1/FiniteBasics.lean) 证明一般双加性 cocycle 的群公理；[Clifford.lean](Char2Theta/Section1/Clifford.lean) 证明平方与交换子公式，在极化形式非退化的显式假设下证明中心恰为零标签。 |
| 中心固定自同构保持 `Q`，及 `O(Q) ⊆ Sp(W)` | [Clifford.lean](Char2Theta/Section1/Clifford.lean) 的 `inducedLabelEquiv` 从自同构本身构造线性标签作用；`inducedQuadraticIsometry` 将其封装为 mathlib 的 `QuadraticMap.IsometryEquiv`，无需另给相容线性映射。`inducedLabelEquiv_preserves_polar` 证明其保持极化形式。 |
| 二维各向异性例外 | `anisotropicPlaneQ` 使用 mathlib 的矩阵二次型；证明它在三个非零向量上取值 1，故每个可逆线性变换均保持它。未另行打包成两个矩阵群相等的定理。 |
| 中心为四阶的 `H₄` | 定义原文 cocycle `2x·y'`，证明换坐标群同构 `heisenbergEquivPauli`；加法嵌入 `twoLift : ZMod 2 →+ ZMod 4` 和中心相位 `phase` 均已验证。 |
| affine symplectic 描述、向整个 `Sp(W)` 的满射、`Aut_Z(P_N)` | `PauliAut` 定义中心逐点固定的自同构群；[Clifford.lean](Char2Theta/Section1/Clifford.lean) 的 `exists_correction`、`ofCorrection`、`exists_correction_description` 给出辛变换加中心修正的双向描述，并证明 `toSymplectic_surjective`。`projectiveCliffordEquiv` 证明实际 Clifford 射影商与 `PauliAut` 同构。未另外给修正数据的集合打包独立群结构，也未声称该正合列有群同态截面。 |
| §1.3：dyadic 域、`𝒪,R,A,k,ϖ,d,e,D` | [DyadicArithmetic.lean](Char2Theta/Section1/DyadicArithmetic.lean) 定义 `Integers F` 是 `ℤ_[2]` 在 `F` 中的整闭包，`R,A` 是 `(2)`、`(4)` 的理想商，并从 `[Field F] [Algebra ℚ_[2] F] [FiniteDimensional ℚ_[2] F]` 推出整数环的有限自由模、Dedekind、局部环、DVR 和分式域实例。 |
| `k=𝒪/ϖ𝒪`、`v(ϖ)=1`、`q=2^f` | [DyadicArithmetic.lean](Char2Theta/Section1/DyadicArithmetic.lean) 建立有限剩余域、特征 2、`𝔽₂`-代数及 `Fintype` 实例；定义 `residueDegree`、`residueCard`，证明 `residueCard_eq_two_pow`。`residueEquivQuotientUniformizer` 给出任意均匀化元下的商环同构；均匀化元存在，原有 `valuation_uniformizer` 可直接用于此整数环。 |
| `d=ef`，`|R|=q^e`，`|A|=q^(2e)` | **已证明**：`degree_eq_ramificationIndex_mul_residueDegree`、`card_R`、`card_A`，汇总于 `dyadic_numerical_identities`。没有额外假设整数环是 DVR 或剩余域有限；`e` 保持原定义 `v_F(2)`。另有 `d,e,f>0`，以及 `R,A` 的有限、非平凡、局部环实例，分别具有特征 2、4 及对应 `ZMod`-代数结构。 |
| 有限函数空间维数 | [DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 的 `dyadic_finiteLatticeSpace_finrank` 从上述实例证明有限函数模型的维数为 `q^(en)`；`localLatticeSpace_finrank` 经线性同构将此公式传到实际局部子空间 `S_L`，并提供有限维实例。 |
| 非分歧时 `R≃k`、`A≃W₂(k)` | **已证明**：[DyadicArithmetic.lean](Char2Theta/Section1/DyadicArithmetic.lean) 的 `unramifiedREquivResidue`，以及同一文件的 `unramifiedAEquivWittTwo` 给出环同构；Witt 环直接使用 mathlib 的 `TruncatedWittVector 2 2 (Residue F)`。假设是 `e=1`，另证明它等价于 `Algebra.FormallyUnramified ℤ_[2] (Integers F)`。两个同构均与约化到 `k` 相容。 |
| 分歧时 `R` 有非零幂零元，`A≠𝒪/ϖ²𝒪` | **已证明**：在 `1<e` 下，`ramified_R_exists_nonzero_nilpotent` 以均匀化元的模 2 类为见证，它非零且 `e` 次幂为零；`card_quotient_uniformizer_sq_lt_card_A` 对任意均匀化元证明 `q²<q^(2e)`，从而 `ramified_A_not_ringEquiv_quotient_uniformizer_sq` 排除环同构，甚至不存在集合等价。 |
| 加法特征的导子式 (1.2) | 使用 `AddChar F ℂˣ`；`HasConductorFour` 保留 `∀ x∈𝒪, ψ(ax)=1` 的集合等于 `4𝒪`。[DyadicCharacter.lean](Char2Theta/Section1/DyadicCharacter.lean) 的 `characterModFour` 将在 `4𝒪` 上平凡的特征下降到实际商环 `A`，代表元公式由 `characterModFour_mk` 验证。`hasConductorFour_iff_isPrimitive` 证明在此平凡性假设下，(1.2) 等价于下降特征满足 mathlib 的 `AddChar.IsPrimitive`；`conductorCharacter_annihilator` 给出 `(∀b, χ(ab)=1) ↔ a=0`。`SmoothCharacter` 独立表达局部常值性。 |
| 满足 (1.2) 的光滑加法特征存在性 | **已构造并证明**：[DyadicCharacter.lean](Char2Theta/Section1/DyadicCharacter.lean) 给出 `conductorFourCharacter F` 及其导子等式；其中 `exists_smooth_character_conductor_four` 同时给出光滑性和 (1.2)，并证明特征连续。一般地，任何在 `4𝒪` 上平凡的加法特征均光滑。构造使用经典选择，没有指定迹公式或规范化选择。 |
| dyadic 局部域拓扑 | [DyadicCharacter.lean](Char2Theta/Section1/DyadicCharacter.lean) 在相容的 `NormedAlgebra ℚ_[2] F` 下提供 `CompleteSpace`、`ProperSpace`、`IsUltrametricDist` 及整数环的 `CompactSpace` 实例；mathlib 随之提供局部紧、Hausdorff、全不连通及拓扑除环结构。证明 `𝒪` 是闭单位球，`𝒪` 和 `4𝒪` 在 `F` 中均紧开。仅有有限扩张假设时，可开启 `Char2Theta.Dyadic.SpectralTopology` 作用域取得相容谱范数；`exists_smooth_character_conductor_four_spectral` 已用此拓扑证明存在性。 |
| `(𝒪/4𝒪,+) ≃ (ℤ/4ℤ)^d` | **已构造**：[DyadicArithmetic.lean](Char2Theta/Section1/DyadicArithmetic.lean) 的 `AAddEquivModFour`。选择 `𝒪` 的 `ℤ₂`-基后，逐坐标模 4 约化，证明该加法同态满射且核恰为 `(4)`，再使用 mathlib 的商群同构定理。它是依赖基选择的加法群同构，对所有有限 dyadic 扩张成立；没有要求 `e=1`。 |
| 不能把导子条件替换成 `ker ψ=4𝒪` | **已补全连接**：`A_character_not_injective` 将 [DyadicCharacter.lean](Char2Theta/Section1/DyadicCharacter.lean) 的有限群反证转移到实际 `A`；`exists_integral_kernel_outside_four` 在 `d>1`、`ψ` 对 `4𝒪` 平凡时给出额外的整数核元素。`character_kernel_ne_four` 对任意域特征证明 `{a : F ∣ ψ a = 1} ≠ 4𝒪`；若满足 (1.2)，`conductor_four_strictSubset_kernel` 进一步证明 `4𝒪 ⊊ ker ψ`。这些结论不需要光滑性假设。 |
| `W,L`、辛形式、`K`、`K(r)`、`K(ϖ)` | 定义有极化的自由模及原文配对；`K` 直接使用 mathlib 辛群。构造环同态上的辛群映射；同余子群定义为该映射的核。`W O n` 可表示积分格，`W F n` 可表示局部空间；尚未打包积分格到局部空间的包含。 |
| 复表示、光滑表示、genuine、逆像子群、`μ_r` | 复用 `Representation`、`Subgroup.comap`、`rootsOfUnity`；定义开稳定子条件及指定元素作用为 `-I` 的条件。`Genuine ρ ε` 的语义依赖调用者将 `ε` 选为覆盖核的非平凡元。 |
| `𝒮(F^n)`、`S_L` 与有限商函数空间 | **已构造同构**：[DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 的 `LocalLatticeSpace` 是原有 `latticeSubmodule` 的别名，保持支撑及平移不变条件。`latticeEquivFinite` 给出 `S_L ≃ₗ[ℂ] ((Fin n → 𝒪/2𝒪) → ℂ)`；正向是限制到整数格并下降到商，逆向是按剩余类取值、格外取零，已验证局部常值、紧支撑及互逆性。 |
| 格子紧开性和 delta 基 | [DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 证明 `𝒪^n`、非零有理整数倍 `r𝒪^n` 及 `x+2𝒪^n` 均紧开。`latticeDeltaBasis` 由 mathlib 标准函数基传递而来；`latticeDelta_reduceVector_eq_indicator` 对任意整数代表元证明 `δ_[x]=1_(x+2𝒪^n)`，普通支撑和拓扑支撑均恰为该陪集。`latticeDeltaBasis_repr` 和 `latticeDelta_expansion` 给出取值坐标与有限 delta 展开。以上结果对所有 `n : ℕ`（含 0）成立，也适用于分歧扩张。 |
| 式 (2.2) 的上根算子与 `S_L` 稳定性 | **已构造并证明**：[DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 先在整个 `SchwartzBruhat (Fin n → F)` 上构造坐标剪切、`ψ(t yᵢ²)` 和 `ψ(2t yᵢyⱼ)` 乘法算子，再证明它们保持原有的支撑和 `2𝒪^n` 平移不变条件。限制为 `S_L` 的线性自同构，证明每个固定根方向满足加法参数群的表示律，并给出有限坐标公式。尚未将这些算子识别为 metaplectic 元素的作用。 |
| 式 (2.3) 的有限 Fourier 配对和同构 | **已构造并证明**：[DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 从 (1.2) 证明 `x mod 2 ↦ ψ(2x)` 的本原性和配对非退化，再复用 mathlib 的特征线性无关定理构造 `finiteFourier`。`fourierPairingChar_integral` 验证其核为 `ψ(2x·y)`；`latticeFiniteFourier` 经原有同构传回实际 `S_L`，保留显式非零标量参数。已证明它在 `c=1/√N` 时等于指定 Haar 测度下的局部 Fourier 限制，其中 `N=q^(en)`；规范 metaplectic 提升的额外 Weil 标量仍未确定。 |
| 生成元稳定性到限制表示 | [DyadicLatticeModel.lean](Char2Theta/Section1/DyadicLatticeModel.lean) 的 `invariant_of_group_generators` 证明有限维子空间的生成元稳定性推出全群稳定性，逆元情形使用有限维单射即满射。`latticeRepresentationOfGenerators` 复用 `Subrepresentation.toRepresentation`；输入必须包括一个实际的环境表示、生成整个群的证明及生成元的算子公式。Fourier 情形要求真实的环境限制等式；`localFourierOperator_generatorFormula` 已为指定 Haar Fourier 算子提供该证明。对实际 Weil 表示，这是**条件性接口**，并非已构造 `τ_L` 的存在性定理。 |
| 局部 Fourier 算子和 `S_L` 稳定性 | **已构造并证明**：[DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 用 Borel Haar 测度上的 Bochner 积分定义正号变换 `∫ψ(2x·y)f(x) dμ(x)`，并证明任意局部测试函数的变换仍局部常值、紧支撑，封装为原有 `SchwartzBruhat` 空间的复线性自映射。`localFourierOperator_stable` 证明归一化算子保持原有 `S_L`。 |
| Haar 归一化与准确的有限限制 | **已证明**：[DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 先令 `vol(2𝒪ⁿ)=1`，缩放后给出 `vol(2𝒪ⁿ)=1/√N`、`vol(𝒪ⁿ)=√N`，并证明此归一化唯一。`localFourierOperator_lattice_eq` 是实际局部算子与 `latticeFiniteFourier (latticeFourierUnit F n)` 在整个 `Fⁿ` 上的等式；系数为 `1/√(q^(en))`。没有假设该限制等式。 |
| 格模型上的 Fourier 反演 | [DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 复用 mathlib 的特征和正交关系，证明未归一化有限变换的平方为 `N` 乘反射。模 2 标签上的反射是恒等，故 `normalizedLatticeFourier_involutive` 及 `localFourierOperator_sq_on_lattice` 证明归一化有限变换和实际局部算子在 `S_L` 上均平方为恒等。这是下面全空间反演证明的起点；全空间中保留反射 `f(-x)`。 |
| 全 Schwartz–Bruhat 空间的 Fourier 反演 | **已证明**：[DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 的 `localFourierOperator_sq` 对任意测试函数和任意 `x∈Fⁿ` 证明 `𝓕ψ²f(x)=f(-x)`。`localFourierEquiv` 将实际积分算子封装为整个原有空间的线性同构，`localFourierEquiv_symm_apply` 给出逆变换 `𝓕ψf(-x)`。 |
| Parseval 与 Plancherel | **已证明**：[DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 从导子推出 `ψ` 取值模长为 1，证明复共轭与 Fourier 的符号关系，再给出任意两测试函数的 Hermitian 积分等式 `localFourierOperator_parseval`，以及平方范数积分保持 `localFourierOperator_plancherel`。平方范数的可积性单独证明；这些积分等式先在整个 Schwartz–Bruhat 空间成立，再用于下述 `L²` 延拓。 |
| Haar 测度的自对偶归一化 | **已验证并证明唯一性**：[DyadicFourier.lean](Char2Theta/Section1/DyadicFourier.lean) 的 `IsSelfDualFourierMeasure` 要求同一 Haar 测度下的两次 Fourier 积分对全部测试函数给出反射。`latticeFourierHaar_isSelfDual` 验证已选测度；`isSelfDualFourierMeasure_iff` 证明任意 Haar 测度满足此条件当且仅当等于所选测度。 |
| 完整 `L²(Fⁿ,μ)` 上的 Fourier 酉算子 | **已构造并证明**：[DyadicWeil.lean](Char2Theta/Section1/DyadicWeil.lean) 的 `LocalL2` 是 mathlib 的 `Lp ℂ 2 μ`，测度仍为 `latticeFourierHaar F n`。`schwartzToL2` 将原有测试函数送到其几乎处处等价类，且单射、稠密；`localFourierL2` 是满射复线性等距同构，`localFourierL2Unitary` 将它封装为有界算子代数的酉元。`localFourierL2_apply_test`、`localFourierL2_coeFn_test` 给出与原算子的类等式和几乎处处积分公式；另证明全 `L²` 上的范数、内积保持，伴随等于逆，连续延拓唯一，以及测试函数逼近下的极限相容性。 |
| 完整 `L²` 上的相位与线性换元 | **已构造并证明**：[DyadicWeil.lean](Char2Theta/Section1/DyadicWeil.lean) 的 `quadraticPhaseL2 Q` 接受任意 mathlib `QuadraticForm F (Fin n → F)`；`linearChangeL2 e` 接受任意 `F`-线性自同构。两者是满射复线性等距同构，并有 `unitary` 封装、全 `L²` 几乎处处代表元公式、参数加法／换元复合律及伴随公式。`localFourierL2_linearChange` 证明 Fourier 的逆转置换元律，`linearChangeL2_quadraticPhase` 证明二次型拉回律。`lowerQuadraticPhaseL2` 定义为 `𝓕ψ⁻¹ M_Q 𝓕ψ`，证明其酉性、加法律及测试函数相容性；利用 `Q(-x)=Q(x)` 证明 `𝓕ψ²` 与上相位可交换，进而得到相反方向的 Fourier 交织公式。 |
| 局部 Gaussian 积分与 Weil 指数 | **已构造并证明**：[DyadicWeil.lean](Char2Theta/Section1/DyadicWeil.lean) 的 `LocalQuadraticDatum.ofNondegenerate` 从 mathlib 的 `Q.Nondegenerate` 构造可逆极化映射。`gaussianTruncation_stabilizes`、`localGaussianIntegral_eventually_eq`、`tendsto_gaussianIntegral` 证明紧开球积分最终等于 `localGaussianIntegral`；`gaussian_fourier_duality` 给出分布公式。`localWeilIndex` 取该值乘 `√δ(B)`，已证明模长为 1，且原 Gaussian 积分模长为 `1/√δ(B)`。 |
| 带准确标量的 Weil 算子关系 | `localFourier_quadratic_bruhat` 与 `localFourierL2_quadratic_bruhat` 给出同一 Bruhat 公式在测试函数和完整 `L²` 上的版本；`localFourierL2Unitary_quadratic_bruhat` 是 mathlib 酉群中的等式。`localFourierL2Unitary_standard_cubic` 证明标准型 `q=∑xᵢ²` 的 `(𝓕ψ M_q)³=γ(q)·Id`；`localFourierL2Unitary_pow_four` 证明 `𝓕ψ⁴=Id`。不将这些关系表述为完整 metaplectic 群的构造。 |
| 秩一归一化 Weil 指数 | `normalizedRankOneWeilIndex a` 定义为 `γ(a x²)/γ(x²)`，适用于任意 `a : Fˣ`；证明模长为 1，且 `a=1` 时等于 1。尚未证明原文后续使用的四次单位根结论、平方类不变性或 Hilbert 符号乘法公式。 |
| `Mp(W),p,ε,ωψ,τ_L`、`K`-type | **未构造**具体二重 metaplectic 群及其 Weil 表示，故尚无原文指定 `K̃=p⁻¹(Sp(L))` 上的 `τ_L`；尚未形式化不可约出现的 `K`-type 条件。根参数群表示、有限 Fourier 自同构和条件性限制接口不能替代这些构造。 |

## 式 (1.1) 的证明入口

核心声明是 `Char2Theta.equation_1_1`。`projectivePauli_eq_mk` 核对左箭头确实将 `(a,b)` 送到 `X_a Z_b` 的射影类；`projectiveSymplectic_mk` 核对右箭头来自实际共轭作用，而非仅证明另一条抽象正合列。

证明分成三部分：

1. [Clifford.lean](Char2Theta/Section1/Clifford.lean) 从中心固定自同构构造辛标签作用，并证明其核恰为标签给出的内自同构。同一文件用标准基将该辛群同构到 mathlib 辛矩阵群。
2. [Clifford.lean](Char2Theta/Section1/Clifford.lean) 对任意辛变换构造对称 cocycle 差，复用 mathlib 的可除交换群特征延拓定理及四次单位根计数，证明中心修正存在，从而得到满射性。该构造使用经典选择，没有提供可执行的量子门分解算法。
3. [Clifford.lean](Char2Theta/Section1/Clifford.lean) 证明 Pauli 矩阵的交换子代数只有标量，并复用 mathlib 特征内积与交织空间维数公式取得非零交织算子。随后将其归一化为酉算子，识别共轭作用的核为 `U(1)I`，最后通过 mathlib 商群同构定理得到实际射影商。

## §1.3 的拓扑、测度与算子约定

各主题的证明入口见覆盖表，证明顺序与必要条件见相应 Lean 文件开头及内部小节。
以下保留跨模块必须一致的归一化约定。

拓扑定理适用于任意延拓标准 `ℚ₂` 范数的 `NormedAlgebra ℚ_[2] F`。若尚未选择范数，使用 `open scoped Char2Theta.Dyadic.SpectralTopology` 即可从有限扩张假设引入谱范数。该作用域中的结构实例采用低优先级；已有相容赋范结构可以直接使用，无需开启作用域。当前没有另外封装基于 `ValuativeRel` 的 `IsNonarchimedeanLocalField` 类；已建立光滑特征和局部格函数模型所需的拓扑、紧开子群及有限乘积结果。局部函数模型本身无需另外假设加法特征；相位和 Fourier 构造使用任意满足 (1.2) 的 `ψ`，可取已有的 `conductorFourCharacter`。这些算子结果同样适用于分歧扩张及 `n=0`；根算子的群含义仍限于给定的根方向。

令 `N=q^(en)`，局部 Fourier 变换采用如下约定：

\[
\mathcal F_\psi f(y)=\int_{F^n}\psi(2x\cdot y)f(x)\,d\mu(x),\qquad
\mu(2\mathcal O^n)=N^{-1/2},\quad\mu(\mathcal O^n)=N^{1/2}.
\]

因此在格函数上，`𝓕ψ = N^(-1/2) · finiteFourier`，其中有限变换按计数求和。这两个体积已由全空间反演验证为此核的自对偶归一化，并已证明满足自对偶条件的 Haar 测度唯一。对整个 Schwartz–Bruhat 空间，已证明 `𝓕ψ²f(x)=f(-x)` 和 `∫‖𝓕ψf‖² dμ=∫‖f‖² dμ`，两边均使用上述同一测度。完整 `L²(Fⁿ,μ)` 上的延拓使用相同测度，并保持 Hilbert 范数和内积。对于测试函数，延拓后的类以原 Fourier 积分为几乎处处代表元；一般 `L²` 元素由连续延拓定义，没有断言其积分绝对收敛或对任意代表元逐点成立。尚未另外构造 Pontryagin 对偶空间及其 Haar 测度。

全 L² 算子采用以下约定（等式按几乎处处理解）：

\[
M_Q f(x)=\psi(Q(x))f(x),\qquad
D_e f(x)=\sqrt{\delta(e)}\,f(ex),\qquad
\delta(e)\,e_*\mu=\mu.
\]

因此 `δ(e)` 是像的体积缩放因子，推前测度的因子为其倒数；这里使用 mathlib 的内在 Haar 模量，没有另外证明它与局部绝对值下行列式的公式。换元采用拉回约定，故 `D_e D_a = D_(a∘e)`。已证明 `𝓕ψ D_e = D_(e⁻ᵀ) 𝓕ψ`、`D_e M_Q = M_(Q∘e) D_e`，以及 `N_Q := 𝓕ψ⁻¹ M_Q 𝓕ψ` 的两个交织式 `𝓕ψ N_Q = M_Q 𝓕ψ`、`𝓕ψ M_Q = N_Q 𝓕ψ`。`N_Q` 在此仅表示这一明确的酉共轭算子，尚未识别为某个规范 metaplectic 提升。

Gaussian 理论使用同一个自对偶测度。对非退化型 `Q`，令 `B` 满足 `Q(x+y)=Q(x)+Q(y)+2x·By`，并令 `Q∨=Q∘B⁻¹`。已证明

```text
C(Q) = ∫_{‖x‖≤r} ψ(Q(x)) dμ(x)       （所有足够大的 r，值完全相同）
γ(Q) = √δ(B) · C(Q),                  |γ(Q)| = 1
𝓕ψ M_Q 𝓕ψ = γ(Q) M_(-Q∨) D_(B⁻¹) 𝓕ψ⁻¹ M_(-Q∨).
```

这里的积分始终在紧集上；没有以全空间 Bochner 积分代替振荡积分。等价的分布公式为 `G_Q(𝓕ψ f)=C(Q)G_(-Q∨)(f)`，其中 `G_Q(f)=∫ψ(Q(x))f(x)dμ(x)` 对任意 Schwartz–Bruhat 函数均可积。它也唯一确定 `C(Q)`。在正号 Fourier 约定下，标准型 `q=∑xᵢ²` 满足 `(𝓕ψ M_q)³=γ(q)·Id`，全空间还满足 `𝓕ψ⁴=Id`；这两式均已封装为酉群等式。秩一归一化指数另定义为 `γ(a x²)/γ(x²)`，不能直接替代 Bruhat 公式中的 `γ(Q)`。尚未证明这些指数的有限单位根阶数或给出其有限 Gauss 和的算术求值。

若后续构造的规范 Weyl 提升作用为 `γ·𝓕ψ`，则有限公式系数是 **`γ/√N`**；`scaled_localFourierOperator_lattice_eq` 已证明这一标量传递公式，没有将 `γ` 设成 1。[Takeda–Wood §1.3](https://arxiv.org/html/1506.05445#S1.SS3) 将这个额外的 Weil 单位根与 Fourier 积分分开。这里的 `γ` 是规范提升的待定标量，尚未证明它与上述 Gaussian 指数的具体对应关系。二重覆盖 `p : Mp(W) → Sp(W)`、实际 `ωψ`、积分提升生成 `K̃` 以及其余群关系仍属待证项；已有 Bruhat、三次和四次算子关系不能替代这些构造。

## 两处约定的处理

1. 原文 `H₄` 的 cocycle 是 `2x·y'`，但有序算子 `X_a Z_b` 的乘法产生 `2b·a'`。项目将两者分别命名，群同构明确取 `((x,y),s) ↦ ((y,x),s)`，所以原文的 `H₄` 元素作用为 `i^s X_y Z_x`，没有默默交换公式。
2. 原文辛配对为 `x·y' - x'·y`；本项目 `Dyadic.pairing` 保留此符号。mathlib 的 `Matrix.J` 是其相反数对应的矩阵，保持一个形式与保持其相反数的条件等价。mathlib 同时证明左右转置约定的等价性（`SymplecticGroup.mem_iff'`）。尚未另外写出本项目 `pairing` 与矩阵群作用的连接定理。

`Pauli.Hilbert` 是有限复函数空间；酉性针对 mathlib 的标准 Hermitian **矩阵**群验证，并未误用普通函数空间的上确界范数作为 Hilbert 范数。`SchwartzBruhat` 指非阿基米德局部常值紧支撑空间，不使用实／复分析中的快速下降 `SchwartzMap`。

## 主要 mathlib 复用

| 主题 | 主要接口 |
|---|---|
| 有限群、正合性与酉实现 | `BilinearForm`、`Matrix.symplecticGroup`、`Matrix.unitaryGroup`、`Function.MulExact`、`QuotientGroup`、`Representation.IntertwiningMap` |
| 整数环、局部环与有限商 | `integralClosure`、`IsDiscreteValuationRing`、`IsLocalRing.ResidueField`、`TruncatedWittVector`、`PadicInt.toZModPow`、`Module.card_eq_pow_finrank` |
| 特征、拓扑与格 | `AddChar.IsPrimitive`、`AddChar.linearIndependent`、`Module.Baer`、`spectralNorm`、`FiniteDimensional.proper`、`IsUltrametricDist`、`LocallyConstant`、`Pi.basisFun` |
| Haar 与 Fourier | `Measure.addHaarMeasure`、`addHaarMeasure_unique`、`integral_add_right_eq_self`、`integral_integral_swap_of_hasCompactSupport`、`distribHaarChar` |
| L²、换元与酉算子 | `Lp`、`MemLp.induction_dense`、`LinearEquiv.extendOfIsometry`、`addEquivAddHaarChar`、`ContinuousLinearMap.holderL`、`Unitary.linearIsometryEquiv` |
| Gaussian 与非退化性 | `QuadraticMap.Nondegenerate`、`nondegenerate_associated_iff`、`LinearMap.BilinForm.toDual`、`integral_indicator`、`Filter.EventuallyEq`、`unitary` |

## 验证与继续工作

[Audit.lean](Audit.lean) 按声明所属的项目模块检查传递公理依赖，包括私有声明及生成在其他命名空间中的辅助声明；仅允许 Lean/mathlib 的通常基础 `propext`、`Classical.choice`、`Quot.sound`。没有 `sorry`、`admit`、自定义公理或 `native_decide`。这验证已编译声明的证明依赖；它不能代替对数学语义、原文忠实性或上述未完成项的审查。

运行 `./scripts/check.sh` 执行项目构建和公理审计。此次整理后从空的项目构建目录重新编译，
保留锁定的 mathlib 依赖缓存；旧模块构建产物未参与验证。独立审查报告见 [REVIEW.md](REVIEW.md)，
交付版本由 [docs/REVIEW_TARGET.sha256](docs/REVIEW_TARGET.sha256) 确定。
未完成的数学事项仍以覆盖表和归一化说明为准。
