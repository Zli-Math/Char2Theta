# Char2Theta 结构精简独立审查报告

审查日期：2026-10-17。审查者为未参与起草的独立 reviewer；未读取既有审查报告、作者自查记录或构建日志，未递归委派。本报告覆盖本轮合并、删除及审计范围修订，不把编译成功或声明数量当作数学覆盖范围的替代证明。

## 版本与审查范围

- 原始版本：`/private/tmp/char2theta-before-structure-cleanup/`，其 `docs/REVIEW_TARGET.sha256` 的 SHA-256 为 `7462901e72a15b2c5f302e2d151ffb63d56b0771d81b29f039f43751a2492ad5`。
- 最终版本：本目录；冻结清单 [docs/REVIEW_TARGET.sha256](docs/REVIEW_TARGET.sha256) 的 SHA-256 为 `b335102411777c52d11b42c0807a0c51c81ba83b925d920a90b4123f3b00c503`。两份清单列出的文件均逐项校验通过。本报告不在冻结清单内，以免产生自引用哈希。
- 工具链：Lean `v4.32.0`；mathlib 提交 `81a5d257c8e410db227a6665ed08f64fea08e997`。所有依赖 checkout 的 HEAD 与 `lake-manifest.json` 一致；mathlib 无已跟踪文件修改。
- 范围：原始 17 个主题文件与最终 7 个主题文件、总入口、`Audit.lean`、README、构建脚本及依赖配置。核对原始 PDF 第 2–4 页的第一节和式 (2.2)–(2.3)，并检查相关公式的页面渲染。

## 总体结论

**本轮结构精简通过独立审查；最终版本没有发现需要修复的确认错误。** 合并保留了既有数学结论、参数、实例与证明，删除的是八项已列明的包装或重复接口。README 说明了旧路径和被删除名称的迁移要求，没有把已有条件性接口或部分算子关系表述为完整 metaplectic／Weil 构造。

审查发现的日常公理审计范围不足已在最终版本修订，并经过独立复查。没有遗留的阻断问题；不据此声称已完成全文形式化或获得全局最小的模块划分。

## 结构、声明及数学内容核查

最终依赖关系为 `FiniteBasics → Clifford` 与 `FiniteBasics → DyadicArithmetic → DyadicCharacter → DyadicLatticeModel → DyadicFourier → DyadicWeil`；总入口导入两条链的终点。公共特征延拓移入 `FiniteBasics` 后，局部理论不再经过 Clifford 辛提升。实际导入图无循环，八个模块（含总入口）均未检出传递冗余导入。

对去掉注释后的顶层源码声明块作配对，最终 699 块中，697 块与原版相同；另两块是 `SmoothRepresentation`、`Genuine` 中 `ComplexRepresentation` 到 `Representation ℂ` 的直接别名展开。再结合独立编译后的声明名称、类型和依赖核查，确认这不是仅凭文本数量作出的保留判断：除明确删除的八个公开名称外，没有发现其他手写公开定义、定理或实例丢失。自动生成的 `_proof_*`、`_simp_*` 名称和编号会随模块合并变化，不能据其数量变化推断数学损失。

保留公开声明的类型差异已逐类核实：宇宙参数重命名、上述别名展开、证明无关的自动证明名变化，以及定义相等的实例项。尤其对 `Pauli.Z_mul_X` 中出现的 `instDistribSMul`／`NonUnitalNonAssocSemiring.toDistribSMul`，另行以 `rfl` 验证定义相等；射影正合列相关类型中的两个自动辅助名均证明同一 `NeZero (1 + 1)`。未发现假设增强、结论弱化或隐式参数丢失。

对八项删除逐项检查原始定义、最终替代内容及原版已编译类型／证明的引用：

| 删除的名称（省略 `Char2Theta.`） | 独立核查结果 |
|---|---|
| `BilinearExtension.labelHom` | 标签投影的群同态包装；没有其他项目声明引用。标签字段及群运算公式保留。 |
| `μ` | 恰为 `rootsOfUnity r ℂ` 的别名；没有其他项目声明引用，README 明示直接复用 mathlib。 |
| `Dyadic.ComplexRepresentation` | 恰为 `Representation ℂ` 的别名；仅有 `SmoothRepresentation`、`Genuine` 两处使用，均已展开，条件不变。 |
| `Dyadic.liftedSubgroup` | 恰为 `Subgroup.comap` 的别名；没有其他项目声明引用。 |
| `binary_field_card` | 直接由 `Module.card_eq_pow_finrank` 得到的重复接口；无项目调用，实际剩余域公式仍在 `DyadicArithmetic.lean:208`。 |
| `Dyadic.smoothConductorFourCharacter` | 将已有对象及性质装入子类型的包装；无项目调用。导子、光滑性及存在性仍分别位于 `DyadicCharacter.lean:471`、`:520`、`:527`。 |
| `Dyadic.LocalQuadraticDatum.dual` | 对已有 `dualForm`、逆极化映射及其加法公式的再包装；无项目调用。相关内容保留于 `DyadicWeil.lean:863`、`:887`，配平方与非退化构造亦保留。 |
| `Dyadic.localWeilIndexUnit` | 由已知非零性构造 `ℂˣ` 的包装；无项目调用。指数、模长定理及更强的 `unitary ℂ` 标量分别保留于 `DyadicWeil.lean` 的相应定义、`:1247`、`:1333`。 |

在完整依赖上下文中，重点核对了以下内容：

- `Clifford.lean:1448` 的正合列仍同时包含左箭头单射、中间正合和右箭头满射；实际共轭作用、射影箭头识别及有限性仍保留。没有将全部 `U(1)` 标量缩成有限单位根。
- 整数环仍为 `ℤ₂` 的整闭包，`R,A` 仍是有理整数理想 `(2)`、`(4)` 的商；非分歧／分歧区别、有限性及数值公式未改变。导子仍是整环作用下的 annihilator 条件，不是普通特征核。
- `latticeSubmodule` 的支撑与 `2𝒪ⁿ` 平移不变条件、有限模型同构、delta 基、维数、根算子及生成元限制接口全部迁移；后者仍要求已有环境表示及生成条件。
- Fourier 核仍为正号 `ψ(2x·y)`，体积仍为 `vol(2𝒪ⁿ)=N^(-1/2)`、`vol(𝒪ⁿ)=N^(1/2)`。全测试函数空间上的平方是反射；格空间上的平方为恒等，两者未混同。
- 全 L² 的酉延拓、几乎处处代表元公式、Gaussian 紧域截断稳定性、单位模长 Weil 指数及 Bruhat／三次／四次关系均保留。没有把一般 L² 变换或振荡积分改称逐点绝对收敛的全空间积分。

七个主题文件均以中文导读解释内容和主要入口，内部主题小节与原证明顺序衔接。README 的所有本地链接有效，旧模块名只在迁移说明中出现；覆盖表继续区分定义、已证明结果、条件性结果和待完成内容。保留不同函数空间上的相容性公式有实际用途，不属于仅凭外观相似即可删除的重复结果。

## 独立验证

审查者在 `/private/tmp/char2theta-independent-structure-review/` 下分别建立原版与候选版的源码副本，均从不存在项目构建产物的目录开始执行 `lake build`。两次构建均成功：原版 3723 jobs，候选版 3713 jobs。

仅共享锁定的外部依赖缓存。已检查候选环境的 `LEAN_PATH`：项目部分只指向独立候选目录，未包含主项目或原版项目的构建路径。候选生成的项目 `.olean` 只有七个新主题和总入口，不存在任何被删除模块的旧产物。因此该构建没有靠旧模块缓存掩盖缺失导入。

另行导出两个环境中项目声明的类型指纹和实际常量依赖，检查被删名称的引用及公开接口迁移。对类型差异进一步查看显式类型并核实实例及辅助证明，没有仅凭源码搜索认定未使用。

通过 importGraph 的 `Environment.findRedundantImports` 对最终全部项目模块检查，结果均为空。此项确认最终依赖状态；未独立重演 README 所述删除 62 条导入的中间操作记录。

除运行项目 `Audit.lean` 外，审查者另写按模块归属筛选的检查，遍历包括私有及其他命名空间辅助声明的全部项目模块常量，核查传递公理依赖。最终修订的 `Audit.lean` 已在上述独立候选目录重跑，输出为：

```text
Audited 1242 declarations from Char2Theta modules (including private and generated declarations): only propext, Classical.choice, Quot.sound allowed.
```

没有发现 `sorryAx` 或其他不允许的公理。源码亦未发现 `sorry`、`admit`、自定义公理或 `native_decide` 的使用。最终冻结后数学模块与独立重建版本逐字一致；后续仅有审计及 README 修订，均已复查，最终清单再次逐项校验通过。

## 问题与修订复查

### 已解决：低严重性，审计筛选范围不足

- **位置**：初审版 `Audit.lean:22`；最终版 `Audit.lean:21–23`，README“验证与继续工作”。
- **证据**：初审按 `Char2Theta`／`_private.Char2Theta` 名称前缀筛选，审计 1240 项；按所属模块检查还发现 `QuadraticMap.proj.congr_simp`、`Homeomorph.addRight.congr_simp` 两项自动声明。
- **影响**：日常检查未把这两项分别列为审计起点，范围描述不够完整；独立检查确认它们均无异常公理，未发现当前数学证明被污染。
- **修订及复查**：主代理改用 `env.getModuleIdxFor?` 与所属模块名称筛选，更新导读和 README。最终版独立运行覆盖 1242 项并通过，与审查者单独实现的模块归属检查一致。此项已关闭。

**最终未解决的确认错误：无。未验证且有具体证据指向错误的疑虑：无。其他必须实施的精简建议：无。** 模块规模和内部小节已形成可读的七主题组织，不要求为了减少文件数量继续合并互不相干的理论。

## 兼容性与验证边界

旧的直接模块导入路径及八个删除名称不再可用，这是已说明的迁移影响；仅使用总入口的项目导入保持可用。未取得外部下游项目，故未实际编译其迁移代码，也不保证自动辅助声明名称的稳定性。

本次核验使用已有外部依赖缓存，没有从零重建 Lean 或全部 mathlib，也没有验证外部参考文献或原文第 2–18 节的全部论证。检查未发现迁移造成的数学损失，但不构成对所有既有数学内容的重新独立推导。

项目仍未构造具体 metaplectic 二重覆盖、规范提升、完整 Weil 表示与原文 `τ_L`，也未证明覆盖表列明的 K-type、归一化秩一 Weil 指数的单位根阶数／平方类不变性／Hilbert 符号公式等事项。内在 Haar 模量与行列式绝对值的连接、Pontryagin 对偶空间及部分几何结构连接亦仍在 README 明示的边界内。这些既有未形式化内容没有因结构整理而被宣称完成。
