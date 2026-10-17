import Char2Theta.Section1.Clifford
import Char2Theta.Section1.DyadicWeil

/-!
# 第一节 Notation and conventions：总入口与阅读顺序

`import Char2Theta` 导入第一节的全部已形式化内容。入口只导入有限群与局部分析
两条依赖链的终点；详细覆盖范围及旧路径迁移见 `README.md`。
每个主题文件开头均有中文内容总览。

* `FiniteBasics`：共用的中心扩张、有限坐标、复相位及特征延拓工具。
* `Clifford`：Pauli、Heisenberg、自同构与辛提升，直到 Clifford 正合列 (1.1)。
* `DyadicArithmetic`：整数环、DVR、剩余域、数值公式及商环比较。
* `DyadicCharacter`：局部拓扑、导子、有限核障碍及光滑特征存在性。
* `DyadicLatticeModel`：紧开格、局部／有限函数模型、delta 基和根算子。
* `DyadicFourier`：Fourier 积分、有限限制、自对偶归一化、反演和 Plancherel。
* `DyadicWeil`：完整 L² 上的酉算子、Gaussian 积分、Weil 指数与具体酉群关系。

完整 metaplectic 覆盖、Weil 表示及原文的 `τ_L` 仍属待完成内容。
`Audit.lean` 单独检查所有项目声明的公理依赖。
-/
