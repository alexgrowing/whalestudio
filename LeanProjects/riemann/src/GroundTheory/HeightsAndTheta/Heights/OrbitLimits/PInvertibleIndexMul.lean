import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PInvertibleIdealIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.POrderIdealIndexExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt

noncomputable section

namespace InvertibleIndexMultiplicative

variable {Ω : Type} [Field Ω]

theorem index_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {I : Ideal B} (hI : I ≠ ⊥) :
    I.toAddSubgroup.index ≠ 0 := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨c, hc, q, hq⟩ := OrderIdealIndexExtensionAlt.exists_int_eq_mul ha
  refine OrderIdealIndexExtensionAlt.index_ne_zero_of_zsmul_mem _ hc fun x => ?_
  have e : c • x = a * (q * x) := by rw [zsmul_eq_mul, hq, mul_assoc]
  rw [Submodule.mem_toAddSubgroup, e]
  exact I.mul_mem_right _ haI

theorem relIndex_mulBy_ne_zero [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by
  rw [map_mul_eq, relIndex_map_subtype]
  exact index_ne_zero (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hβ)

theorem relIndex_mulBy_mul {B : Subring Ω} {x y : Ω} (hx : x ≠ 0) (hxB : x ∈ B) (hyB : y ∈ B) :
    (B.toAddSubgroup.map (mulBy (x * y))).relIndex B.toAddSubgroup =
      (B.toAddSubgroup.map (mulBy x)).relIndex B.toAddSubgroup *
        (B.toAddSubgroup.map (mulBy y)).relIndex B.toAddSubgroup := by
  have e : B.toAddSubgroup.map (mulBy (x * y)) = (B.toAddSubgroup.map (mulBy y)).map (mulBy x) := by
    rw [AddSubgroup.map_map]
    congr 1
    ext z
    simp [mul_assoc]
  have h1 : B.toAddSubgroup.map (mulBy y) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hyB hz
  have h2 : B.toAddSubgroup.map (mulBy x) ≤ B.toAddSubgroup := by
    rintro _ ⟨z, hz, rfl⟩; exact B.mul_mem hxB hz
  rw [e, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono h1) h2,
    AddSubgroup.relIndex_map_map_of_injective (f := mulBy x) _ _ (mulBy_injective hx), mul_comm]

theorem ne_bot_of_rep {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by
  intro hI
  obtain ⟨⟨x, hxX⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hX0
  obtain ⟨y, hy, hxy⟩ := (hX x).1 hxX
  rw [hI, Ideal.mem_bot] at hy
  subst hy
  have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  simp [hβL, hx] at hxy

theorem genIndex_rep [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {X : AddSubgroup Ω} {β δ : B}
    {I : Ideal B} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hI : I ≠ ⊥)
    (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) :
    genIndex X B.toAddSubgroup = ((B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup : ℝ) /
      (((B.toAddSubgroup.map (mulBy (δ : Ω))).relIndex B.toAddSubgroup : ℝ) * (I.toAddSubgroup.index : ℝ)) := by
  have hβL : (β : Ω) ≠ 0 := fun h => hβ (Subtype.ext h)
  have hδL : (δ : Ω) ≠ 0 := fun h => hδ (Subtype.ext h)
  have g := genIndex_eq (X := B.toAddSubgroup) (J := I.toAddSubgroup.map B.subtype.toAddMonoidHom)
    (M := X) hβL hδL
    (by rintro _ ⟨y, _, rfl⟩; exact y.2)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem β.2 hy)
    (by rintro _ ⟨y, hy, rfl⟩; exact B.mul_mem δ.2 hy)
    (by rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨β * y, I.mul_mem_left β hy, rfl⟩)
    (by
      intro x
      rw [hX x]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨y, ⟨y, hy, rfl⟩, h⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
        exact ⟨y, hy, h⟩)
    (by rw [relIndex_map_subtype]; exact index_ne_zero hI)
    (relIndex_mulBy_ne_zero hδ)
  rwa [relIndex_map_subtype] at g

end InvertibleIndexMultiplicative

open InvertibleIndexMultiplicative in

theorem InvertibleIndexMul.proof (h1 : LocalGenFamily.Statement) (h2 : LocallyPrincipalCoprimeField.Statement)
    (h3 : InvertibleProductRep.Statement) (h4 : InvertibleIndexCharP.Statement) :
    InvertibleIndexMul.Statement := by
  intro Ω _ B M N P η _ g h hB hM hN hP hg0 hh0 hgc hhc hloc
  have hlocM : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B M m (g i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.1
  have hlocN : ∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B N m (h i) :=
    fun m hm => (hloc m hm).imp fun _ hi => hi.2.1
  by_cases hc : ringChar Ω ≠ 0
  · rw [h4 Ω B M η g hc hB hM hg0 hlocM, h4 Ω B N η h hc hB hN hh0 hlocN,
      h4 Ω B P η (fun i => g i * h i) hc hB hP (fun i => mul_ne_zero (hg0 i) (hh0 i))
        (fun m hm => (hloc m hm).imp fun _ hi => hi.2.2)]
    norm_num
  push Not at hc
  have : CharP Ω 0 := ringChar.eq_iff.mp hc
  have : CharZero Ω := CharP.charP_to_charZero Ω
  have := hB
  obtain ⟨hM0, ιM, _, aM, haM, hdM, hlM⟩ := h1 Ω B M η g hB hM hg0 hgc hlocM
  obtain ⟨β, δ, I, hβ, hδ, -, hMI⟩ := h2 Ω B M ιM aM hB hM haM hdM hlM hM0 1 one_ne_zero
  have hI0 := ne_bot_of_rep hβ hM0 hMI
  obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  obtain ⟨hN0, ιN, _, aN, haN, hdN, hlN⟩ := h1 Ω B N η h hB hN hh0 hhc hlocN
  obtain ⟨β', δ', J, hβ', hδ', hJt, hNJ⟩ := h2 Ω B N ιN aN hB hN haN hdN hlN hN0 t ht0
  have hJ0 := ne_bot_of_rep hβ' hN0 hNJ
  have hIJ : I ⊔ J = ⊤ := by
    rw [eq_top_iff, ← hJt, sup_comm I J]
    exact sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr htI) _
  have hPr := h3 Ω B M N P η g h β δ β' δ' I J hβ hδ hβ' hδ' hMI hNJ hP hloc
  have hIJ0 : I * J ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot]
    tauto
  have hidx : (I * J).toAddSubgroup.index = I.toAddSubgroup.index * J.toAddSubgroup.index :=
    cardQuot_mul_of_coprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)
  have hβL : (β : Ω) ≠ 0 := fun e => hβ (Subtype.ext e)
  have hδL : (δ : Ω) ≠ 0 := fun e => hδ (Subtype.ext e)
  rw [genIndex_rep hβ hδ hI0 hMI, genIndex_rep hβ' hδ' hJ0 hNJ,
    genIndex_rep (mul_ne_zero hβ hβ') (mul_ne_zero hδ hδ') hIJ0 hPr, hidx, Subring.coe_mul, Subring.coe_mul,
    relIndex_mulBy_mul hβL β.2 β'.2, relIndex_mulBy_mul hδL δ.2 δ'.2]
  have p1 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ)
  have p2 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ)
  have p3 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hβ')
  have p4 := Nat.pos_of_ne_zero (relIndex_mulBy_ne_zero hδ')
  have p5 := Nat.pos_of_ne_zero (index_ne_zero hI0)
  have p6 := Nat.pos_of_ne_zero (index_ne_zero hJ0)
  refine ⟨by positivity, by positivity, ?_⟩
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Targets
