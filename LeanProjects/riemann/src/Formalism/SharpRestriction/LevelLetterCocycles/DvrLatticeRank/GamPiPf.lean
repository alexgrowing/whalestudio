import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantUniformizer

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gampi_delta {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T δ (W.γD T W.gamK x - x) = W.γD T W.gamK x - x := by
  intro δ hδ
  rw [map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

theorem gampi_letter (c : ZMod n) {x : W.DD T} (hx : x ∈ letS W T c) :
    W.γD T W.gamK x - x ∈ letS W T c := by
  have hl : letγ (W.γ₀ W.gamK) (letE c : LetA O n) = letE c := by
    funext j
    show W.γ₀ W.gamK ((letE c : LetA O n) j) = (letE c : LetA O n) j
    rcases eq_or_ne j c with rfl | h
    · simp [letE]
    · simp [letE, Pi.single_apply, h]
  have key : ∀ y : W.DD T, W.γD T W.gamK ((letE c : LetA O n) • y) = (letE c : LetA O n) • W.γD T W.gamK y := by
    intro y
    rw [← algebraMap_smul W.EE (letE c : LetA O n) y, W.γD_smul, W.γE_ext, hl, algebraMap_smul]
  unfold letS at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply] at hx ⊢
  rw [smul_sub, ← key, sub_eq_zero.1 hx, sub_self]

theorem gampi_local (π' π'₀ u : LetA O n) (hu : π'₀ = u * π')
    (hm : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γD T W.gamK x - x = π'₀ • x') :
    GamPi W T π' := by
  intro c x hx
  unfold NcS at hx
  rw [Submodule.mem_inf, Submodule.mem_inf] at hx
  obtain ⟨⟨hxN, hxD⟩, hxL⟩ := hx
  rw [Submodule.restrictScalars_mem] at hxN
  have hxfix : ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro δ hδ
    unfold DelS at hxD
    have h1 := (Submodule.mem_iInf _).1 hxD δ
    have h2 := (Submodule.mem_iInf _).1 h1 hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h2
    exact h2
  have hxΔ : x ∈ W.NΔ T := show x ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x from ⟨hxN, hxfix⟩
  obtain ⟨x', hx'mem, hx'⟩ := hm x hxΔ
  have hx'N : x' ∈ W.N T := (show x' ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ x' = x' from hx'mem).1
  rw [Submodule.mem_inf]
  refine ⟨?_, gampi_letter W T c hxL⟩
  unfold PiNS
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    unfold Formalism.MainNotions.DeltaInvariantLattices.aN
    refine Submodule.mem_map.2 ⟨u • x', (W.N T).smul_mem u hx'N, ?_⟩
    unfold Formalism.MainNotions.DeltaInvariantLattices.smulA
    rw [LinearMap.smul_apply, LinearMap.id_apply, hx', hu, pow_one, smul_smul, mul_comm]
  · unfold DelS
    rw [Submodule.mem_iInf]
    intro δ
    rw [Submodule.mem_iInf]
    intro hδ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact gampi_delta W T hxfix δ hδ

end Local

theorem gamPiCondition : GamPiStep := by
  intro D HW F Cm CA CB CK hA l _ hl K LL hG π' E hp9 T hcrys
  have hT1 := hA.1 l K 1 LL hG
  have hP9 := hT1.2.2.2.2.2.2.2.2.1
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hp]; exact hl
  obtain ⟨-, ⟨π₁, E₁, hr₁, hm₁⟩, -⟩ := hP9 T hcrys hs1 hp2
  obtain ⟨w₁, hw₁⟩ := hr₁.2.2.1
  obtain ⟨w, hw⟩ := hp9.2.2.1
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2
  refine gampi_local _ T π' π₁ ((w₁ * w⁻¹ : (LetA _ _)ˣ) : LetA _ _) ?_ ?_
  · rw [hw₁, hw, hp, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  · intro x hx
    obtain ⟨x', hx', h⟩ := hm₁.2 x hx
    exact ⟨x', hx', by rw [hgam]; exact h⟩

end Formalism.MainNotions.N.Ln34

end
