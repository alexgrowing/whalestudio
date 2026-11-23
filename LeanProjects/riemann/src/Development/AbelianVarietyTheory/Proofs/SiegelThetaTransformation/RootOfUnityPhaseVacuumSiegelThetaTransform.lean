import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMul
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticEqParabolicJParabolicJParabolic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsWeilOfSymplectic
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMu
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPhStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualVacuumGaussianShapeRootOfUnityPhases
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSIntertwines
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TransSUnique
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelParabolicTransformPhaseStatement

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.WeilPV

variable {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem trans_unique {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ ψ' : Matrix κ ι ℚ → ℂ} (h1 : IsSB ψ) (h2 : IsSB ψ') (t1 : TransS σ φ ψ)
    (t2 : TransS σ φ ψ') : ψ = ψ' := by
  obtain ⟨hd, hs, -⟩ := GlobalTheory.SiegelAction.symplectic_action ι σ hσ _ (I_mem_siegel (ι := ι))
  refine GlobalTheory.SW.eq_of_thS_eq κ ι ψ ψ' h1 h2 _ hs fun ζ => ?_
  have e1 := t1 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e2 := t2 _ I_mem_siegel (fun k => ζ k ᵥ* spDen σ (I • 1))
  have e := e1.trans e2.symm
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
    Matrix.vecMul_one] at e
  exact e

omit [DecidableEq ι] in

theorem thS_smul (c : ℂ) (φ : Matrix κ ι ℚ → ℂ) (τ : Matrix ι ι ℂ) (ζ : κ → ι → ℂ) :
    thS (c • φ) τ ζ = c * thS φ τ ζ := by
  unfold thS
  rw [← tsum_mul_left]
  exact tsum_congr fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem trans_smul {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} {φ ψ : Matrix κ ι ℚ → ℂ} (c : ℂ)
    (t : TransS σ φ ψ) : TransS σ (c • φ) (c • ψ) := fun τ hτ ζ => by
  rw [thS_smul, thS_smul, t τ hτ ζ]; ring

omit [DecidableEq ι] in

theorem sb_smul (c : ℂ) {φ : Matrix κ ι ℚ → ℂ} (h : IsSB φ) : IsSB (c • φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx => h1 x fun h0 => hx ?_, fun x y hy => ?_⟩
  · simp [h0]
  · simp [h2 x y hy]

theorem vac_trans {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ} (hσ : σ ∈ Matrix.symplecticGroup ι ℚ)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : ∃ A ε, VacS A ε φ) :
    ∃ A ε, VacS A ε ψ := by
  obtain ⟨A, ε, h⟩ := h
  obtain ⟨T, hom, hT⟩ := GlobalTheory.Phase.transS_intertwines κ ι σ hσ
  have mem : ∀ y, y ∈ A.map T.toAddMonoidHom ↔ T.symm y ∈ A := fun y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa using hz, fun hy => ⟨_, hy, by simp⟩⟩
  have hom' : ∀ y y', om (T.symm y) (T.symm y') = om y y' := fun y y' => by
    rw [← hom]; simp
  refine ⟨A.map T.toAddMonoidHom, fun y => ε (T.symm y), ?_, ?_, ?_, ?_, ?_, hψ, ?_⟩
  · obtain ⟨S, hS⟩ := h.fg
    classical
    exact ⟨S.image T, by rw [← hS, AddMonoidHom.map_closure]; simp⟩
  · intro y
    rw [mem, h.dual]
    constructor
    · intro H y' hy'
      rw [← hom']; exact H _ ((mem _).1 hy')
    · intro H y' hy'
      have := H (T y') ((mem _).2 (by simpa using hy'))
      rw [← hom'] at this
      simpa using this
  · intro y hy; exact h.norm _ ((mem _).1 hy)
  · intro y hy y' hy'
    rw [map_add, h.semi _ ((mem _).1 hy) _ ((mem _).1 hy'), hom']
  · obtain ⟨m, hm, H⟩ := h.ord
    exact ⟨m, hm, fun y hy => by rw [map_nsmul]; exact H _ ((mem _).1 hy)⟩
  · intro y hy
    have t1 := trans_smul (ε (T.symm y)) (hT φ ψ h.sb hψ t (T.symm y))
    rw [h.fix _ ((mem _).1 hy), T.apply_symm_apply] at t1
    exact trans_unique hσ (sb_smul _ (GlobalTheory.SW.heisS_laws _ _ _ _ ψ hψ).1) hψ t1 t

omit [DecidableEq ι] in

theorem pv_sb {φ : Matrix κ ι ℚ → ℂ} (h : PV φ) : IsSB φ := by
  obtain ⟨⟨_, _, h⟩, -⟩ := h
  exact h.sb

theorem pv_parabolic (he : Even (Fintype.card κ)) {σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (h0 : σ.toBlocks₂₁ = 0)
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS σ φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans hσ hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.T.siegelParabolic_transform_values_rootOfUnity κ ι he σ hσ h0 φ ψ (pv_sb h) hψ t y
  rw [e]; exact hu.mul (h.2 _)

theorem pv_J (he : Even (Fintype.card κ))
    {φ ψ : Matrix κ ι ℚ → ℂ} (hψ : IsSB ψ) (t : TransS (Matrix.J ι ℚ) φ ψ) (h : PV φ) : PV ψ := by
  refine ⟨vac_trans (SymplecticGroup.J_mem ι ℚ) hψ t h.1, fun y => ?_⟩
  obtain ⟨u, y', hu, e⟩ := GlobalTheory.Phase.val_trans_J κ ι he φ ψ (pv_sb h) hψ t y
  rw [e]
  exact hu.mul (GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase κ ι _
    ((GlobalTheory.Phase.shape_conj_chr_mul κ ι φ ((GlobalTheory.Phase.VacShape.vacuum_shape κ ι φ).2.1 h)).2.1 y'))

theorem pv_mul (he : Even (Fintype.card κ)) {σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ}
    (hσ : σ ∈ Matrix.symplecticGroup ι ℚ) (hσ' : σ' ∈ Matrix.symplecticGroup ι ℚ)
    (H : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ)
    (H' : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ' φ ψ → PV φ → PV ψ) :
    ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (σ' * σ) φ ψ → PV φ → PV ψ := by
  intro φ ψ hψ t h
  obtain ⟨w, hw⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ he hσ
  obtain ⟨w', hw'⟩ := GlobalTheory.SW.exists_weil_of_symplectic κ ι σ' he hσ'
  obtain ⟨s1, t1, -⟩ := hw φ (pv_sb h)
  obtain ⟨s2, t2, -⟩ := hw' (w φ) s1
  have t3 := GlobalTheory.SW.transS_comp κ ι σ σ' hσ hσ' _ _ _ t1 t2
  rw [trans_unique (mul_mem hσ' hσ) hψ s2 t t3]
  exact H' _ _ s2 t2 (H _ _ s1 t1 h)

theorem pv_of_transS : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], Even (Fintype.card κ) → ∀ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS σ φ ψ → PV φ → PV ψ := by
  intro κ ι _ _ _ he σ hσ
  obtain ⟨p₁, h1, p₂, h2, p₃, h3, z1, z2, z3, rfl⟩ :=
    GlobalTheory.SW.symplectic_eq_parabolic_J_parabolic_J_parabolic ι σ hσ
  have hJ := SymplecticGroup.J_mem ι ℚ
  have P : ∀ p ∈ Matrix.symplecticGroup ι ℚ, p.toBlocks₂₁ = 0 →
      ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS p φ ψ → PV φ → PV ψ :=
    fun p hp z φ ψ hψ t h => pv_parabolic he hp z hψ t h
  have Q : ∀ φ ψ : Matrix κ ι ℚ → ℂ, IsSB ψ → TransS (Matrix.J ι ℚ) φ ψ → PV φ → PV ψ :=
    fun φ ψ hψ t h => pv_J he hψ t h
  have a := mul_mem h1 hJ
  have b := mul_mem a h2
  have c := mul_mem b hJ
  exact pv_mul he h3 c (P _ h3 z3) (pv_mul he hJ b Q (pv_mul he h2 a (P _ h2 z2)
    (pv_mul he hJ h1 Q (P _ h1 z1))))

end GlobalTheory.Phase.WeilPV
