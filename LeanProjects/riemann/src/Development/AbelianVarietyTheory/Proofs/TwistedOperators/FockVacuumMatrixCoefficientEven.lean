import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumMaximalCompactCharacterRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorMixedLaplacianKilledLoweringKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumEven

theorem cartan_laws {k p : ℕ} {G s B Y : Matrix (Fin k) (Fin k) ℂ} (hB : IsONBasis G s B p) (hY : IsPMat p Y) :
    (∃ κ, IsKMat p κ ∧ B * κ * B⁻¹ = s) ∧ (B * Y * B⁻¹)ᴴ * G + G * (B * Y * B⁻¹) = 0 ∧
      s * (B * Y * B⁻¹) = -(B * Y * B⁻¹ * s) := by
  obtain ⟨ε, hε, hBG, hsB⟩ := hB
  obtain ⟨hYh, hY0⟩ := hY

  have hEE : (diagonal fun a => (ε a : ℂ)) * (diagonal fun a => (ε a : ℂ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have hEh : (diagonal fun a => (ε a : ℂ))ᴴ = diagonal fun a => (ε a : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rcases hε a with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]

  have hEY : (diagonal fun a => (ε a : ℂ)) * Y = -(Y * diagonal fun a => (ε a : ℂ)) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
    by_cases hij : (i.val < p ↔ j.val < p)
    · rw [hY0 i j hij]
      simp
    · rcases hε i with ⟨hi, hip⟩ | ⟨hi, hip⟩ <;> rcases hε j with ⟨hj, hjp⟩ | ⟨hj, hjp⟩
      · exact absurd (iff_of_true hip hjp) hij
      · rw [hi, hj]
        push_cast
        ring
      · rw [hi, hj]
        push_cast
        ring
      · exact absurd (iff_of_false (not_lt.2 hip) (not_lt.2 hjp)) hij
  have hoff : ∀ i j, ¬ (i.val < p ↔ j.val < p) → (diagonal fun a => (ε a : ℂ)) i j = 0 := by
    intro i j hij
    apply Matrix.diagonal_apply_ne
    intro h
    subst h
    exact hij Iff.rfl
  generalize (diagonal fun a => (ε a : ℂ)) = E at hEE hEh hEY hoff hBG hsB

  have hdet : IsUnit B.det := by
    have h1 : (Bᴴ * G * B * E).det = 1 := by rw [hBG, hEE, Matrix.det_one]
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul] at h1
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    rw [h0] at h1
    simp at h1
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hdet
  have hc3 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi', Matrix.conjTranspose_one]
  have hc4 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  have hc1 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, B⁻¹ * (B * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hc2 : ∀ Z : Matrix (Fin k) (Fin k) ℂ, Bᴴ * ((B⁻¹)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hc4, Matrix.one_mul]
  have hs : s = B * E * B⁻¹ := by
    calc s = s * B * B⁻¹ := by rw [Matrix.mul_assoc, hBi', Matrix.mul_one]
      _ = B * E * B⁻¹ := by rw [hsB]
  have hG : G = (B⁻¹)ᴴ * E * B⁻¹ := by
    rw [← hBG]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B⁻¹)ᴴ, hc3, Matrix.one_mul, hBi', Matrix.mul_one]
  subst hs hG
  refine ⟨⟨E, ⟨?_, hoff⟩, rfl⟩, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hEh, hEE]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hYh]
    simp only [Matrix.mul_assoc, hc1, hc2]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, add_neg_cancel]
  · simp only [Matrix.mul_assoc, hc1]
    rw [← Matrix.mul_assoc E Y, hEY]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem atTau_oneP {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    {s X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hs : IsCartanInv (gramAt D V τ) s) (hX : X ∈ lieAt V τ)
    (ha : s * X = -(X * s)) (t : ℝ) : atTau θ V τ s * oneP θ V τ X t = oneP θ V τ X (-t) * atTau θ V τ s := by
  obtain ⟨hss, hsU, -⟩ := hs
  unfold oneP
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hsU (GlobalTheory.Mem.Lift.exp_mem hX t),
    ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (GlobalTheory.Mem.Lift.exp_mem hX (-t)) hsU, GlobalTheory.FockKill.conj_exp hss ha t]

theorem ipO_smul_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f g : Mx D m n → ℂ) :
    ipO μ 𝓕 (c • f) (c • g) = (Complex.normSq c : ℂ) * ipO μ 𝓕 f g := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO
  rw [← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← Complex.mul_conj]
  ring

theorem coeff_even : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ (τ : D.what₂.Tau) YS YT, IsPMat (pS τ) YS → IsPMat (pT τ) YT → BS τ * YS * (BS τ)⁻¹ ∈ lieAt S τ ∧ BT τ * YT * (BT τ)⁻¹ ∈ lieAt T τ ∧ ∀ f g, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → IsThetaFunO ψ S T g → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) g) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ t : ℝ, ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT τ YS YT hYS hYT
  obtain ⟨⟨κS, hκS, hsS⟩, hlS, haS⟩ := cartan_laws (hbS τ) hYS
  obtain ⟨⟨κT, hκT, hsT⟩, hlT, haT⟩ := cartan_laws (hbT τ) hYT
  refine ⟨hlS, hlT, ?_⟩
  intro f g hf hvf hg hvg μ 𝓕 hμ t
  obtain ⟨mS, mT, hchar⟩ := GlobalTheory.VacCharAtPlace.vacuum_char_at_place D ψ θ S T χS χT om hom hθ τ
  have hUS : sS τ ∈ Formalism.QuantumDeterminants.UH (gramAt D S τ) := by
    obtain ⟨-, h, -⟩ := hcS τ
    exact h
  have hUT : sT τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    obtain ⟨-, h, -⟩ := hcT τ
    exact h
  have hssS : sS τ * sS τ = 1 := by
    obtain ⟨h, -, -⟩ := hcS τ
    exact h
  have hssT : sT τ * sT τ = 1 := by
    obtain ⟨h, -, -⟩ := hcT τ
    exact h

  have hmul : ∀ a b φ, om a (om b φ) = om (a * b) φ := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]

  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ φ, IsThetaFunO ψ S T φ →
      (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) φ) →
      om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) φ = c • φ :=
    ⟨_, fun φ hφ hvφ => hchar sS BS sT BT pS pT hpS hpT hcS hcT hbS hbT φ hφ hvφ κS κT hκS hκT _ _
      (by rw [hsS]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ S τ hUS)
      (by rw [hsT]; exact GlobalTheory.PointAtPlaceHom.atTau_spec hθ T τ hUT)⟩
  by_cases hf0 : f = 0
  · subst hf0
    simp [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.ipO]

  have hkk : om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f) = f := by
    have h1 : ((1 : GA D S), (1 : GA D T)) = (1 : GA D S × GA D T) := rfl
    rw [hmul, Prod.mk_mul_mk, ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hUS hUS,
      ← GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hUT hUT, hssS, hssT, GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ,
      GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ, h1, map_one, Module.End.one_apply]
  rw [hc f hf hvf, map_smul, hc f hf hvf, smul_smul] at hkk
  have hcc : c * c = 1 := by
    by_contra hne
    apply hf0
    have h0 : (c * c - 1) • f = 0 := by rw [sub_smul, hkk, one_smul, sub_self]
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hn : (Complex.normSq c : ℂ) = 1 := by
    have h2 : Complex.normSq c * Complex.normSq c = 1 := by
      rw [← Complex.normSq_mul, hcc, Complex.normSq_one]
    have h3 : Complex.normSq c = 1 := by nlinarith [Complex.normSq_nonneg c]
    rw [h3, Complex.ofReal_one]

  have hconj : (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) *
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) =
      (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) *
      (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) := by
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, atTau_oneP hθ S τ (hcS τ) hlS haS (-t),
      atTau_oneP hθ T τ (hcT τ) hlT haT (-t), neg_neg]

  have hU : ∀ p φ φ', IsThetaFunO ψ S T φ → IsThetaFunO ψ S T φ' →
      ipO μ 𝓕 (om p φ) (om p φ') = ipO μ 𝓕 φ φ' := fun p φ φ' hφ hφ' =>
    GlobalTheory.WeilInner.om_inner D ψ S T χS χT om hom μ 𝓕 hμ p φ φ' hφ hφ'
  calc ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f) g
      = ipO μ 𝓕 (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ))
          (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) (-t), oneP θ T τ (BT τ * YT * (BT τ)⁻¹) (-t)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := (hU _ _ g (hom.om_pres _ f hf) hg).symm
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t)
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) f))
          (om (atTau θ S τ (sS τ), atTau θ T τ (sT τ)) g) := by
      congr 1
      rw [hmul, hmul, hconj]
    _ = ipO μ 𝓕 (c • om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) (c • g) := by
      rw [hc f hf hvf, hc g hg hvg, map_smul]
    _ = ipO μ 𝓕 (om (oneP θ S τ (BS τ * YS * (BS τ)⁻¹) t, oneP θ T τ (BT τ * YT * (BT τ)⁻¹) t) f) g := by
      rw [ipO_smul_smul, hn, one_mul]

end GlobalTheory.VacuumEven
