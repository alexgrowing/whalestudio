import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.IsoLineCarry

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_smul (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : E) (u : Fin n → E) :
    Formalism.UG.hform (σ : E →+* E) J (b • u) (a • u) = σ b * a * Formalism.UG.hform (σ : E →+* E) J u u := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [AlgHom.coe_toRingHom]
  ring

theorem exists_unitary_isotropic (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : IsHermND σ J) (x z : Fin n → E) (hx : x ≠ 0) (hz : z ≠ 0) (hxx : hE σ J x x = 0) (hzz : hE σ J z z = 0) :
    ∃ g : GL (Fin n) E, g ∈ Formalism.UG.UJ (σ : E →+* E) J ∧ (g : Matrix (Fin n) (Fin n) E) *ᵥ x = z := by
  have hxx' : Formalism.UG.hform (σ : E →+* E) J x x = 0 := hxx
  have hzz' : Formalism.UG.hform (σ : E →+* E) J z z = 0 := hzz
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.HermWitt.exists_gl_isometry_comp_eq (c := (σ : E →+* E)) (G := Jᵀ) two_ne_zero
    (GlobalTheory.RatOrbit.sigma_sigma σ hCM) (fun a b => hJ.1 a b) (by rw [Matrix.det_transpose]; exact hJ.2)
    (g := LinearMap.toSpanSingleton E _ x) (f := LinearMap.toSpanSingleton E _ z)
    (fun a => by simp [LinearMap.toSpanSingleton_apply, smul_eq_zero, hx, hz])
    (fun a b => by
      simp only [LinearMap.toSpanSingleton_apply]
      rw [← GlobalTheory.RatOrbit.hform_eq, ← GlobalTheory.RatOrbit.hform_eq, hform_smul, hform_smul, hxx', hzz'])
  refine ⟨g, GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun a b => ?_, ?_⟩
  · rw [GlobalTheory.RatOrbit.hform_eq, GlobalTheory.RatOrbit.hform_eq]; exact hg b a
  · simpa using hgx 1

theorem col0v_isotropic_ne_zero (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}
    {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hX : IsWittFrame σ J X Y) :
    GlobalTheory.EisMidHt.firstColumn X ≠ 0 ∧ hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn X) = 0 := by
  constructor
  · intro h0
    have h := congrFun (congrFun hX.xy 0) 0
    have hc : ∀ i, X i 0 = 0 := fun i => congrFun h0 i
    simp [Matrix.mul_apply, Formalism.UG.cT, hc] at h
  · have h := congrFun (congrFun hX.xx 0) 0
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Finset.sum_mul] at h
    show Formalism.UG.hform (σ : E →+* E) J _ _ = 0
    rw [Formalism.UG.hform, Finset.sum_comm]
    exact h

theorem adMat_col0_mulVec {n : ℕ} {r : ℕ} (X : Matrix (Fin n) (Fin (r + 1)) E) :
    adMat F (col0 X) *ᵥ (fun _ => 1) = GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) := by
  funext i
  simp [Matrix.mulVec, dotProduct, col0, GlobalTheory.EisMidHt.adVec, GlobalTheory.EisMidHt.firstColumn]

theorem bc_mulVec_adVec {n : ℕ} (h : GL (Fin n) E) (x : Fin n → E) :
    ((Formalism.UG.bc (inclR (F := F) (AF F)) h : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *ᵥ
      GlobalTheory.EisMidHt.adVec F x = GlobalTheory.EisMidHt.adVec F ((h : Matrix (Fin n) (Fin n) E) *ᵥ x) := by
  funext i
  exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ _ i).symm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
        (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F (col0 X) = l.1 • adMat F (col0 X)) →
    ∀ z : Fin n → E, z ≠ 0 → hE σ J z z = 0 →
      ∃ t ∈ T, ∃ c : E, c ≠ 0 ∧
        (matHom _ σ J (t : GAd σ J)⁻¹).1 *ᵥ GlobalTheory.EisMidHt.adVec F (GlobalTheory.EisMidHt.firstColumn X) = GlobalTheory.EisMidHt.adVec F (c • z) := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hJ hX T hT z hz hzz
  obtain ⟨hx0, hxx⟩ := col0v_isotropic_ne_zero σ J hX
  obtain ⟨g, hgU, hgx⟩ := exists_unitary_isotropic σ hCM J hJ _ z hx0 hz hxx hzz
  let ι : E →+* AF F ⊗[F] E := inclR (F := F) (AF F)
  have hbc : ∀ h : GL (Fin n) E, h ∈ Formalism.UG.UJ (σ : E →+* E) J → Formalism.UG.bc ι h ∈ HR (AF F) σ J := fun h hh =>
    GlobalTheory.RatOrbit.bc_mem ι (σ : E →+* E) (sigR (AF F) σ) (fun t => by simp [ι, inclR, sigR]) J h hh
  let γ0 : GAd σ J := ⟨Formalism.UG.bc ι g⁻¹, hbc _ (inv_mem hgU)⟩
  have hγ0 : γ0 ∈ ratPts σ J := by
    show (γ0 : HR (AF F) σ J) ∈ HFinIn (AF F) σ J
    exact ⟨g⁻¹, inv_mem hgU, rfl⟩
  obtain ⟨t, ⟨htT, l, hl⟩, -⟩ := hT ⟨γ0, hγ0⟩
  obtain ⟨g', hg'U, hg'⟩ := t.2
  have hMt : matHom (AF F) σ J (t : GAd σ J) = Formalism.UG.bc ι g' := hg'.symm
  have hMt' : matHom (AF F) σ J (t : GAd σ J)⁻¹ = Formalism.UG.bc ι g'⁻¹ := by rw [map_inv, hMt, map_inv]
  have hMγ : matHom (AF F) σ J γ0 = Formalism.UG.bc ι g⁻¹ := rfl
  set w : Fin n → E := ((g'⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ GlobalTheory.EisMidHt.firstColumn X with hw
  have hv := congrArg (fun M => M *ᵥ (fun _ : Fin 1 => (1 : AF F ⊗[F] E))) hl
  have hmul : ((⟨γ0, hγ0⟩ * t⁻¹ : ratPts σ J) : GAd σ J) = γ0 * (t : GAd σ J)⁻¹ := rfl
  rw [hmul, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, adMat_col0_mulVec,
    Matrix.smul_mulVec, adMat_col0_mulVec, hMt', hMγ, bc_mulVec_adVec, bc_mulVec_adVec] at hv

  have hw' : GlobalTheory.EisMidHt.adVec F w = l.1 • GlobalTheory.EisMidHt.adVec F z := by
    have key : GlobalTheory.EisMidHt.adVec F w = ((Formalism.UG.bc ι g : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ
        GlobalTheory.EisMidHt.adVec F (((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ w) := by
      rw [bc_mulVec_adVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [key, hv, Matrix.mulVec_smul, bc_mulVec_adVec, hgx]
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra h; push_neg at h; exact hz (funext h)
  have hinj := GlobalTheory.RatOrbit.inclR_injective F E
  have hwi : ι (w i) = l.1 * ι (z i) := congrFun hw' i
  have hwi0 : w i ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hwi
    have : ι (z i) = 0 := by
      have := congrArg (fun a => (l⁻¹ : (AF F ⊗[F] E)ˣ).1 * a) hwi
      simpa [← mul_assoc] using this.symm
    exact hi (hinj (by rw [this, map_zero]))
  refine ⟨t, htT, w i / z i, div_ne_zero hwi0 hi, ?_⟩
  have hl' : l.1 = ι (w i / z i) := by
    rw [div_eq_mul_inv, map_mul, hwi, mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, mul_one]
  rw [hMt', bc_mulVec_adVec, ← hw, hw']
  funext j
  simp only [GlobalTheory.EisMidHt.adVec, Pi.smul_apply, smul_eq_mul, hl', map_mul]
  rfl

end GlobalTheory.IsoLineCarry
