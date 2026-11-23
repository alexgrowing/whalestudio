import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutSer
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.HermitianFormRealCoordinateMatrixHermitianDetNeZ
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourierStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal

noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW.Trc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

theorem sgsg (C : Ctx σ B JS JT ξ₀ θ ι) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [C.good.cm.2.2.2 τ, C.good.cm.2.2.2 τ, star_star]

theorem piWF_add (x y : WOF F E nS nT) : piWF θ (x + y) = piWF θ x + piWF θ y := (piWA θ).map_add x y

theorem piWF_of_fin {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : piWF θ u = 0 := by
  funext p
  show θ p.2 (infPartF F E (u p.1.1 p.1.2)) = 0
  rw [show infPartF F E (u p.1.1 p.1.2) = 0 from congrFun (congrFun hu p.1.1) p.1.2, map_zero]

theorem coe_finRatF (y : Matrix (Fin nT) (Fin nS) E) :
    (finRatF F y : WOF F E nS nT) = finIdem F E • ratWF (F := F) y := rfl

theorem iota_fin (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) : (iotaVF ι v).map (finPartF F E) = 0 := by
  funext i j
  exact C.chart.fin _

theorem symplOHF_act (C : Ctx σ B JS JT ξ₀ θ ι) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF
  rw [symplOF_actOF C]

theorem actOF_zero' (g : GAF σ JS) (h : GAF σ JT) : actOF σ JS JT g h (0 : WOF F E nS nT) = 0 := by
  unfold actOF
  rw [Matrix.mul_zero, Matrix.zero_mul]

theorem symplOHF_zero_left' (y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ 0 y = 0 := by
  have h := GlobalTheory.HeisLineF.symplOHF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y
  rw [add_zero] at h
  linear_combination -h

theorem ratWF_eq (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    ratWF (F := F) y = iotaVF ι (infRatF (tauB B) y) + (finRatF F y : WOF F E nS nT) := by
  rw [add_comm, ← piWF_ratWF C y]
  exact finIdem_add_iota C.chart _

theorem beta_fin (C : Ctx σ B JS JT ξ₀ θ ι) (x y : Matrix (Fin nT) (Fin nS) E) :
    B.ψ (symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (finRatF F y)) *
      Complex.exp (-(Real.pi * Complex.I) *
        (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) x) (infRatF (tauB B) y) : ℝ)) = 1 := by
  have h1 := psi_rat C x y
  have h2 := beta_iota_left C (infRatF (tauB B) x) (ratWF (F := F) y)
  have h3 := beta_iota_right C (finRatF F x : WOF F E nS nT) (infRatF (tauB B) y)
  rw [piWF_of_fin (finRatF F x).fin, LinearMap.map_zero, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at h3
  have d1 : symplOHF σ JS JT ξ₀ (ratWF x) (ratWF y) =
      symplOHF σ JS JT ξ₀ (iotaVF ι (infRatF (tauB B) x)) (ratWF y) +
        symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (ratWF y) := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_left, ← ratWF_eq C]
  have d2 : symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (ratWF y) =
      symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (iotaVF ι (infRatF (tauB B) y)) +
        symplOHF σ JS JT ξ₀ (finRatF F x : WOF F E nS nT) (finRatF F y) := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_right, ← ratWF_eq C]
  rw [d1, d2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h2, h3, one_mul, mul_comm, piWF_ratWF C] at h1
  exact h1

theorem chiLat_add_iota (C : Ctx σ B JS JT ξ₀ θ ι) (x : WOF F E nS nT) (v : IxF F nS nT → ℂ) :
    chiLatF σ JS JT ξ₀ B.ψ Λ w (x + iotaVF ι v) = chiLatF σ JS JT ξ₀ B.ψ Λ w x := by
  unfold chiLatF
  rw [smul_add, finIdem_smul_of_real (iota_fin C v), add_zero]

theorem ratWF_injective (C : Ctx σ B JS JT ξ₀ θ ι) :
    Function.Injective (ratWF (F := F) : Matrix (Fin nT) (Fin nS) E → WOF F E nS nT) := fun x y h =>
  infRatF_injective B (by rw [← piWF_ratWF C, ← piWF_ratWF C, h])

def ratEquivF (C : Ctx σ B JS JT ξ₀ θ ι) : Matrix (Fin nT) (Fin nS) E ≃ ratLF F E nS nT :=
  Equiv.ofBijective (fun y => ⟨ratWF y, y, rfl⟩)
    ⟨fun _ _ h => ratWF_injective C (congrArg Subtype.val h), by rintro ⟨_, y, rfl⟩; exact ⟨y, rfl⟩⟩

theorem coe_ratEquivF (C : Ctx σ B JS JT ξ₀ θ ι) (y : Matrix (Fin nT) (Fin nS) E) :
    (ratEquivF C y : WOF F E nS nT) = ratWF y := rfl

theorem piWA_apply (x : WOF F E nS nT) : piWA θ x = piWF θ x := rfl

theorem iotaA_apply (v : IxF F nS nT → ℂ) : iotaA (nS := nS) (nT := nT) ι v = iotaVF ι v := rfl

theorem serF_eq (C : Ctx σ B JS JT ξ₀ θ ι) (a : IxF F nS nT → ℂ) (x : WOF F E nS nT) :
    serF σ JS JT ξ₀ B θ ι s Λ w a x = ∑' y : Matrix (Fin nT) (Fin nS) E,
      B.ψ (symplOHF σ JS JT ξ₀ (ratWF y) x) * B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι a) (ratWF y + x)) *
        chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + x) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y + (a + piWF θ x))
          (jV s (infRatF (tauB B) y + (a + piWF θ x))) : ℝ)) := by
  unfold serF GlobalTheory.HeisenbergGaussianSeries.series
  rw [← (ratEquivF C).tsum_eq]
  simp only [coe_ratEquivF, piWA_apply, iotaA_apply, piWF_ratWF C]

section Act

variable {g : GAF σ JS} {h : GAF σ JT} {a : Matrix (Fin nS) (Fin nS) E} {b : Matrix (Fin nT) (Fin nT) E}

theorem act_eq (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (x : WOF F E nS nT) :
    actOF σ JS JT g⁻¹ h⁻¹ x = b.map (incAF F E) * x * a.map (incAF F E) := by
  have ha' : mtF σ JS g = a.map (incAF F E) := ha
  have hb' : mtF σ JT h⁻¹ = b.map (incAF F E) := hb
  unfold actOF
  rw [inv_inv, ha', hb']

theorem act_ratW (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (y : Matrix (Fin nT) (Fin nS) E) :
    actOF σ JS JT g⁻¹ h⁻¹ (ratWF (F := F) y) = ratWF (b * y * a) := by
  rw [act_eq ha hb, ratWF, ratWF, Matrix.map_mul, Matrix.map_mul]

theorem act_finRat (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) (y : Matrix (Fin nT) (Fin nS) E) :
    actOF σ JS JT g⁻¹ h⁻¹ (finRatF F y : WOF F E nS nT) = finRatF F (b * y * a) := by
  rw [coe_finRatF, coe_finRatF, actOF_smul, act_ratW ha hb]

theorem act_iota (C : Ctx σ B JS JT ξ₀ θ ι) (v : IxF F nS nT → ℂ) :
    actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) := by
  have e := finIdem_add_iota C.chart (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
  rw [← actOF_smul, finIdem_smul_of_real (iota_fin C v), actOF_zero', zero_add, piWF_actOF C,
    piWF_iotaVF C.chart] at e
  exact e

theorem omV_act (C : Ctx σ B JS JT ξ₀ θ ι) (u v : IxF F nS nT → ℂ) :
    omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) =
      omV (HMF JS JT ξ₀ (tauB B)) u v := by
  have key : ∀ t : ℝ, Complex.exp (-(Real.pi * Complex.I) *
      (omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (t • u)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (t • u) v : ℝ)) := by
    intro t
    have h1 := beta_iota_left C (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (t • u)) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v))
    have h2 := beta_iota_left C (t • u) (iotaVF ι v)
    rw [piWF_actOF C, piWF_iotaVF C.chart, ← act_iota C, symplOHF_act C] at h1
    rw [piWF_iotaVF C.chart] at h2
    exact h1.symm.trans h2
  by_contra hne
  have hd : omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) -
      omV (HMF JS JT ξ₀ (tauB B)) u v ≠ 0 := sub_ne_zero.2 hne
  have k := key (omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) -
      omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹
  rw [mulVec_smul, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at k
  have k2 := Complex.exp_sub (-(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ) : ℂ))
    (-(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) u v : ℝ) : ℂ))
  rw [k, div_self (Complex.exp_ne_zero _)] at k2
  have e : -(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) : ℝ) : ℂ) -
      -(Real.pi * Complex.I) * (((omV (HMF JS JT ξ₀ (tauB B)) (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ u)
      (mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v) - omV (HMF JS JT ξ₀ (tauB B)) u v)⁻¹ *
      omV (HMF JS JT ξ₀ (tauB B)) u v : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
    rw [← mul_sub, ← Complex.ofReal_sub, ← mul_sub, inv_mul_cancel₀ hd, Complex.ofReal_one, mul_one]
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I] at k2
  norm_num at k2

theorem actR_add_infRat (C : Ctx σ B JS JT ξ₀ θ ι) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (y : Matrix (Fin nT) (Fin nS) E) (v : IxF F nS nT → ℂ) :
    mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ (infRatF (tauB B) y + v) =
      infRatF (tauB B) (b * y * a) + mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v := by
  rw [mulVec_add, ← piWF_ratWF C y, ← piWF_ratWF C (b * y * a), ← act_ratW ha hb, piWF_actOF C]

end Act

theorem phase_identity (C : Ctx σ B JS JT ξ₀ θ ι) {W : AEF F E} (hW : W + cAF σ W = 1) (U Y : WOF F E nS nT)
    (hi : symplOHF σ JS JT ξ₀ (W • (U + Y)) (U + Y) = symplOHF σ JS JT ξ₀ (W • Y) Y) :
    symplOHF σ JS JT ξ₀ (W • U) U + symplOHF σ JS JT ξ₀ (U + Y) Y = symplOF σ JS JT ξ₀ (cAF σ W • U) Y := by
  have hσ := sgsg C
  have h1 : symplOHF σ JS JT ξ₀ Y Y = 0 := by
    unfold symplOHF; rw [GlobalTheory.HeisLineF.symplOF_self σ JS JT hσ C.hS C.hT ξ₀ C.hξ, mul_zero]
  have h2 : symplOHF σ JS JT ξ₀ U Y = symplOHF σ JS JT ξ₀ (W • U) Y + symplOHF σ JS JT ξ₀ (cAF σ W • U) Y := by
    rw [← GlobalTheory.HeisLineF.symplOHF_add_left, ← add_smul, hW, one_smul]
  have h3 : symplOHF σ JS JT ξ₀ (W • Y) U = -symplOHF σ JS JT ξ₀ (cAF σ W • U) Y := by
    rw [symplOHF_smul σ JS JT hσ, symplOHF_skew σ JS JT hσ C.hS C.hT ξ₀ C.hξ]
  rw [smul_add, GlobalTheory.HeisLineF.symplOHF_add_left, GlobalTheory.HeisLineF.symplOHF_add_right,
    GlobalTheory.HeisLineF.symplOHF_add_right] at hi
  rw [GlobalTheory.HeisLineF.symplOHF_add_left, ← symplOHF_add_self]
  linear_combination hi + h1 + h2 - h3

theorem gam_periodic {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
    {s : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (H : IsHeis s w γ W) {A : Submodule R X}
    (hA : SelfDual γ A) (φ : X →ₗ[R] X) (hφ : ∀ x y, γ (φ x) (φ y) = γ x y) (r : R) {y c : X} (hy : φ y - y ∈ A)
    (hc : c ∈ A) (hc' : φ c ∈ A) : γ (r • (φ (y + c) - (y + c))) (y + c) = γ (r • (φ y - y)) y := by
  have e1 : φ (y + c) - (y + c) = (φ y - y) + (φ c - c) := by rw [map_add]; abel
  have e2 : γ (r • c) y = γ (r • φ c) y := by
    rw [← hφ, map_smul, ← sub_add_cancel (φ y) y, H.add_right, H.iso hA (A.smul_mem r hc') hy, one_mul]
  have e3 : γ (r • (φ c - c)) y = 1 := by
    rw [smul_sub, sub_eq_add_neg, H.add_left, H.neg_left, e2, mul_inv_cancel₀ (H.ne_zero _ _)]
  rw [H.add_right, H.iso hA (A.smul_mem r (e1 ▸ A.add_mem hy (A.sub_mem hc' hc))) hc, mul_one, e1, smul_add,
    H.add_left, e3, mul_one]

variable (σ JS JT ξ₀) in

def gaussQF (ψ : AddChar (AF F) ℂ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
    (a : Matrix (Fin nS) (Fin nS) E) (b : Matrix (Fin nT) (Fin nT) E) (y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  if b * y * a - y ∈ Λ then gamQF σ JS JT ξ₀ ψ (sgOF σ w • (b * y * a - y)) y else 0

section Left

variable {g : GAF σ JS} {h : GAF σ JT} {a : Matrix (Fin nS) (Fin nS) E} {b : Matrix (Fin nT) (Fin nT) E}

theorem chiLat_mul_exp (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hw : w + sgOF σ w = 1) (y : Matrix (Fin nT) (Fin nS) E) :
    chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF (b * y * a - y)) = gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
      Complex.exp (-(Real.pi * Complex.I) *
        (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) (b * y * a)) (infRatF (tauB B) y) : ℝ)) := by
  have hm : ∀ z, finIdem F E • ratWF (F := F) z ∈ latOF F E nS nT Λ ↔ z ∈ Λ := fun z =>
    finRatF_mem_iff C hG hR hA z
  unfold chiLatF gaussQF
  by_cases hy : b * y * a - y ∈ Λ
  · rw [if_pos ((hm _).2 hy), if_pos hy]
    show B.ψ (symplOHF σ JS JT ξ₀ (intAF F w • (finRatF F (b * y * a - y) : WOF F E nS nT))
      (finRatF F (b * y * a - y))) = _
    have e : (finRatF F (b * y * a - y) : WOF F E nS nT) + finRatF F y = finRatF F (b * y * a) := by
      rw [← XFF.coe_add, ← map_add, sub_add_cancel]
    have h1 := phase_identity C (W := intAF F w) (by rw [cAF_intAF, ← map_add, hw, map_one])
      (finRatF F (b * y * a - y) : WOF F E nS nT) (finRatF F y)
      (by rw [e, ← act_finRat ha hb, ← actOF_smul, symplOHF_act C])
    have h2 : gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y =
        B.ψ (symplOF σ JS JT ξ₀ (cAF σ (intAF F w) • (finRatF F (b * y * a - y) : WOF F E nS nT)) (finRatF F y)) := by
      rw [gamQF, gamFF, map_smul, cAF_intAF]
      rfl
    rw [h2, ← h1, e, AddChar.map_add_eq_mul, mul_assoc, beta_fin C, mul_one]
  · rw [if_neg (fun h => hy ((hm _).1 h)), if_neg hy, zero_mul]

theorem left_side (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ)) (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hw : w + sgOF σ w = 1) (halt : ∀ x y, omV (HMF JS JT ξ₀ (tauB B)) x y = -omV (HMF JS JT ξ₀ (tauB B)) y x)
    (hbij : Function.Bijective fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x) (v : IxF F nS nT → ℂ) :
    serF σ JS JT ξ₀ B θ ι s Λ w (-v) (actOF σ JS JT g⁻¹ h⁻¹ (iotaVF ι v)) =
      ∑' y, gaussQF σ JS JT ξ₀ B.ψ Λ w a b y *
        gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) (infRatF (tauB B) y + v) := by
  rw [act_iota C, serF_eq C, ← (Equiv.ofBijective _ hbij).tsum_eq]
  refine tsum_congr fun y => ?_
  have h0 := omV_act (g := g) (h := h) C (infRatF (tauB B) y) v
  have h1 := actR_add_infRat C ha hb y 0
  rw [mulVec_zero, add_zero, add_zero] at h1
  rw [h1] at h0
  rw [Equiv.ofBijective_apply, chiLat_add_iota C, chiLat_mul_exp C hG hR hA ha hb hw, beta_iota_right C,
    beta_iota_left C, gaussV, actR_add_infRat C ha hb, piWF_add, piWF_iotaVF C.chart, piWF_ratWF C, map_sub (infRatF (tauB B))]
  generalize mMF σ JS JT θ (g⁻¹, h⁻¹) *ᵥ v = u at h0 ⊢
  generalize infRatF (tauB B) (b * y * a) = z at h0 ⊢
  generalize infRatF (tauB B) y = x at h0 ⊢
  have e1 : z - x + (-v + u) = z + u - (x + v) := by abel
  have e2 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z - x) u : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (z - x + u) : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) z x : ℝ)) =
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (z + u) (x + v) : ℝ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← mul_add, ← mul_add, ← Complex.ofReal_add, ← Complex.ofReal_add]
    congr 3
    simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply]
    linarith [halt x u, halt v z, halt v x, halt v u]
  rw [e1, ← e2]
  ring

end Left

def coefQF (σ : E →ₐ[F] E) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (B : Base F E)
    (s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ)
    (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E) (u : XFF F E nS nT)
    (y : Matrix (Fin nT) (Fin nS) E) : ℂ :=
  phaseF σ JS JT ξ₀ B.ψ w u * (B.ψ (symplOHF σ JS JT ξ₀ (ratWF y) u) *
    chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + (u : WOF F E nS nT)) *
    Complex.exp (-(Real.pi / 2 : ℂ) *
      (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y) (jV s (infRatF (tauB B) y)) : ℝ)))

theorem right_side (C : Ctx σ B JS JT ξ₀ θ ι)
    (halt : ∀ x y, omV (HMF JS JT ξ₀ (tauB B)) x y = -omV (HMF JS JT ξ₀ (tauB B)) y x)
    (u : XFF F E nS nT) (v : IxF F nS nT → ℂ) :
    (phaseF σ JS JT ξ₀ B.ψ w u • heisOF σ JS JT ξ₀ B.ψ u (serF σ JS JT ξ₀ B θ ι s Λ w (-v))) (iotaVF ι v) =
      ∑' y, coefQF σ JS JT ξ₀ B s Λ w u y *
        Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
  have hu : piWF θ (u : WOF F E nS nT) = 0 := piWF_of_fin u.fin
  rw [Pi.smul_apply, smul_eq_mul, heisOF, beta_iota_left C, hu, LinearMap.map_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, serF_eq C, ← tsum_mul_left]
  refine tsum_congr fun y => ?_
  have e1 : ratWF (F := F) y + (iotaVF ι v + (u : WOF F E nS nT)) = (ratWF y + (u : WOF F E nS nT)) + iotaVF ι v := by
    abel
  have e2 : omV (HMF JS JT ξ₀ (tauB B)) v v = 0 := by linarith [halt v v]
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y) v : ℝ)) *
      Complex.exp (-(Real.pi * Complex.I) * (omV (HMF JS JT ξ₀ (tauB B)) (-v) (infRatF (tauB B) y + v) : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_add, map_neg, LinearMap.neg_apply, e2, halt v (infRatF (tauB B) y)]
    push_cast
    ring
  rw [coefQF, GlobalTheory.HeisLineF.symplOHF_add_right, AddChar.map_add_eq_mul, beta_iota_right C, beta_iota_left C,
    piWF_add, piWF_add, hu, piWF_iotaVF C.chart, piWF_ratWF C, add_zero, neg_add_cancel, add_zero, e1,
    chiLat_add_iota C, ← e3]
  ring

theorem summable_coefQF (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hA : SelfDual (gamFF σ JS JT ξ₀ B.ψ) (latF F E nS nT Λ))
    (hpos : ∀ v, v ≠ 0 → 0 < omV (HMF JS JT ξ₀ (tauB B)) v (jV s v)) (w : 𝓞 E) (u : XFF F E nS nT) :
    Summable fun y => ‖coefQF σ JS JT ξ₀ B s Λ w u y‖ := by
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B C.good).1
  have h := GlobalTheory.HeisenbergGaussianSeries.summable_coeff (G := WOF F E nS nT) (piWA θ)
    (omV (HMF JS JT ξ₀ (tauB B))) (jV s) (ratLF F E nS nT)
    ((latOF F E nS nT Λ).comap (DistribSMul.toAddMonoidHom (WOF F E nS nT) (finIdem F E)))
    (chiLatF σ JS JT ξ₀ B.ψ Λ w) hpos
    (by
      rintro _ ⟨y, rfl⟩ hy
      have : y = 0 := infRatF_injective B (((piWF_ratWF C y).symm.trans hy).trans (map_zero _).symm)
      rw [this, map_zero])
    (fun R => by
      refine ((finite_lat C.good hG R).image (fun y => ratWF (F := F) y)).subset ?_
      rintro _ ⟨⟨y, rfl⟩, h1, h2⟩
      exact ⟨y, ⟨(finRatF_mem_iff C hG hR hA y).1 h1, by rw [← piWF_ratWF C]; exact h2⟩, rfl⟩)
    (fun x hx => if_neg hx)
    (fun x => by
      unfold chiLatF
      split_ifs
      · exact (hψ.2.1 _).le
      · simp)
    (fun y => B.ψ (symplOHF σ JS JT ξ₀ y u)) (fun y => hψ.2.1 _) u 0 0 0
  rw [← (ratEquivF C).summable_iff] at h
  refine h.congr fun y => ?_
  have e : ‖phaseF σ JS JT ξ₀ B.ψ w u‖ = 1 := hψ.2.1 _
  simp only [Function.comp_apply, coe_ratEquivF, piWA_apply, piWF_ratWF C, add_zero, zero_mul, Real.exp_zero,
    mul_one]
  rw [coefQF, norm_mul (phaseF σ JS JT ξ₀ B.ψ w u), e, one_mul]

theorem mem_of_coefQF_ne_zero {w : 𝓞 E} {u : XFF F E nS nT} {y : Matrix (Fin nT) (Fin nS) E}
    (h : coefQF σ JS JT ξ₀ B s Λ w u y ≠ 0) : finRatF F y + u ∈ latF F E nS nT Λ := by
  by_contra hn
  apply h
  have e : chiLatF σ JS JT ξ₀ B.ψ Λ w (ratWF y + (u : WOF F E nS nT)) = 0 := by
    unfold chiLatF
    rw [smul_add, finIdem_smul_of_fin u.fin]
    exact if_neg hn
  rw [coefQF, e, mul_zero, zero_mul, mul_zero]

theorem coefQF_zero (w : 𝓞 E) {u : XFF F E nS nT} (hu : u ∈ latF F E nS nT Λ) :
    coefQF σ JS JT ξ₀ B s Λ w u 0 = 1 := by
  have e : ratWF (F := F) (0 : Matrix (Fin nT) (Fin nS) E) = 0 := Matrix.map_zero _ (incAF F E).map_zero
  rw [coefQF, e, zero_add, map_zero, symplOHF_zero_left', AddChar.map_zero_eq_one, one_mul, map_zero,
    LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, chiLatF,
    finIdem_smul_of_fin u.fin, if_pos (mem_latF.1 hu), phaseF, ← AddChar.map_add_eq_mul, neg_add_cancel,
    AddChar.map_zero_eq_one]

def sandF (b : Matrix (Fin nT) (Fin nT) E) (a : Matrix (Fin nS) (Fin nS) E) :
    Matrix (Fin nT) (Fin nS) E →+ Matrix (Fin nT) (Fin nS) E :=
  AddMonoidHom.mk' (fun x => b * x * a) (fun x y => by rw [Matrix.mul_add, Matrix.add_mul])

theorem gauss_mul_integral_A (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hR : RatSD σ JS JT ξ₀ Λ)
    (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (hs : CartF σ JS JT ξ₀ B θ s) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b)
    (hbij : Function.Bijective (fun x : Matrix (Fin nT) (Fin nS) E => b * x * a - x))
    (hF : Integrable (gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹))) volume) (κ : ℂ)
    (hκ : ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, Fixes (opFF hc w) (latF F E nS nT Λ) f → IsVacF σ JS JT ξ₀ B.ψ ι s f → ∀ x,
      (f : WOF F E nS nT → ℂ) (actOF σ JS JT g⁻¹ h⁻¹ x) = κ * ((sumOp (opFF hc w) (latF F E nS nT Λ)
        ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, h))) f : thetaSubF σ JS JT ξ₀ B.ψ) : WOF F E nS nT → ℂ) x)
    (n : ℕ) (t : Fin n → Matrix (Fin nT) (Fin nS) E) (ht : ∀ k, b * t k * a - t k ∈ Λ)
    (hu : ∀ y, b * y * a - y ∈ Λ → ∃! k, y - t k ∈ Λ) :
    ∃ r : ℝ, 0 < r ∧ (∑ k, gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * t k * a - t k)) (t k)) *
      ∫ v, gaussV (HMF JS JT ξ₀ (tauB B)) s (mMF σ JS JT θ (g⁻¹, h⁻¹)) v = r * κ := by
  have hσ := sgsg C
  obtain ⟨hH, -⟩ := PositivityTheory.ThKW.hermitian_majorant_selfAdjoint_posDef F E σ B C.good nS nT JS JT C.hS C.hT ξ₀ C.h0 C.hξ
  obtain ⟨halt, -, -, hpos⟩ := omV_laws (H := HMF JS JT ξ₀ (tauB B)) hH hs.sq hs.pos
  have hw := hO.hw
  have H := isHeis_opFF hσ C.hS C.hT C.hξ hc hw
  have hA := hO.sd
  have hB := hO.sd' (g, h)
  have hmem : ∀ y, finRatF F y ∈ latF F E nS nT Λ ↔ y ∈ Λ := finRatF_mem_iff C hG hR hA
  obtain ⟨m, u, huB, huT⟩ := exists_transversal_of_idx_ne_zero _ _ (hO.fin (g, h))
  let Cg : AddSubgroup (Matrix (Fin nT) (Fin nS) E) :=
    Λ.toAddSubgroup ⊓ Λ.toAddSubgroup.comap (sandF b a)
  have hC : ∀ x, x ∈ Cg ↔ x ∈ Λ ∧ b * x * a ∈ Λ := fun x => Iff.rfl
  have hQ : ∀ y, b * y * a - y ∈ Λ →
      gaussQF σ JS JT ξ₀ B.ψ Λ w a b y = gamQF σ JS JT ξ₀ B.ψ (sgOF σ w • (b * y * a - y)) y := fun y hy => if_pos hy
  have hQ0 : ∀ y, b * y * a - y ∉ Λ → gaussQF σ JS JT ξ₀ B.ψ Λ w a b y = 0 := fun y hy => if_neg hy
  have h0 : κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) 0 = κ := by
    obtain ⟨i, hi, hi'⟩ := huT 0 (zero_mem _)
    rw [Finset.sum_eq_single i, coefQF_zero w (by simpa using hi), mul_one]
    · intro j _ hj
      by_contra hn
      exact hj (hi' j (by simpa using mem_of_coefQF_ne_zero hn))
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  have key := GlobalTheory.T.unfold_poincareSeries_lattice_fourier (IxF F nS nT → ℂ) volume _ (infRatF (tauB B)) (infRatF_injective B) Cg
    (fun R => (finite_lat C.good hG R).subset fun c hc => ⟨((hC c).1 hc.1).1, hc.2⟩) ?_ n t
    (gaussQF σ JS JT ξ₀ B.ψ Λ w a b) ?_ ?_ ?_ _ hF
    (fun y => κ * ∑ i, coefQF σ JS JT ξ₀ B s Λ w (u i) y)
    (fun y => -omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨r, hr, e⟩ := key
    refine ⟨r, hr, ?_⟩
    rw [h0, Finset.sum_congr rfl fun k _ => hQ _ (ht k)] at e
    exact e
  · rw [eq_top_iff, ← span_infRatF C.good, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨N, hN, h1⟩ := hG.den y
    obtain ⟨M, hM, h2⟩ := hG.den (b * y * a)
    have h3 : (M * N) • y ∈ Cg := by
      refine (hC _).2 ⟨?_, ?_⟩
      · rw [mul_smul]
        exact Submodule.smul_of_tower_mem Λ M h1
      · have e : b * ((M * N) • y) * a = (N * M) • (b * y * a) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, mul_comm]
        rw [e, mul_smul]
        exact Submodule.smul_of_tower_mem Λ N h2
    have h4 : infRatF (tauB B) y = ((M * N : ℕ) : ℝ)⁻¹ • infRatF (tauB B) ((M * N) • y) := by
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ (Nat.cast_ne_zero.2 (Nat.mul_pos hM hN).ne')]
    rw [h4]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h3, rfl⟩)
  · intro y hy
    have h1 : b * y * a - y ∈ Λ := by_contra fun hn => hy (hQ0 y hn)
    obtain ⟨k, hk, -⟩ := hu y h1
    refine ⟨k, (hC _).2 ⟨hk, ?_⟩⟩
    have e : b * (y - t k) * a = (b * y * a - y) - (b * t k * a - t k) + (y - t k) := by
      rw [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e]
    exact add_mem (sub_mem h1 (ht k)) hk
  · intro k k' hk
    exact ((hu (t k) (ht k)).unique (by rw [sub_self]; exact zero_mem _) ((hC _).1 hk).1)
  · intro y c hc
    obtain ⟨hc1, hc2⟩ := (hC c).1 hc
    have e : b * (y + c) * a - (y + c) = (b * y * a - y) + (b * c * a - c) := by
      rw [Matrix.mul_add, Matrix.add_mul]; abel
    have hc' : b * c * a - c ∈ Λ := sub_mem hc2 hc1
    by_cases hy : b * y * a - y ∈ Λ
    · rw [hQ _ hy, hQ _ (e ▸ add_mem hy hc'), gamQF, gamQF, map_smul, map_smul, map_sub, map_sub,
        ← rhoFF_finRatF ha hb, ← rhoFF_finRatF ha hb, map_add (finRatF F)]
      refine gam_periodic H hA _ (fun x y => ?_) _ ?_ ((hmem c).2 hc1) ?_
      · unfold gamFF
        rw [coe_rhoFF, coe_rhoFF, symplOF_actOF C]
      · rw [rhoFF_finRatF ha hb, ← map_sub]; exact (hmem _).2 hy
      · rw [rhoFF_finRatF ha hb]; exact (hmem _).2 hc2
    · rw [hQ0 _ hy, hQ0]
      intro hn
      rw [e] at hn
      exact hy ((add_mem_cancel_right hc').1 hn)
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
      ((summable_sum fun i (_ : i ∈ Finset.univ) => summable_coefQF C hG hR hA hpos w (u i)).mul_left ‖κ‖)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
  · simp
  · intro y hy hn
    have h1 : infRatF (tauB B) y ≠ 0 := fun h => hy (infRatF_injective B (h.trans (map_zero _).symm))
    have h2 := hpos _ h1
    rw [neg_eq_zero.1 hn] at h2
    exact lt_irrefl _ h2
  · intro y hy c hc
    obtain ⟨hc1, hc2⟩ := (hC c).1 hc
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hy)
    have h1 : finRatF F c ∈ (latF F E nS nT Λ).map (rhoFF σ JS JT (g, h)) := by
      refine ⟨finRatF F (b * c * a), (hmem _).2 hc2, ?_⟩
      rw [← rhoFF_finRatF ha hb, ← Module.End.mul_apply, ← map_mul,
        show ((g, h) : GAF σ JS × GAF σ JT) * (g⁻¹, h⁻¹) = 1 from mul_inv_cancel (g, h), map_one,
        Module.End.one_apply]
    have h2 := H.iso hA (mem_of_coefQF_ne_zero hi) ((hmem c).2 hc1)
    rw [H.add_left, H.iso hB (huB i) h1, mul_one] at h2
    obtain ⟨z, hz⟩ := (gamQF_eq_one_iff C y c).1 h2
    exact ⟨-z, by rw [LinearMap.neg_apply, hz, Int.cast_neg]⟩
  · intro v
    obtain ⟨hf, hfix, hvac⟩ := ser_vacuum C hG hR hO hs (-v)
    have e := hκ ⟨_, hf⟩ hfix hvac (iotaVF ι v)
    rw [(sumOp_eq_sum_transversal H _ _ hB _ hfix _ u huB huT).1, Submodule.coe_sum, Finset.sum_apply] at e
    simp only [coe_opFF, right_side C halt, left_side C hG hR hA ha hb hw halt hbij] at e
    rw [e, ← Summable.tsum_finsetSum, ← tsum_mul_left]
    · refine tsum_congr fun y => ?_
      beta_reduce
      rw [← Finset.sum_mul, mul_assoc κ]
    · intro i _
      refine Summable.of_norm ((summable_coefQF C hG hR hA hpos w (u i)).congr fun y => ?_)
      have e1 : (2 * Real.pi * Complex.I *
          ((-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) =
          ((2 * Real.pi * (-omV (HMF JS JT ξ₀ (tauB B)) (infRatF (tauB B) y)) v : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [norm_mul, e1, Complex.norm_exp_ofReal_mul_I, mul_one]

end PositivityTheory.ThKW.Trc

end
