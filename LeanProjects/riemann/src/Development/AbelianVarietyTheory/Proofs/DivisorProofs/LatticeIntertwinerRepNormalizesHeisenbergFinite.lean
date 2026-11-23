import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem unitary_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : GAF σ J) :
    ((mtF σ J g).map (cAF σ))ᵀ * J.map (incAF F E) * mtF σ J g = J.map (incAF F E) :=
  g.2

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.mpr hS.2
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]
    exact Matrix.map_one _ (incAF F E).map_zero (incAF F E).map_one
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 (unitary_mtF h) (unitary_mtF g⁻¹) x y

theorem symplOHF_actOF (hS : IsHermND σ JS) (ξ₀ : E) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOHF σ JS JT ξ₀ x y := by
  unfold symplOHF symplOF
  rw [hOF_actOF hS]

variable (F E) in

def realIdF : AEF F E := algebraMap (AF F) (AEF F E) (pairA F 1 0)

theorem infPartF_realIdF : infPartF F E (realIdF F E) = 1 := by
  show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (pairA F 1 0 ⊗ₜ[F] (1 : E)) = 1
  rw [Algebra.TensorProduct.map_tmul, show fstA F (pairA F 1 0) = 1 from rfl]
  rfl

theorem realIdF_mul_of_inf {z : AEF F E} (hz : infPartF F E z = 0) : realIdF F E * z = 0 := by
  rw [realIdF, ← Algebra.smul_def]
  exact GlobalTheory.HeisThetaF.smul_eq_zero_of_infPartF hz

theorem realIdF_smul_of_fin {x : WOF F E nS nT} (hx : x.map (infPartF F E) = 0) : realIdF F E • x = 0 := by
  ext i j
  exact realIdF_mul_of_inf (congrFun (congrFun hx i) j)

theorem fin_part (w₀ : WOF F E nS nT) : ((1 - realIdF F E) • w₀).map (infPartF F E) = 0 := by
  funext i j
  show infPartF F E ((1 - realIdF F E) * w₀ i j) = 0
  rw [map_mul, map_sub, infPartF_realIdF, map_one, sub_self, zero_mul]

theorem decomp (w₀ : WOF F E nS nT) : w₀ = realIdF F E • w₀ + (1 - realIdF F E) • w₀ := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem symplOF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  rw [symplOF_smul σ JS JT hσ, realIdF, GlobalTheory.HeisThetaF.cAF_algebraMap, ← realIdF, realIdF_smul_of_fin hx,
    GlobalTheory.HeisLineF.symplOF_zero_right]

theorem symplOHF_real_fin (hσ : ∀ x, σ (σ x) = x) (ξ₀ : E) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ (realIdF F E • u) x = 0 := by
  unfold symplOHF; rw [symplOF_real_fin hσ ξ₀ u hx, mul_zero]

theorem symplOHF_fin_real (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E}
    (hξ : σ ξ₀ = -ξ₀) (u : WOF F E nS nT) {x : WOF F E nS nT}
    (hx : x.map (infPartF F E) = 0) : symplOHF σ JS JT ξ₀ x (realIdF F E • u) = 0 := by
  unfold symplOHF
  rw [GlobalTheory.HeisLineF.symplOF_skew σ JS JT hσ hS hT ξ₀ hξ, symplOF_real_fin hσ ξ₀ u hx, neg_zero, mul_zero]

theorem realIdF_smul_mtF {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ J) :
    realIdF F E • mtF σ J g = realIdF F E • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : (mtF σ J g).map (infPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  rw [← sub_eq_zero, ← smul_sub]
  refine Matrix.ext fun i j => ?_
  show realIdF F E * (mtF σ J g - 1) i j = 0
  refine realIdF_mul_of_inf ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (infPartF F E) (infPartF F E).map_zero (infPartF F E).map_one]
  rfl

theorem actOF_real {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GfCF σ JS)
    (hh : h ∈ GlobalTheory.WeilPartsF.GfCF σ JT) (u : WOF F E nS nT) :
    actOF σ JS JT g h (realIdF F E • u) = realIdF F E • u := by
  have h1 := realIdF_smul_mtF hh
  have h2 := realIdF_smul_mtF ((GlobalTheory.WeilPartsF.GfCF σ JS).inv_mem hg)
  unfold actOF
  have hI : realIdF F E * realIdF F E = realIdF F E := by
    rw [realIdF, ← map_mul]
    congr 1
    show ((1 : Ainf F) * 1, (0 : Af F) * 0) = ((1 : Ainf F), (0 : Af F))
    rw [one_mul, mul_zero]
  calc mtF σ JT h * (realIdF F E • u) * mtF σ JS g⁻¹
      = (realIdF F E • mtF σ JT h) * u * (realIdF F E • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hI]
    _ = realIdF F E • u := by
        rw [h1, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hI]

end GlobalTheory.FinLatHeis

namespace GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ}

theorem phaseF_rhoFF (hS : IsHermND σ JS) (w : 𝓞 E) (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) :
    phaseF σ JS JT ξ₀ ψ w (rhoFF σ JS JT p x) = phaseF σ JS JT ξ₀ ψ w x := by
  rw [phaseF, phaseF, coe_rhoFF, ← actOF_smul, symplOHF_actOF hS]

theorem phaseF_ne_zero (w : 𝓞 E) (x : XFF F E nS nT) : phaseF σ JS JT ξ₀ ψ w x ≠ 0 := by
  intro h0
  have h := AddChar.map_add_eq_mul ψ (-symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
    (symplOHF σ JS JT ξ₀ (intAF F w • (x : WOF F E nS nT)) x)
  rw [neg_add_cancel, AddChar.map_zero_eq_one] at h
  rw [phaseF] at h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

variable {hc : HeisClosedF σ JS JT ξ₀ ψ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {w : 𝓞 E}
  {lam : ℕ →* ℂ} {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)}

theorem comm (hσ : ∀ x, σ (σ x) = x) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : σ ξ₀ = -ξ₀)
    (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hL : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v))
    (p : GAF σ JS × GAF σ JT) (f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ) : Om p (L f) = L (Om p f) := by
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have : Om p ∘ₗ L = L ∘ₗ Om p := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have he' : Fixes (opFF hc w) (latF F E nS nT Λ) (L e) := fun a ha => by rw [← hL, he a ha]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, hR.op, hR.op, hL, hR.vac p e he, hR.vac p _ he',
      GlobalTheory.FinWeilO.normOp_comm H lam (hR.sd' p) (hR.fin p) L hL he]
  exact LinearMap.congr_fun this f

theorem heis_fin (hS : IsHermND σ JS) (hR : IsLatRepF σ JS JT ξ₀ ψ hc Λ w lam Om)
    (p : GAF σ JS × GAF σ JT) (x : XFF F E nS nT) (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ ψ)
    (hf : (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ x f) :
    (Om p f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ ψ (actOF σ JS JT p.1 p.2 x) (Om p f) := by
  have h1 : opFF hc w x f = phaseF σ JS JT ξ₀ ψ w x • f' := Subtype.ext (by rw [coe_opFF, Submodule.coe_smul, hf])
  have h2 := congrArg Subtype.val (hR.op p x f)
  rw [h1, map_smul, Submodule.coe_smul, coe_opFF, phaseF_rhoFF hS, coe_rhoFF] at h2
  exact smul_right_injective _ (phaseF_ne_zero w x) h2

end GlobalTheory.FinLatHeis

open GlobalTheory.FinLatF GlobalTheory.FinLatHeis in

theorem GlobalTheory.FinLatHeis.isLatRepF_heis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GfCF σ JT, ∀ (w₀ : WOF F E nS nT)
          (f f' : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ),
          (f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ w₀ f →
          (Om (g, h) f' : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (actOF σ JS JT g h w₀) (Om (g, h) f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh w₀ f f' hf
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]
  set r := realIdF F E
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ :=
    (heisLF σ JS JT ξ₀ B.ψ (r • w₀)).restrict fun f hf => hc _ f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = heisOF σ JS JT ξ₀ B.ψ (r • w₀) m := fun _ => rfl
  have hLop : ∀ x v, L (opFF hc w x v) = opFF hc w x (L v) := fun x v => Subtype.ext (by
    rw [hL, coe_opFF, coe_opFF, hL, GlobalTheory.WeilPartsF.heisOF_smul, heisOF_heisOF', heisOF_heisOF',
      symplOHF_real_fin hσ ξ₀ w₀ x.fin, symplOHF_fin_real hσ hS hT hξ w₀ x.fin, add_comm])
  let f₁ : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := ⟨_, hc ((1 - r) • w₀) f f.2⟩
  have hf' : f' = L f₁ := Subtype.ext (by
    rw [hf, hL]
    show heisOF σ JS JT ξ₀ B.ψ w₀ f = heisOF σ JS JT ξ₀ B.ψ (r • w₀) (heisOF σ JS JT ξ₀ B.ψ ((1 - r) • w₀) f)
    rw [heisOF_heisOF', symplOHF_real_fin hσ ξ₀ w₀ (fin_part w₀), AddChar.map_zero_eq_one, one_smul, ← decomp])
  have h1 := heis_fin hS hR (g, h) (XFF.mk _ (fin_part w₀)) f f₁ rfl
  rw [XFF.coe_mk] at h1
  rw [hf', comm hσ hS hT hξ hR L hLop, hL, h1, heisOF_heisOF',
    symplOHF_real_fin hσ ξ₀ w₀ (actOF_mem_finSubF g h (fin_part w₀)), AddChar.map_zero_eq_one, one_smul]
  congr 1
  conv_rhs => rw [decomp w₀, actOF_add, actOF_real hg hh]

end
