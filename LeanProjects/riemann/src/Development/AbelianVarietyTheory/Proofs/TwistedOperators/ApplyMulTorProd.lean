import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicFormFrameExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

def torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s : D.what₂.Tau → Fin V.rank → ℝ) : GA D V :=
  (Finset.univ.toList.map fun ρ => torAt θ V B ρ (s ρ)).prod

def conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} : Frame Ψ r →ₗ[ℝ] Frame Ψ r where
  toFun Z := fun τ a b => conj (Z τ a b)
  map_add' Z Z' := funext fun τ => funext fun a => funext fun b => map_add (starRingEnd ℂ) _ _
  map_smul' c Z := funext fun τ => funext fun a => funext fun b => by
    change conj ((c : ℂ) * Z τ a b) = (c : ℂ) * conj (Z τ a b)
    rw [map_mul, Complex.conj_ofReal]

theorem mat_conjL {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (Z : Frame Ψ r) (τ : Ψ) :
    mat (conjL Z) τ = (mat Z τ).map (starRingEnd ℂ) := rfl

def toLieC (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas) :
    Frame C.X.Ψ T.rank →ₗ[ℝ] GlobalTheory.SmoothForms.LieN T :=
  (GlobalTheory.HolRead.AdExt.toLie R B (fun ρ => C.m.e ρ)).comp conjL

theorem isUnit_det_B (C : Ctx S T) {B : C.Bas} (hB : C.IsB B) (ρ : D.what₂.Tau) : IsUnit (B ρ).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have := congrArg det (hB ρ)
  rw [det_mul, det_mul, h0, mul_zero, sgnM, det_diagonal] at this
  refine Finset.prod_ne_zero_iff.2 (fun c _ => ?_) this.symm
  unfold sgn
  split_ifs <;> norm_num

theorem exp_map_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (NormedSpace.exp A).map (starRingEnd ℂ) = NormedSpace.exp (A.map (starRingEnd ℂ)) := by
  have h : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = Mᴴᵀ := fun M => by
    ext i j
    simp [conjTranspose_apply]
  rw [h, h, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def trLin (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →ₗ[ℝ] ℂ where
  toFun Y := ∑ ρ, (m ρ : ℂ) * trace (Y ρ).1
  map_add' Y Y' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace ((Y ρ).1 + (Y' ρ).1) = _
    rw [trace_add, mul_add]
  map_smul' c Y := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    change (m ρ : ℂ) * trace (c • (Y ρ).1) = c • ((m ρ : ℂ) * trace (Y ρ).1)
    rw [trace_smul, mul_smul_comm]

def trCL (V : HSp D) (m : D.what₂.Tau → ℤ) : GlobalTheory.SmoothForms.LieN V →L[ℝ] ℂ where
  toLinearMap := trLin V m
  cont := continuous_finset_sum _ fun ρ _ =>
    continuous_const.mul ((continuous_subtype_val.comp (continuous_apply ρ)).matrix_trace)

theorem trCL_apply (V : HSp D) (m : D.what₂.Tau → ℤ) (Y : GlobalTheory.SmoothForms.LieN V) : trCL V m Y = trLin V m Y := rfl

end GlobalTheory.AdSpan.ConjHol

namespace GlobalTheory.AdSpan.ConjHol

variable {D : D7} {S T : HSp D}

theorem apply_mul_torProd (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Fin V.rank → ℤ) (ψ : GA D V → ℂ)
    (h : ∀ (ρ : D.what₂.Tau) (t : Fin V.rank → ℝ) (g : GA D V),
      ψ (g * torAt θ V B ρ t) = cexp (((∑ a, (w ρ a : ℝ) * t a : ℝ) : ℂ) * I) * ψ g)
    (s : D.what₂.Tau → Fin V.rank → ℝ) (g : GA D V) :
    ψ (g * torProd θ V B s) = cexp (((∑ ρ, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g := by
  unfold torProd
  suffices H : ∀ l : List D.what₂.Tau, l.Nodup → ∀ g, ψ (g * (l.map fun ρ => torAt θ V B ρ (s ρ)).prod) =
      cexp (((∑ ρ ∈ l.toFinset, ∑ a, (w ρ a : ℝ) * s ρ a : ℝ) : ℂ) * I) * ψ g by
    have := H (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) g
    rwa [Finset.toList_toFinset] at this
  intro l hl
  induction l with
  | nil => intro g; simp
  | cons ρ l ih =>
    intro g
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, ← mul_assoc, ih hl.2, h, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1), ← mul_assoc, ← Complex.exp_add, ← add_mul]
    congr 3
    push_cast
    ring

theorem xB_mvB_mul (C : Ctx S T) (B : C.Bas) (hB : C.IsB B) (a k : GA D T) (b : Frame C.X.Ψ T.rank)
    (hk : ∀ ρ, compAt C.θ ρ (Formalism.L2.Theta.mt T k) = B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) :
    C.xB (C.mvB (a * k) B) = rmul (C.xB (C.mvB a B)) b := by
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  funext σ i j
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective σ
  have e1 : C.mvB (a * k) B ρ = C.mvB a B ρ * (mat b (C.m.e ρ)).map (starRingEnd ℂ) := by
    have hm : compAt C.θ ρ (Formalism.L2.Theta.mt T (a * k)) =
        compAt C.θ ρ (Formalism.L2.Theta.mt T a) * compAt C.θ ρ (Formalism.L2.Theta.mt T k) := R.2.2.2.1 a k ρ
    simp only [Ctx.mvB]
    rw [hm, hk]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_B C hB ρ), Matrix.mul_one]
  simp only [Ctx.xB, rmul, mat, Equiv.symm_apply_apply, e1, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply,
    map_sum, map_mul, Complex.conj_conj]

end GlobalTheory.AdSpan.ConjHol
