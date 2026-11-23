import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine.RhoSlice

variable {F : Type} [Field F] [NumberField F]

theorem at_mul {v : Pl F} {b : AF F} (hb : At (evFin F v) b) (a : AF F) : At (evFin F v) (a * b) := by
  intro u hu
  rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u b, hb u hu, mul_zero]

theorem at_add {v : Pl F} {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b) :
    At (evFin F v) (a + b) := by
  intro u hu
  rw [smul_add, ha u hu, hb u hu, add_zero]

theorem at_dot {κ : Type} [Fintype κ] {v : Pl F} (a b : κ → AF F) (hb : ∀ i, At (evFin F v) (b i)) :
    At (evFin F v) (a ⬝ᵥ b) := by
  intro u hu
  simp only [dotProduct, Finset.smul_sum]
  exact Finset.sum_eq_zero fun i _ => at_mul (hb i) (a i) u hu

theorem singleFin_one_mul (v : Pl F) (y : Af F) : singleFin v 1 * y = singleFin v (evalV F v y) := by
  refine af_ext fun u => ?_
  rw [map_mul]
  by_cases h : u = v
  · subst h; rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
  · rw [evalV_singleFin_ne h, evalV_singleFin_ne h, zero_mul]

theorem evFin_inr_singleFin (v : Pl F) (c : Fv F v) :
    evFin F v (LinearMap.inr F (Ainf F) (Af F) (singleFin v c)) = c :=
  evalV_singleFin_self v c

theorem eq_inr_of_at {v : Pl F} {a : AF F} (ha : At (evFin F v) a) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  have h1 := ha (1 - (show AF F from LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)))
    (by rw [map_sub, map_one, evFin_inr_singleFin, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h1
  refine h1.trans (Prod.ext ?_ ?_)
  · show (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  · show singleFin v 1 * a.2 = singleFin v (evFin F v a)
    exact singleFin_one_mul v a.2

theorem evFin_invOf_two (v : Pl F) : evFin F v (⅟(2 : AF F)) = (2 : Fv F v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]

end GlobalTheory.VacLine.RhoSlice

namespace GlobalTheory.VacLine.RhoSlice

theorem at_coord {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {v : Pl F} {w : Matrix (Fin n) (Fin d) (AE F E)}
    (hw : At (evFin F v) w) (i : Fin n × Fin d) :
    At (evFin F v) ((M.co.e w).1 i) ∧ At (evFin F v) ((M.co.e w).2 i) := by
  have h : ∀ u : AF F, evFin F v u = 0 → u • M.co.e w = 0 := fun u hu => by
    rw [← LinearEquiv.map_smul, hw u hu, map_zero]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have := congrArg (fun p => p.1 i) (h u hu)
    simpa using this
  · have := congrArg (fun p => p.2 i) (h u hu)
    simpa using this

theorem rho_slice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (Φ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      slice (M.co.rho ψ w Φ) x = finOp ψ v (locPt v (M.co.e w)) (slice Φ x) := by
  intro F E _ _ _ _ _ σ n d X W M ψ v w hw Φ x
  funext y
  have hc := at_coord M hw
  have hz : At (evFin F v) (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) :=
    at_add (at_dot _ _ fun i => (hc i).2) (at_mul (at_dot _ _ fun i => (hc i).2) _)
  show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) * Φ (mkPt x y + (M.co.e w).1) = _
  rw [show ψ (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2)) =
    psiLoc ψ v (evFin F v (mkPt x y ⬝ᵥ (M.co.e w).2 + ⅟(2 : AF F) * ((M.co.e w).1 ⬝ᵥ (M.co.e w).2))) from
    congrArg ψ (eq_inr_of_at hz)]
  unfold finOp slice locPt
  congr 2
  · simp only [dotProduct, map_add, map_mul, map_sum, evFin_invOf_two, evFin_mkPt]
    ring
  · funext i
    show mkPt x y i + (M.co.e w).1 i = _
    rw [eq_inr_of_at (hc i).1]
    exact Prod.ext (add_zero _) rfl

end GlobalTheory.VacLine.RhoSlice
