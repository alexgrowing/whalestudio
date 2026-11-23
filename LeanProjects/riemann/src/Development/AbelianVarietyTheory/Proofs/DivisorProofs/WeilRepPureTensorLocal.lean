import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinComm.RhoPure

variable {F : Type} [Field F] [NumberField F]

theorem eq_single_of_ann (v : Pl F) (a : AF F) (h : ∀ u : AF F, evFin F v u = 0 → u * a = 0) :
    a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v a)) := by
  set e : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1) with he_def
  have he : evFin F v e = 1 := evalV_singleFin_self v 1
  have h1 : (1 - e) * a = 0 := h _ (by rw [map_sub, map_one, he, sub_self])
  have hea : a = e * a := by linear_combination h1
  have key : e * a = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v (e * a))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf F) * a.1 = 0
      exact zero_mul _
    · show singleFin v 1 * a.2 = singleFin v (evFin F v (e * a))
      apply af_ext
      intro u
      rw [map_mul]
      by_cases hu : u = v
      · subst hu
        rw [evalV_singleFin_self, evalV_singleFin_self, one_mul]
        show evalV F u a.2 = evalV F u (singleFin u 1 * a.2)
        rw [map_mul, evalV_singleFin_self, one_mul]
      · rw [evalV_singleFin_ne hu, evalV_singleFin_ne hu, zero_mul]
  rw [← hea] at key
  exact key

theorem mulSupport_finite {κ : Type} [Finite κ] (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) (y : κ → AF F) :
    (Function.mulSupport fun u : Pl F => φ u fun i => evFin F u (y i)).Finite := by
  have h2 : ∀ᶠ u : Pl F in cofinite, ∀ i, evFin F u (y i) ∈ u.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => (y i).2.2
  have h3 : ∀ᶠ u : Pl F in cofinite, (φ u fun i => evFin F u (y i)) = 1 := by
    filter_upwards [hφ, h2] with u hu hu2
    rw [hu]
    exact Set.indicator_of_mem (s := {x : κ → Fv F u | ∀ i, x i ∈ u.adicCompletionIntegers F}) hu2 _
  exact Filter.eventually_cofinite.1 h3

theorem finprod_update_mul {ι : Type} (g : ι → ℂ) (hg : (Function.mulSupport g).Finite) (v : ι) (c : ℂ) :
    ∏ᶠ u, Function.update g v (c * g v) u = c * ∏ᶠ u, g u := by
  have hg' : (Function.mulSupport (Function.update g v (c * g v))).Finite :=
    (hg.insert v).subset fun u hu => by
      by_cases h : u = v
      · exact Or.inl h
      · exact Or.inr (by rwa [Function.mem_mulSupport, Function.update_of_ne h] at hu)
  rw [← mul_finprod_cond_ne v hg', ← mul_finprod_cond_ne v hg, Function.update_self, mul_assoc]
  congr 2
  apply finprod_congr; intro u; apply finprod_congr; intro h; exact Function.update_of_ne h _ _

theorem rho_pure_tensor {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)) (hw : At (evFin F v) w)
    (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ)
    (hφ : ∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) :
    M.co.rho ψ w (pure f φ) =
      pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) := by
  funext x
  simp only [Darboux.rho, schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.add_apply]
  set p := M.co.e w with hp_def
  have hp : ∀ u : AF F, evFin F v u = 0 → u • p = 0 := by
    intro u hu
    rw [hp_def, ← map_smul, hw u hu, map_zero]
  have h1 : ∀ i, p.1 i = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v (p.1 i))) := fun i =>
    eq_single_of_ann v _ fun u hu => congrArg (fun q => q.1 i) (hp u hu)
  have hfst : ∀ i, (p.1 i).1 = 0 := fun i => congrArg Prod.fst (h1 i)
  have hsnd : ∀ i, (p.1 i).2 = singleFin v (evFin F v (p.1 i)) := fun i => congrArg Prod.snd (h1 i)
  have hI : ∀ i, evI F (x i + p.1 i) = evI F (x i) := by
    intro i
    unfold evI
    congr 1
    show (x i).1 + (p.1 i).1 = (x i).1
    rw [hfst, add_zero]
  have hFne : ∀ u, u ≠ v → ∀ i, evFin F u (x i + p.1 i) = evFin F u (x i) := by
    intro u hu i
    rw [map_add]
    show _ + evalV F u (p.1 i).2 = _
    rw [hsnd, evalV_singleFin_ne hu, add_zero]
  have hp2 : ∀ u : AF F, evFin F v u = 0 → u • p.2 = 0 := fun u hu => congrArg Prod.snd (hp u hu)
  set s : AF F := x ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2) with hs
  have hs1 : s = LinearMap.inr F (Ainf F) (Af F) (singleFin v (evFin F v s)) := by
    apply eq_single_of_ann
    intro u hu
    have e1 : u * (x ⬝ᵥ p.2) = 0 := by rw [← smul_eq_mul, ← dotProduct_smul, hp2 u hu, dotProduct_zero]
    have e2 : u * (p.1 ⬝ᵥ p.2) = 0 := by rw [← smul_eq_mul, ← dotProduct_smul, hp2 u hu, dotProduct_zero]
    rw [hs]
    linear_combination e1 + ⅟(2 : AF F) * e2
  have h2' : evFin F v (⅟(2 : AF F)) = 2⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hev : evFin F v s = (fun i => evFin F v (x i)) ⬝ᵥ (GlobalTheory.FinComm.locPt v p).2 +
      (GlobalTheory.FinComm.locPt v p).1 ⬝ᵥ (GlobalTheory.FinComm.locPt v p).2 / 2 := by
    rw [hs]
    simp only [GlobalTheory.FinComm.locPt, dotProduct, map_add, map_mul, map_sum, h2']
    try ring
  set g : Pl F → ℂ := fun u => φ u fun i => evFin F u (x i + p.1 i) with hg
  have hfin : (Function.mulSupport g).Finite := mulSupport_finite φ hφ (x + p.1)
  have hprod : (fun u => Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v p) (φ v)) u
      fun i => evFin F u (x i)) = Function.update g v (ψ s * g v) := by
    funext u
    rcases eq_or_ne u v with rfl | hu
    · rw [Function.update_self, Function.update_self]
      simp only [GlobalTheory.FinComm.locOp, hg]
      conv_rhs => rw [hs1]
      rw [hev]
      congr 1
    · rw [Function.update_of_ne hu, Function.update_of_ne hu, hg]
      simp only [hFne u hu]
  rw [hprod, finprod_update_mul g hfin v (ψ s)]
  simp only [hI]
  ring

theorem rho_pure : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ u : Pl F, (Fin n × Fin d → Fv F u) → ℂ),
      (∀ᶠ u in cofinite, φ u = GlobalTheory.FinComm.indO u) →
      M.co.rho ψ w (pure f φ) =
        pure f (Function.update φ v (GlobalTheory.FinComm.locOp ψ v (GlobalTheory.FinComm.locPt v (M.co.e w)) (φ v))) :=
  fun M ψ v w hw f φ hφ => rho_pure_tensor M ψ v w hw f φ hφ

end GlobalTheory.FinComm.RhoPure
