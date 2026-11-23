import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host
open GlobalTheory.CuspRep (Af GA finGL)

namespace UpperTheory.V.TR.Cen

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

theorem commute_cap_of_commute_Eop (τ : InfinitePlace E) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem commute_cap_Eop (τ τ' : InfinitePlace E) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

open Classical in

theorem lieS_single (v : InfinitePlace E) (i j : Fin a) (t : ℝ) :
    lieS E a i j (Pi.single v t) = (t : ℂ) • Eop v i j := by
  have e : (Pi.single v t : Rinf E) = t • Pi.single v 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [e, map_smul, Eop_eq]
  rfl

theorem commute_cap_lie (τ : InfinitePlace E) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  classical
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  rw [← Finset.univ_sum_single (X i j), map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [lieS_single]
  exact (commute_cap_Eop τ w u i j).smul_right _

theorem commute_cap_finRep (τ : InfinitePlace E) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) :=
  commute_cap_of_commute_Eop τ u _ fun _ _ => lie_rt_fin _ k

theorem rt_lie (y : GL (Fin a) (Rinf E)) (X : Matrix (Fin a) (Fin a) (Rinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

theorem rt_Eop (y : GL (Fin a) (Rinf E)) (τ : InfinitePlace E) (i j : Fin a) :
    rt E a (infGL E a y) * Eop τ i j =
      (∑ k, ∑ l, (((y.val k i τ : ℝ) : ℂ) * (((y⁻¹).val j l τ : ℝ) : ℂ)) • Eop τ k l) * rt E a (infGL E a y) := by
  classical
  rw [Eop_eq, lieS_apply, rt_lie]
  congr 1
  have e : y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val =
      ∑ k, ∑ l, Matrix.single k l (Pi.single τ (y.val k i τ * (y⁻¹).val j l τ) : Rinf E) := by
    rw [Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    have h1 : (y.val * Matrix.single i j (Pi.single τ 1 : Rinf E) * (y⁻¹).val) k l =
        y.val k i * (y⁻¹).val j l * Pi.single τ 1 := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]
    rw [h1]
    funext w
    by_cases hw : w = τ
    · subst hw; simp
    · simp [Pi.single_eq_of_ne hw]
  rw [e]
  let L : Matrix (Fin a) (Fin a) (Rinf E) →ₗ[ℝ] Module.End ℂ (Sm E a) := lie E a
  have key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Rinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l) :=
    fun f => by simp only [map_sum]
  refine (key _).trans (Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_)
  rw [← Complex.ofReal_mul, ← lieS_single]
  rfl

theorem commute_cap_rt_infGL (τ : InfinitePlace E) (u : ℂ) (y : GL (Fin a) (Rinf E)) :
    Commute (cap (a := a) τ u) (rt E a (infGL E a y)) := by
  have h := GlobalTheory.CapAdInv.qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)
  let c : Rinf E →+* ℂ := Complex.ofRealHom.comp (Pi.evalRingHom (fun _ => ℝ) τ)
  have hQP : ((y⁻¹).val.map c) * (y.val.map c) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  have h2 := GlobalTheory.CapAdInv.qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)
  exact (h.trans (congrArg (· * rt E a (infGL E a y)) h2)).symm

theorem commute_cap_act (τ : InfinitePlace E) (u : ℂ) (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact commute_cap_rt_infGL τ u _
  | lie X => exact commute_cap_lie τ u X

theorem commute_Zalg_act {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (o : Op E a) : Commute z (act o) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨τ, u, rfl⟩ := hx; exact commute_cap_act τ u o
  | algebraMap r => exact Algebra.commutes r _
  | add x y _ _ hx hy => exact hx.add_left hy
  | mul x y _ _ hx hy => exact hx.mul_left hy

theorem exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  have hc := commute_Zalg_act hz
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem exists_cap_scalar (π : CuspSub E a) : ∃ c : InfinitePlace E → ℂ → ℂ, ∀ v u, ∀ φ ∈ π.V, cap v u φ = c v u • φ := by
  have hc : ∀ v u, ∃ c : ℂ, ∀ φ ∈ π.V, cap v u φ = c • φ := fun v u =>
    exists_scalar π (Algebra.subset_adjoin ⟨v, u, rfl⟩)
  choose c hc using hc
  exact ⟨c, hc⟩

theorem exists_hasInfChar (π : CuspSub E a) (v : InfinitePlace E) : ∃ m, π.HasInfChar v m := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := GlobalTheory.CuspRep.exists_multiset_qdet (Eop (a := a) v) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := exists_cap_scalar π
  have h2 : f (cap v u φ) = _ := h u
  rw [h1 v u φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 v u ψ hψ, h2]

theorem continuous_cptRep (φ : Sm E a) (g : GA E a) : Continuous fun k : Kinf E a => (cptRep E a k φ).1 g := by
  have e : (fun k : Kinf E a => (cptRep E a k φ).1 g) =
      fun k => chart φ.1 g (toL (Unitary.toUnits k : GL (Fin a) (Rinf E)).val) := by
    funext k
    rw [chart_val]
    rfl
  rw [e]
  have h3 : Continuous fun k : Kinf E a =>
      toL ((Unitary.toUnits k : GL (Fin a) (Rinf E)) : Matrix (Fin a) (Fin a) (Rinf E)) := continuous_subtype_val
  exact (φ.2 g).continuousOn.comp_continuous h3 fun k => val_mem_invSet _

end UpperTheory.V.TR.Cen
