import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PadicIntermediateFieldIntRingCompleteDvr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.AdicExt

def ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {x | ‖φ x‖ ≤ c}
  zero_mem' := by simpa using hc
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  smul_mem' := fun a b hb => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (hφ a)).trans hb

theorem mem_ballIdeal {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] {φ : R →+* K}
    {hφ : ∀ x, ‖φ x‖ ≤ 1} {c : ℝ} {hc : 0 ≤ c} {x : R} : x ∈ ballIdeal φ hφ c hc ↔ ‖φ x‖ ≤ c := Iff.rfl

theorem exists_bound {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K] (φ : R →+* K)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (I : Ideal R) (hI : I.FG) (h : ∀ x ∈ I, ‖φ x‖ < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ n : ℕ, ∀ x ∈ I ^ n, ‖φ x‖ ≤ c ^ n := by
  obtain ⟨s, rfl⟩ := hI
  obtain ⟨c, hc0, hc1, hs⟩ : ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x ∈ s, ‖φ x‖ ≤ c := by
    refine ⟨(s.sup fun x => ‖φ x‖₊ : NNReal), NNReal.coe_nonneg _, ?_, fun x hx => ?_⟩
    · have : (s.sup fun x => ‖φ x‖₊ : NNReal) < 1 :=
        (Finset.sup_lt_iff (by simp)).2 fun x hx => h x (Ideal.subset_span hx)
      exact_mod_cast this
    · have : ‖φ x‖₊ ≤ (s.sup fun x => ‖φ x‖₊ : NNReal) := Finset.le_sup (f := fun x => ‖φ x‖₊) hx
      exact_mod_cast this
  have h1 : Ideal.span (s : Set R) ≤ ballIdeal φ hφ c hc0 := Ideal.span_le.2 fun x hx => hs x hx
  refine ⟨c, hc0, hc1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simpa using hφ x
  | succ n ih =>
    have : Ideal.span (s : Set R) ^ (n + 1) ≤ ballIdeal φ hφ (c ^ (n + 1)) (pow_nonneg hc0 _) := by
      rw [pow_succ, Ideal.mul_le]
      intro a ha b hb
      rw [mem_ballIdeal, map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih a ha) (h1 hb) (norm_nonneg _) (pow_nonneg hc0 _)
    exact fun x hx => this hx

theorem norm_le_of_mem_smul_top {R A K : Type} [CommRing R] [CommRing A] [Algebra R A] [NormedField K]
    [IsUltrametricDist K] (F : A →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (J : Ideal R) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ J, ‖F (algebraMap R A x)‖ ≤ c) (y : A) (hy : y ∈ J • (⊤ : Submodule R A)) :
    ‖F y‖ ≤ c := by
  refine Submodule.smul_induction_on (p := fun y => ‖F y‖ ≤ c) hy (fun a ha w _ => ?_) (fun a b ha hb => ?_)
  · rw [Algebra.smul_def, map_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hF w)).trans (h a ha)
  · rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem ringHom_ext_of_norm {R K : Type} [CommRing R] [NormedField K] [IsUltrametricDist K]
    (I : Ideal R) (hI : I.FG) (F G : AdicCompletion I R →+* K) (hF : ∀ x, ‖F x‖ ≤ 1) (hG : ∀ x, ‖G x‖ ≤ 1)
    (h : ∀ x ∈ I, ‖F (algebraMap R _ x)‖ < 1) (e : ∀ a, F (algebraMap R _ a) = G (algebraMap R _ a)) :
    F = G := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_bound (F.comp (algebraMap R _)) (fun x => hF _) I hI h
  ext r
  have key : ∀ n : ℕ, ‖F r - G r‖ ≤ c ^ n := by
    intro n
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R n r)
    have hm : r - algebraMap R _ a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub, ← ha, sub_eq_zero]
      rfl
    have h1 := norm_le_of_mem_smul_top F hF _ _ (pow_nonneg hc0 n) (hc n) _ hm
    have h2 := norm_le_of_mem_smul_top G hG _ _ (pow_nonneg hc0 n)
      (fun x hx => by rw [← e]; exact hc n x hx) _ hm
    have : F r - G r = F (r - algebraMap R _ a) + - G (r - algebraMap R _ a) := by
      rw [map_sub, map_sub, e]; ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
  have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1) key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem completion_ringHom_ext : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (p : ℕ) [Fact p.Prime] (f g : AdicCompletion (maximalIdeal O) O →+* OO p), IsLocalHom (f.comp (algebraMap O _)) → (∀ a, f (algebraMap O _ a) = g (algebraMap O _ a)) → f = g := by
  intro O _ _ _ p _ f g hf e
  have := ringHom_ext_of_norm (maximalIdeal O) (maximalIdeal O).fg_of_isNoetherianRing
    ((OO p).subtype.comp f) ((OO p).subtype.comp g)
    (fun x => (mem_OO_iff _).1 (f x).2) (fun x => (mem_OO_iff _).1 (g x).2)
    (fun x hx => (not_isUnit_OO_iff _).1 fun hu =>
      (IsLocalRing.mem_maximalIdeal x).1 hx (hf.map_nonunit x hu))
    (fun a => congrArg Subtype.val (e a))
  ext r
  exact RingHom.congr_fun this r

end GlobalTheory.AdicExt
