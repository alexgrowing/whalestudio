import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeTwoForm

section Generic

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {n : ℕ}

theorem sum_pairs {N : Type} [AddCommMonoid N] (g : Fin n → Fin n → N) (hd : ∀ i, g i i = 0) :
    ∑ i, ∑ j, g i j = ∑ i, ∑ j ∈ Finset.Ioi i, (g i j + g j i) := by
  have h1 : ∀ i, ∑ j, g i j = ∑ j ∈ Finset.Ioi i, g i j + ∑ j ∈ Finset.Iio i, g i j := by
    intro i
    have e : (Finset.univ : Finset (Fin n)) = Finset.Ioi i ∪ ({i} ∪ Finset.Iio i) := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Ioi, Finset.mem_singleton,
        Finset.mem_Iio, true_iff]; omega
    rw [e, Finset.sum_union, Finset.sum_union]
    · simp [hd]
    · simp
    · rw [Finset.disjoint_left]; intro j; simp only [Finset.mem_Ioi, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_Iio]; omega
  simp_rw [h1, Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm' (by simp)

def L2 (L : Fin n → Module.Dual A M) (i j : Fin n) : ⋀[A]^2 M →ₗ[A] A :=
  exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 ![L i, L j])

theorem wedge_functional_iota_multi (L : Fin n → Module.Dual A M) (i j : Fin n) (a b : M) :
    L2 L i j (exteriorPower.ιMulti A 2 ![a, b]) = L i a * L j b - L j a * L i b := by
  rw [L2, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two]
  simp

def wb : M →ₗ[A] M →ₗ[A] ⋀[A]^2 M :=
  LinearMap.mk₂ A (fun a b ↦ exteriorPower.ιMulti A 2 ![a, b])
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, add_mul]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply, mul_add]))
    (fun _ _ _ ↦ Subtype.ext (by simp [ExteriorAlgebra.ιMulti_apply]))

theorem wb_apply (a b : M) : wb (A := A) a b = exteriorPower.ιMulti A 2 ![a, b] := rfl

theorem wb_self (a : M) : wb (A := A) a a = 0 :=
  Subtype.ext (by simp [wb_apply, ExteriorAlgebra.ιMulti_apply])

theorem wb_swap (a b : M) : wb (A := A) b a = -wb a b :=
  Subtype.ext (by
    simpa [wb_apply, ExteriorAlgebra.ιMulti_apply] using
      eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := A) b a))

theorem eq_two (v : Fin 2 → M) : v = ![v 0, v 1] := by
  ext i; fin_cases i <;> rfl

theorem wb_expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (a b : M) :
    wb (A := A) a b = ∑ i, ∑ j ∈ Finset.Ioi i, (L i a * L j b - L j a * L i b) • wb (A := A) (e i) (e j) := by
  have h1 : wb (A := A) a b = ∑ i, ∑ j, (L i a * L j b) • wb (A := A) (e i) (e j) := by
    conv_lhs => rw [h a, h b]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_smul,
      Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mul_comm]
  rw [h1, sum_pairs _ (fun i ↦ by rw [wb_self, smul_zero])]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [wb_swap (e i) (e j), sub_smul, smul_neg, sub_eq_add_neg]

theorem expand (e : Fin n → M) (L : Fin n → Module.Dual A M) (h : ∀ x, x = ∑ i, L i x • e i)
    (z : ⋀[A]^2 M) :
    z = ∑ i, ∑ j ∈ Finset.Ioi i, L2 L i j z • wb (A := A) (e i) (e j) := by
  have hz : z ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    have e1 : exteriorPower.ιMulti A 2 v = wb (A := A) (v 0) (v 1) := by rw [wb_apply, ← eq_two]
    rw [e1]
    conv_lhs => rw [wb_expand e L h]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [wb_apply (v 0), wedge_functional_iota_multi]
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [map_add, add_smul, Finset.sum_add_distrib]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]

end Generic

section Forms

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def wedgeAt (T : C) : Glob1 F [⋀^Fin 2]→ₗ[R] Om R (F.obj T) 2 where
  toMultilinearMap := ((exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).toMultilinearMap.restrictScalars
    R).compLinearMap fun _ ↦ evForm F T
  map_eq_zero_of_eq' v i j hv hij :=
    (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R])).map_eq_zero_of_eq _
      (congrArg (evForm F T) hv) hij

def nu : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2 :=
  LinearMap.pi fun T ↦ exteriorPower.alternatingMapLinearEquiv (wedgeAt F T)

theorem nu_ιMulti (a b : Glob1 F) (T : C) :
    nu F (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T) := by
  rw [wedge_eq_ιMulti]
  change exteriorPower.alternatingMapLinearEquiv (wedgeAt F T) _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti (F.obj T) 2 (fun i ↦ evForm F T (![a, b] i)) = _
  congr 1
  ext i; fin_cases i <;> rfl

variable {F}

def Lf (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) : Module.Dual (F.obj T) Ω[F.obj T⁄R] :=
  (hP T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l)

theorem Lf_ev (hP : Par F) (l : Module.Dual R (Glob1 F)) (T : C) (x : Glob1 F) :
    Lf hP l T (evForm F T x) = algebraMap R (F.obj T) (l x) :=
  (hP T).lift_eq _ x

theorem form_pullback_evaluation {T T' : C} (φ : T ⟶ T') (x : Glob1 F) : p1 F φ (evForm F T x) = evForm F T' x :=
  (x.2 φ).symm

theorem linear_form_extension_naturality (hP : Par F) (l : Module.Dual R (Glob1 F)) {T T' : C} (φ : T ⟶ T')
    (α : Ω[F.obj T⁄R]) : Lf hP l T' (p1 F φ α) = mp F φ (Lf hP l T α) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · rw [form_pullback_evaluation, Lf_ev, Lf_ev, AlgHom.commutes]
  · rw [oneFormsMapOfFunctorMorphism_smul, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  · simp only [map_add, hy, hz]

theorem Lf_expand (hP : Par F) {n : ℕ} (w : Fin n → Glob1 F) (l : Fin n → Module.Dual R (Glob1 F))
    (h : ∀ x, x = ∑ i, l i x • w i) (T : C) (α : Ω[F.obj T⁄R]) :
    α = ∑ i, Lf hP (l i) T α • evForm F T (w i) := by
  refine (hP T).inductionOn α _ (by simp) (fun x ↦ ?_) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
  · conv_lhs => rw [h x]
    simp only [map_sum, map_smul, Lf_ev, algebraMap_smul]
  · conv_lhs => rw [hy]
    simp only [map_smul, smul_eq_mul, mul_smul, Finset.smul_sum]
  · conv_lhs => rw [hy, hz]
    simp only [map_add, add_smul, Finset.sum_add_distrib]

theorem wedge_functional_two_form_naturality (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) {T T' : C}
    (φ : T ⟶ T') (z : Om R (F.obj T) 2) :
    L2 (fun i ↦ Lf hP (l i) T') i j (pOm F 2 φ z) = mp F φ (L2 (fun i ↦ Lf hP (l i) T) i j z) := by
  have hz : z ∈ Submodule.span (F.obj T) (Set.range (exteriorPower.ιMulti (F.obj T) 2 (M := Ω[F.obj T⁄R]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, ← wedge_eq_ιMulti, pOm_wedge, wedge_eq_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    simp only [linear_form_extension_naturality, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [pOm_smul, map_smul, hx, smul_eq_mul, map_mul]

theorem wedge_functional_constant_on_image (hP : Par F) {n : ℕ} (l : Fin n → Module.Dual R (Glob1 F)) (i j : Fin n) (T : C)
    (t : ⋀[R]^2 (Glob1 F)) :
    L2 (fun i ↦ Lf hP (l i) T) i j (nu F t T) = algebraMap R (F.obj T) (L2 l i j t) := by
  have ht : t ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := Glob1 F))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [eq_two v, nu_ιMulti, wedge_eq_ιMulti, wedge_functional_iota_multi, wedge_functional_iota_multi]
    change Lf hP (l i) T (evForm F T _) * Lf hP (l j) T (evForm F T _) -
      Lf hP (l j) T (evForm F T _) * Lf hP (l i) T (evForm F T _) = _
    simp only [Lf_ev, map_sub, map_mul]
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
  | smul c x _ hx =>
    simp only [map_smul, Pi.smul_apply, hx, smul_eq_mul, map_mul]
    rw [← algebraMap_smul (F.obj T) c, map_smul, hx, smul_eq_mul]

end Forms

theorem twoFormCohSt : TwoFormCohSt := by
  intro R _ C _ F ⟨hS, hP, hF, hPr⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R (Glob1 F)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let w : Fin n → Glob1 F := fun i ↦ f (Pi.single i 1)
  let l : Fin n → Module.Dual R (Glob1 F) := fun i ↦ LinearMap.proj i ∘ₗ s
  have hdual : ∀ x, x = ∑ i, l i x • w i := by
    intro x
    have h1 : f (s x) = x := LinearMap.congr_fun hs x
    conv_lhs => rw [← h1, pi_eq_sum_univ' (s x)]
    simp [w, l, map_sum, map_smul]
  have hexp : ∀ (T : C) (z : Om R (F.obj T) 2), z = ∑ i, ∑ j ∈ Finset.Ioi i,
      L2 (fun i ↦ Lf hP (l i) T) i j z • wedge R _ (evForm F T (w i)) (evForm F T (w j)) := by
    intro T z
    conv_lhs => rw [expand (fun i ↦ evForm F T (w i)) (fun i ↦ Lf hP (l i) T)
      (Lf_expand hP w l hdual T) z]
    simp only [wb_apply, wedge_eq_ιMulti]
  refine ⟨nu F, nu_ιMulti F, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro t ht
    have h0 : ∀ i j, L2 l i j t = 0 := by
      intro i j
      apply hS.2
      rw [map_zero]
      funext T
      have := wedge_functional_constant_on_image hP l i j T t
      rw [ht] at this
      simpa using this.symm
    rw [expand w l hdual t]
    simp [h0]
  · intro u hu
    have hc : ∀ i j, ∃ r : R, ∀ T, algebraMap R (F.obj T) r = L2 (fun i ↦ Lf hP (l i) T) i j (u T) := by
      intro i j
      have hz : d0 F (fun T ↦ L2 (fun i ↦ Lf hP (l i) T) i j (u T)) = 0 := by
        funext T T' φ
        rw [amitsur_d0_apply, hu T T' φ, wedge_functional_two_form_naturality, sub_self]
        rfl
      obtain ⟨r, hr⟩ := (hS.1 _).1 hz
      exact ⟨r, fun T ↦ congrFun hr T⟩
    choose r hr using hc
    refine ⟨∑ i, ∑ j ∈ Finset.Ioi i, r i j • wb (A := R) (w i) (w j), ?_⟩
    funext T
    conv_rhs => rw [hexp T (u T)]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, wb_apply, nu_ιMulti]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hr, algebraMap_smul]
    rfl

end GlobalTheory.CompanionTheory.HodgeTwoForm
