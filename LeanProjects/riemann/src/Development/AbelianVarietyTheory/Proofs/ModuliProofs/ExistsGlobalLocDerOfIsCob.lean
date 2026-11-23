import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueInvariantVectorFieldOfTangentStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS.GlueDer

theorem rsT_eq {Y : Scheme.{0}} {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem res_res {Y : Scheme.{0}} {U V V' : Y.Opens} (h : V ≤ U) (h' : V' ≤ V) (s : Γ(Y, U)) :
    resG Y h' (resG Y h s) = resG Y (h'.trans h) s := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_app {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U) (f : Γ(X, U)) :
    resG Y h' ((m.app U).hom f) = (m.app V).hom (resG X h f) := by
  simp only [resG]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, m.naturality]
  rfl

theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn p U a) = constFn p V a := by
  simp only [resG, constFn]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)

theorem app_const {R K : Type} [CommRing R] [CommRing K] {X Y : Scheme.{0}} (x₀ : R →+* K) (p : X ⟶ Sp R)
    (q : Y ⟶ Sp K) (m : Y ⟶ X) (hm : m ≫ p = q ≫ spMap x₀) (U : X.Opens) (a : R) :
    (m.app U).hom (constFn p U a) = constFn q (m ⁻¹ᵁ U) (x₀ a) := by
  have h1 : (m.app U).hom (constFn p U a) = constFn (m ≫ p) (m ⁻¹ᵁ U) a := by
    simp only [constFn]
    rw [Scheme.Hom.app_eq_appLE]
    exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE m p ⊤ U (m ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl)
  rw [h1, hm]
  simp only [constFn]
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (x₀ a) =
      ((spMap x₀).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x₀)
    exact congrArg (fun φ => φ.hom a) this
  rw [h2]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.comp_appLE q (spMap x₀) ⊤ (m ⁻¹ᵁ U) (fun _ _ => trivial))

theorem pre_mono {Y X : Scheme.{0}} (m : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) : m ⁻¹ᵁ V ≤ m ⁻¹ᵁ U :=
  fun _ hx => h hx

theorem pre_cover {Y X : Scheme.{0}} (m : Y ⟶ X) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤) (O : X.Opens) :
    m ⁻¹ᵁ O ≤ ⨆ i, m ⁻¹ᵁ (O ⊓ W i) := by
  intro y hy
  have : m y ∈ ⨆ i, W i := by rw [hW]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hy, hi⟩

theorem glue {K : Type} [Field K] {R : Type} [CommRing R] {Y X : Scheme.{0}} (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (D : R → K) {I : Type} (W : I → X.Opens) (hW : ⨆ i, W i = ⊤)
    (e : I → ∀ O : X.Opens, Γ(X, O) → Γ(Y, m ⁻¹ᵁ O)) (he : ∀ i, LocDerK q p m D (W i) (e i))
    (hc : ∀ i j O, O ≤ W i ⊓ W j → ∀ f, e i O f = e j O f) : ∃ d₁, LocDerK q p m D ⊤ d₁ := by
  have ex : ∀ (O : X.Opens) (f : Γ(X, O)), ∃ s : Γ(Y, m ⁻¹ᵁ O), ∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = e i (O ⊓ W i) (resG X inf_le_left f) := by
    intro O f
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O)
      (fun i => e i (O ⊓ W i) (resG X inf_le_left f)) (by
        intro i j
        have hi := (he i).res (O ⊓ W i) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_left inf_le_right (resG X inf_le_left f)
        have hj := (he j).res (O ⊓ W j) ((O ⊓ W i) ⊓ (O ⊓ W j)) inf_le_right inf_le_right (resG X inf_le_left f)
        rw [rsT_eq (pre_mono m inf_le_left), res_res] at hi
        rw [rsT_eq (pre_mono m inf_le_right), res_res] at hj
        have := hc i j ((O ⊓ W i) ⊓ (O ⊓ W j)) (inf_le_inf inf_le_right inf_le_right)
          (resG X (inf_le_left.trans inf_le_left) f)
        exact hi.symm.trans (this.trans hj))
    exact ⟨s, hs⟩
  have ext : ∀ (O : X.Opens) (s t : Γ(Y, m ⁻¹ᵁ O)), (∀ i,
      resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) s = resG Y (pre_mono m (inf_le_left : O ⊓ W i ≤ O)) t) →
      s = t := fun O s t h =>
    Y.sheaf.eq_of_locally_eq' (fun i => m ⁻¹ᵁ (O ⊓ W i)) (m ⁻¹ᵁ O)
      (fun i => homOfLE (pre_mono m inf_le_left)) (pre_cover m W hW O) s t h
  choose d₁ hd using ex
  refine ⟨d₁, ?_, ?_, ?_, ?_⟩
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, hd, hd, hd, map_add, (he i).add _ inf_le_right]
  · intro O _ f f'
    refine ext O _ _ fun i => ?_
    rw [map_add, map_mul, map_mul, hd, hd, hd, map_mul, (he i).mul _ inf_le_right,
      res_app m inf_le_left, res_app m inf_le_left]
  · intro O O' h _ f
    refine ext O' _ _ fun i => ?_
    have h' : O' ⊓ W i ≤ O ⊓ W i := inf_le_inf_right _ h
    have h1 := (he i).res (O ⊓ W i) (O' ⊓ W i) h' inf_le_right (resG X inf_le_left f)
    rw [rsT_eq (pre_mono m h'), res_res, ← hd, res_res] at h1
    rw [hd, rsT_eq (pre_mono m h), res_res, res_res, h1]
  · intro O _ r
    refine ext O _ _ fun i => ?_
    rw [hd, res_const, res_const, (he i).base _ inf_le_right]

end GlobalTheory.KS.GlueDer

open GlobalTheory.KS.GlueDer in

theorem GlobalTheory.KS.exists_global_locDer_of_isCob : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D : R → K) d θ, ⨆ i, W i = ⊤ → KSCoc A₀.hom p m D W dd d θ → (∀ a, IsCob _ (θ a)) → ∃ d₁, LocDerK A₀.hom p m D ⊤ d₁ := by
  intro K _ A₀ _ g v dd _ hv hdd R _ x₀ X p m hm I W D d θ hW hc hb
  choose b hb using hb
  have H := fun a => (GlobalTheory.T.exists_unique_invariantVectorField_of_tangent K A₀ (v a) (hv.1 a)).2 (dd a) (hdd a)
  refine glue A₀.hom p m D W hW
    (fun i O f => d i O f - ∑ a, rsT (b a i) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) (fun i => ?_) ?_
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro O hO f f'
      simp only [(hc.der i).add O hO, map_add, fun a => (H a).1, mul_add, Finset.sum_add_distrib]
      ring
    · intro O hO f f'
      simp only [(hc.der i).mul O hO, map_mul, fun a => (H a).2.1, mul_add, Finset.sum_add_distrib, mul_sub,
        Finset.mul_sum, mul_left_comm (rsT _ _)]
      ring
    · intro O O' h hO f
      have h' := pre_mono m h
      rw [(hc.der i).res O O' h hO, rsT_eq h', rsT_eq h', map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      have h2 := (H a).2.2.1 _ _ ((m.app O).hom f) h'
      rw [rsT_eq h', rsT_eq h', res_app m h] at h2
      rw [map_mul, h2, rsT_eq (pre_mono m hO), rsT_eq (pre_mono m (h.trans hO)), res_res]
    · intro O hO r
      simp only [(hc.der i).base O hO, app_const x₀ p A₀.hom m hm.w, fun a => (H a).2.2.2.1, mul_zero,
        Finset.sum_const_zero, sub_zero]
  · intro i j O hO f
    have h1 := hc.diff i j O hO f
    have hi : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i := pre_mono m (hO.trans inf_le_left)
    have hj : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W j := pre_mono m (hO.trans inf_le_right)
    have h2 : ∀ a, rsT (θ a i j) (m ⁻¹ᵁ O) = rsT (b a j) (m ⁻¹ᵁ O) - rsT (b a i) (m ⁻¹ᵁ O) := by
      intro a
      rw [hb, rsT_eq (le_inf hi hj), map_sub, rsT_eq inf_le_right, rsT_eq inf_le_left, res_res, res_res,
        rsT_eq hi, rsT_eq hj]
    simp only [h2, sub_mul, Finset.sum_sub_distrib] at h1
    show _ - _ = _ - _
    linear_combination -h1
