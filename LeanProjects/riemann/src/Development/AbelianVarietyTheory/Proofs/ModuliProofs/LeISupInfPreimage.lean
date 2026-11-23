import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS
section Basic
variable {Y Z : Scheme.{0}}

theorem rsT_of_le {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) : rsT s O = resG Y h s := dif_pos h

theorem pbT_of_le (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) (s : Γ(Y, O₀)) :
    pbT f s O = (f.appLE O₀ O h).hom s := dif_pos h

theorem rsT_add {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_sub {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_neg {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Y.Opens) : rsT (-s) O = -rsT s O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_mul {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Y.Opens) : rsT (s * t) O = rsT s O * rsT t O := by
  unfold rsT; split_ifs <;> simp

theorem rsT_zero {O₀ : Y.Opens} (O : Y.Opens) : rsT (0 : Γ(Y, O₀)) O = 0 := by
  unfold rsT; split_ifs <;> simp

theorem rsT_one {O₀ O : Y.Opens} (h : O ≤ O₀) : rsT (1 : Γ(Y, O₀)) O = 1 := by
  rw [rsT_of_le h, map_one]

theorem rsT_sum {J : Type*} (S : Finset J) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Y.Opens) :
    rsT (∑ a ∈ S, s a) O = ∑ a ∈ S, rsT (s a) O := by
  unfold rsT; split_ifs <;> simp

theorem pbT_add (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s + t) O = pbT f s O + pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_sub (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s - t) O = pbT f s O - pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_neg (f : Z ⟶ Y) {O₀ : Y.Opens} (s : Γ(Y, O₀)) (O : Z.Opens) : pbT f (-s) O = -pbT f s O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_mul (f : Z ⟶ Y) {O₀ : Y.Opens} (s t : Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (s * t) O = pbT f s O * pbT f t O := by
  unfold pbT; split_ifs <;> simp

theorem pbT_zero (f : Z ⟶ Y) {O₀ : Y.Opens} (O : Z.Opens) : pbT f (0 : Γ(Y, O₀)) O = 0 := by
  unfold pbT; split_ifs <;> simp

theorem pbT_one (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ O₀) : pbT f (1 : Γ(Y, O₀)) O = 1 := by
  rw [pbT_of_le f h, map_one]

theorem pbT_sum {J : Type*} (S : Finset J) (f : Z ⟶ Y) {O₀ : Y.Opens} (s : J → Γ(Y, O₀)) (O : Z.Opens) :
    pbT f (∑ a ∈ S, s a) O = ∑ a ∈ S, pbT f (s a) O := by
  unfold pbT; split_ifs <;> simp

theorem rsT_self {O : Y.Opens} (s : Γ(Y, O)) : rsT s O = s := by
  rw [rsT_of_le le_rfl]
  simp [resG]

theorem rsT_rsT {O₀ O₁ O₂ : Y.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ O₁) (s : Γ(Y, O₀)) :
    rsT (rsT s O₁) O₂ = rsT s O₂ := by
  rw [rsT_of_le h₁, rsT_of_le h₂, rsT_of_le (h₂.trans h₁)]
  exact (congrArg (fun φ => φ.hom s)
    (Y.presheaf.map_comp (homOfLE h₁).op (homOfLE h₂).op)).symm

theorem rsT_pbT (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ O₂ : Z.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀) (h₂ : O₂ ≤ O₁)
    (s : Γ(Y, O₀)) : rsT (pbT f s O₁) O₂ = pbT f s O₂ := by
  rw [pbT_of_le f h₁, rsT_of_le h₂, pbT_of_le f (h₂.trans h₁)]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_map f h₁ (homOfLE h₂).op)

theorem pbT_rsT (f : Z ⟶ Y) {O₀ O₁ : Y.Opens} {O₂ : Z.Opens} (h₁ : O₁ ≤ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁)
    (s : Γ(Y, O₀)) : pbT f (rsT s O₁) O₂ = pbT f s O₂ := by
  rw [rsT_of_le h₁, pbT_of_le f h₂, pbT_of_le f (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.map_appLE f h₂ (homOfLE h₁).op)

theorem rsT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) {O₀ O : Y.Opens} (h : O ≤ O₀) (a : R) :
    rsT (constFn q O₀ a) O = constFn q O a := by
  rw [rsT_of_le h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_map q (U := ⊤) (V := O₀) (fun _ _ => trivial) (homOfLE h).op)

theorem pbT_constFn {R : Type} [CommRing R] (q : Y ⟶ Sp R) (f : Z ⟶ Y) {O₀ : Y.Opens} {O : Z.Opens}
    (h : O ≤ f ⁻¹ᵁ O₀) (a : R) : pbT f (constFn q O₀ a) O = constFn (f ≫ q) O a := by
  rw [pbT_of_le f h]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ O₀ O (fun _ _ => trivial) h)

theorem eq_of_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s t : Γ(Y, O)) (h : ∀ k, rsT s (V k) = rsT t (V k)) : s = t := by
  refine Y.sheaf.eq_of_locally_eq' V O (fun k => homOfLE (hV k)) hc s t fun k => ?_
  have := h k
  rw [rsT_of_le (hV k), rsT_of_le (hV k)] at this
  exact this

theorem exists_rsT_eq {J : Type} (V : J → Y.Opens) {O : Y.Opens} (hV : ∀ k, V k ≤ O) (hc : O ≤ iSup V)
    (s : ∀ k, Γ(Y, V k)) (h : ∀ k l, rsT (s k) (V k ⊓ V l) = rsT (s l) (V k ⊓ V l)) :
    ∃ t : Γ(Y, O), ∀ k, rsT t (V k) = s k := by
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' V O (fun k => homOfLE (hV k)) hc s (fun k l => by
    have := h k l
    rw [rsT_of_le inf_le_left, rsT_of_le inf_le_right] at this
    exact this)
  exact ⟨t, fun k => (rsT_of_le (hV k) _).trans (ht k)⟩

theorem le_iSup_inf_preimage (f : Z ⟶ Y) {I : Type} (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤) (O : Z.Opens) :
    O ≤ ⨆ k, O ⊓ f ⁻¹ᵁ U k := by
  intro x hx
  have : f x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩

end Basic

variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}

theorem IsCob.add {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c + c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i + b' i, fun i j => ?_⟩
  simp only [Pi.add_apply, rsT_add, hb, hb']
  ring

theorem IsCob.sub {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c - c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i - b' i, fun i j => ?_⟩
  simp only [Pi.sub_apply, rsT_sub, hb, hb']
  ring

theorem isCob_lc (q : Y ⟶ Sp K) {g : ℕ} (a : Fin g → K) (c : Fin g → C1 U) (h : ∀ x, IsCob U (c x)) :
    IsCob U (lc q a c) := by
  choose b hb using h
  refine ⟨fun i => ∑ x, constFn q (U i) (a x) * b x i, fun i j => ?_⟩
  simp only [lc, rsT_sum, rsT_mul, hb, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rsT_constFn q inf_le_left, rsT_constFn q inf_le_right]
  ring

theorem cohom_lc (q : Y ⟶ Sp K) (f : Y ⟶ Y) (hf : f ≫ q = q) {g : ℕ} (a : Fin g → K) (c c' : Fin g → C1 U)
    (h : ∀ x, Cohom f U (c x) (c' x)) : Cohom f U (lc q a c) (lc q a c') := by
  choose b hb hb' using h
  refine ⟨fun i k => ∑ x, constFn q (U i ⊓ f ⁻¹ᵁ U k) (a x) * b x i k, fun i i' k => ?_, fun i k k' => ?_⟩
  · simp only [lc, rsT_sum, rsT_mul, ← hb, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rsT_constFn q (inf_le_inf_right _ inf_le_left), rsT_constFn q (inf_le_inf_right _ inf_le_right),
      rsT_constFn q inf_le_left]
    ring
  · simp only [lc, rsT_sum, rsT_mul, pbT_sum, pbT_mul, ← hb', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ f ⁻¹ᵁ (U k ⊓ U k') := fun y hy => ⟨hy.1.2, hy.2⟩
    have e' : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U k' ≤ U i ⊓ f ⁻¹ᵁ U k' := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [rsT_constFn q inf_le_left, rsT_constFn q e', pbT_constFn q f e, hf]
    ring

theorem Cohom.isCob_sub (f : Y ⟶ Y) (hU : ⨆ i, U i = ⊤) {c c₁ c' c₁' : C1 U} (h : Cohom f U c c')
    (h₁ : Cohom f U c₁ c₁') (hc : IsCob U (c' - c₁')) : IsCob U (c - c₁) := by
  obtain ⟨b, hb, hb'⟩ := h
  obtain ⟨b₁, hb₁, hb₁'⟩ := h₁
  obtain ⟨β, hβ⟩ := hc
  have glue : ∀ i, ∃ t : Γ(Y, U i), ∀ k, rsT t (U i ⊓ f ⁻¹ᵁ U k) =
      b i k - b₁ i k + pbT f (β k) (U i ⊓ f ⁻¹ᵁ U k) := by
    intro i
    refine exists_rsT_eq (fun k => U i ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
      (le_iSup_inf_preimage f U hU _) _ fun k l => ?_
    have e : (U i ⊓ f ⁻¹ᵁ U k) ⊓ (U i ⊓ f ⁻¹ᵁ U l) ≤ U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l :=
      fun y hy => ⟨hy.1, hy.2.2⟩
    have e₁ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ f ⁻¹ᵁ (U k ⊓ U l) := fun y hy => ⟨hy.1.2, hy.2⟩
    have e₂ : U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l ≤ U i ⊓ f ⁻¹ᵁ U l := fun y hy => ⟨hy.1.1, hy.2⟩
    rw [← rsT_rsT inf_le_left e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => pbT f s (U i ⊓ f ⁻¹ᵁ U k ⊓ f ⁻¹ᵁ U l)) (hβ k l)
    simp only [Pi.sub_apply, pbT_sub] at k₀
    rw [pbT_rsT f inf_le_right e₁, pbT_rsT f inf_le_left e₁, ← hb', ← hb₁'] at k₀
    simp only [rsT_add, rsT_sub]
    rw [rsT_pbT f inf_le_right inf_le_left, rsT_pbT f inf_le_right e₂]
    linear_combination k₀
  choose t ht using glue
  refine ⟨t, fun i j => ?_⟩
  refine eq_of_rsT_eq (fun k => U i ⊓ U j ⊓ f ⁻¹ᵁ U k) (fun k => inf_le_left)
    (le_iSup_inf_preimage f U hU _) _ _ fun k => ?_
  have e₁ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U i ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_left
  have e₂ : U i ⊓ U j ⊓ f ⁻¹ᵁ U k ≤ U j ⊓ f ⁻¹ᵁ U k := inf_le_inf_right _ inf_le_right
  simp only [Pi.sub_apply, rsT_sub]
  rw [rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (t j), ← rsT_rsT inf_le_left e₁ (t i), ht, ht, ← hb, ← hb₁]
  simp only [rsT_add, rsT_sub]
  rw [rsT_pbT f inf_le_right e₁, rsT_pbT f inf_le_right e₂]
  ring

theorem cohom_calculus : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (q : Y ⟶ Sp K) (f : Y ⟶ Y) (I : Type) (U : I → Y.Opens), f ≫ q = q → ⨆ i, U i = ⊤ → (∀ c c₁ c' c₁' : C1 U, Cohom f U c c' → Cohom f U c₁ c₁' → IsCob U (c' - c₁') → IsCob U (c - c₁)) ∧ (∀ (g : ℕ) (a : Fin g → K) (c c' : Fin g → C1 U), (∀ x, Cohom f U (c x) (c' x)) → Cohom f U (lc q a c) (lc q a c')) ∧ (∀ (g : ℕ) (a : Fin g → K) (c : Fin g → C1 U), (∀ x, IsCob U (c x)) → IsCob U (lc q a c)) ∧ ∀ c c' : C1 U, IsCob U c → IsCob U c' → IsCob U (c + c') ∧ IsCob U (c - c') :=
  fun _ _ _ q f _ _ hf hU =>
    ⟨fun _ _ _ _ h h₁ hc => Cohom.isCob_sub f hU h h₁ hc, fun _ a c c' h => cohom_lc q f hf a c c' h,
      fun _ a c h => isCob_lc q a c h, fun _ _ h h' => ⟨h.add h', h.sub h'⟩⟩

end GlobalTheory.KS
end
