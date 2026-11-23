import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.TensorProductTheorem.Restricted
import GroundTheory.AutomorphicForms.TensorProductTheorem.TotallyDisconnectedSpaceRestrictedProduct

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open PiTensorProduct Filter Function Module Set Topology

open scoped TensorProduct RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}

omit [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  hKo hKc in

theorem tensorRep_mulSingle_tprod [DecidableEq ι] (a : ι) (k : G a) (x : ∀ v, V v) :
    tensorRep K π (RestrictedProduct.mulSingle K a k) (tprod ℂ x) =
      tprod ℂ (Function.update x a (π a k (x a))) := by
  rw [tensorRep_tprod]
  congr 1
  funext v
  by_cases hv : v = a
  · subst hv
    simp
  · rw [Function.update_of_ne hv, RestrictedProduct.coe_mulSingle_apply,
      Pi.mulSingle_eq_of_ne hv, map_one, Module.End.one_apply]

omit [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  hKo hKc in
theorem mulSingle_mem_boxSubgroup [DecidableEq ι] {K' : ∀ v, Subgroup (G v)} {a : ι} {k : G a}
    (hk : k ∈ K' a) :
    RestrictedProduct.mulSingle K a k ∈ boxSubgroup K K' := by
  intro v
  rw [RestrictedProduct.coe_mulSingle_apply]
  by_cases hv : v = a
  · subst hv
    simpa using hk
  · rw [Pi.mulSingle_eq_of_ne hv]
    exact (K' v).one_mem

theorem exists_boxSubgroup_fixing (hπ : ∀ v, IsSmooth (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) {t : ⨂[ℂ] v, V v}
    (ht : t ∈ restrictedTensor ξ) :
    ∃ K' : ∀ v, Subgroup (G v), (∀ v, IsCompact (K' v : Set (G v))) ∧
      (∀ v, IsOpen (K' v : Set (G v))) ∧ (∀ v, K' v ≤ K v) ∧ (∀ᶠ v in cofinite, K' v = K v) ∧
        ∀ g ∈ boxSubgroup K K', tensorRep K π g t = t := by
  classical
  have hKcs : ∀ v, IsCompact (K v : Set (G v)) := fun v => isCompact_iff_compactSpace.2 (hKc v)
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, rfl⟩ := ht
    have hL : ∀ v, ∃ L : Subgroup (G v), IsCompact (L : Set (G v)) ∧ IsOpen (L : Set (G v)) ∧
        L ≤ K v ∧ ∀ g ∈ L, π v g (x v) = x v := by
      intro v
      obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset
        (((hπ v) (x v)).inter (hKo.out v) |>.mem_nhds ⟨(stabilizerOf (π v) (x v)).one_mem,
          (K v).one_mem⟩)
      exact ⟨L, hLc, L.isOpen, fun g hg => (hLU hg).2, fun g hg => (hLU hg).1⟩
    choose L hLc hLo hLK hLfix using hL
    set K' : ∀ v, Subgroup (G v) :=
      fun v => if x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) then K v else L v
    refine ⟨K', fun v => ?_, fun v => ?_, fun v => ?_, ?_, fun g hg => ?_⟩
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLc v, hKcs v]
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLo v, hKo.out v]
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLK v]
    · filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, hξ] with v h1 h2
      simp [K', h1, h2]
    · rw [tensorRep_tprod]
      congr 1
      funext v
      have hgv := hg v
      by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v)
      · simp only [K', h, and_self, if_true] at hgv
        rw [h.1]
        exact h.2 _ hgv
      · simp only [K', h, if_false] at hgv
        exact hLfix v _ hgv
  | zero =>
    exact ⟨K, hKcs, fun v => hKo.out v, fun v => le_rfl, Eventually.of_forall fun v => rfl,
      fun g _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := ha
    obtain ⟨B, hBc, hBo, hBK, hBe, hBfix⟩ := hb
    refine ⟨fun v => A v ⊓ B v, fun v => (hAc v).inter_right (Subgroup.isClosed_of_isOpen _
      (hBo v)), fun v => (hAo v).inter (hBo v), fun v => inf_le_left.trans (hAK v), ?_,
      fun g hg => ?_⟩
    · filter_upwards [hAe, hBe] with v h1 h2
      rw [h1, h2, inf_idem]
    · rw [map_add, hAfix g fun v => (hg v).1, hBfix g fun v => (hg v).2]
  | smul c a _ ha =>
    obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := ha
    exact ⟨A, hAc, hAo, hAK, hAe, fun g hg => by rw [map_smul, hAfix g hg]⟩

theorem isSmooth_restrictedTensorRep (hπ : ∀ v, IsSmooth (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    IsSmooth (restrictedTensorRep π ξ hξ) := by
  intro t
  obtain ⟨K', hK'c, hK'o, -, hK'e, hfix⟩ := exists_boxSubgroup_fixing hπ hξ t.2
  refine Subgroup.isOpen_mono (H₁ := boxSubgroup K K') (fun g hg => ?_)
    (isOpen_boxSubgroup hK'o hK'e)
  exact Subtype.ext (hfix g hg)

section Window

variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)

include hK'c hK'e in
omit hKc in
theorem isCompact_boxSubgroup_of_eq :
    IsCompact (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) :=
  isCompact_boxSubgroup hK'c (hK'e.mono fun v h => h.le)

include hπ hξ hK'c hK'o hK'e in

theorem coe_fixedProj_tprod {x : ∀ v, V v} (hx : IsRestricted ξ x) :
    ((fixedProj (restrictedTensorRep π ξ hξ) (isSmooth_restrictedTensorRep hπ hξ)
      (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
      ⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩ : restrictedTensor ξ) : ⨂[ℂ] v, V v) =
      tprod ℂ fun v => (fixedProj (π v) (hπ v) (hK'c v) (hK'o v) (x v) : V v) := by
  classical
  set ρW := restrictedTensorRep π ξ hξ
  set H := boxSubgroup K K'
  set y : ∀ v, V v := fun v => (fixedProj (π v) (hπ v) (hK'c v) (hK'o v) (x v) : V v)
  have hy : IsRestricted ξ y := by
    filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, hξ, hK'e] with v h1 h2 h3
    simp only [y, h1]
    exact fixedProj_apply_of_mem (hπ v) (hK'c v) (hK'o v) (by rw [h3]; exact h2)
  have hyfix : (⟨tprod ℂ y, tprod_mem_restrictedTensor hy⟩ : restrictedTensor ξ) ∈
      fixedVectors ρW H := by
    intro g hg
    refine Subtype.ext ?_
    show tensorRep K π g (tprod ℂ y) = tprod ℂ y
    rw [tensorRep_tprod]
    congr 1
    funext v
    exact (fixedProj (π v) (hπ v) (hK'c v) (hK'o v) (x v)).2 _ (hg v)
  have key := (fixedProj_eq_iff (isSmooth_restrictedTensorRep hπ hξ)
    (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
    (v := ⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩) (w := ⟨_, hyfix⟩)).2 ?_
  · rw [key]

  have hpw : ∀ s : Finset ι, IsRestricted ξ (s.piecewise y x) := by
    intro s
    filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, hy] with v h1 h2
    by_cases hv : v ∈ s
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv, h2]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv, h1]
  have hstep : ∀ s : Finset ι, (⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩ : restrictedTensor ξ) -
      ⟨tprod ℂ (s.piecewise y x), tprod_mem_restrictedTensor (hpw s)⟩ ∈ coinvariantsKer ρW H := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.piecewise_empty, sub_self]
      exact Submodule.zero_mem _
    | insert a s has ih =>
      have hins : (insert a s).piecewise y x = Function.update (s.piecewise y x) a (y a) := by
        funext v
        by_cases hv : v = a
        · subst hv
          rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_self _ _), Function.update_self]
        · rw [Function.update_of_ne hv]
          by_cases hvs : v ∈ s
          · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_of_mem hvs),
              Finset.piecewise_eq_of_mem _ _ _ hvs]
          · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp [hv, hvs]),
              Finset.piecewise_eq_of_notMem _ _ _ hvs]
      have hza : s.piecewise y x a = x a := Finset.piecewise_eq_of_notMem _ _ _ has
      set z := s.piecewise y x
      have hz : IsRestricted ξ z := hpw s

      let L : V a →ₗ[ℂ] restrictedTensor ξ :=
        LinearMap.codRestrict (restrictedTensor ξ) ((PiTensorProduct.tprod ℂ).toLinearMap z a)
          fun u => tprod_mem_restrictedTensor (hz.update a u)
      have hL : ∀ u, (L u : ⨂[ℂ] v, V v) = tprod ℂ (Function.update z a u) := fun u => rfl
      have hLco : coinvariantsKer (π a) (K' a) ≤ (coinvariantsKer ρW H).comap L := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨⟨⟨k, hk⟩, u⟩, rfl⟩
        show L ((π a).comp (K' a).subtype ⟨k, hk⟩ u - u) ∈ coinvariantsKer ρW H
        rw [map_sub]
        change L (π a k u) - L u ∈ coinvariantsKer ρW H
        have hact : L (π a k u) = ρW (RestrictedProduct.mulSingle K a k)
            (L u) := by
          refine Subtype.ext ?_
          rw [coe_restrictedTensorRep_apply, hL, hL, tensorRep_mulSingle_tprod,
            Function.update_idem, Function.update_self]
        rw [hact]
        exact sub_mem_coinvariantsKer (mulSingle_mem_boxSubgroup hk) _
      have hmem := hLco (sub_fixedProj_mem (hπ a) (hK'c a) (hK'o a) (x a))
      rw [Submodule.mem_comap, map_sub] at hmem
      have heq : (⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩ : restrictedTensor ξ) -
          ⟨tprod ℂ ((insert a s).piecewise y x), tprod_mem_restrictedTensor (hpw _)⟩ =
          ((⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩ : restrictedTensor ξ) -
            ⟨tprod ℂ z, tprod_mem_restrictedTensor hz⟩) + (L (x a) - L (y a)) := by
        refine Subtype.ext ?_
        simp only [Submodule.coe_sub, Submodule.coe_add, hL]
        rw [hins, ← hza, Function.update_eq_self]
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hmem
  set F := (isRestricted_iff_finite.1 (hx.and hy |>.mono fun v h => h.1.trans h.2.symm :
    IsRestricted y x)).toFinset
  have hFy : F.piecewise y x = y := by
    funext v
    by_cases hv : v ∈ F
    · rw [Finset.piecewise_eq_of_mem _ _ _ hv]
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hv]
      simpa [F] using hv
  have := hstep F
  simp only [hFy] at this
  exact this

end Window

section Admissible

variable (hπ : ∀ v, IsAdmissible (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v)))

omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in

def windowEmbed [DecidableEq ι] (ξ : ∀ v, V v) (S : Finset ι) :
    (⨂[ℂ] v : S, fixedVectors (π v) (K' v)) →ₗ[ℂ] ⨂[ℂ] v, V v :=
  finiteEmbed ξ S ∘ₗ PiTensorProduct.map fun v => (fixedVectors (π v) (K' v)).subtype

omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem windowEmbed_tprod [DecidableEq ι] (S : Finset ι)
    (w : ∀ v : S, fixedVectors (π v) (K' v)) :
    windowEmbed ξ S (tprod ℂ w) = tprod ℂ (extend ξ S fun v => (w v : V v)) := by
  rw [windowEmbed, LinearMap.comp_apply, PiTensorProduct.map_tprod, finiteEmbed_tprod]
  rfl

include hπ hK'c hK'o in
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem finiteDimensional_range_windowEmbed [DecidableEq ι] (S : Finset ι) :
    FiniteDimensional ℂ (LinearMap.range (windowEmbed (π := π) (K' := K') ξ S)) := by
  have : ∀ v : S, FiniteDimensional ℂ (fixedVectors (π v) (K' v)) :=
    fun v => (hπ v).2 _ (hK'c v) (hK'o v)
  exact LinearMap.finiteDimensional_range _

include hπ hK'c hK'o in

theorem le_range_windowEmbed [DecidableEq ι] (hK'e : ∀ᶠ v in cofinite, K' v = K v)
    (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
    (hSgel : ∀ v ∉ S, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v)) :
    (fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K')).map
        (restrictedTensor ξ).subtype ≤
      LinearMap.range (windowEmbed (π := π) (K' := K') ξ S) := by
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  rintro _ ⟨t, ht, rfl⟩
  have hHc := isCompact_boxSubgroup_of_eq hK'c hK'e
  have hHo := isOpen_boxSubgroup hK'o hK'e
  have hts := isSmooth_restrictedTensorRep hπs hξ
  have h1 : t = (fixedProj _ hts hHc hHo t : restrictedTensor ξ) :=
    (fixedProj_apply_of_mem hts hHc hHo ht).symm
  rw [Submodule.subtype_apply, h1]
  obtain ⟨t₀, ht₀⟩ := t
  clear h1 ht
  induction ht₀ using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, rfl⟩ := ht
    rw [coe_fixedProj_tprod hπs hξ hK'c hK'o hK'e hx]
    set y : ∀ v, V v := fun v => (fixedProj (π v) (hπs v) (hK'c v) (hK'o v) (x v) : V v)
    have hyfix : ∀ v, y v ∈ fixedVectors (π v) (K' v) := fun v => Subtype.prop _
    have hy : IsRestricted ξ y := by
      filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, hξ, hK'e] with v h1 h2 h3
      simp only [y, h1]
      exact fixedProj_apply_of_mem (hπs v) (hK'c v) (hK'o v) (by rw [h3]; exact h2)
    have hc : ∀ v, ∃ c : ℂ, v ∉ S → y v = c • ξ v := by
      intro v
      by_cases hv : v ∈ S
      · exact ⟨1, fun h => absurd hv h⟩
      · obtain ⟨c, hc⟩ := hSgel v hv (y v) (by rw [← hSK v hv]; exact hyfix v)
        exact ⟨c, fun _ => hc⟩
    choose c hc using hc
    set F : Finset ι := (isRestricted_iff_finite.1 hy).toFinset.filter (· ∉ S)
    set m : ∀ v, V v := extend ξ S fun v => y v
    have hym : F.piecewise (fun v => c v • m v) m = y := by
      funext v
      by_cases hvF : v ∈ F
      · rw [Finset.piecewise_eq_of_mem _ _ _ hvF]
        have hvS : v ∉ S := (Finset.mem_filter.1 hvF).2
        simp only [m, extend, hvS, dif_neg, not_false_eq_true]
        exact (hc v hvS).symm
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hvF]
        by_cases hvS : v ∈ S
        · simp [m, extend, hvS]
        · have : y v = ξ v := by
            by_contra hne
            exact hvF (Finset.mem_filter.2 ⟨by simpa using hne, hvS⟩)
          simp [m, extend, hvS, this]
    rw [← hym, MultilinearMap.map_piecewise_smul]
    refine Submodule.smul_mem _ _ ⟨tprod ℂ fun v => ⟨y v, hyfix v⟩, ?_⟩
    rw [windowEmbed_tprod]
  | zero =>
    exact (show ((fixedProj _ hts hHc hHo (0 : restrictedTensor ξ) : restrictedTensor ξ) :
      ⨂[ℂ] v, V v) ∈ _ by rw [map_zero]; exact Submodule.zero_mem _)
  | add a b ha' hb' ha hb =>
    have := map_add (fixedProj _ hts hHc hHo) ⟨a, ha'⟩ ⟨b, hb'⟩
    rw [show (⟨a + b, Submodule.add_mem _ ha' hb'⟩ : restrictedTensor ξ) = ⟨a, ha'⟩ + ⟨b, hb'⟩
      from rfl, this, Submodule.coe_add]
    exact Submodule.add_mem _ ha hb
  | smul r a ha' ha =>
    have := map_smul (fixedProj _ hts hHc hHo) r ⟨a, ha'⟩
    rw [show (⟨r • a, Submodule.smul_mem _ r ha'⟩ : restrictedTensor ξ) = r • ⟨a, ha'⟩
      from rfl, this, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ ha

end Admissible

theorem isAdmissible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) :
    IsAdmissible (restrictedTensorRep π ξ hξ) := by
  classical
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  refine ⟨isSmooth_restrictedTensorRep hπs hξ, fun H hHc hHo => ?_⟩
  obtain ⟨K', hK'c, hK'o, -, hK'e, hsub⟩ := exists_boxSubgroup_subset
    (fun v => isCompact_iff_compactSpace.2 (hKc v)) (hHo.mem_nhds H.one_mem)
  set S : Finset ι := ((Filter.eventually_cofinite.1 ((hK'e.and hgel).and hξ))).toFinset
  have hS : ∀ v ∉ S, K' v = K v ∧ (∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) ∧
      ξ v ∈ fixedVectors (π v) (K v) := fun v hv => by simpa [S] using hv
  have hle := le_range_windowEmbed hπ hξ hK'c hK'o hK'e S (fun v hv => (hS v hv).1)
    (fun v hv => (hS v hv).2.1) (fun v hv => (hS v hv).2.2)
  have hfin := finiteDimensional_range_windowEmbed hπ hK'c hK'o (ξ := ξ) S
  have hbox : FiniteDimensional ℂ (fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K')) := by
    let f := ((restrictedTensor ξ).subtype ∘ₗ
      (fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K')).subtype)
    have hf : ∀ a b, f a = f b → a = b := fun a b h => Subtype.ext (Subtype.ext h)
    let f' := LinearMap.codRestrict (LinearMap.range (windowEmbed (π := π) (K' := K') ξ S)) f
      (fun t => hle ⟨t, t.2, rfl⟩)
    exact Module.Finite.of_injective f' (fun a b h => hf a b (by
      have := congrArg Subtype.val h
      simpa [f'] using this))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hsub)

end RestrictedTensor

end GroundTheory.Automorphic
