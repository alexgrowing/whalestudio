import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.Smooth
import GroundTheory.AutomorphicForms.TensorProductTheorem.Window

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open PiTensorProduct Filter Function Module Set Topology

open scoped TensorProduct RestrictedProduct

variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem tprod_ne_zero {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (h0 : ∀ v, x v ≠ 0) :
    tprod ℂ x ≠ 0 := by
  have hex : ∀ v, ∃ f : Dual ℂ (V v), f (x v) = 1 := by
    intro v
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (x v) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 v ((Module.forall_dual_apply_eq_zero_iff ℂ (x v)).1 hcon)
    exact ⟨(f (x v))⁻¹ • f, by simp [hf]⟩
  choose l hl using hex
  have hl' : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    (show ∀ᶠ v in cofinite, x v = ξ v from hx).mono fun v h => by rw [← h, hl v]
  intro h
  have := evalForm_tprod (l := l) (hl := hl') hx
  rw [h, map_zero] at this
  simp [hl] at this

omit [∀ v, Module ℂ (V v)] in

theorem nontrivial_of_isIrreducible {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ H W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩

variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}

omit [∀ v, Module ℂ (V v)] in
theorem map_update_id_mul {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) (a b : End ℂ (M i)) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (a * b)) =
      PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i a) *
        PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i b) := by
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]
    rfl

omit [∀ v, Module ℂ (V v)] in
theorem map_update_id_one {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i 1) =
      LinearMap.id := by
  have : Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i 1 =
      fun j => (LinearMap.id : M j →ₗ[ℂ] M j) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hj]
  rw [this, PiTensorProduct.map_id]

section Window

variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
  [DecidableEq ι] (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
  (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v))

include hSK hSξ in
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem windowEmbed_mem (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ∃ h : windowEmbed ξ S t ∈ restrictedTensor ξ,
      (⟨windowEmbed ξ S t, h⟩ : restrictedTensor ξ) ∈
        fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    have hmem : windowEmbed ξ S (c • tprod ℂ w) ∈ restrictedTensor ξ := by
      rw [map_smul, windowEmbed_tprod]
      exact Submodule.smul_mem _ _ (tprod_mem_restrictedTensor (isRestricted_extend ξ S _))
    refine ⟨hmem, fun g hg => Subtype.ext ?_⟩
    show tensorRep K π g (windowEmbed ξ S (c • tprod ℂ w)) = windowEmbed ξ S (c • tprod ℂ w)
    rw [map_smul, map_smul, windowEmbed_tprod, tensorRep_tprod]
    congr 2
    funext v
    unfold extend
    split_ifs with hv
    · exact (w ⟨v, hv⟩).2 _ (hg v)
    · exact hSξ v hv _ (hSK v hv ▸ hg v)
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by rw [map_add]; exact Submodule.add_mem _ ha1 hb1, ?_⟩
    have := Submodule.add_mem _ ha2 hb2
    convert this using 1
    exact Subtype.ext (map_add _ _ _)

def windowEmbedFixed : (⨂[ℂ] v : S, fixedVectors (π v) (K' v)) →ₗ[ℂ]
    fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (restrictedTensor ξ) (windowEmbed ξ S)
    fun t => (windowEmbed_mem hξ S hSK hSξ t).1) fun t => (windowEmbed_mem hξ S hSK hSξ t).2

omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem coe_windowEmbedFixed (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ((windowEmbedFixed hξ S hSK hSξ t : restrictedTensor ξ) : ⨂[ℂ] v, V v) =
      windowEmbed ξ S t :=
  rfl

include hπ hK'c hK'o hK'e in

theorem lift_adjoin_heckeOps (v : S) {a : End ℂ (fixedVectors (π v) (K' v))}
    (ha : a ∈ Algebra.adjoin ℂ (heckeOps (hπ v) (hK'c v) (hK'o v))) :
    ∃ A ∈ Algebra.adjoin ℂ (heckeOps (isSmooth_restrictedTensorRep hπ hξ)
        (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)),
      ∀ t, A (windowEmbedFixed hξ S hSK hSξ t) =
        windowEmbedFixed hξ S hSK hSξ
          (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) v a) t) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    refine ⟨heckeOp _ _ _ (RestrictedProduct.mulSingle K v g),
      Algebra.subset_adjoin (heckeOp_mem_heckeOps _ _ _ _), fun t => ?_⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c w =>
      rw [map_smul, map_smul, map_smul, map_smul]
      congr 1
      refine Subtype.ext (Subtype.ext ?_)
      rw [heckeOp_apply]
      have hx : IsRestricted ξ (extend ξ S fun u => (w u : V u)) := isRestricted_extend ξ S _
      have hx' : IsRestricted ξ (Function.update (extend ξ S fun u => (w u : V u)) v
          (π v g (w v))) := hx.update _ _
      have hρ : restrictedTensorRep π ξ hξ (RestrictedProduct.mulSingle K v g)
          (windowEmbedFixed hξ S hSK hSξ (tprod ℂ w) : restrictedTensor ξ) =
          ⟨tprod ℂ _, tprod_mem_restrictedTensor hx'⟩ := by
        refine Subtype.ext ?_
        rw [coe_restrictedTensorRep_apply, coe_windowEmbedFixed, windowEmbed_tprod,
          tensorRep_mulSingle_tprod]
        congr 2
        simp [extend]
      rw [hρ, coe_fixedProj_tprod hπ hξ hK'c hK'o hK'e hx', coe_windowEmbedFixed,
        PiTensorProduct.map_tprod, windowEmbed_tprod]
      congr 1
      funext u
      by_cases huv : u = v
      · subst huv
        simp [extend, heckeOp_apply]
      · rw [Function.update_of_ne huv]
        unfold extend
        split_ifs with hu
        · have hne : (⟨u, hu⟩ : S) ≠ v := fun h => huv (congrArg Subtype.val h)
          dsimp only
          rw [Function.update_of_ne hne]
          exact fixedProj_apply_of_mem (hπ u) (hK'c u) (hK'o u) (w ⟨u, hu⟩).2
        · exact fixedProj_apply_of_mem (hπ u) (hK'c u) (hK'o u) (hSK u hu ▸ hSξ u hu)
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, fun t => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      PiTensorProduct.map_update_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      map_update_id_one]
    rfl
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, hAt⟩ := ha
    obtain ⟨B, hB, hBt⟩ := hb
    refine ⟨A + B, Subalgebra.add_mem _ hA hB, fun t => ?_⟩
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply, LinearMap.add_apply, hAt, hBt,
      map_add]
  | mul a b _ _ ha hb =>
    obtain ⟨A, hA, hAt⟩ := ha
    obtain ⟨B, hB, hBt⟩ := hb
    refine ⟨A * B, Subalgebra.mul_mem _ hA hB, fun t => ?_⟩
    rw [Module.End.mul_apply, hBt, hAt, map_update_id_mul, Module.End.mul_apply]

end Window

theorem isSimpleUnder_heckeOps_box (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
    (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
    (hne : fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') ≠ ⊥) :
    IsSimpleUnder (heckeOps (isSmooth_restrictedTensorRep (fun v => (hπ v).1) hξ)
      (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)) := by
  classical
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  set S : Finset ι := ((Filter.eventually_cofinite.1 ((hK'e.and hgel).and hξ))).toFinset
  have hS : ∀ v ∉ S, K' v = K v ∧ (∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) ∧
      ξ v ∈ fixedVectors (π v) (K v) := fun v hv => by simpa [S] using hv
  have hSK : ∀ v ∉ S, K' v = K v := fun v hv => (hS v hv).1
  have hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v) := fun v hv => (hS v hv).2.2
  have hle := le_range_windowEmbed hπ hξ hK'c hK'o hK'e S hSK (fun v hv => (hS v hv).2.1) hSξ
  set J := windowEmbedFixed (π := π) (K' := K') hξ S hSK hSξ
  have hJ : Function.Surjective J := by
    intro t
    obtain ⟨s, hs⟩ := hle ⟨t, t.2, rfl⟩
    exact ⟨s, Subtype.ext (Subtype.ext hs)⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  obtain ⟨s, rfl⟩ := hJ z
  have hs0 : s ≠ 0 := by rintro rfl; exact hz0 (map_zero _)

  have hMnt : ∀ v : S, Nontrivial (fixedVectors (π v) (K' v)) := by
    intro v
    by_contra hv
    rw [not_nontrivial_iff_subsingleton] at hv
    apply hs0
    have : ∀ t : ⨂[ℂ] u : S, fixedVectors (π u) (K' u), t = 0 := by
      intro t
      induction t using PiTensorProduct.induction_on with
      | smul_tprod c w =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero v (Subsingleton.elim _ _), smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    exact this s
  have hfd : ∀ v : S, FiniteDimensional ℂ (fixedVectors (π v) (K' v)) :=
    fun v => (hπ v).2 _ (hK'c v) (hK'o v)

  let b : ∀ v : S, Basis (Basis.ofVectorSpaceIndex ℂ (fixedVectors (π v) (K' v))) ℂ
      (fixedVectors (π v) (K' v)) := fun v => Basis.ofVectorSpace ℂ _
  let B := Basis.piTensorProduct b
  obtain ⟨k, hk⟩ : ∃ k, B.repr s k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs0 (B.repr.injective (Finsupp.ext fun k => by simp [hcon k]))
  have hadj : ∀ v : S, Algebra.adjoin ℂ (heckeOps (hπs v) (hK'c v) (hK'o v)) = ⊤ := fun v =>
    have : (π v).IsIrreducible := hirr v
    adjoin_eq_top (isSimpleUnder_heckeOps (hπs v) (hK'c v) (hK'o v)
      (Submodule.nontrivial_iff_ne_bot.1 (hMnt v)))
  have hpadj := IsStable.adjoin hp

  have htarget : ∀ w : ∀ v : S, fixedVectors (π v) (K' v), J (tprod ℂ w) ∈ p := by
    intro w
    let r : ∀ v : S, End ℂ (fixedVectors (π v) (K' v)) := fun v => (b v).coord (k v) |>.smulRight (w v)
    have hstep : ∀ T : Finset S, J (PiTensorProduct.map (T.piecewise r fun _ => LinearMap.id) s) ∈ p := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.piecewise_empty, PiTensorProduct.map_id, LinearMap.id_apply]
        exact hz
      | insert v T hvT ih =>
        obtain ⟨A, hA, hAt⟩ := lift_adjoin_heckeOps hπs hξ hK'c hK'o hK'e S hSK hSξ v
          (a := r v) (by rw [hadj v]; trivial)
        have hmap : (PiTensorProduct.map ((insert v T).piecewise r fun _ => LinearMap.id)) =
            PiTensorProduct.map (Function.update (fun _ => LinearMap.id) v (r v)) *
              PiTensorProduct.map (T.piecewise r fun _ => LinearMap.id) := by
          rw [← PiTensorProduct.map_mul]
          congr 1
          funext u
          by_cases hu : u = v
          · subst hu
            rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_self _ _),
              Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ hvT]
            rfl
          · rw [Function.update_of_ne hu]
            by_cases huT : u ∈ T
            · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_of_mem huT),
                Finset.piecewise_eq_of_mem _ _ _ huT]
              rfl
            · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp [hu, huT]),
                Finset.piecewise_eq_of_notMem _ _ _ huT]
              rfl
        rw [hmap, Module.End.mul_apply, ← hAt]
        exact hpadj A hA _ ih
    have hall := hstep Finset.univ
    rw [Finset.piecewise_univ] at hall
    have hrs : PiTensorProduct.map r s = B.repr s k • tprod ℂ w := by
      have key : PiTensorProduct.map r = (B.coord k).smulRight (tprod ℂ w) := by
        refine B.ext fun k' => ?_
        rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
          Basis.coord_apply, ← Basis.piTensorProduct_apply, Basis.repr_self]
        simp only [r, LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self]
        rw [MultilinearMap.map_smul_univ, Finsupp.single_apply]
        by_cases hkk : k' = k
        · subst hkk; simp
        · rw [if_neg hkk]
          obtain ⟨v, hv⟩ : ∃ v, k' v ≠ k v := by
            by_contra hcon
            push Not at hcon
            exact hkk (funext hcon)
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [Finsupp.single_apply, hv]),
            zero_smul]
      rw [key, LinearMap.smulRight_apply, Basis.coord_apply]
    rw [hrs, map_smul] at hall
    have := p.smul_mem (B.repr s k)⁻¹ hall
    rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this
  rw [eq_top_iff]
  rintro t -
  obtain ⟨u, rfl⟩ := hJ t
  have hspan : u ∈ Submodule.span ℂ (range (tprod ℂ : (∀ v : S, fixedVectors (π v) (K' v)) →
      ⨂[ℂ] v : S, fixedVectors (π v) (K' v))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    exact htarget w
  | zero => rw [map_zero]; exact p.zero_mem
  | add a b _ _ ha hb => rw [map_add]; exact p.add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact p.smul_mem c ha

theorem isIrreducible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0)
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) :
    (restrictedTensorRep π ξ hξ).IsIrreducible := by
  classical
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  have hnt : Nontrivial (restrictedTensor ξ) := by
    have hv : ∀ v, ∃ u : V v, u ≠ 0 := fun v =>
      have := nontrivial_of_isIrreducible (hirr v)
      exists_ne 0
    choose u hu using hv
    set x : ∀ v, V v := fun v => if ξ v ≠ 0 then ξ v else u v
    have hx : IsRestricted ξ x := hξ0.mono fun v h => by simp [x, h]
    have hx0 : ∀ v, x v ≠ 0 := fun v => by
      by_cases h : ξ v = 0
      · simp [x, h, hu v]
      · simp [x, h]
    refine ⟨⟨⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩, 0, fun h => ?_⟩⟩
    exact tprod_ne_zero hx hx0 (congrArg Subtype.val h)
  refine isIrreducible_of_forall (isSmooth_restrictedTensorRep hπs hξ) fun x y hx0 => ?_
  obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := exists_boxSubgroup_fixing hπs hξ x.2
  obtain ⟨B, hBc, hBo, hBK, hBe, hBfix⟩ := exists_boxSubgroup_fixing hπs hξ y.2
  set K' : ∀ v, Subgroup (G v) := fun v => A v ⊓ B v
  have hK'c : ∀ v, IsCompact (K' v : Set (G v)) :=
    fun v => (hAc v).inter_right (Subgroup.isClosed_of_isOpen _ (hBo v))
  have hK'o : ∀ v, IsOpen (K' v : Set (G v)) := fun v => (hAo v).inter (hBo v)
  have hK'e : ∀ᶠ v in cofinite, K' v = K v := by
    filter_upwards [hAe, hBe] with v h1 h2
    simp [K', h1, h2]
  have hxK : x ∈ fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
    fun g hg => Subtype.ext (hAfix g fun v => (hg v).1)
  have hyK : y ∈ fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
    fun g hg => Subtype.ext (hBfix g fun v => (hg v).2)
  refine ⟨boxSubgroup K K', isCompact_boxSubgroup_of_eq hK'c hK'e, isOpen_boxSubgroup hK'o hK'e,
    hxK, hyK, isSimpleUnder_heckeOps_box hπ hirr hξ hgel hK'c hK'o hK'e ?_⟩
  intro h
  have : x ∈ (⊥ : Submodule ℂ (restrictedTensor ξ)) := h ▸ hxK
  exact hx0 ((Submodule.mem_bot ℂ).1 this)

end RestrictedTensor

end GroundTheory.Automorphic
