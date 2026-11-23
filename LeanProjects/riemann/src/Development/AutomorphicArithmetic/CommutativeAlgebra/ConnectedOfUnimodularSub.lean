import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

private theorem exists_mem_basicOpen {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : T) : ∃ j, x ∈ T.basicOpen (v j) := by
  by_contra hc
  push_neg at hc
  let φ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (T.presheaf.stalk x)).comap φ := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h1 := hc j
    rw [Scheme.mem_basicOpen_top] at h1
    exact h1
  rw [h, top_le_iff] at hle
  have h1 : (1 : Γ(T, ⊤)) ∈ (IsLocalRing.maximalIdeal (T.presheaf.stalk x)).comap φ := by
    rw [hle]; trivial
  simp at h1

private theorem isUnit_ι {T : Scheme.{0}} (f : Γ(T, ⊤)) : IsUnit ((T.basicOpen f).ι.appTop.hom f) := by
  have h := T.toRingedSpace.isUnit_res_basicOpen f
  have key : ∀ (W : T.Opens) (_ : W = T.basicOpen f) (hle : W ≤ ⊤),
      IsUnit ((T.presheaf.map (homOfLE hle).op).hom f) := by
    intro W hW hle
    subst hW
    exact h
  rw [Scheme.Opens.ι_appTop]
  exact key _ (by simp) _

private def sieveOf {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤)) : Sieve T where
  arrows V k := ∃ j, IsUnit (k.appTop.hom (v j))
  downward_closed := by
    rintro Y Z f ⟨j, hj⟩ g
    refine ⟨j, ?_⟩
    have h := hj.map g.appTop.hom
    rw [Scheme.Hom.comp_appTop]
    exact h

private theorem sieveOf_mem {T : Scheme.{0}} {N : ℕ} (v : Fin N → Γ(T, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) : sieveOf v ∈ Scheme.etaleTopology.{0} T := by
  choose j hj using exists_mem_basicOpen v h
  let 𝒰 : Scheme.Cover (Scheme.precoverage @Etale) T :=
    Scheme.Cover.mkOfCovers (Fin N) (fun j => (T.basicOpen (v j)).toScheme)
      (fun j => (T.basicOpen (v j)).ι) (fun x => ⟨j x, ⟨x, hj x⟩, rfl⟩) (fun _ => inferInstance)
  refine Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, ?_⟩
  rintro _ _ ⟨i⟩
  exact ⟨i, isUnit_ι _⟩

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem rel_unit {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} (h : (Vec D N).rel x y)
    (j : Fin N) (hy : IsUnit (y.1.2 j)) : IsUnit (x.1.2 j) := by
  obtain ⟨_, u, h2⟩ := h
  rw [h2]
  exact u.isUnit.mul hy

private theorem unimodular_of_unit_coord {A : Type} [CommRing A] {x : (Vec D (d + 1)).obj A} (j : Fin d)
    (h : IsUnit (x.1.2 j.castSucc)) : P2 x :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) h

private theorem cond1 (p : ℕ) (T : Scheme.{0}) (y : Sx (CN (Vec D (d + 1))) p T) :
    EtLoc T fun V k =>
      (∃ u : Sx (CN (L2 D d)) p V,
        sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u = sxRes k y) ∨
      ∃ a : Sx (CN (L1 D d)) p V,
        sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a = sxRes k y := by
  let y' : Sm (Vec D (d + 1)) p T := y
  refine ⟨sieveOf (y'.1 0).1.2, sieveOf_mem _ (y'.1 0).2, ?_⟩
  rintro V k ⟨j, hj⟩
  have hrel : ∀ i, (Vec D (d + 1)).rel ((Vec D (d + 1)).map k.appTop.hom (y'.1 i))
      ((Vec D (d + 1)).map k.appTop.hom (y'.1 0)) := fun i => (Vec D (d + 1)).map_rel _ (y'.2 i 0)
  induction j using Fin.lastCases with
  | last =>
    right
    refine ⟨(⟨fun i => ⟨(Vec D (d + 1)).map k.appTop.hom (y'.1 i), rel_unit D (hrel i) _ hj⟩,
      fun i j => (Vec D (d + 1)).map_rel _ (y'.2 i j)⟩ : Sm (L1 D d) p V), rfl⟩
  | cast j =>
    left
    refine ⟨(⟨fun i => ⟨(Vec D (d + 1)).map k.appTop.hom (y'.1 i),
      unimodular_of_unit_coord D d j (rel_unit D (hrel i) _ hj)⟩,
      fun i j => (Vec D (d + 1)).map_rel _ (y'.2 i j)⟩ : Sm (L2 D d) p V), rfl⟩

private theorem cond2 (p : ℕ) (T : Scheme.{0}) (a b : Sx (CN (L1 D d)) p T)
    (h : sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a =
      sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) b) :
    EtLoc T fun V k => sxRes k a = sxRes k b ∨ ∃ u : Sx (CN (L2 D d)) p V,
      sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u =
        sxRes k (sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a) := by
  have hab : a = b := by
    let a' : Sm (L1 D d) p T := a
    let b' : Sm (L1 D d) p T := b
    have h' : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    exact Subtype.ext (funext fun i => Subtype.ext (h' i))
  exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V k _ => Or.inl (by rw [hab])⟩

private theorem mono2 : Mono (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) := by
  have h : ∀ n, Mono ((CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)).app n) := by
    intro n
    have h' : ∀ U, Mono (((CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro a b hab
      let a' : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := a
      let b' : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := b
      have h2 : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val hab) i
      exact Subtype.ext (funext fun i => Subtype.ext (h2 i))
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

private theorem isPb : IsPullback (CN.map (bothToSecond D d) (both_to_second_relation D d)) (CN.map (bothToFirst D d) (both_to_first_relation D d))
    (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map))
    (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) := by
  refine IsPullback.of_forall_isPullback_app fun n => IsPullback.of_forall_isPullback_app fun U => ?_
  rw [Types.isPullback_iff]
  refine ⟨rfl, fun x y h => ?_, fun x₂ x₃ h => ?_⟩
  · let x' : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} := x
    let y' : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} := y
    have h1 : ∀ i, (x'.1 i).1 = (y'.1 i).1 := fun i =>
      congrArg (fun z : (L2 D d).obj Γ(U.unop, ⊤) => z.1) (congrFun (congrArg Subtype.val h.1) i)
    exact Subtype.ext (funext fun i => Subtype.ext (h1 i))
  · let a : {x : Fin (n.unop.len + 1) → (L2 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L2 D d).rel (x i) (x j)} := x₂
    let b : {x : Fin (n.unop.len + 1) → (L1 D d).obj Γ(U.unop, ⊤) // ∀ i j, (L1 D d).rel (x i) (x j)} := x₃
    have h' : ∀ i, (a.1 i).1 = (b.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    let z : {x : Fin (n.unop.len + 1) → (lift_levelP_alt₂ D d).obj Γ(U.unop, ⊤) // ∀ i j, (lift_levelP_alt₂ D d).rel (x i) (x j)} :=
      ⟨fun i => ⟨(a.1 i).1, (a.1 i).2, by rw [h' i]; exact (b.1 i).2⟩, fun i j => a.2 i j⟩
    refine ⟨z, ?_, ?_⟩
    · exact Subtype.ext (funext fun i => Subtype.ext rfl)
    · exact Subtype.ext (funext fun i => Subtype.ext (h' i))

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory

theorem UpperTheory.connected_of_unimodular_sub :
    LeafExc → A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) (d : ℕ) (D : Type) [CommRing D], Conn R F c (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) → Conn R F c (CN.map (bothToFirst D d) (both_to_first_relation D d)) := by
  intro hE hA R _ F c d D _ hC
  haveI := UpperTheory.mono2 D d
  have h := (hE hA R F c (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map))
    (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map))
    (UpperTheory.cond1 D d) (UpperTheory.cond2 D d)).1 hC
  have hp := UpperTheory.isPb D d
  refine (conn_sq F c (CN.map (bothToFirst D d) (both_to_first_relation D d)) _ hp.isoPullback.hom (𝟙 _) ?_
    (UpperTheory.eqv_iso F _) (UpperTheory.eqv_iso F (Iso.refl _))).2 h
  rw [Category.comp_id, IsPullback.isoPullback_hom_snd]
