import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4.CurveCut

open LateralTheory.E.E4

def LeafMV : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens), U ⊔ V = ⊤ →
  ∀ n : ℤ, ∃ δ : H R (sch.obj (U ⊓ V).toScheme) F n →+ H R (sch.obj X) F (n + 1),
    ∀ x : H R (sch.obj X) F (n + 1),
      (pull R (sch.map U.ι) F (n + 1) x = 0 ∧ pull R (sch.map V.ι) F (n + 1) x = 0) ↔ x ∈ δ.range

def LeafCover : Prop := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c →
  ∃ U V : C.Opens, U ⊔ V = ⊤ ∧ ∀ W ∈ ({U, V, U ⊓ V} : Set C.Opens),
    ∃ (B : Type) (_ : CommRing B) (_ : IsDedekindDomain B) (_ : Algebra Ω B) (_ : Algebra.FiniteType Ω B),
      Nonempty (W.toScheme ≅ Sp B)

def isoH (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (e : X ≅ Y) (n : ℤ) :
    H R (sch.obj Y) F n ≃ H R (sch.obj X) F n where
  toFun := pull R (sch.map e.hom) F n
  invFun := pull R (sch.map e.inv) F n
  left_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  right_inv x := by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem finite_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (U V : X.Opens)
    (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Finite (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Finite (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Finite (H R (sch.obj V.toScheme) F (n + 1))) :
    Finite (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  let φ := (pull R (sch.map U.ι) F (n + 1)).prod (pull R (sch.map V.ι) F (n + 1))
  have hker : φ.ker = δ.range := by
    ext x
    rw [← hδ x, AddMonoidHom.mem_ker]
    simp [φ, Prod.ext_iff]
  have : Finite φ.ker := by
    rw [hker]
    exact Set.finite_range δ |>.to_subtype
  have : Finite (H R (sch.obj X) F (n + 1) ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_addSubgroup_quotient φ.ker

theorem subsingleton_of_mv (hMV : LeafMV) (hH : Hyps) (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0})
    (U V : X.Opens) (hUV : U ⊔ V = ⊤) (n : ℤ) (h0 : Subsingleton (H R (sch.obj (U ⊓ V).toScheme) F n))
    (h1 : Subsingleton (H R (sch.obj U.toScheme) F (n + 1))) (h2 : Subsingleton (H R (sch.obj V.toScheme) F (n + 1))) :
    Subsingleton (H R (sch.obj X) F (n + 1)) := by
  obtain ⟨δ, hδ⟩ := hMV hH R F X U V hUV n
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj X) F (n + 1), z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (hδ z).1 ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

theorem goal_of (hH0 : H0TwistOverClosedField) (hMV : LeafMV) (hCov : LeafCover) : LeafCurve := by
  intro hH q _ Ω _ _ hq i hB C c hc
  have hC2 : C2 := hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, V, hUV, hW⟩ := hCov Ω c hc

  have key : ∀ W ∈ ({U, V, U ⊓ V} : Set C.Opens), ∀ m : ℤ,
      (m = 0 ∨ m = 1 → Finite (Ht q (sch.obj W.toScheme) m i)) ∧ (2 ≤ m → Subsingleton (Ht q (sch.obj W.toScheme) m i)) := by
    intro W hWm m
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := hW W hWm
    have eq := isoH (ZMod q) (tw q i) e m
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rcases hm with rfl | rfl
      · have h0 := hH0 hH q Ω hq i
        have := h0.1
        have hbij := h0.2 (Spec.map (CommRingCat.ofHom (algebraMap Ω B)) : Sp B ⟶ Sp Ω)
        have : Finite (Ht q (sch.obj (Sp B)) 0 i) := Finite.of_surjective _ hbij.2
        exact Finite.of_equiv _ eq
      · have := hB B
        exact Finite.of_equiv _ eq
    · have := hC2 q Ω B hq m i hm
      exact eq.symm.injective.subsingleton
  have hU : U ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  have hV : V ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  have hI : U ⊓ V ∈ ({U, V, U ⊓ V} : Set C.Opens) := by simp
  refine ⟨?_, ?_, ?_⟩
  · have := finite_of_mv hMV hH (ZMod q) (tw q i) C U V hUV 0 ((key _ hI 0).1 (Or.inl rfl))
      ((key _ hU 1).1 (Or.inr rfl)) ((key _ hV 1).1 (Or.inr rfl))
    simpa using this
  · have := finite_of_mv hMV hH (ZMod q) (tw q i) C U V hUV 1 ((key _ hI 1).1 (Or.inr rfl))
      (by have := (key _ hU (1 + 1)).2 (by norm_num); exact Finite.of_subsingleton)
      (by have := (key _ hV (1 + 1)).2 (by norm_num); exact Finite.of_subsingleton)
    exact this
  · intro m hm
    obtain ⟨k, rfl⟩ : ∃ k : ℤ, m = k + 1 := ⟨m - 1, by ring⟩
    exact subsingleton_of_mv hMV hH (ZMod q) (tw q i) C U V hUV k ((key _ hI k).2 (by omega))
      ((key _ hU (k + 1)).2 (by omega)) ((key _ hV (k + 1)).2 (by omega))

end LateralTheory.E.E4.CurveCut
