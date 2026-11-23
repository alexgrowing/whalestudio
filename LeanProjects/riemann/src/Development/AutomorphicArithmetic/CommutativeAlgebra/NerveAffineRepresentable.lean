import Mathlib
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import Development.AutomorphicArithmetic.CommutativeAlgebra.RepresentedByUnits
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory.LevelRep

noncomputable section

private abbrev Smp (D : Type) [CommRing D] (d p : ℕ) (A : Type) [CommRing A] : Type :=
  {x : Fin (p + 1) → (Vec D d).obj A // ∀ i j, (Vec D d).rel (x i) (x j)}

variable {D : Type} [CommRing D] {d p : ℕ}

private theorem rel_iff {A : Type} [CommRing A] {x y : (Vec D d).obj A} :
    (Vec D d).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

private def smpMap {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (x : Smp D d p A) : Smp D d p A' :=
  ⟨fun i => (Vec D d).map f (x.1 i), fun i j => (Vec D d).map_rel f (x.2 i j)⟩

private theorem scalar_unique {A : Type} [CommRing A] {N : ℕ} {v : Fin N → A}
    (hv : Ideal.span (Set.range v) = ⊤) {a b : A} (h : ∀ j, a * v j = b * v j) : a = b := by
  have key : ∀ y ∈ Ideal.span (Set.range v), a * y = b * y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact h j
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, mul_add, hy, hz]
    | smul c y _ hy =>
      simp only [smul_eq_mul]
      rw [mul_left_comm, hy, mul_left_comm]
  have h1 := key 1 (by rw [hv]; trivial)
  simpa using h1

private theorem exists_unit {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) :
    ∃ u : Aˣ, (x.1 k.succ).1.2 = fun j => (u : A) * (x.1 0).1.2 j :=
  (rel_iff.1 (x.2 k.succ 0)).2

private def uOf {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) : Aˣ :=
  Classical.choose (exists_unit x k)

private theorem uOf_spec {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) (j : Fin d) :
    (x.1 k.succ).1.2 j = (uOf x k : A) * (x.1 0).1.2 j :=
  congrFun (Classical.choose_spec (exists_unit x k)) j

private def toRing {A : Type} [CommRing A] (x : Smp D d p A) : MvPolynomial (Fin d ⊕ Fin p) D →+* A :=
  MvPolynomial.eval₂Hom (x.1 0).1.1 (Sum.elim (x.1 0).1.2 fun k => (uOf x k : A))

private theorem toRing_C {A : Type} [CommRing A] (x : Smp D d p A) (c : D) :
    toRing x (MvPolynomial.C c) = (x.1 0).1.1 c := by
  simp [toRing]

private theorem toRing_inl {A : Type} [CommRing A] (x : Smp D d p A) (j : Fin d) :
    toRing x (MvPolynomial.X (Sum.inl j)) = (x.1 0).1.2 j := by
  simp [toRing]

private theorem toRing_inr {A : Type} [CommRing A] (x : Smp D d p A) (k : Fin p) :
    toRing x (MvPolynomial.X (Sum.inr k)) = (uOf x k : A) := by
  simp [toRing]

private theorem toRing_map {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (x : Smp D d p A) :
    toRing (smpMap f x) = f.comp (toRing x) := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · rw [toRing_C, RingHom.comp_apply, toRing_C]
    rfl
  · rcases j with j | k
    · rw [toRing_inl, RingHom.comp_apply, toRing_inl]
      rfl
    · rw [toRing_inr, RingHom.comp_apply, toRing_inr]
      refine scalar_unique ((smpMap f x).1 0).2 fun j => ?_
      rw [← uOf_spec]
      change f ((x.1 k.succ).1.2 j) = f (uOf x k : A) * f ((x.1 0).1.2 j)
      rw [uOf_spec, map_mul]

private def Jd (D : Type) [CommRing D] (d p : ℕ) : Ideal (MvPolynomial (Fin d ⊕ Fin p) D) :=
  Ideal.span (Set.range fun j : Fin d => (MvPolynomial.X (Sum.inl j) : MvPolynomial (Fin d ⊕ Fin p) D)) *
    Ideal.span {∏ k : Fin p, (MvPolynomial.X (Sum.inr k) : MvPolynomial (Fin d ⊕ Fin p) D)}

private theorem map_Jd_iff {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A) :
    (Jd D d p).map ξ = ⊤ ↔
      Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤ ∧
        ∀ k : Fin p, IsUnit (ξ (MvPolynomial.X (Sum.inr k))) := by
  rw [Jd, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, ← Set.range_comp, map_prod]
  change Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) * _ = ⊤ ↔ _
  constructor
  · intro h
    refine ⟨top_le_iff.1 (h ▸ Ideal.mul_le_left), fun k => ?_⟩
    have h2 : Ideal.span {∏ k : Fin p, ξ (MvPolynomial.X (Sum.inr k))} = ⊤ :=
      top_le_iff.1 (h ▸ Ideal.mul_le_right)
    rw [Ideal.span_singleton_eq_top] at h2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)] at h2
    exact isUnit_of_mul_isUnit_left h2
  · rintro ⟨h1, h2⟩
    have h3 : IsUnit (∏ k : Fin p, ξ (MvPolynomial.X (Sum.inr k))) := by
      refine Finset.prod_induction _ IsUnit (fun a b => IsUnit.mul) isUnit_one fun k _ => h2 k
    rw [h1, Ideal.span_singleton_eq_top.2 h3, Ideal.top_mul]

private theorem map_toRing {A : Type} [CommRing A] (x : Smp D d p A) : (Jd D d p).map (toRing x) = ⊤ := by
  refine (map_Jd_iff _).2 ⟨?_, fun k => ?_⟩
  · simp only [toRing_inl]
    exact (x.1 0).2
  · rw [toRing_inr]
    exact (uOf x k).isUnit

private theorem toRing_injective {A : Type} [CommRing A] {x y : Smp D d p A} (h : toRing x = toRing y) : x = y := by
  have h0 : x.1 0 = y.1 0 := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · ext c
      rw [← toRing_C, ← toRing_C, h]
    · funext j
      rw [← toRing_inl, ← toRing_inl, h]
  refine Subtype.ext (funext fun i => ?_)
  refine Fin.cases h0 (fun k => ?_) i
  have hr : (x.1 k.succ).1.1 = (y.1 k.succ).1.1 := by
    rw [(rel_iff.1 (x.2 k.succ 0)).1, (rel_iff.1 (y.2 k.succ 0)).1, h0]
  refine Subtype.ext (Prod.ext hr (funext fun j => ?_))
  have hu : (uOf x k : A) = uOf y k := by
    rw [← toRing_inr, ← toRing_inr, h]
  rw [uOf_spec, uOf_spec, hu, h0]

private def wOf {A : Type} [CommRing A] (w : Fin p → Aˣ) (i : Fin (p + 1)) : Aˣ :=
  Fin.cases 1 w i

private def ofRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h1 : Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤) (w : Fin p → Aˣ) :
    Smp D d p A :=
  ⟨fun i => ⟨(ξ.comp MvPolynomial.C, fun j => ξ (MvPolynomial.X (Sum.inl j)) * (wOf w i : A)),
      span_mul_unit _ (wOf w i).isUnit h1⟩,
    fun i j => rel_iff.2 ⟨rfl, wOf w i * (wOf w j)⁻¹, funext fun l => by
      change ξ (MvPolynomial.X (Sum.inl l)) * (wOf w i : A) =
        ((wOf w i * (wOf w j)⁻¹ : Aˣ) : A) * (ξ (MvPolynomial.X (Sum.inl l)) * (wOf w j : A))
      rw [Units.val_mul, mul_comm (ξ _) (wOf w j : A), mul_assoc, ← mul_assoc _ (wOf w j : A), Units.inv_mul, one_mul,
        mul_comm]⟩⟩

private theorem toRing_ofRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h1 : Ideal.span (Set.range fun j : Fin d => ξ (MvPolynomial.X (Sum.inl j))) = ⊤) (w : Fin p → Aˣ)
    (hw : ∀ k, (w k : A) = ξ (MvPolynomial.X (Sum.inr k))) :
    toRing (ofRing ξ h1 w) = ξ := by
  have h0 : ∀ j, ((ofRing ξ h1 w).1 0).1.2 j = ξ (MvPolynomial.X (Sum.inl j)) := fun j => by
    change ξ (MvPolynomial.X (Sum.inl j)) * (wOf w 0 : A) = _
    simp [wOf]
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
  · rw [toRing_C]
    rfl
  · rcases j with j | k
    · rw [toRing_inl, h0]
    · rw [toRing_inr, ← hw]
      refine scalar_unique ((ofRing ξ h1 w).1 0).2 fun j => ?_
      rw [← uOf_spec, h0, mul_comm]
      change ξ (MvPolynomial.X (Sum.inl j)) * (wOf w k.succ : A) = _
      simp [wOf]

private theorem existsUnique_toRing {A : Type} [CommRing A] (ξ : MvPolynomial (Fin d ⊕ Fin p) D →+* A)
    (h : (Jd D d p).map ξ = ⊤) : ∃! x : Smp D d p A, toRing x = ξ := by
  obtain ⟨h1, h2⟩ := (map_Jd_iff ξ).1 h
  refine ⟨ofRing ξ h1 fun k => (h2 k).unit, toRing_ofRing ξ h1 _ fun k => (h2 k).unit_spec, fun y hy => ?_⟩
  exact toRing_injective (hy.trans (toRing_ofRing ξ h1 _ fun k => (h2 k).unit_spec).symm)

end

end UpperTheory.LevelRep

open UpperTheory.LevelRep in
theorem UpperTheory.nerve_affine_representable :
    ∀ (D : Type) [CommRing D] (d : ℕ) (n : SimplexCategoryᵒᵖ), ∃ (Y : Scheme.{0}) (_ : D →+* Γ(Y, ⊤)) (φ : (CN (Vec D d)).obj n ⟶ yoneda.obj Y), ∀ T : Scheme.{0}, IsAffine T → Function.Bijective (φ.app (op T)) := by
  intro D _ d n
  obtain ⟨U, hU⟩ := exists_compl (Jd D d n.unop.len)
  obtain ⟨φ, -, hφ⟩ := UpperTheory.represented_by_units (Jd D d n.unop.len) U hU ((CN (Vec D d)).obj n)
    (fun T x => toRing (D := D) (d := d) (p := n.unop.len) x)
    (fun f x => toRing_map f.appTop.hom x) (fun T x => map_toRing x)
    (fun T ξ h => existsUnique_toRing ξ h)
  exact ⟨U, U.ι.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin d ⊕ Fin n.unop.len) D))).inv.hom.comp
    MvPolynomial.C), φ, hφ⟩
