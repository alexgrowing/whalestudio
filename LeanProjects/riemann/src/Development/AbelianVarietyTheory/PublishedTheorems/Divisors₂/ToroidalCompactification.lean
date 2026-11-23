import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.LogKS
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogDR

section Nabla

variable {R : Type} [CommRing R]

def derHom (D : Derivation ℤ R R) : R →+* DualNumber R where
  toFun r := TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r)
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp [mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

theorem derHom_apply (D : Derivation ℤ R R) (r : R) :
    derHom D r = TrivSqZeroExt.inl r + TrivSqZeroExt.inr (D r) := rfl

variable (A : Over (Sp R)) [GrpObj A]

theorem derMor (D : Derivation ℤ R R) :
    GrpMor (dp0 R) (𝟙 _) A (epsDP R) (epsRed R) A (derHom D) (𝟙 _) (Over.Hom.left (𝟙 A)) :=
  GrpMor.of_hom (isDPMorphism_of_eq_bot _ rfl _ _)
    (by
      rw [← Cris.spMap_comp, show (TrivSqZeroExt.fstHom R R R).toRingHom.comp (derHom D) = RingHom.id R from
        RingHom.ext fun r ↦ by simp [derHom_apply]]
      exact (Cris.spMap_id R).symm) (𝟙 A)

variable {A}

def IsNabla (D : Derivation ℤ R R) (h k : HdR A) : Prop :=
  ∃ d : Crys (epsDP R) (epsRed R) A, (derMor A D).Corr h d ∧
    ∀ c : primDR A, d ((constMor A).pull c) = TrivSqZeroExt.inl (h c) + TrivSqZeroExt.inr (k c)

variable {D : Derivation ℤ R R}

theorem isNabla_zero_zero (D : Derivation ℤ R R) : IsNabla D (0 : HdR A) 0 :=
  ⟨0, fun _ ↦ (map_zero (derHom D)).symm, fun _ ↦ by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem IsNabla.add {h k h' k' : HdR A} (e : IsNabla D h k) (e' : IsNabla D h' k') :
    IsNabla D (h + h') (k + k') := by
  obtain ⟨d, a, b⟩ := e
  obtain ⟨d', a', b'⟩ := e'
  refine ⟨d + d', fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [LinearMap.add_apply, a, a', LinearMap.add_apply, map_add]
  · rw [LinearMap.add_apply, b, b']
    ext <;> simp

theorem IsNabla.smul {h k : HdR A} (e : IsNabla D h k) (r : R) : IsNabla D (r • h) (r • k + D r • h) := by
  obtain ⟨d, a, b⟩ := e
  refine ⟨derHom D r • d, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [LinearMap.smul_apply, a, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  · rw [LinearMap.smul_apply, b, derHom_apply]
    ext <;> simp [mul_comm]

theorem IsNabla.push {B : Over (Sp R)} [GrpObj B] {h k : HdR A} (e : IsNabla D h k) (f : A ⟶ B) [IsMonHom f] :
    IsNabla D (push (dp0 R) (𝟙 _) f h) (push (dp0 R) (𝟙 _) f k) := by
  obtain ⟨d, a, b⟩ := e
  refine ⟨DeRham.push _ _ f d, GrpMor.Corr.push (derMor B D) f f (by simp) a, fun c ↦ ?_⟩
  have m := (homMor (dp0 R) (𝟙 _) f).comp (constMor A)
  have e1 : primPull _ _ f ((constMor B).pull c) = m.pull c :=
    GrpMor.pull_pull (constMor B) (homMor _ _ f) m (fun _ ↦ rfl) (by simp) c
  have e2 : (constMor A).pull (primPull _ _ f c) = m.pull c :=
    GrpMor.pull_pull (homMor _ _ f) (constMor A) m (fun _ ↦ rfl) rfl c
  rw [push_apply, push_apply, push_apply, e1, ← e2, b]

theorem IsNabla.unique (H : Submodule.span (DualNumber R) (Set.range (derMor A D).pull) = ⊤) {h k k' : HdR A}
    (e : IsNabla D h k) (e' : IsNabla D h k') : k = k' := by
  obtain ⟨d, a, b⟩ := e
  obtain ⟨d', a', b'⟩ := e'
  obtain rfl : d = d' := LinearMap.ext_on_range H fun c ↦ (a c).trans (a' c).symm
  refine LinearMap.ext fun c ↦ ?_
  simpa using congrArg TrivSqZeroExt.snd ((b c).symm.trans (b' c))

theorem derMor_zero_pull (c : primDR A) : (derMor A 0).pull c = (constMor A).pull c :=
  (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (𝟙 A)) (derMor A 0) (derMor A 0) (fun _ ↦ rfl) (by simp) c).symm.trans
    (GrpMor.pull_pull (homMor (dp0 R) (𝟙 _) (𝟙 A)) (derMor A 0) (constMor A)
      (fun r ↦ by ext <;> simp [derHom_apply, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) c)

theorem IsNabla.eq_zero {h k : HdR A} (e : IsNabla 0 h k) : k = 0 := by
  obtain ⟨d, a, b⟩ := e
  refine LinearMap.ext fun c ↦ ?_
  have := a c
  rw [derMor_zero_pull, b] at this
  simpa [derHom_apply] using congrArg TrivSqZeroExt.snd this

theorem isNabla_zero (H : (constMor A).IsBC) (h : HdR A) : IsNabla 0 h 0 := by
  obtain ⟨d, hd⟩ := H.exists h
  refine ⟨d, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [derMor_zero_pull, hd c]
    ext <;> simp [derHom_apply, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [hd c, LinearMap.zero_apply, TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl]

end Nabla

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

structure Chart (t : SAB H X) (V : X.Opens) where

  U : X.affineOpens

  S : Type
  [ring : CommRing S]
  [alg : Algebra Γ(X, U.1) S]
  isOpenImmersion : IsOpenImmersion (spMap (algebraMap Γ(X, U.1) S) ≫ chart U)
  range : Set.range (spMap (algebraMap Γ(X, U.1) S) ≫ chart U :) = (U.1 ⊓ V : X.Opens)

  A : Over (Sp S)
  [grp : GrpObj A]

  φ : A.left ⟶ t.G.left
  cart : IsGrpPullback A t.G (spMap (algebraMap Γ(X, U.1) S) ≫ chart U) φ

attribute [instance] Chart.ring Chart.alg Chart.grp

variable {t : SAB H X} {V : X.Opens}

theorem exists_chart (t : SAB H X) (U : X.affineOpens) (h : IsAffineOpen (U.1 ⊓ V)) :
    ∃ c : Chart t V, c.U = U := by
  let _ : Algebra Γ(X, U.1) Γ(X, U.1 ⊓ V) := (resG X inf_le_left).toAlgebra
  have e : spMap (algebraMap Γ(X, U.1) Γ(X, U.1 ⊓ V)) ≫ chart U = h.fromSpec :=
    U.2.map_fromSpec h (homOfLE inf_le_left).op
  refine ⟨{ U := U, S := Γ(X, U.1 ⊓ V), isOpenImmersion := ?_, range := ?_
            A := (Over.pullback _).obj t.G, φ := _, cart := isGrpPullback_pullback t.G _ }, rfl⟩
  · rw [e]; infer_instance
  · rw [e]; exact h.range_fromSpec

theorem exists_chart_mem (t : SAB H X)
    (h : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal V.compl)) (x : X) :
    ∃ c : Chart t V, x ∈ c.U.1 := by
  obtain ⟨-, U, hx, n, f, J, -, hI⟩ := h x
  have e : U.1 ⊓ V = X.basicOpen (∏ i ∈ J, f i) := by
    ext y
    constructor
    · rintro ⟨hU, hV⟩
      by_contra hy
      have : y ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
        rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, hI, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
        exact hy
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
      exact this hV
    · intro hy
      have hU : y ∈ U.1 := X.basicOpen_le _ hy
      refine ⟨hU, by_contra fun hV ↦ ?_⟩
      have : y ∈ (Scheme.IdealSheafData.vanishingIdeal V.compl).support := by
        rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hV
      rw [Scheme.IdealSheafData.mem_support_iff_of_mem hU, hI, Scheme.zeroLocus_span,
        Scheme.zeroLocus_singleton] at this
      exact this hy
  obtain ⟨c, rfl⟩ := exists_chart t U (V := V) (e ▸ U.2.basicOpen _)
  exact ⟨c, hx⟩

namespace Chart

variable (c : Chart t V)

def HasImage (h : HdR c.A) (v : Sp (DualNumber Γ(X, c.U.1)) ⟶ t.G.left) : Prop :=
  ∃ w : epsR c.S ⟶ c.A, w.left ≫ c.φ = spMap (dualMap (algebraMap Γ(X, c.U.1) c.S)) ≫ v ∧ IsLieImage h w

variable {c} in

theorem HasImage.sub_mem {h h' : HdR c.A} {v : Sp (DualNumber Γ(X, c.U.1)) ⟶ t.G.left} (e : c.HasImage h v)
    (e' : c.HasImage h' v) : h - h' ∈ Fil c.A := by
  obtain ⟨w, a, b⟩ := e
  obtain ⟨w', a', b'⟩ := e'
  obtain rfl : w = w' :=
    Over.OverMorphism.ext (c.cart.1.hom_ext (a.trans a'.symm) ((Over.w w).trans (Over.w w').symm))
  exact b.sub_mem b'

def coLie (ψ : LinearMap.BilinForm c.S (HdR c.A)) : Submodule Γ(X, c.U.1) (HdR c.A) where
  carrier := {f | f ∈ Fil c.A ∧ ∀ h v, IsTanAtG t (chart c.U) v → c.HasImage h v →
    ψ f h ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)}
  zero_mem' := ⟨zero_mem _, fun h v _ _ ↦ ⟨0, by simp⟩⟩
  add_mem' := fun {f g} hf hg ↦ ⟨add_mem hf.1 hg.1, fun h v a b ↦ by
    obtain ⟨r, hr⟩ := hf.2 h v a b
    obtain ⟨s, hs⟩ := hg.2 h v a b
    exact ⟨r + s, by simp [hr, hs]⟩⟩
  smul_mem' := fun r f hf ↦ by
    rw [← algebraMap_smul c.S r f]
    refine ⟨Submodule.smul_mem _ _ hf.1, fun h v a b ↦ ?_⟩
    obtain ⟨s, hs⟩ := hf.2 h v a b
    exact ⟨r * s, by rw [map_smul, LinearMap.smul_apply, map_mul, hs, smul_eq_mul]⟩

end Chart

def IsCanLattice {K : Type} [CommRing K] (s : X ⟶ Sp K) (c : Chart t V) (L : Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  Module.Finite Γ(X, c.U.1) L ∧ Module.Projective Γ(X, c.U.1) L ∧ Submodule.span c.S (L : Set (HdR c.A)) = ⊤ ∧
  (∃ ψ : LinearMap.BilinForm c.S (HdR c.A), IsPolForm (dp0 c.S) (𝟙 _) c.A (t.PP.L.pull c.φ) ψ ∧
    (∀ x, x ∈ L ↔ ∀ y ∈ L, ψ x y ∈ Set.range (algebraMap Γ(X, c.U.1) c.S)) ∧
    (∀ x, x ∈ c.coLie ψ ↔ x ∈ L ∧ x ∈ Fil c.A) ∧ ∀ x ∈ c.coLie ψ, ∀ y ∈ c.coLie ψ, ψ x y = 0) ∧
  (∀ h ∈ L, ∃ v, IsTanAtG t (chart c.U) v ∧ c.HasImage h v) ∧
  (∀ v, IsTanAtG t (chart c.U) v → ∃ h ∈ L, c.HasImage h v) ∧
  (∀ D ∈ logDer s (Scheme.IdealSheafData.vanishingIdeal V.compl) c.U, ∃ D' : Derivation ℤ c.S c.S,
    (∀ r, D' (algebraMap Γ(X, c.U.1) c.S r) = algebraMap Γ(X, c.U.1) c.S (D r)) ∧
      ∀ h ∈ L, ∃ k ∈ L, IsNabla D' h k) ∧
  ∀ (a : 𝓞 E) (f : c.A ⟶ c.A) [IsMonHom f], f.left ≫ c.φ = c.φ ≫ (t.act.act a).left →
    ∀ h ∈ L, push (dp0 c.S) (𝟙 _) f h ∈ L

def IsCanExt {K : Type} [CommRing K] (s : X ⟶ Sp K)
    (L : ∀ c : Chart t V, Submodule Γ(X, c.U.1) (HdR c.A)) : Prop :=
  (∀ c, IsCanLattice s c (L c)) ∧
    ∀ c c' : Chart t V, c'.U.1 ≤ c.U.1 → ∀ (σ : c.S →+* c'.S) (q : c'.A.left ⟶ c.A.left)
      (m : GrpMor (dp0 c.S) (𝟙 _) c.A (dp0 c'.S) (𝟙 _) c'.A σ (spMap σ) q), q ≫ c.φ = c'.φ →
      L c' = Submodule.span Γ(X, c'.U.1) {h' | ∃ h ∈ L c, m.Corr h h'}

theorem IsCanLattice.eq_top {K : Type} [CommRing K] {s : X ⟶ Sp K} {c : Chart t V}
    {L : Submodule Γ(X, c.U.1) (HdR c.A)} (h : IsCanLattice s c L)
    (hs : Function.Surjective (algebraMap Γ(X, c.U.1) c.S)) : L = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  have hx : x ∈ Submodule.span c.S (L : Set (HdR c.A)) := h.2.2.1 ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem (hy trivial) (hz trivial)
  | smul a y _ hy =>
    obtain ⟨r, rfl⟩ := hs a
    rw [algebraMap_smul]
    exact L.smul_mem r (hy trivial)

end GlobalTheory.LogDR

namespace GlobalTheory.Published

open GlobalTheory.LogDR

def DeRhamCanonicalExtension : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
      ∃ Y : Model Xo c (RingHom.id c.F),
        SmoothOfRelativeDimension Dw.dim Y.s ∧ ReciprocityTheory.AnForm.R.FinalTheorems.Snc (boundary Y) ∧
          HasLogKS Y.t Y.s (interior Y) ∧
          ∃ L : ∀ ch : Chart Y.t (interior Y), Submodule Γ(Y.X, ch.U.1) (HdR ch.A), IsCanExt Y.s L

theorem DeRhamCanonicalExtension.toroidalCompactification (h : DeRhamCanonicalExtension) :
    ToroidalCompactification := fun E _ _ _ H Dw hr l Xo c ↦
  (h E H Dw hr l Xo c).imp fun _ hY ↦ ⟨hY.1, hY.2.1, hY.2.2.1⟩

end GlobalTheory.Published
