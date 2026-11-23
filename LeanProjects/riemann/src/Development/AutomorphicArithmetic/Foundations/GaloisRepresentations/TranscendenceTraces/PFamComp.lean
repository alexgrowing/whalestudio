import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

noncomputable section

namespace UpperTheory.Gal.TranscendenceTraces.FamilyComposition

variable {W Z S : Scheme.{0}} (r : W ⟶ Z) (p : Z ⟶ S)

private def cr (A : Sq (r ≫ p)) : A.V ⟶ pullback p A.u :=
  pullback.lift (A.v ≫ r) A.r (by rw [Category.assoc]; exact A.pb.w)

private lemma cr_fst (A : Sq (r ≫ p)) : cr r p A ≫ pullback.fst p A.u = A.v ≫ r := pullback.lift_fst _ _ _

private lemma cr_snd (A : Sq (r ≫ p)) : cr r p A ≫ pullback.snd p A.u = A.r := pullback.lift_snd _ _ _

private abbrev sqB (A : Sq (r ≫ p)) : Sq p := Sq.of p A.u

private def sqC (A : Sq (r ≫ p)) : Sq r :=
  ⟨pullback p A.u, A.V, pullback.fst p A.u, A.v, cr r p A,
    IsPullback.of_bot (by rw [cr_snd]; exact A.pb) (cr_fst r p A).symm (IsPullback.of_hasPullback p A.u)⟩

variable {r p}

private def mid {A A' : Sq (r ≫ p)} (t : A.To A') : pullback p A.u ⟶ pullback p A'.u :=
  pullback.lift (pullback.fst p A.u) (pullback.snd p A.u ≫ t.g)
    (by rw [Category.assoc, t.hu]; exact pullback.condition)

private lemma mid_fst {A A' : Sq (r ≫ p)} (t : A.To A') : mid t ≫ pullback.fst p A'.u = pullback.fst p A.u :=
  pullback.lift_fst _ _ _

private lemma mid_snd {A A' : Sq (r ≫ p)} (t : A.To A') :
    mid t ≫ pullback.snd p A'.u = pullback.snd p A.u ≫ t.g := pullback.lift_snd _ _ _

private def toB {A A' : Sq (r ≫ p)} (t : A.To A') : (sqB r p A).To (sqB r p A') :=
  ⟨t.g, mid t, t.hu, mid_fst t, mid_snd t⟩

private def toC {A A' : Sq (r ≫ p)} (t : A.To A') : (sqC r p A).To (sqC r p A') :=
  ⟨mid t, t.k, mid_fst t, by
      have := t.hv
      exact this, by
      change t.k ≫ cr r p A' = cr r p A ≫ mid t
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, cr_fst, mid_fst, cr_fst, ← Category.assoc, t.hv]
      · rw [Category.assoc, Category.assoc, cr_snd, mid_snd, ← Category.assoc, cr_snd, t.hr]⟩

variable (r p)

private def comp0 {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {F : Shv R₁} {G : Shv R₂} {H : Shv R₃}
    (a : Fam0 r F G) (b : Fam0 p G H) : Fam0 (r ≫ p) F H where
  app A := (b.app (sqB r p A)).comp (a.app (sqC r p A))
  nat {A A'} t x := by
    have h1 := b.nat (toB t) (a.app (sqC r p A') x)
    have h2 := a.nat (toC t) x
    exact h1.trans (congrArg (b.app (sqB r p A)) h2)

private lemma zsmul_finsum_mem {ι M : Type*} [AddCommGroup M] (d : ℤ) {s : Set ι} (f : ι → M) (hs : s.Finite) :
    d • ∑ᶠ i ∈ s, f i = ∑ᶠ i ∈ s, d • f i :=
  (zsmulAddGroupHom d).map_finsum_mem f hs

end UpperTheory.Gal.TranscendenceTraces.FamilyComposition

open UpperTheory.Gal.TranscendenceTraces.FamilyComposition in
theorem UpperTheory.Gal.TranscendenceTraces.famComp_of :
    SumComp → FibFin → FamComp := by
  intro hS hF q i W Z S r p _ _ w' w τ' τ h' h
  refine ⟨⟨fun s => comp0 r p (τ'.deg s) (τ.deg s), fun A s t a => ?_⟩, fun A a => ?_, fun n a => ?_⟩
  · exact ((τ.comm (sqB r p A) s t _).trans
      (congrArg ((τ.deg t).app (sqB r p A)) (τ'.comm (sqC r p A) s t a)))
  · obtain ⟨b1, e1, s1⟩ := h' (sqC r p A) a
    obtain ⟨b2, e2, s2⟩ := h (sqB r p A) b1
    refine ⟨b2, (congrArg ((τ.deg 0).app (sqB r p A)) e1).trans e2, ?_⟩
    intro Ω _ _ x
    haveI fB : IsFinite (pullback.snd p A.u) := Sq.finite (sqB r p A)
    haveI fC : IsFinite (cr r p A) := Sq.finite (sqC r p A)
    have key := hS (cr r p A) (pullback.snd p A.u) Ω x (Sec (tw q i) (gp Ω))
      (fun z => (Wt.mul r w' w) Ω (z ≫ A.v) • Sec.res z a)
    rw [cr_snd] at key
    refine (s2 Ω x).trans (Eq.trans ?_ key.symm)
    refine finsum_mem_congr rfl fun (y : gp Ω ⟶ pullback p A.u) _ => ?_
    have e : (Sec.res y b1 : Sec (tw q i) (gp Ω)) = ∑ᶠ z ∈ fib (cr r p A) y, w' Ω (z ≫ A.v) • Sec.res z a := s1 Ω y
    refine (congrArg (fun m => w Ω (y ≫ pullback.fst p A.u) • m) e).trans ?_
    refine (zsmul_finsum_mem _ _ (hF (cr r p A) Ω y)).trans ?_
    refine finsum_mem_congr rfl fun z hz => ?_
    have hy : (z ≫ A.v) ≫ r = y ≫ pullback.fst p A.u := by
      have hz' : z ≫ cr r p A = y := hz
      rw [← hz', Category.assoc, Category.assoc, cr_fst]
    change _ = (w' Ω (z ≫ A.v) * w Ω ((z ≫ A.v) ≫ r)) • Sec.res z a
    rw [hy, mul_comm, mul_smul]
  · let t1 : (sqB r p (Sq.self (r ≫ p))).To (Sq.self p) :=
      ⟨𝟙 S, pullback.fst p (𝟙 S), Category.comp_id _, Category.comp_id _,
        pullback.condition⟩
    let t2 : (sqC r p (Sq.self (r ≫ p))).To (Sq.self r) :=
      ⟨pullback.fst p (𝟙 S), 𝟙 W, Category.comp_id _, Category.comp_id _, by
        have := cr_fst r p (Sq.self (r ≫ p))
        exact (Eq.trans this.symm rfl : _)⟩
    have n1 := (τ.deg n).nat t1 ((τ'.deg n).app (Sq.self r) a)
    have n2 := (τ'.deg n).nat t2 a
    have e1 : (τ.deg n).app (Sq.self p) ((τ'.deg n).app (Sq.self r) a) =
        (τ.deg n).app (sqB r p (Sq.self (r ≫ p))) (Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a)) :=
      (res_id _).symm.trans n1
    have e2 : Sec.res (pullback.fst p (𝟙 S)) ((τ'.deg n).app (Sq.self r) a) =
        (τ'.deg n).app (sqC r p (Sq.self (r ≫ p))) a :=
      n2.trans (congrArg _ (res_id a))
    exact (e1.trans (congrArg _ e2)).symm
