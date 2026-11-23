import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.EtaleCohomology.EtaleSheaves.LeafTwistPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.LPdCut

def Dp (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)) : (PN k N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)

def Std (k : Type) [Field k] (N : ℕ) : (PN k N).Opens := ⨆ j : Fin N, Dp k N j.succ

def ZariskiLocallyAffineLine {U Y : Scheme.{0}} (f : U ⟶ Y) : Prop := ∀ y : Y, ∃ (A : Type) (_ : CommRing A)
  (j : Spec (CommRingCat.of A) ⟶ Y) (j' : Spec (CommRingCat.of (Polynomial A)) ⟶ U), IsOpenImmersion j ∧ y ∈ Set.range j ∧
    IsPullback j' (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))) f j

def LChart : Prop := ∀ (k : Type) [Field k] (N : ℕ) (i : Fin (N + 1)),
  ∃ j : Spec (CommRingCat.of (MvPolynomial (Fin N) k)) ⟶ PN k N, IsOpenImmersion j ∧
    j ≫ PNto k N = Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (Fin N) k)) ∧
    Set.range j = (Dp k N i : Set (PN k N))

def LProper : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsProper (PNto k N)

def LSmooth : Prop := ∀ (k : Type) [Field k] (N : ℕ), SmoothOfRelativeDimension N (PNto k N)

def LIntegral : Prop := ∀ (k : Type) [Field k] (N : ℕ), IsIntegral (PN k N)

def LMove : Prop := ∀ (k : Type) [Field k] (N : ℕ) (t : Pt (PNto k N)),
  ∃ g : PN k N ⟶ PN k N, IsIso g ∧ ((g ⁻¹ᵁ Std k N : (PN k N).Opens) : Set (PN k N)) = (Set.range t.1)ᶜ

def LProjn : Prop := ∀ (k : Type) [Field k] (e : ℕ), ∃ f : (Std k (e + 1)).toScheme ⟶ PN k e, ZariskiLocallyAffineLine f

def AffineLineTwistInvariance : Prop := B3 → C4 → ∀ (q : ℕ) [NeZero q] {U Y : Scheme.{0}} (f : U ⟶ Y), ZariskiLocallyAffineLine f → IsUnit (q : Γ(Y, ⊤)) →
  ∀ i : ℤ, Eqv _ (sch.map f) (tw q i)

def LEmpty : Prop := A5 → A9 → ∀ (R : Type) [CommRing R] (X : Scheme.{0}), IsEmpty X → ∀ (F : Shv R) (n : ℤ),
  Subsingleton (H R (sch.obj X) F n)

def LLoc : Prop := Base → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LLim : Prop := ∀ (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ), (∀ j, Nonempty (Ht (l ^ j) E n i ≃+ ZMod (l ^ j))) →
  (∀ j, Function.Surjective (red (l ^ (j + 1)) (l ^ j) E n i)) → Nontrivial (HQ l E n i)

theorem unit_of {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ S k) {q : ℕ} (h : IsUnit (q : k)) : IsUnit (q : Γ(X, ⊤)) := by
  simpa using (h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn; subst hi; rfl

theorem vanish (a9 : A9) (e8 : E8) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p] (n i : ℤ)
    (hn : 2 * (d : ℤ) < n) : Subsingleton (Ht q (sch.obj X) n i) := by
  obtain ⟨tr, h⟩ := e8 q k hq p d
  have hs : Subsingleton (Ht q (sch.obj X) (2 * d - n) (d - i)) := (a9 _ _).1 _ _ (by omega)
  refine ⟨fun a a' => (h n i 0).unique (fun b => ?_) (fun b => ?_)⟩ <;>
    rw [Subsingleton.elim b 0, map_zero, map_zero, cast_zero, map_zero]

theorem sub_iso {R : Type} [CommRing R] {X Y : Scheme.{0}} (a : X ⟶ Y) [IsIso a] (F : Shv R) (n : ℤ)
    [h : Subsingleton (H R (sch.obj Y) F n)] : Subsingleton (H R (sch.obj X) F n) := by
  have : ∀ y, pull R (sch.map a) F n (pull R (sch.map (inv a)) F n y) = y := fun y => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨fun y y' => by rw [← this y, ← this y', Subsingleton.elim (pull R (sch.map (inv a)) F n y)]⟩

theorem goal_of (hP : LProper) (hS : LSmooth) (hI : LIntegral) (hM : LMove) (hJ : LProjn) (hA : AffineLineTwistInvariance) (hE : LEmpty)
    (hL : LLoc) (hLim : LLim) (hB : LateralTheory.KummerTheory.Bock) (hT : LateralTheory.E.LeafTwistPf.LeafTwSec) : LPd := by
  intro hb l hl k _ _ hlk d
  have hb' := hb
  obtain ⟨⟨-, -, -, -, a5, -, -, -, -, a7, a8, a9, a10, a11⟩, ⟨-, -, b3, -, -⟩, ⟨c4, -, -⟩, -, -, -, -, -, e8⟩ := hb'
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by
    rw [Nat.cast_pow]; exact (IsUnit.mk0 _ hlk).pow j
  have hz : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have := hP k
  have := hS k
  have := hI k
  refine ⟨⟨hP k d, hS k d⟩, hI k d, fun t U hU => ?_⟩
  have hnt : Nontrivial (V l (PN k d) (2 * d)) := by
    refine hLim l _ _ 0 (fun j => ?_) (fun j => ?_)
    · obtain ⟨tr, -⟩ := e8 (l ^ j) k (hu j) (PNto k d) d
      obtain ⟨ζ⟩ := LateralTheory.E.LeafKumCut.prim_of_isAlgClosed (l ^ j) k (hu j)
      obtain ⟨e, he⟩ := hT (l ^ j) k ζ 0 d
      obtain ⟨w⟩ := hL hb _ (PN k d) _ _ (fun U x => e U (x ≫ PNto k d))
        (fun g x s => by rw [Category.assoc]; exact he g _ s) (2 * d)
      exact ⟨w.trans tr⟩
    · obtain ⟨u, δ, h⟩ := hB a7 a8 a10 a11 l j (sch.obj (PN k d)) 0
        (fun W ⟨x⟩ => unit_of ((show W ⟶ PN k d from x) ≫ PNto k d) (IsUnit.mk0 _ hlk))
      have := vanish a9 e8 (l ^ 1) k (hu 1) (PNto k d) d (2 * d + 1) 0 (by omega)
      exact fun y => ((h 1 (2 * d)).2.1 y).1 (Subsingleton.elim _ _)
  obtain ⟨z, hz0⟩ := exists_ne (0 : V l (PN k d) (2 * d))
  obtain ⟨g, hg, hgU⟩ := hM k d t
  obtain rfl : U = g ⁻¹ᵁ Std k d := TopologicalSpace.Opens.ext (hU.trans hgU.symm)
  have h1 : ∀ j, Subsingleton (Ht (l ^ j) (sch.obj (Std k d).toScheme) (2 * d) 0) := fun j => by
    cases d with
    | zero =>
      refine hE a5 a9 _ _ ⟨fun x => ?_⟩ _ _
      obtain ⟨m, -⟩ := TopologicalSpace.Opens.mem_iSup.1 x.2
      exact m.elim0
    | succ e =>
      obtain ⟨f, hf⟩ := hJ k e
      have := vanish a9 e8 (l ^ j) k (hu j) (PNto k e) e (2 * (e + 1 : ℕ)) 0 (by omega)
      exact (hA b3 c4 (l ^ j) f hf (unit_of (PNto k e) (hu j)) 0 _).2.subsingleton
  have h2 : ∀ j, Subsingleton (HtL l j (sch.obj (g ⁻¹ᵁ Std k d).toScheme) (2 * d) 0) := fun j =>
    sub_iso (g ∣_ Std k d) _ _ (h := h1 j)
  have h3 : Subsingleton (V l (g ⁻¹ᵁ Std k d).toScheme (2 * d)) := inferInstance
  exact ⟨z, hz0, Subsingleton.elim _ _⟩

end LateralTheory.EtaleTrace.LPdCut

end
