import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open GlobalTheory.EtC

namespace GlobalTheory.EtC

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_isUnit_zero (U : Scheme) (h : IsUnit (0 : Γ(U, ⊤))) : IsEmpty U := by
  constructor
  intro x
  have h01 : (0 : Γ(U, ⊤)) = 1 := isUnit_zero_iff.1 h
  have := congrArg (U.presheaf.germ ⊤ x trivial).hom h01
  rw [map_zero, map_one] at this
  exact zero_ne_one this

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma isEmpty_of_prim_zero (U : Scheme)
    (ζ : _root_.GlobalTheory.EtC.Prim 0 Γ(U, ⊤)) : IsEmpty U :=
  isEmpty_of_isUnit_zero U (by simpa using ζ.2.1)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
private lemma sec_eq_of_isEmpty' {R : Type} [CommRing R] (F : _root_.GlobalTheory.EtC.Shv R) (U : Scheme)
    [IsEmpty U] (a b : _root_.GlobalTheory.EtC.Sec F U) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F U).1 a b
    ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun _ _ h => h.elim⟩

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.twPair_spec (q : ℕ) (i j : ℤ) :
    _root_.GlobalTheory.EtC.IsTwPair (_root_.GlobalTheory.EtC.twPair q i j) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsTwPair
    intro U ζ
    haveI := isEmpty_of_prim_zero U ζ
    exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact (_root_.GlobalTheory.EtC.TwPairUniq.main q i j).1

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.kumT_spec (q : ℕ) : _root_.GlobalTheory.EtC.IsKum q (_root_.GlobalTheory.EtC.kumT q) := by
  by_cases hq : q = 0
  · subst hq
    unfold _root_.GlobalTheory.EtC.IsKum
    refine ⟨fun V U g v h => ?_, fun U ζ v w _ => ?_⟩
    · haveI := isEmpty_of_isUnit_zero U (by simpa using h)
      haveI : IsEmpty V := ⟨fun x => IsEmpty.false (g.base x)⟩
      exact sec_eq_of_isEmpty' _ _ _ _
    · haveI := isEmpty_of_prim_zero U ζ
      exact sec_eq_of_isEmpty' _ _ _ _
  · haveI : NeZero q := ⟨hq⟩
    exact _root_.GlobalTheory.EtC.KummerSplit.isKum_kumT q

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.restrMap_spec {S R : Type} [CommRing S] [CommRing R] (φ : R →+* S)
    (F : _root_.GlobalTheory.EtC.Shv S) (U : Scheme.{0}) (a : _root_.GlobalTheory.EtC.Sec F U) :
    (_root_.GlobalTheory.EtC.restrMap φ F).app U 0
        (_root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι S F) a) =
      _root_.GlobalTheory.EtC.Sec.map (_root_.GlobalTheory.EtC.resι R ((_root_.GlobalTheory.EtC.restr φ).obj F))
        (show _root_.GlobalTheory.EtC.Sec ((_root_.GlobalTheory.EtC.restr φ).obj F) U from a) :=
  _root_.GlobalTheory.EtC.restrMap_spec' R S φ F U a

end GlobalTheory.EtC

end
