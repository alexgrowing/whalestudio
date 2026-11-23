import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjSpace

namespace GlobalTheory.AmpleTwistNef

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem nefFib_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (hL : ArInt.NefFib L) :
    ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (L.B.pull i) (pull_isLB L.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull L.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB L.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  exact hL Z i κ hd

theorem nefFib_of_cls_eq_ample [Module.Finite ℤ k] [IsProper p] {M : HermLB p} {B : LB X} (hB : IsAmpleLB B)
    (h : cls M.B M.isLB = cls B hB.isLB) : ArInt.NefFib M := by
  intro Z i _ _ κ _ _ _ hd
  have e : cls (B.pull i) (pull_isLB hB.isLB i) = cls (M.B.pull i) (pull_isLB M.isLB i) := by
    rw [cls_pull hB.isLB i, cls_pull M.isLB i, h]
  rw [← topSelf_congr κ (pull_isLB hB.isLB i) (pull_isLB M.isLB i) ((cls_eq_iff _ _).1 e)]
  have hA := hB.pull_of_isClosedImmersion i
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e' : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e']; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have h := (isNef_iff_isClosedImmersion.1 (hA.isNef (k := κ))).2 Z (𝟙 Z) inferInstance inferInstance hd
    (by rw [Category.id_comp]; infer_instance)
  rw [interNumOn_id] at h
  refine h.trans_eq (congrArg _ (funext fun j => ?_))
  fin_cases j
  rfl

end GlobalTheory.AmpleTwistNef

namespace GlobalTheory.AmpleTwistNef

open GlobalTheory.ArInt

theorem exists_nefFib_twists : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (p : X ⟶ Sp (𝓞 F)),
    IsProjOver p → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), ∃ H : HermLB p,
      ∀ (X' : Scheme.{0}) (q : X' ⟶ Sp (𝓞 F)), IsProjOver q → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q),
        NefFib (H.pull π hπ) ∧ ∀ i, NefFib ((H.pull π hπ).tens ((L i).pull π hπ)) ∧
          NefFib ((H.pull π hπ).tens ((L i).pull π hπ).dual) := by
  intro F _ _ X p hp ι _ L
  haveI : IsProper p := CommonModel.isProper_of_isProjOver hp
  obtain ⟨N, j, hj, hjp⟩ := hp
  let A : HermLB p := (hermitianTwistingSheaf (𝓞 F) N).pull j hjp
  have hA : IsAmpleLB A.B := (isAmple_projective_O_one (𝓞 F) N).pull_of_isClosedImmersion j
  obtain ⟨t, h0, h1, h2⟩ := ((AmpleDominates.eventually_isAmpleLB p hA (LB.isLB_triv X)).and
    ((Filter.eventually_all.2 fun i =>
        AmpleDominates.eventually_isAmpleLB p hA (isLB_dual (L i).isLB)).and
      (Filter.eventually_all.2 fun i => AmpleDominates.eventually_isAmpleLB p hA (L i).isLB))).exists
  let H : HermLB p := A.pow t
  have cP : cls (lbPow A.B t) (isLB_lbPow A.isLB t) = cls H.B H.isLB := rfl
  have nH : NefFib H := nefFib_of_cls_eq_ample h0 (by
    rw [cls_div (isLB_lbPow A.isLB t) (LB.isLB_triv X), ← cP]
    exact (sub_zero _).symm)
  have nT (i : ι) : NefFib (H.tens (L i)) := nefFib_of_cls_eq_ample (h1 i) (by
    rw [cls_div (isLB_lbPow A.isLB t) (isLB_dual (L i).isLB), cls_dual (L i).isLB, sub_neg_eq_add, cP]
    rfl)
  have nD (i : ι) : NefFib (H.tens (L i).dual) := nefFib_of_cls_eq_ample (h2 i) (by
    rw [cls_div (isLB_lbPow A.isLB t) (L i).isLB, sub_eq_add_neg,
      ← cls_dual (L i).isLB (isLB_dual (L i).isLB), cP]
    rfl)
  have hp : IsProjOver p := ⟨N, j, hj, hjp⟩
  refine ⟨H, fun X' q hq π hπ => ?_⟩
  refine ⟨ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ H nH, fun i => ⟨?_, ?_⟩⟩
  · refine nefFib_of_cls_eq ?_ (ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ _ (nT i))
    exact (cls_pull (isLB_tens H.isLB (L i).isLB) π _).trans
      (map_add (CechPic.pull π) (cls H.B H.isLB) (cls (L i).B (L i).isLB))
  · refine nefFib_of_cls_eq ?_ (ArInt.nefFib_pull (𝓞 F) X X' p q hp hq π hπ _ (nD i))
    refine (cls_pull (isLB_tens H.isLB (isLB_dual (L i).isLB)) π _).trans
      ((map_add (CechPic.pull π) (cls H.B H.isLB) (cls _ (isLB_dual (L i).isLB))).trans ?_)
    refine Eq.trans ?_ (cls_tens (pull_isLB H.isLB π) (isLB_dual (pull_isLB (L i).isLB π)) _).symm
    refine congrArg (CechPic.pull π (cls H.B H.isLB) + ·) ?_
    rw [cls_dual (L i).isLB, map_neg]
    exact (cls_dual (pull_isLB (L i).isLB π) (isLB_dual (pull_isLB (L i).isLB π))).symm

end GlobalTheory.AmpleTwistNef
