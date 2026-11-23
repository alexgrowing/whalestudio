import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Inhabit
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitMore
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitFurther
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

namespace ChernClassOnFlagPair

theorem fieldNum_spec (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type) [∀ k, Fintype (κ k)] :
    IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem append_pullDeg {K K' : Type} {a b : ℕ} (u : Fin a → K → ℤ) (v : Fin b → K → ℤ) :
    Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (u i))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (v j)) =
      fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (Fin.append u v l) := by
  funext l
  induction l using Fin.addCases with
  | left i => simp
  | right j => simp

theorem isVertDiv_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    (b : K → ℤ) (hb : b = 0) : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b 1 1 := by
  subst hb
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι O) 0 := by
    simpa using IndefiniteRowSideFullHecke.NumbersDVR.Bundles.isMultiHomog_C O (ι := ι) (1 : O)
  refine ⟨⟨0, 0, h1, h1, by simp⟩, ?_, ?_, fun Q hQ _ _ => ⟨1, 1, ⟨0, h1⟩, ⟨0, h1⟩, ?_, ?_, by simp⟩⟩
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)
  · exact fun h => hQ.1.ne_top ((Ideal.eq_top_iff_one Q).mpr h)

theorem length_classList {K σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) :
    (classList cls μ).length = μ.degree := by
  simp [classList, Finsupp.card_toMultiset, Finsupp.sum]
  rfl

theorem isFlagPair_self {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} [(pointIdeal O y).IsPrime] {N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
    {B : ChartBundle O (segreVec y) N E} {w : Module.Basis (Fin N) Ω E} {x : Fin N → K → ℤ}
    (h : IsFlagFrame y B w x) :
    IsFlagPair ϖ y B B w w x x (fun _ => 1) (fun _ => 1) where
  flag := h
  flag' := h
  sameFlag i j hij := by rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hij.ne]
  vertical i := by
    rw [sub_self]
    exact isVerticalDivisor_one ϖ _
  generic i := by simp [Module.Basis.repr_self]

end ChernClassOnFlagPair

open ChernClassOnFlagPair in

theorem ChernClassOnFlagPair.proof (h1 : JoinPointFlagModel.Statement)
    (h2 : JoinPointNumbers.Statement) (h3 : FlagModelValueIndependence.Statement)
    (h4 : FlagModelRootIndependence.Statement) (h5 : plainPolynomialPairNumber.Statement)
    (h6 : RootPolynomialNumber.Statement) (h7 : PairNumberExpansionIndependence.Statement)
    (h8 : dividedDifferenceExpansion.Statement) : ChernClassOnFlagPair.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hK hW N E _ _ B B' hBB' w w' x x' f g hfp
  have hW2 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) d :=
    (BundleExamples.isModelOver_iff O _ d).mpr ⟨hK, hW⟩
  have hprime : (pointIdeal O y).IsPrime := hW2.2.1.1
  refine ⟨fun k hk1 hk2 Gs hGs q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, hd', hf, hg⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B' hBB' w w' x x' f g hfp
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B' :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B') := ⟨F₀⟩
    have hv : F₀.value O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _) (Fin.append φ.deg' _)
        (Fin.append φ.f _) (Fin.append φ.g _) _ = _
      rw [hd, hd', hf, hg]
    have hW' : ∀ H : MvPolynomial (Fin (N + q)) ℤ, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i))
            fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (L l))
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1)
          (Fin.append (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))
            fun _ => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) 1) H =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O y) d (Fin.append x L) (Fin.append x' L) (Fin.append f fun _ => 1)
          (Fin.append g fun _ => 1) H := by
      intro H
      unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
      simp only [append_pullDeg]
      refine Finset.sum_congr rfl fun l _ => ?_
      induction l using Fin.addCases with
      | left i =>
        simp only [Fin.append_left]
        exact (h2 O ϖ hϖ Ω K ι y d hW _ _ _).1 _ _ _ (hfp.vertical i)
      | right j =>
        simp only [Fin.append_right, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc, sub_self,
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval, Finsupp.sum_zero_index]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ck
    rw [dif_pos hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h3 O Ω K ι y d N E B B' hW2 ((BundleExamples.sameGeneric_iff hϖ y B B').mpr hBB')
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => isVertDiv_one hprime _ (sub_self _)) k Q hk2 (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((hW' _).trans ((h5 O K ι (pointIdeal O y) d N x x' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q L Q hQ).trans ?_))
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList L μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [h7 O ϖ hϖ K ι (pointIdeal O y) d hW N x x' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ Gs (h8 N k _ (isHomogeneous_psum N k)) hGs (classList L μ) hlen]
  · have hsame : SameGenericFibre ϖ B B := fun c _ =>
      ⟨fun v hv => ⟨0, by simpa using hv⟩, fun v hv => ⟨0, by simpa using hv⟩⟩
    obtain ⟨EB, E'B, φ, hm, hb, hp, hp', hd, -, -, -⟩ :=
      h1 O ϖ hϖ Ω K ι y d hW N E B B hsame w w x x _ _ (isFlagPair_self hfp.flag)
    let F₀ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B :=
      { K' := Unit, ι' := ptIdx, z := ptCoord, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O y d N B B) := ⟨F₀⟩
    have hv : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι F₀.ι')) W d
          (Fin.append F₀.flag.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := F₀.K') (L l))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y F₀.z)) (C a))) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) W d
          (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (Fin.append x L j))
          (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) := by
      show IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum _ W d
          (Fin.append φ.deg _) _) _ = _
      rw [hd, append_pullDeg]
    unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.rootNum
    rw [dif_pos hne]
    let _ := (Classical.choice hne).finK
    let _ := (Classical.choice hne).finι
    refine (h4 O Ω K ι y d N E B B hW2 ((BundleExamples.sameGeneric_iff hϖ y B B).mpr hsame)
      (Classical.choice hne) F₀ _ _ (fieldNum_spec _ _) (fieldNum_spec _ _) c G hsym hG hc q L Q hQ a
      ha).trans ?_
    refine hv.trans (((h2 O ϖ hϖ Ω K ι y d hW _ _ _).2 a ha).trans ?_)
    exact h6 O K ι (pointIdeal O y) d N x c G hG hc q L Q hQ a

end GroundTheory.Heights₂.Heights.NumbersDVR
