import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreExtra
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.TwoExpansionsExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPlainPolyPairNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumberExpansionKoszul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsFieldIntersectionExample
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

namespace FlagPlainValueIndependence

theorem vEval_intNum {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Fintype K]
    [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (d : ℕ) {m : ℕ} (deg : Fin m → K → ℤ)
    (H : MvPolynomial (Fin m) ℤ) (Z : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι) →₀ ℤ)
    (hZ : ∀ W, Z W ≠ 0 → ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d deg H) Z =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
        (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          W d deg H) Z := by
  classical
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval
  refine Finsupp.sum_congr fun W hW => ?_
  have hV := hZ W (Finsupp.mem_support_iff.mp hW)
  congr 1
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
  refine Finset.sum_congr rfl fun μ _ => ?_
  split_ifs with h
  · rw [Numbers.agree_of FieldNumbers.IntNumBase.full FieldNumbers.CutRational.full
      FieldNumbers.ExistsForm.full FieldNumbers.DivCycleSupport.full I hI _ d _ hV]
  · rfl

theorem pairNum_intNum (hSupp : VerticalDivisorSupportFibre.Statement)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V}
    (hM : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E')
    (I : ReciprocityTheory.ChartRestriction.G.AI.I1.IFamily (IsLocalRing.ResidueField O) ι)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I1.IsFieldIntersection I) (r : ℕ) (L : Fin r → K → ℤ)
    (H : MvPolynomial (Fin (N + r)) ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
                              (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
                              (Fin.append φ.g fun _ => 1) H =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d
        (Fin.append φ.deg L) (Fin.append φ.deg' L) (Fin.append φ.f fun _ => 1)
        (Fin.append φ.g fun _ => 1) H := by
  unfold IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum
  refine Finset.sum_congr rfl fun l _ => ?_
  induction l using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact vEval_intNum I hI d _ _ _ fun W hW => hSupp O K ι _ d hM _ _ _ (φ.vert i) W hW
  | right j =>
    simp only [Fin.append_right]
    have h0 : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) 1 1 = 0 := sub_self _
    exact vEval_intNum I hI d _ _ _ fun W hW => absurd (by rw [h0]; rfl) hW

theorem exists_isFlagPair (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω}
    {d N : ℕ} (hN : 0 < N) {V : Type} [AddCommGroup V] [Module Ω V]
    {E E' : ReciprocityTheory.ChartRestriction.G.Geo.ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V} {ϖ : O}
    (hϖ : Irreducible ϖ) (hM : IsModelOver (pointIdeal O x) d)
    (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O x E E') :
    ∃ w w' : Module.Basis (Fin N) Ω V, IsFlagPair ϖ x E E' w w' φ.deg φ.deg' φ.f φ.g := by
  have hne : ∀ k, ∃ j, x ⟨k, j⟩ ≠ 0 := fun k => by
    obtain ⟨j, hj⟩ := hM.multiProj.relevant k
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : ∃ c, segreVec x c ≠ 0 := ⟨c, Finset.prod_ne_zero_iff.mpr fun k _ => hc k⟩
  have hiff := hF O Ω K ι x N V E E' ϖ hϖ hM.multiProj
  obtain ⟨hl, hl'⟩ := hiff.2 hyc φ
  have hrank : Fintype.card (Fin N) = Module.finrank Ω V := by
    rw [Fintype.card_fin, ← finrank_top Ω V, ← φ.top, φ.dim]
    rfl
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl hrank,
    basisOfLinearIndependentOfCardEqFinrank hl' hrank, (hiff.1 _ _ _ _ _ _).mpr ⟨φ, ?_, ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl hrank).symm
  · exact (coe_basisOfLinearIndependentOfCardEqFinrank hl' hrank).symm

theorem proof (hFlag : FlagIndependence.Statement) (hF : FlagPairCharacterisation.Statement.{0, 0, 0})
    (hSupp : VerticalDivisorSupportFibre.Statement) : FlagPlainValueIndependence.Statement := by
  classical
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hM hS φ₁ φ₂ I hI G hG r L c Q hc hGc hQ
  rw [pairNum_intNum hSupp hM φ₁ I hI r L, pairNum_intNum hSupp hM φ₂ I hI r L,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ,
    plainPolynomialPairNumber.proof O K ι _ d N _ _ _ _ c G hGc hc r L Q hQ]
  refine Finset.sum_congr rfl fun μ hμ => congrArg (Q.coeff μ * ·) ?_
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : φ₁.deg = φ₂.deg := Subsingleton.elim _ _
    have h2 : φ₁.deg' = φ₂.deg' := Subsingleton.elim _ _
    have h3 : φ₁.f = φ₂.f := Subsingleton.elim _ _
    have h4 : φ₁.g = φ₂.g := Subsingleton.elim _ _
    rw [h1, h2, h3, h4]
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨-, hM'⟩ := (BundleExamples.isModelOver_iff O _ d).mp hM
    have hS' := (BundleExamples.sameGeneric_iff hϖ x E E').mp hS
    obtain ⟨w₁, w₁', h₁⟩ := exists_isFlagPair hF hN hϖ hM' φ₁
    obtain ⟨w₂, w₂', h₂⟩ := exists_isFlagPair hF hN hϖ hM' φ₂
    have hE := dividedDifferenceExpansion.proof N c G hGc
    exact hFlag O ϖ hϖ Ω K ι x d hM' N V E E' hS' w₁ w₁' w₂ w₂' _ _ _ _ _ _ _ _ h₁ h₂ c G hGc hG _ _ hE hE
      (classList L μ) (by rw [classList_length_of_mem_support L hQ hμ]; omega)

end FlagPlainValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
