import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabMultiHomogIdeal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KleimanNefF

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_dvr [DecidableEq K] {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    NumbersDVR.IsMultiProjPrime (R := F) (ι := ι) V :=
  ⟨hV.1, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι V).1 hV.2.1, hV.2.2⟩

theorem isProjVarF_of_mem_support [DecidableEq K] {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V (n + 1)) {f g : MRingOver F ι} {bf bg : K → ℕ}
    (hf : NumbersDVR.IsMultiHomog f bf) (hg : NumbersDVR.IsMultiHomog g bg) (hfV : f ∉ V) (hgV : g ∉ V)
    {W : Ideal (MRingOver F ι)} (hW : W ∈ (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g).support) :
    IsProjVarF W n := by
  have hVd := isMultiProjPrime_dvr hV.1
  have hrel : FieldNumbers.relDim V = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) :=
    (FieldNumbers.CutRegular.relDim_eq_natCast_iff V (n + 1)).2 hV.2
  have key : ∀ (s : MRingOver F ι) (b : K → ℕ), NumbersDVR.IsMultiHomog s b → s ∉ V →
      ReciprocityTheory.ChartRestriction.G.Geo.divCycle V s W ≠ 0 → IsProjVarF W n := by
    intro s b hs hsV hne
    have hne' : NumbersDVR.divCycle V s W ≠ 0 := by
      rw [← NumbersDVR.VocabDivCycle.proof F K ι V s W]
      exact_mod_cast hne
    obtain ⟨hW1, hW2⟩ := FieldNumbers.DivCycleSupport.full F K ι V hVd n hrel b s hs hsV W hne'
    exact ⟨⟨hW1.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
      hW1.multiHomog, hW1.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W n).1 hW2⟩
  rw [Finsupp.mem_support_iff, ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.mapRange_apply] at hW
  by_cases hfW : ReciprocityTheory.ChartRestriction.G.Geo.divCycle V f W = 0
  · refine key g bg hg hgV fun h => hW ?_
    rw [hfW, h]
    simp
  · exact key f bf hf hfV hfW

theorem eq_intNum [DecidableEq K] {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum F V L := by
  have hJ : IsFieldIntersection (F := F) (ι := ι) (fun V _ L => NumbersDVR.intNum F V L) :=
    NumbersDVR.IntNumIsFieldIntersection.full F K ι
  intro n
  induction n with
  | zero =>
    intro V L hV
    choose i hi using hV.1.2.2
    exact (hI.1 V L i hV hi).trans (hJ.1 V L i hV hi).symm
  | succ n ih =>
    intro V L hV
    obtain ⟨bf, bg, f, g, hf, hg, hfV, hgV, hb⟩ :=
      FieldNumbers.ExistsForm.full F K ι V (isMultiProjPrime_dvr hV.1) (L (Fin.last n))
    have hs : IsRatSection V (L (Fin.last n)) f g :=
      ⟨bf, bg, (NumbersDVR.VocabMultiHomog.proof F K ι f bf).2 hf,
        (NumbersDVR.VocabMultiHomog.proof F K ι g bg).2 hg, hfV, hgV, fun k => congrFun hb k⟩
    have e1 : I V (n + 1) L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval (fun W => I W n (Fin.init L))
        (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hI.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    have e2 : NumbersDVR.intNum F V L = ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval
        (fun W => NumbersDVR.intNum F W (Fin.init L)) (ReciprocityTheory.ChartRestriction.G.AI.I1.ratDiv V f g) := by
      have h := hJ.2 V n (Fin.init L) (L (Fin.last n)) f g hV hs
      rwa [Fin.snoc_init_self] at h
    rw [e1, e2, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval, ReciprocityTheory.ChartRestriction.G.AI.I1.cycEval]
    refine Finsupp.sum_congr fun W hW => ?_
    rw [ih W _ (isProjVarF_of_mem_support hV hf hg hfV hgV hW)]

theorem map_update_add₂ {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (x y : K → ℤ) :
    I V n (Function.update L j (x + y)) = I V n (Function.update L j x) + I V n (Function.update L j y) := by
  classical
  rw [eq_intNum hI n V _ hV, eq_intNum hI n V _ hV, eq_intNum hI n V _ hV]
  have hVd := isMultiProjPrime_dvr hV.1
  exact FieldNumbers.IntNumAdd.full F K ι V hVd.multiHomog hVd.relevant n
    ((FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2) L j x y

theorem nsmul_position {I : IFamily F ι} (hI : IsFieldIntersection I) {V : Ideal (MRingOver F ι)} {n : ℕ}
    (hV : IsProjVarF V n) (L : Fin n → K → ℤ) (j : Fin n) (m : ℕ) (x : K → ℤ) :
    I V n (Function.update L j ((m : ℤ) • x)) = m * I V n (Function.update L j x) := by
  induction m with
  | zero =>
    have h := map_update_add₂ hI hV L j 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, zero_smul, zero_mul]
    linarith
  | succ m ih =>
    rw [Nat.cast_succ, add_smul, one_smul, map_update_add₂ hI hV, ih]
    ring

end KleimanNefF

theorem KleimanNefF.proof (hKA : KH.KAmpStatement) (hGP : GeneratedProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  let H : K → ℤ := fun _ => ((1 : ℕ) : ℤ)
  let c : Finset (Fin n) → ℤ := fun S => I V n (fun i => if i ∈ S then H else a i)
  have key : ∀ q : ℕ, 1 ≤ q → 0 ≤ ∑ S : Finset (Fin n), (q : ℤ) ^ Sᶜ.card * c S := by
    intro q hq
    have hamp := fun j => hKA F K ι I V n (a j) q 1 hI hV (hnef j) hq le_rfl
    choose p hp hgen _ using hamp
    let B : Fin n → K → ℤ := fun j => p j • (q • a j + H)
    have hB : 0 ≤ I V n B := hGP F K ι I V n B hI hV hgen
    have hposition : ∀ (L : Fin n → K → ℤ) (i : Fin n), I V n (Function.update L i (B i)) =
        ((q : ℤ) * p i) * I V n (Function.update L i (a i)) + (p i : ℤ) * I V n (Function.update L i H) := by
      intro L i
      have e : B i = ((q * p i : ℕ) : ℤ) • a i + ((p i : ℕ) : ℤ) • H := by
        funext k
        simp only [B, Pi.add_apply, Pi.smul_apply]
        simp only [H, nsmul_eq_mul, smul_eq_mul]
        push_cast
        ring
      rw [e, KleimanNefF.map_update_add₂ hI hV, KleimanNefF.nsmul_position hI hV, KleimanNefF.nsmul_position hI hV]
      push_cast
      ring
    have hexp := Kleiman.sum_expand_positions (I V n) B a (fun _ => H) (fun i => (q : ℤ) * p i)
      (fun i => (p i : ℤ)) hposition
    have hw : ∀ S : Finset (Fin n), (∏ i ∈ S, (p i : ℤ)) * (∏ i ∈ Sᶜ, ((q : ℤ) * p i)) =
        (∏ i, (p i : ℤ)) * (q : ℤ) ^ Sᶜ.card := by
      intro S
      rw [Finset.prod_mul_distrib, Finset.prod_const, ← mul_assoc, mul_comm _ ((q : ℤ) ^ _), mul_assoc,
        Finset.prod_mul_prod_compl, mul_comm]
    simp only [hw, mul_assoc] at hexp
    rw [← Finset.mul_sum] at hexp
    have hprod : 0 < ∏ i, (p i : ℤ) := Finset.prod_pos fun i _ => by exact_mod_cast hp i
    rw [hexp] at hB
    exact (mul_nonneg_iff_of_pos_left hprod).mp hB
  have h0 := Kleiman.nonneg_of_poly c key
  simpa [c] using h0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
