import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpFibreDegree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleNeZeroFacts
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

theorem mem_map_iff_of_ker_le {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : Function.Surjective f) {I : Ideal A} (hI : RingHom.ker f ≤ I) (a : A) :
    f a ∈ I.map f ↔ a ∈ I := by
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.mpr hI]

theorem contractPrime_specialIdeal {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type}
    (W' : Ideal (MRing (extIdx ι J) O)) (hϖW : (C ϖ : MRing (extIdx ι J) O) ∈ W') :
    (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
        Ideal (MRing ι (IsLocalRing.ResidueField O))) =
      specialIdeal (W'.comap (liftForm (ι := ι) (J := J) (R := O))) := by
  have hres := IsLocalRing.residue_surjective (R := O)
  have hs : Function.Surjective
      (MvPolynomial.map (IsLocalRing.residue O) : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) :=
    MvPolynomial.map_surjective _ hres
  have hker' : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing (extIdx ι J) O →+* MRing (extIdx ι J) (IsLocalRing.ResidueField O)) ≤ W' := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    exact hϖW
  have hker : RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) :
      MRing ι O →+* MRing ι (IsLocalRing.ResidueField O)) ≤
        W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    rw [ker_map_residue_eq_span hϖ, Ideal.span_le, Set.singleton_subset_iff]
    change liftForm (J := J) (C ϖ : MRing ι O) ∈ W'
    rw [liftForm_C]
    exact hϖW
  ext y
  obtain ⟨z, rfl⟩ := hs y
  have e : rename (FieldNumbers.blockIncl Function.Embedding.some (extIdx ι J))
      (MvPolynomial.map (IsLocalRing.residue O) z) =
      MvPolynomial.map (IsLocalRing.residue O) (liftForm (J := J) z) :=
    (map_rename (IsLocalRing.residue O) _ z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le hs hker z).symm
  refine Iff.trans ?_ (mem_map_iff_of_ker_le (MvPolynomial.map_surjective _ hres) hker' (liftForm z))
  exact Iff.of_eq (congrArg (· ∈ specialIdeal W') e)

theorem relDim_eq_of_dim {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = (m : WithBot (WithTop ℤ)) := by
  rw [FieldNumbers.relDim, h]
  have : (((m + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = m := by push_cast; ring
  exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this

theorem relDim_lt_of_dim_lt {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F : Type*}
    [Field F] (I : Ideal (MRing ι F)) (m : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) < ((m + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I < (m : WithBot (WithTop ℤ)) := by
  unfold FieldNumbers.relDim
  generalize ringKrullDim (MRing ι F ⧸ I) = x at h ⊢
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    induction y using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe e =>
      have he : e < m + Fintype.card K := by exact_mod_cast h
      show (((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) < (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
      exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))

theorem lt_of_two_drops {x y : WithBot ℕ∞} {N : ℕ} (h1 : x + 1 ≤ y)
    (h2 : y + 1 ≤ ((N + 1 : ℕ) : WithBot ℕ∞)) : x < (N : WithBot ℕ∞) := by
  have hy := withBot_lt_natCast_of_add_one_le y (N + 1) h2
  have hx : x + 1 < ((N + 1 : ℕ) : WithBot ℕ∞) := lt_of_le_of_lt h1 hy
  have hx' : x + 1 ≤ (N : WithBot ℕ∞) := by
    induction x using WithBot.recBotCoe with
    | bot => simp
    | coe a =>
      induction a using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : ((⊤ : ℕ∞) + 1 : ℕ∞) < ((N + 1 : ℕ) : ℕ∞) := by exact_mod_cast hx
        simp at h3
      | coe a =>
        have : a + 1 < N + 1 := by exact_mod_cast hx
        exact_mod_cast (by omega : a + 1 ≤ N)
  exact withBot_lt_natCast_of_add_one_le x N hx'

end Helpers

theorem BlowUpVerticalFibre.proof (hmodel : BlowUpModel.Statement.{u})
    (hdeg : BlowUpFibreDegree.Statement.{u})
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{u}) :
    BlowUpVerticalFibre.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a W hϖW
  classical
  have hB : IsModelOver (blowUpOf P u) n := hmodel O K ι J P n hP N u hu hu'
  have hxB : liftForm (J := J) x ∉ blowUpOf P u := liftForm_not_mem_blowUpOf hxP
  have hxl : IsMultiHomog (liftForm (J := J) x) (liftMDeg c) := isMultiHomog_liftForm hx
  have hl : liftDegs a = fun i => FieldNumbers.pullDeg Function.Embedding.some (a i) := by
    funext i
    exact FlagBundlePullbackVanish.liftDeg_eq_pullDeg (a i)

  have key : ∀ W' : Ideal (MRing (extIdx ι J) O), divCycle (blowUpOf P u) (liftForm x) W' ≠ 0 →
      W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W →
      IsMultiProjPrime (specialIdeal W') ∧ FieldNumbers.relDim (specialIdeal W') = (n : ℕ) ∧
        (FieldNumbers.contractPrime Function.Embedding.some (specialIdeal W') :
          Ideal (MRing ι (IsLocalRing.ResidueField O))) = specialIdeal W := by
    intro W' hW' hcomap
    obtain ⟨hWp, hWrel, -, hWh⟩ := divCycle_ne_zero_facts hB.multiProj.multiHomog hxl hW'
    have hϖ' : (C ϖ : MRing (extIdx ι J) O) ∈ W' := by
      rw [← hcomap, Ideal.mem_comap, liftForm_C] at hϖW
      exact hϖW
    obtain ⟨hsp, -, hrel, -⟩ :=
      SpecialIdealCorresp.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) W' hWp hϖ'
    refine ⟨⟨hsp, SpecialIdealMultiHomog.proof O (Option K) (extIdx ι J) W' hWh, hrel.mp hWrel⟩, ?_, ?_⟩
    · apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ (Option K) (extIdx ι J) W' hϖ',
        ComponentDim.proof O ϖ hϖ (Option K) (extIdx ι J) (blowUpOf P u) n hB (liftMDeg c) _ hxl hxB
          W' hW' hϖ']
    · rw [← hcomap]
      exact contractPrime_specialIdeal hϖ W' hϖ'
  by_cases hW : divCycle P x W ≠ 0
  ·
    have hdimW : FieldNumbers.relDim (specialIdeal W) = (n : ℕ) := by
      apply relDim_eq_of_dim
      rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW, ComponentDim.proof O ϖ hϖ K ι P n hP c x hx hxP W hW hϖW]
    have hterm : ∀ W' : Ideal (MRing (extIdx ι J) O),
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * vNum W' (liftDegs a) else 0) =
        (if W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W then
          divCycle (blowUpOf P u) (liftForm x) W' * (specialRelDeg W' : ℤ) else 0) * vNum W a := by
      intro W'
      split_ifs with h1
      · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
        · simp [h0]
        obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
        have hpf' := (hpf (IsLocalRing.ResidueField O) K (Option K) Function.Embedding.some (extIdx ι J)
          (specialIdeal W') hmp n hrd (by rw [hcon]; exact hdimW) a).2
        rw [mul_assoc]
        congr 1
        unfold vNum specialRelDeg
        rw [dif_pos hmp.isPrime, hl, hpf', hcon]
        rfl
      · simp
    rw [finsum_congr hterm, ← finsum_mul, hdeg O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hW]
  ·
    rw [not_not] at hW
    rw [hW, zero_mul]
    refine finsum_eq_zero_of_forall_eq_zero fun W' => ?_
    split_ifs with h1
    · by_cases h0 : divCycle (blowUpOf P u) (liftForm x) W' = 0
      · rw [h0, zero_mul]
      obtain ⟨hmp, hrd, hcon⟩ := key W' h0 h1
      obtain ⟨hWmin', hWrel'⟩ :
          W' ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes ∧ IsRelevant W' := by
        by_contra hc
        exact h0 (by unfold divCycle; rw [dif_neg hc])
      obtain ⟨hWp, hPW, hWrel, -⟩ := comap_liftForm_facts hWmin'.1.1
        (le_sup_left.trans hWmin'.1.2) hWrel'
      rw [h1] at hWp hPW hWrel
      have hxW : x ∈ W := by
        rw [← h1, Ideal.mem_comap]
        exact hWmin'.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      have hJW : P ⊔ Ideal.span {x} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hxW)

      have hnmin : W ∉ (P ⊔ Ideal.span {x}).minimalPrimes := by
        intro hWmin
        refine (show divCycle P x W ≠ 0 from ?_) hW
        unfold divCycle
        rw [dif_pos ⟨hWmin, hWrel⟩]
        have := localizedQuot_nontrivial_of_le (P ⊔ Ideal.span {x}) W hJW
        have h0 : multAt (P ⊔ Ideal.span {x}) W ≠ 0 :=
          (Module.length_pos (R := Localization.AtPrime W)
            (M := LocalizedModule W.primeCompl (MRing ι O ⧸ (P ⊔ Ideal.span {x})))).ne'
        have htop := length_localizedQuot_ne_top _ W hWmin
        exact_mod_cast (ENat.toNat_pos h0 htop).ne'
      obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le hJW
      have hQp : Q.IsPrime := hQ.1.1
      have hQW' : Q < W := lt_of_le_of_ne hQW (fun h => hnmin (h ▸ hQ))
      have hPQ : P < Q := lt_of_le_of_ne (le_sup_left.trans hQ.1.2) (fun h =>
        hxP (h ▸ hQ.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))))
      have := hP.multiProj.isPrime
      have hd1 := DimStrictDrop.proof (MRing ι O) Q W hQW'
      have hd2 := DimStrictDrop.proof (MRing ι O) P Q hPQ
      rw [hP.dim, show n + 1 + Fintype.card K = (n + Fintype.card K) + 1 by omega] at hd2
      have hlt := lt_of_two_drops hd1 hd2
      have hltW : FieldNumbers.relDim (specialIdeal W) < ((n : ℕ) : WithBot (WithTop ℤ)) :=
        relDim_lt_of_dim_lt _ _ (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hlt)
      have hz := FieldNumbers.ProjectionFormulaContracted.full (IsLocalRing.ResidueField O) K (Option K)
        Function.Embedding.some (extIdx ι J) (specialIdeal W') hmp n hrd (by rw [hcon]; exact hltW) a
      unfold vNum
      rw [hl, hz, mul_zero]
    · rfl

end GroundTheory.Heights₂.Heights.NumbersDVR
