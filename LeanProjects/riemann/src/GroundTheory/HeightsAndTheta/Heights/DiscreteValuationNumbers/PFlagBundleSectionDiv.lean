import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleSectionDiv
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsMultAtOfSaturated
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsProjIdealFormValue
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTruncSpecialize
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleChartSection
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleSectionDivProof

theorem eq_of_lt_of_le_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [P.IsPrime] [Q.IsPrime] {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  have hQW' : Q < W := lt_of_le_of_ne hQW hne
  have : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := hPQ.le.trans hQW
  have hker : RingHom.ker f = P := Ideal.mk_ker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPW)
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPQ.le)
  have h1 : (W.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hlt : Q.map f < W.map f := by
    refine (Ideal.map_mono hQW).lt_of_not_ge fun e => hQW'.not_ge ?_
    have := Ideal.comap_mono (f := f) e
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ.le] at this
  have : (W.map f).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h2 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h2
  refine hPQ.not_ge fun q hq => ?_
  have h3 : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
  rw [h2, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
  exact h3

theorem divCycle_eq_zero_of_not_mem {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dif_neg]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

theorem divCycle_congr {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x x' : MRing ι R} (h : x - x' ∈ P) : divCycle P x = divCycle P x' := by
  have hJ : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {x'} := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.add_mem _ (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x'})
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x') : x' ∈ P ⊔ Ideal.span {x'})
      rwa [sub_add_cancel] at this
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x) : x ∈ P ⊔ Ideal.span {x})
        (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x})
      rwa [sub_sub_cancel] at this
  funext W
  unfold divCycle
  split_ifs with h1 h2 h2
  · simp only [hJ]
  · exact absurd (hJ ▸ h1) h2
  · exact absurd (hJ.symm ▸ h2) h1
  · rfl

end FlagBundleSectionDivProof

open FlagBundleSectionDivProof in

theorem FlagBundleSectionDiv.proof (hDim : FlagBundleDim.Statement)
    (hSat : MultAtOfSaturated.Statement.{0}) (hForm : ProjIdealFormValue.Statement)
    (hTrunc : TruncSpecialize.Statement) (hChart : FlagBundleChartSection.Statement) :
    FlagBundleSectionDiv.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi bf bg f g hf hg
    hdeg hgP hval W
  classical
  have hQ : IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi i.2.le).1
  have hP : IsMultiProjPrime (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2).1
  have := hP.isPrime
  have := hQ.isPrime
  obtain ⟨hPQ, hspec⟩ := hTrunc F Ω K ι y N E w M φ Φ t ht i
  have hti : t i ≠ 0 := ht.ne_zero i
  have hval0 := fun (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F) (hx : IsMultiHomog x d) =>
    hForm F Ω K ι y N E w M φ Φ (truncCoord t ((i : ℕ) + 1)) d x hx
  have hgv := fun h => hgP ((hval0 _ _ hg).mpr h)
  have hfP : f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
    mul_ne_zero hti hgv (hval ▸ (hval0 _ _ hf).mp h)
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hW
    choose c hc using fun k => hWrel (some k)
    have hy : segreVec y c ≠ 0 := by
      unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro k _ hk
      apply hc k (hPW ?_)
      rw [hval0 _ _ (isWeightedHomogeneous_X F _ _), eval₂_X]
      simp [projCoord, hk]
    obtain ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩ :=
      hChart F Ω K ι y N E B w b hB M a φ hφ Φ t ht i c hy
    have hsW : ∀ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n ∉ W := by
      intro n h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp (hWp.mem_of_pow_mem n h)
      exact hc k hk
    have hμW : μ ∉ W := by
      rw [hμ]
      intro h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp h
      exact hc k (hWp.mem_of_pow_mem _ hk)
    have hμP : μ ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h => hμW (hPW h)
    have hμv := fun h => hμP ((hval0 _ _ hμh).mpr h)
    have hlP : l ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
      mul_ne_zero hti hμv (hlv ▸ (hval0 _ _ hl).mp h)
    have hdeg' : bf + dm = dl + bg := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : f * μ - l * g ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      have h2 := hl.mul hg
      rw [← hdeg'] at h2
      have h1 : IsMultiHomog (f * μ - l * g) (bf + dm) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hf.mul hμh))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
      rw [hval0 _ _ h1, eval₂_sub, eval₂_mul, eval₂_mul, hval, hlv]
      ring
    have hrat : ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
        divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) l W := by
      have h1 := congrFun (divCycle_congr hdiff) W
      rw [DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ f μ hP.isPrime hfP hμP,
        DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ l g hP.isPrime hlP hgP] at h1
      simp only [Pi.add_apply, divCycle_eq_zero_of_not_mem hμW] at h1
      unfold ratDiv
      omega
    rw [hrat]
    have hlQ : l ∈ projIdeal F y w φ (truncCoord t i) :=
      (hForm F Ω K ι y N E w M φ Φ (truncCoord t i) dl l hl).mpr (hspec l μ hlv)
    split_ifs with hWQ
    · subst hWQ
      obtain ⟨hmin, hmult⟩ := hSat F (Option K) (bundleIdx ι M) _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hlQ))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat q hq
          exact ⟨_, hsW n, hn⟩)
      unfold divCycle
      rw [dif_pos ⟨hmin, hQ.relevant⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h
        · exact h.1
        · exact absurd rfl hne
      have hQW : projIdeal F y w φ (truncCoord t i) ≤ W := fun q hq => by
        obtain ⟨n, hn⟩ := hsat q hq
        exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (hsW n)
      have hPQ' : projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) < projIdeal F y w φ (truncCoord t i) :=
        lt_of_le_of_ne hPQ (fun h => hlP (by rw [h]; exact hlQ))
      exact hWQ (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm
  · have h0 : ∀ x, divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) x W = 0 := fun x => by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h, hr⟩
      exact hW ⟨h.1.1, hr, le_sup_left.trans h.1.2⟩
    have hWQ : W ≠ projIdeal F y w φ (truncCoord t i) := by
      rintro rfl
      exact hW ⟨hQ.isPrime, hQ.relevant, hPQ⟩
    simp [ratDiv, h0, hWQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
