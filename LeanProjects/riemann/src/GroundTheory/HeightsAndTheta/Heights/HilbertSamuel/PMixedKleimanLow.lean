import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanLow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntegralAgainstPositive
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem MixedKleimanLow.exists_monomial {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (hP : P.IsPrime) (hrel : IsRelevant P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ (monomial μ 1 : MRing ι) ∉ P ∧
      IsMultiHomog (monomial μ 1 : MRing ι) a := by
  classical
  choose c hc using hrel
  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := fun k => by simp [μ]
  refine ⟨μ, hμ, fun hmem => ?_, fun m hm k => ?_⟩
  · rw [monomial_eq, map_one, one_mul, Finsupp.prod, hP.prod_mem_iff] at hmem
    obtain ⟨p, hp, hXp⟩ := hmem
    have hp2 : p.2 = c p.1 := by
      by_contra h
      exact (Finsupp.mem_support_iff.mp hp) (by simp [μ, h])
    obtain ⟨k, i⟩ := p
    obtain rfl : i = c k := hp2
    exact hc k (hP.mem_of_pow_mem _ hXp)
  · rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
    exact hμ k

theorem MixedKleimanLow.proof (hI : IntegralAgainstPositive.Statement)
    (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg) : MixedKleimanLow.Statement := by
  classical
  intro d hd K _ ι _ P P0 M A a II hII h1 hP hP0 hMs hMn hMc hMW hAa hAs hAb hAc j hj
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hd
  let L : Fin n → HermLine ι := fun i => if (i : ℕ) < j then M else A
  have hsnoc : (fun i : Fin (n + 1) => if (i : ℕ) < j then M else A) = Fin.snoc L A := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last, if_neg (by simp; omega)]
    · rw [Fin.snoc_castSucc]; rfl
  have hLs : ∀ i, IsSemipositiveRel P0 P (L i) := fun i => by
    simp only [L]; split_ifs <;> assumption
  obtain ⟨μ, hμ, hsP, hsh⟩ := MixedKleimanLow.exists_monomial P hP.2.1.1 hP.2.1.2.2 a
  have hAk : ∀ k, A.a k = a k := fun k => by rw [hAa]

  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz => ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  rw [hsnoc, (hII K ι).2.2 P n L A _ a hP (fun i => (hLs i).1) hAs.1 hAk hsh hsP]
  unfold recR
  refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW => ?_))
  ·
    refine hI K ι P P0 n L _ hP0 hLs fun z hz => ?_
    have hpos := A.pos z hz.1
    unfold logNorm
    refine Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le) ((div_le_one hpos).mpr ?_)
    rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact hAb z hz μ hμ
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n A _ W hP ⟨a, hAk, hsh, hsP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd hWv (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)
      exact hd K ι W P0 M A a II hII hn hWv (hP0.trans hPW)
        ⟨hMs.1, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) hAa ⟨hAs.1, fun z hz => hAs.2 z (hpts hPW hz)⟩
        (fun z hz => hAb z (hpts hPW hz)) hAc j (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun i => (L i).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun i => ?_
        intro W' h1 h2 h3
        simp only [L]
        split_ifs
        · exact hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        · rw [hAa]
          exact ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by positivity) W' h1 le_rfl (hchar W W' h2 hc) h3
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
