import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBStarOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.TensorPrimeModuli.SBStarOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.OddSpanRank.RankSpanLe

noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

open PrimeModuloFree LargePrimeDiscriminant in
theorem sBStarOdd_of : SBStarOdd := by
  intro hC hSep hBr hStab hSurj hWt L _ _ hTC k hk hkr l hl n hn
  haveI : IsTotallyComplex L := hTC
  obtain ⟨θ, hθs, hθ0, hθn⟩ := hBr k
  obtain ⟨τ, hτW, hτ⟩ := hWt L k hk
  have hcard : Fintype.card (InfinitePlace L) = nrComplexPlaces L := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  have hM : 2 * (k + 1) + 4 ≤ lev l n k := le_trans hn (PrimeModuloFree.le_lev hl n k)
  let C : Submodule ℝ (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker :=
    Submodule.span ℝ {y | ∃ z0 : Chn (GL (Fin n) (𝓞 L)) (k + 1), IsCyc z0 ∧
      (y : Chn (GL (Fin (lev l n k)) (𝓞 L)) (k + 1)) = PrimeModuloFree.zc (𝓞 L) hl z0 k}
  calc _ ≤ ((Fintype.card (InfinitePlace L) : ℕ) : Cardinal) :=
        TwOdd.rank_span_le _ ((θ (GL (Fin (lev l n k)) (𝓞 L))).comp C.subtype)
          ((LinearMap.pi fun w : InfinitePlace L => τ w (lev l n k)).comp
            ((bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker.subtype.comp C.subtype)) ?_ ?_
    _ = _ := by rw [hcard]
  · intro z hT
    have hTw : ∀ w, τ w (lev l n k) (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1 = 0 :=
      fun w => congrFun hT w
    show (θ _) (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker) = 0
    refine (hθ0 _ _).2 ?_
    by_contra hnb
    have hcyc : IsCyc (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1 :=
      LinearMap.mem_ker.mp (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).2
    obtain ⟨N, hMN, hN⟩ := hSurj L hTC k hkr (lev l n k)
    have hz'c := LargePrimeDiscriminant.isCyc_cmap hC (stab (𝓞 L) (lev l n k) N hMN) hcyc
    have hz'nb : ¬ IsBd (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) :=
      fun h => hnb ((hStab (𝓞 L) k (lev l n k) N hMN hM).1 _ hcyc h)
    obtain ⟨c, hcI, hcd, hcne⟩ := hSep _ k _ hz'c hz'nb
    obtain ⟨ω, hωI, hω⟩ := hN c hcI hcd
    obtain ⟨cc, a, ha, hdec⟩ := hτ N ω hωI
    have hazero : ∀ j ∈ Finset.Icc 2 (k + 1), ∀ y ∈ C,
        a j (lev l n k) (y : Chn (GL (Fin (lev l n k)) (𝓞 L)) (k + 1)) = 0 := by
      intro j hj y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨z0, hz0, hx⟩ := hx
        rw [hx, PrimeModuloFree.wsys_zc (R := 𝓞 L) hC (ha j hj) hl hz0 k]
        apply mul_eq_zero_of_left
        rw [Finset.mem_Icc] at hj
        apply Finset.prod_eq_zero (i := j - 2)
        · rw [Finset.mem_range]; omega
        · rw [Nat.sub_add_cancel hj.1, sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp [hx, hy]
      | smul r x _ hx => simp [hx]
    apply hcne
    rw [hω _ hz'c, hdec _ hz'c]
    have h1 : ∀ w, τ w N (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) = 0 := by
      intro w
      rw [(hτW w).2.1 _ _ hMN _ hcyc]
      exact hTw w
    have h2 : ∀ j ∈ Finset.Icc 2 (k + 1), a j N (cmap (stab (𝓞 L) (lev l n k) N hMN) (k + 1)
        (z : (bd (GL (Fin (lev l n k)) (𝓞 L)) k).ker).1) = 0 := by
      intro j hj
      rw [(ha j hj).2.1 _ _ hMN _ hcyc]
      exact hazero j hj _ z.2
    rw [Finset.sum_eq_zero (fun w _ => by rw [h1 w, mul_zero]), Finset.sum_eq_zero h2, add_zero]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨z0, hz0⟩ := hθs (GL (Fin n) (𝓞 L)) (1 ⊗ₜ x)
    refine ⟨⟨⟨PrimeModuloFree.zc (𝓞 L) hl z0.1 k,
      PrimeModuloFree.isCyc_zc hC (𝓞 L) hl (LinearMap.mem_ker.mp z0.2) k⟩,
      Submodule.subset_span ⟨z0.1, LinearMap.mem_ker.mp z0.2, rfl⟩⟩, ?_⟩
    exact PrimeModuloFree.th_zc θ hθn hC (𝓞 L) hl z0.1 (LinearMap.mem_ker.mp z0.2) x hz0 k

end PositivityTheory.KB

end
