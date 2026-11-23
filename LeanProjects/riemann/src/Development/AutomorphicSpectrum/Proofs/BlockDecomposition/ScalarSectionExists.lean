import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity

noncomputable section

namespace GlobalTheory.CompanionTheory.ScalWall

open PositivityTheory.RgEis ResidueKilled.Tr GlobalTheory.CompanionTheory.SiegelFrame

theorem pos_eq_norm_cosetSum {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (l : G' → ℝ) (hc : Conv Γ' P' l)
    (hl : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, l (γ * y) = l y) (g : G) :
    pos Γ' P' l (Φ g) = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (l (Φ x)) : ℂ)) g‖ := by
  have hs : HasSum (fun q : PositivityTheory.RgEis.Cos P' Γ' => Real.exp (l (PositivityTheory.RgEis.rep q * Φ g)))
      (PositivityTheory.RgEis.pos Γ' P' l (Φ g)) := (hc (Φ g)).hasSum
  have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ Γ P Γ' P' hΓ hP (fun y => Real.exp (l y))
    (fun γ hγ hγP y => by simp only [hl γ hγ hγP y]) (Φ g) _ hs
  have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ => ((Real.exp (l (Φ (PositivityTheory.RgEis.rep q * g))) : ℝ) : ℂ))
      ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (by simpa only [map_mul] using h2)
  have h4 : GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (l (Φ x)) : ℝ) : ℂ)) g
      = ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) := h3.tsum_eq
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (hs.nonneg fun _ => (Real.exp_pos _).le)]

theorem fin_along {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (K' : Subgroup G') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))) := by
  have e : (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))
      = (LinearMap.funLeft ℂ ℂ (⇑Φ.symm)) '' (Set.range fun k : K' => fun x => f (x * Φ.symm k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k y
    simp [LinearMap.funLeft_apply, map_mul]
  rw [e, ← Submodule.map_span]
  exact Module.Finite.map _ _

theorem tScal : TScal := by
  unfold ResidueKilled.Tr.TScal ResidueKilled.Tr.Scal
  intro hSec hWL G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η N hK hPar hHt hΓ hP hW f hf hlaw hfin
  have hcrat : ∀ γ ∈ Γ', γ ∈ P' → c γ = 1 := by
    obtain ⟨_, _, ⟨_, _, h, _⟩⟩ := hPar
    exact h
  have hηl : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g := by
    obtain ⟨h, _, _, _⟩ := hHt
    exact h
  have hηr : ∀ γ ∈ Γ', γ ∈ P' → η γ = 0 := by
    obtain ⟨_, _, h, _⟩ := hHt
    exact h
  have hβ : PositivityTheory.RgEis.IsHt Γ' K' P' (fun g => N * η g) := by
    obtain ⟨h1, h2, h3, h4⟩ := hHt
    exact ⟨fun p hp g => by simp only [h1 p hp g, mul_add], fun g k hk => by simp only [h2 g k hk],
      fun γ hγ hγP => by simp only [h3 γ hγ hγP, mul_zero], continuous_const.mul h4⟩
  have hlaw' : ∀ p ∈ P', ∀ x : G', (fun y => f (Φ.symm y)) (p * x)
      = c p * Complex.exp (0 * ↑(η p)) * (fun y => f (Φ.symm y)) x := by
    intro p hp x
    have hp' : Φ.symm p ∈ P := (hP (Φ.symm p)).mpr (by simpa using hp)
    simp only [map_mul, zero_mul, Complex.exp_zero, mul_one]
    rw [hlaw _ hp']
    simp
  have hfin' := fin_along Φ.toMulEquiv K' f hfin
  obtain ⟨R, D, H, hD, hDz, hHd, hHc, hconv1, hconv2, hbd, hsum⟩ :=
    GlobalTheory.CompanionTheory.SiegelFrame.scalar_wall hSec hWL Γ' K' P' c η (fun g => N * η g) hK hPar hHt hβ hW
      (fun y => f (Φ.symm y)) 0 (hf.comp (map_continuous Φ.symm)) hlaw' hfin'
  refine ⟨D, fun z g => H z (Φ g), R, hD, hDz, fun g => hHd (Φ g), ?_, ?_, ?_⟩
  · exact hHc.comp (continuous_fst.prodMk ((map_continuous Φ).comp continuous_snd))
  · intro z hz g
    show H z (Φ g) = _
    have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ.toMulEquiv Γ P Γ' P' hΓ hP
      (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
      (fun γ hγ hγP y => by
        have hγ' : Φ.symm γ ∈ P := (hP (Φ.symm γ)).mpr (by simpa using hγP)
        simp only [hηl γ hγP y, hηr γ hγ hγP, zero_add, map_mul]
        rw [hlaw _ hγ']
        simp [hcrat γ hγ hγP])
      (Φ g) _ (hsum z hz (Φ g))
    have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ =>
        D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g))) (H z (Φ g)) := by
      have e : (fun q : PositivityTheory.RgEis.Cos P Γ =>
          D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g)))
          = fun q => (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
              (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g) := by
        funext q
        have hm : Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g = Φ (PositivityTheory.RgEis.rep q * g) :=
          (map_mul Φ _ _).symm
        show _ = D z * (Complex.exp ((z - 0) * ↑(η (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
          * f (Φ.symm (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
        rw [hm, sub_zero, ContinuousMulEquiv.symm_apply_apply]
      rw [e]
      exact h2
    rw [← h3.tsum_eq, tsum_mul_left]
    rfl
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨M, fun z hz1 hz2 g => ?_⟩
    have hl2 : (fun x : G' => N * η x - b * η x) = fun x => (N - b) * η x := by
      funext x
      ring
    have hinv : ∀ (t : ℝ), ∀ γ ∈ Γ', γ ∈ P' → ∀ y, t * η (γ * y) = t * η y := by
      intro t γ hγ hγP y
      rw [hηl γ hγP y, hηr γ hγ hγP, zero_add]
    have e1 : PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (a * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => a * η x) (hconv1 a ha)
      (fun γ hγ hγP y => hinv a γ hγ hγP y) g
    have hc2 : PositivityTheory.RgEis.Conv Γ' P' (fun x => (N - b) * η x) := by
      rw [← hl2]
      exact hconv2 b hb
    have e2 : PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp ((N - b) * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => (N - b) * η x) hc2
      (fun γ hγ hγP y => hinv (N - b) γ hγ hγP y) g
    have key := hM z hz1 hz2 (Φ g)
    have e3 : PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)
        = PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g) := by
      rw [hl2]
    calc ‖H z (Φ g)‖ ≤ M * (PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
          + PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)) := key
      _ = _ := by
        rw [e3, e1, e2]
        try rfl

end GlobalTheory.CompanionTheory.ScalWall

end
