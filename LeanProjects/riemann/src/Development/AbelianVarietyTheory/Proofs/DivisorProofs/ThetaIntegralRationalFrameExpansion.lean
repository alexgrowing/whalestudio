import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoExistsBlockSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameLocalLanglandsUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetInducedCharFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubquotientTransport

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspBlock

theorem isHermND_skew' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {B : Base F E} {d : ℕ} {W : Spc F E d} {r s : ℕ}
    (h : W.IsSkew σ B r s) {c : E} (hc : c ≠ 0) (hcs : σ c = -c) : IsHermND σ (c • W.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hcs]
    rw [h.skew j i]
    ring
  · have hJ : W.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply GlobalTheory.UnitaryVol.det_ne_zero_of_isCartan (h.cartan w)
      rw [Matrix.det_smul, show W.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix W.J from rfl, ← RingHom.map_det, hz,
        map_zero, mul_zero]
    rw [Matrix.det_smul, show W.J.map σ = (σ : E →+* E).mapMatrix W.J from rfl, ← RingHom.map_det]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero _).2 hJ)

theorem exists_blockStart {r : ℕ} (S : Finset (Fin r)) (i : Fin r) :
    ∃ l : ℕ, l ≤ i.val ∧ (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) ∧ ∀ j ∈ S, j < i → j.val + 1 ≤ l := by
  classical
  by_cases hP : (S.filter (· < i)).Nonempty
  · have hm := Finset.mem_filter.1 (Finset.max'_mem _ hP)
    refine ⟨((S.filter (· < i)).max' hP).val + 1, hm.2, Or.inr ⟨_, hm.1, rfl⟩, fun j hj hji => ?_⟩
    have := Finset.le_max' (S.filter (· < i)) j (Finset.mem_filter.2 ⟨hj, hji⟩)
    exact Nat.succ_le_succ this
  · exact ⟨0, Nat.zero_le _, Or.inl rfl, fun j hj hji => absurd ⟨j, (Finset.mem_filter.2 ⟨hj, hji⟩ : j ∈ S.filter (· < i))⟩ hP⟩

end GlobalTheory.CuspBlock

theorem GlobalTheory.CuspBlock.valuation_eq_one_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (y : p.adicCompletion K) :
    ValuativeRel.valuation (p.adicCompletion K) y = 1 ↔
      (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ))) y = 1 := by
  haveI : (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation (p.adicCompletion K))
    (Valued.v : Valuation (p.adicCompletion K) (WithZero (Multiplicative ℤ)))
  rw [le_antisymm_iff, le_antisymm_iff, h.le_one_iff_le_one, ← not_lt, ← not_lt, h.lt_one_iff_lt_one]
  exact and_congr Iff.rfl not_lt

theorem GlobalTheory.CuspBlock.unram_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (χ : (Fv F v)ˣ →* ℂˣ), IsUnram χ →
    IsUnram (χ.comp (Units.map (complEquiv t (splitPrime_under t)).symm.toRingHom.toMonoidHom)) := by
  intro F E _ _ _ _ _ v t χ hχ x hx
  have hv := GlobalTheory.LFun.SplitTie.valued_complMap t (splitPrime_under t) ((complEquiv t (splitPrime_under t)).symm (x : _))
  rw [← complEquiv_apply, RingEquiv.apply_symm_apply] at hv
  exact hχ _ ((GlobalTheory.CuspBlock.valuation_eq_one_iff v _).2 (by
    show Valued.v ((complEquiv t (splitPrime_under t)).symm (x : _)) = 1
    rw [← hv]; exact (GlobalTheory.CuspBlock.valuation_eq_one_iff (splitPrime t) _).1 hx))

namespace GlobalTheory.CuspBlock

theorem block_bridge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), IsWittFrame σ (c • G.W.J.map σ) Xf Yf →
        ∀ K, IsMaxCpt σ (c • G.W.J.map σ) K →
          IsAut σ (c • G.W.J.map σ) K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) →
          ∀ (S : Finset (Fin r)) (φc : GAd σ (c • G.W.J.map σ) → ℂ),
            GlobalTheory.StdPar.IsCuspComp σ (c • G.W.J.map σ) Xf Yf S K (fun x => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm x)) φc →
            φc ≠ 0 → ∀ k ∈ S, ∀ i : Fin r, i < k → (∀ j : Fin r, i ≤ j → j < k → j ∉ S) →
              ∃ (w : HeightOneSpectrum (𝓞 E)) (x x' : ℕ) (τ : GlobalTheory.CuspRep.CuspSub E (x + x'))
                (χ₁ χ₂ : (w.adicCompletion E)ˣ →* ℂˣ) (s₁ s₂ : ℝ),
                2 ≤ x + x' ∧ GlobalTheory.SplitWeil.IsUnram χ₁ ∧ GlobalTheory.SplitWeil.IsUnram χ₂ ∧
                (∀ u, ‖(χ₁ u : ℂ)‖ = 1) ∧ (∀ u, ‖(χ₂ u : ℂ)‖ = 1) ∧ (x = 1 → x' = 1 → 1 < |s₁ - s₂|) ∧
                ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
                  (Q : Representation ℂ (GL (Fin (x + x')) (w.adicCompletion E)) V),
                  GlobalTheory.SmGL.IsSubquotient Q (GlobalTheory.SmGL.prod₂
                    (GlobalTheory.SmGL.detRep (Fin x) (χ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₁ : ℂ)))
                    (GlobalTheory.SmGL.detRep (Fin x') (χ₂ * GlobalTheory.SmGL.absPow (w.adicCompletion E) (s₂ : ℂ)))) ∧
                  ∃ f : Q.IntertwiningMap (τ.locRep w), f ≠ 0 := by
  intro F E _ _ _ _ _ _ σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ r Xf Yf hW K hK hAut S φc hφc hne k hk i hik hgap
  have hcm : IsCMExt F E σ := hT.base.cm
  have hJ : IsHermND σ (c • G.W.J.map σ) := isHermND_skew' hσ hT.geo.hW hc hcs
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.T.witt_frame_local_langlands_unitary hKP hKP.cuspidalSpectrumGL F E σ hcm (a + a') (c • G.W.J.map σ) hJ r Xf Yf hW hKP.automorphicFormsUnitary.2 B.v₁ B.τ₁
  obtain ⟨b, hb, χ, hbab, hunr, hunit, m, T, x, hTi, hsum⟩ := GlobalTheory.T.pol_data_so_exists_block_splitting F E σ hσ B a a' G X om om' hKP hT c hc hcs Φ hΦ B₀
  obtain ⟨l, hli, hl0, hlt⟩ := exists_blockStart S i
  obtain ⟨d, hd⟩ : ∃ d, d = k.val + 1 - l := ⟨_, rfl⟩
  have hik' : i.val < k.val := hik
  have hd1 : 1 ≤ d := by omega
  have hgap' : ∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S := by
    intro j hlj hjd hjS
    by_cases hji : j < i
    · have := hlt j hjS hji
      omega
    · exact hgap j (not_lt.1 hji) (show j.val < k.val by omega) hjS
  obtain ⟨hld, τ, W', _, _, Q, hQ, f, hf⟩ := hB₀ K hK _ hAut _ (pairInd (Fv F B.v₁) b hb χ) (isSmooth_parInd _ _) m T x hTi
    hsum S φc hφc hne l d hd1 hgap' ⟨k, hk, by omega⟩ hl0
  obtain ⟨x₁, x₂, c₁, c₂, hx, s₁, s₂, hcc, hs, V', _, _, Q', hQ', f', hf'⟩ :=
    GlobalTheory.T.jacquet_induced_char_filtration hKP.geometricLemmaFiltration (Fv F B.v₁) (a + a') b hb χ (fun j => isSmoothChar_of_isUnram (hunr j)) l d hld _
      _ W' Q hQ f hf
  subst hx
  obtain ⟨V'', _, _, Q'', hQ'', f'', hf''⟩ := GlobalTheory.FieldTransportInd.exists_subquotient_transport F E B.v₁ B.τ₁ x₁ x₂ (χ 0) (χ 1) s₁ s₂ _ (τ.locRep (splitPrime B.τ₁))
    V' Q' hQ' f' hf'
  have hwitt := GlobalTheory.WittBound.wittIndex_le F E σ B (a + a') G.W (a + a' - (G.p + G.q)) (G.p + G.q) hT.base hT.geo.hW c hc hcs
    r Xf Yf hW
  have heB := hT.geo.eBig
  have hlt' := hT.geo.lt
  have hkr : k.val < r := k.isLt
  refine ⟨splitPrime B.τ₁, x₁, x₂, τ, _, _, s₁, s₂, by omega, unram_transport F E B.v₁ B.τ₁ _ (hunr 0),
    unram_transport F E B.v₁ B.τ₁ _ (hunr 1), fun u => hunit 0 _, fun u => hunit 1 _, ?_, V'', _, _, Q'', hQ'', f'', hf''⟩
  intro h1 h2
  subst h1 h2
  have hab : 4 * (G.p + G.q) + 4 ≤ a - a' := by omega
  have hab' : 4 * ((G.p : ℝ) + G.q) + 4 ≤ (a : ℝ) - a' := by
    have := (Nat.cast_le (α := ℝ)).2 hab
    push_cast [Nat.cast_sub hlt'.le] at this
    linarith
  have hl2 : l + 2 ≤ G.p + G.q := by omega
  have hl2' : (l : ℝ) + 2 ≤ (G.p : ℝ) + G.q := by exact_mod_cast hl2
  have hcc' : (c₁ : ℝ) + c₂ = l := by exact_mod_cast hcc
  have hc1 : (0 : ℝ) ≤ c₁ := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ c₂ := Nat.cast_nonneg _
  push_cast at hs hab' hl2'
  rcases hbab with ⟨hb0, hb1⟩ | ⟨hb0, hb1⟩ <;> rw [hb0, hb1] at hs
  · rw [hs, lt_abs]; right; linarith
  · rw [hs, lt_abs]; left; linarith

end GlobalTheory.CuspBlock
