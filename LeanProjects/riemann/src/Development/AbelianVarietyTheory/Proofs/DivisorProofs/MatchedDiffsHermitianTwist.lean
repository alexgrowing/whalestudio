import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactPolDataPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataWittFrameScaledStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicLinearCombinationConstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxCompactConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConjMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermLinearContinuousStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.ThK.CuspComponentDifferences

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCuspComp_zero {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {S : Finset (Fin r)} {K : Subgroup (GAd σ J)} : GlobalTheory.StdPar.IsCuspComp σ J X Y S K 0 0 := by
  refine ⟨⟨GlobalTheory.StdPar.isAutOn_const σ J X Y S K 0, fun S' _ => GlobalTheory.StdPar.isConstAlong_const σ J X S' 0⟩, 0,
    GlobalTheory.StdPar.isConstAlong_const σ J X S 0, fun ψ _ μ 𝓕 _ _ g g' => ⟨?_, ?_, ?_⟩⟩ <;> simp

theorem polData_of_polMatch
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {R : RealMaps F a a'} {Rf : FinMaps F a a'} {Φ Φ'}
    (h : PolMatch B G X R Rf Φ Φ') : Φ ∈ GlobalTheory.ThK.PolData B G.M ∧ Φ' ∈ GlobalTheory.ThK.PolData B G.M' := by
  obtain ⟨T, -, m, m', f, φ, f', φ', hi, hj, rfl, rfl, -⟩ := h
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, (hi i).1, φ i, (hi i).2.1, ?_, rfl⟩,
    Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨f' j, (hj j).1, φ' j, (hj j).2.1, ?_, rfl⟩⟩
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hi i).2.2 v hT))
  · exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by_contra fun hT => hv ((hj j).2.2 v hT))

theorem imag_of_isHermND {B : Base F E} {n : ℕ} {W : Spc F E n} {r s : ℕ} (hW : W.IsSkew σ B r s) (hn : n ≠ 0)
    {c : E} (hJ : IsHermND σ (c • W.J.map σ)) : σ c = -c := by
  by_contra hc
  apply hJ.2
  have h0 : c • W.J.map σ = 0 := by
    ext j i
    have h1 := hJ.1 i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul] at h1
    rw [hW.skew i j, map_neg, hW.skew j i] at h1
    have h2 : (σ c + c) * W.J j i = 0 := by linear_combination h1
    have h3 : W.J j i = 0 := (mul_eq_zero.1 h2).resolve_left fun e => hc (eq_neg_of_add_eq_zero_left e)
    simp [h3]
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [h0]
  exact Matrix.det_zero

omit [NumberField F] [NumberField E] in

theorem ne_zero_of_isWittFrame {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (h : GlobalTheory.SiegelSet.IsWittFrame σ J X Y) (k : Fin r) : n ≠ 0 := by
  rintro rfl
  have := congrFun (congrFun h.xy k) k
  simp [Matrix.mul_apply] at this

theorem cuspComp_diffs_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf → ∀ c : ℂ, ∀ f ∈ Diffs B G X om om' R Rf c,
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • G.W.J.map σ) → ∀ φ' : GAd σ (c₀ • G.W.J.map σ) → ℂ,
        (∀ (g : UA σ G.W.J) (g' : GAd σ (c₀ • G.W.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • G.W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • G.W.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin (a + a')) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • G.W.J.map σ) Xf Yf →
          ∀ S : Finset (Fin r), ¬ (∀ k ∈ S, ∀ l ≤ k, l ∈ S) → GlobalTheory.StdPar.IsCuspComp σ (c₀ • G.W.J.map σ) Xf Yf S K φ' 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM c f hf c₀ hc₀ hJ φ' hφ' K hK r Xf Yf hW S hS
  have h : IsCMExt F E σ := hM.triple.base.cm
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma h
  have hn : a + a' ≠ 0 := by
    by_contra hn
    exact hS fun k _ => absurd hn (ne_zero_of_isWittFrame hW k)
  have hcσ : σ c₀ = -c₀ := imag_of_isHermND hM.triple.geo.hW hn hJ
  have eφ : φ' = fun x => f ((toGAd hσ G.W.J hc₀).symm x) := funext fun x => hφ' _ x rfl
  subst eφ
  clear hφ'
  suffices H : Continuous (fun x => f ((toGAd hσ G.W.J hc₀).symm x)) ∧
      (∀ γ ∈ GlobalTheory.AdelicU.ratPts σ (c₀ • G.W.J.map σ), ∀ g,
        f ((toGAd hσ G.W.J hc₀).symm (γ * g)) = f ((toGAd hσ G.W.J hc₀).symm g)) ∧
      GlobalTheory.StdPar.IsCuspComp σ (c₀ • G.W.J.map σ) Xf Yf S K (fun x => f ((toGAd hσ G.W.J hc₀).symm x)) 0 from H.2.2
  have lin := GlobalTheory.T.constant_term_linear_continuous F E σ h (a + a') _ hJ r Xf Yf hW K S
  unfold Diffs at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Φ, Φ', hΦ', hPM, rfl⟩ := hx
    obtain ⟨hΦd, hΦ'd⟩ := polData_of_polMatch hPM
    obtain ⟨K₁, hK₁, hAV, hAV'⟩ := GlobalTheory.T.max_compact_pol_data_pair F E σ hσ B a a' G X om om' hKP hM.triple c₀ hc₀ hcσ Φ hΦd Φ' ⟨hΦ'd, hΦ'⟩
    refine ⟨hAV.mod.cont.sub (continuous_const.mul hAV'.mod.cont), fun γ hγ g => ?_, ?_⟩
    · have e1 := hAV.mod.left γ hγ g
      have e2 := hAV'.mod.left γ hγ g
      simp only at e1 e2 ⊢
      rw [e1, e2]
    · have h1 := GlobalTheory.T.pol_data_witt_frame_scaled F E σ hσ B a a' G X om om' hKP hM.triple c₀ hc₀ hcσ Φ hΦd r Xf Yf hW K₁ hK₁ hAV S hS
      have h2 := GlobalTheory.T.pol_data_so_witt_frame F E σ hσ B a a' G X om om' hKP hM.triple c₀ hc₀ hcσ Φ' ⟨hΦ'd, hΦ'⟩ r Xf Yf hW K₁ hK₁ hAV' S hS
      have h3 := GlobalTheory.T.automorphic_linear_combination_const F E σ h (a + a') _ hJ r Xf Yf hW K₁ S _ _ 0 0 c (GlobalTheory.StdPar.isAutOn_empty.2 hAV)
        (GlobalTheory.StdPar.isAutOn_empty.2 hAV') h1 h2
      obtain ⟨u, hu, huK⟩ := GlobalTheory.T.max_compact_conjugate F E σ h (a + a') _ hJ K₁ K hK₁ hK
      refine GlobalTheory.T.automorphic_conj_max_compact F E σ h (a + a') _ hJ r Xf Yf hW K₁ K u hu huK S _ ?_
      convert h3 using 1
      funext x; simp
  | zero => exact ⟨continuous_const, fun _ _ _ => rfl, isCuspComp_zero⟩
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, fun γ hγ g => by simp only [Pi.add_apply, hx.2.1 γ hγ g, hy.2.1 γ hγ g], ?_⟩
    have := lin _ _ (-1) hx.1 hy.1 hx.2.1 hy.2.1 hx.2.2 hy.2.2
    convert this using 1
    funext g; simp
  | smul z x _ hx =>
    refine ⟨continuous_const.mul hx.1, fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, hx.2.1 γ hγ g], ?_⟩
    have := lin 0 _ (-z) continuous_const hx.1 (fun _ _ _ => rfl) hx.2.1 isCuspComp_zero hx.2.2
    convert this using 1
    funext g; simp

end GlobalTheory.ThK.CuspComponentDifferences
