import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLevelPPowerFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelMapOverInclusionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPairingApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorApproximationStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatModel

theorem lt_norm_mul_of_close {K : Type} [NormedField K] [IsUltrametricDist K] {a₁ a₂ c₁ c₂ : K} {ε : ℝ}
    (h₂ : ‖a₂‖ ≤ 1) (hc₁ : ‖c₁ - a₁‖ ≤ ε) (hc₂ : ‖c₂ - a₂‖ ≤ ε) (hε1 : ε ≤ 1) (h₁ : ‖a₁‖ ≤ 1)
    (hε : ε < ‖a₁ * a₂‖) : ε < ‖c₁ * c₂‖ := by
  have hc2 : ‖c₂‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (c₂ - a₂) a₂
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hc₂.trans hε1) h₂)
  have e : c₁ * c₂ - a₁ * a₂ = (c₁ - a₁) * c₂ + a₁ * (c₂ - a₂) := by ring
  have hd : ‖c₁ * c₂ - a₁ * a₂‖ ≤ ε := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_mul hc₁ hc2 (norm_nonneg _) ((norm_nonneg _).trans hc₁)).trans_eq (mul_one ε)
    · rw [norm_mul]
      exact (mul_le_mul h₁ hc₂ (norm_nonneg _) zero_le_one).trans_eq (one_mul ε)
  have := IsUltrametricDist.norm_add_le_max (a₁ * a₂ - c₁ * c₂) (c₁ * c₂)
  rw [sub_add_cancel, norm_sub_rev] at this
  rcases le_max_iff.1 this with h | h
  · exact absurd (hε.trans_le h) (not_lt.2 hd)
  · exact hε.trans_le h

theorem exists_large_minors : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      (p : ℝ)⁻¹ ^ n < ‖((((discr E : ℤ) : ℂ_[p]) ^ 2 * (p : ℂ_[p]) ^ 2) ^ (Dw.mult τ.1 + Dw.mult (conjEmb τ.1)))‖ →
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∃ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) := by
  intro hKer hTate hVal hBound E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat _ f yb yy P π ψ y
    hHT hn β hβ g e U₁ U₂ h hTan hE₁ hE₂ hApp
  obtain ⟨ta, w₁, w₂, σ, hta, hw₁, hw₂, hG₁, hG₂⟩ :=
    GlobalTheory.T.integral_model_level_p_power_frame hKer hTate hVal E H Dw τ p hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLat yb yy P π ψ y
      hHT β hβ
  obtain ⟨x, hx, hM⟩ := GlobalTheory.T.integral_model_map_over_inclusion E H Dw p l l' Xo Xo' c c' W Y r ν hle hov yb yy P π ψ y hHT β hβ g e hTan
  have hCB : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.CokernelBound P := (hKer p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.1
  set d : ℂ_[p] := ((discr E : ℤ) : ℂ_[p]) with hd
  have hnorm : ∀ z : 𝓞_ℂ_[p], ‖(z : ℂ_[p])‖ ≤ 1 := fun z => (GlobalTheory.PadicComplexHost.mem_iff_norm p _).1 z.2
  have hd0 : d ^ 2 * (p : ℂ_[p]) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)))
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero))
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))

  have key : ∀ (σ' : E →+* ℂ) (U : Fin g → Fin g → 𝓞_ℂ_[p]), EigAt Y.t yb (β.comp (embV c' W σ')) e U →
      ∀ w : P.V, w ∈ htLat c P σ' → w ∈ Submodule.span ℂ_[p] (Set.range P.bLie) →
        w ∈ P.eigV (embInt c P.integers σ') → ∃ M : Fin g → 𝓞_ℂ_[p],
          (d ^ 2 * (p : ℂ_[p]) ^ 2) • w = ∑ k, (M k : ℂ_[p]) • ∑ b, (U k b : ℂ_[p]) • P.bLie (x b) := by
    intro σ' U hU w h1 h2 h3
    obtain ⟨x', hx'e, hx'⟩ := hBound E H l c p P hCB σ' w h1 h2 h3
    obtain ⟨M, hM'⟩ := hM σ' U hU x' hx'e
    refine ⟨M, ?_⟩
    rw [← hM', hx', smul_smul]
    congr 1
    ring
  choose M₁ hM₁ using fun i => key τ.1 U₁ hE₁ (w₁ i) (hw₁ i).1 (hw₁ i).2.1 (hw₁ i).2.2
  choose M₂ hM₂ using fun i => key (conjEmb τ.1) U₂ hE₂ (w₂ i) (hw₂ i).1 (hw₂ i).2.1 (hw₂ i).2.2
  have hcong : ∀ (U : Fin g → 𝓞_ℂ_[p]) (Tc : Ind Dw τ.1 → Fin N → 𝓞_ℂ_[p]) (i : Ind Dw τ.1),
      ‖(((∑ b, (∑ a, Tc i a * h a b) * U b : 𝓞_ℂ_[p]) : ℂ_[p]) -
        P.pairV (∑ b, (U b : ℂ_[p]) • P.bLie (x b)) (∑ m, (Tc i m : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))‖ ≤ (p : ℝ)⁻¹ ^ n :=
    fun U Tc i => GlobalTheory.T.p_adic_pairing_approximation E p P n N g ta x h Tc U (fun m b => hApp m (ta m) (hta m) b (x b) (hx b)) i
  have hpair : ∀ (M : Fin g → 𝓞_ℂ_[p]) (X : Fin g → P.V) (t : P.V),
      P.pairV (∑ k, (M k : ℂ_[p]) • X k) t = ∑ k, (M k : ℂ_[p]) * P.pairV (X k) t := by
    intro M X t
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨K₁, hK₁, hK₁', hK₁''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult τ.1) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₁ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (T (σ (Sum.inl j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₁ k) (∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₁ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₁ k) (fun i a => β (T i a)) (σ (Sum.inl j))) (fun i k => hnorm _) hG₁
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₁ i, hpair])
  obtain ⟨K₂, hK₂, hK₂', hK₂''⟩ := GlobalTheory.T.exists_minor_norm_det_bounds_and_det_sub_le p n (Dw.mult (conjEmb τ.1)) g (d ^ 2 * (p : ℂ_[p]) ^ 2)
    (fun k j => P.pairV (∑ b, (U₂ k b : ℂ_[p]) • P.bLie (x b))
      (∑ m, ((β (S (σ (Sum.inr j)) m) : 𝓞_ℂ_[p]) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ k b : 𝓞_ℂ_[p]) : ℂ_[p]))
    (Matrix.of fun k k' => P.pairV (w₂ k) (∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m))
    (fun i k => (M₂ i k : ℂ_[p])) hd0 (fun k j => hnorm _)
    (fun k j => hcong (U₂ k) (fun i a => β (S i a)) (σ (Sum.inr j))) (fun i k => hnorm _) hG₂
    (fun i j => by
      rw [Matrix.of_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, hM₂ i, hpair])
  refine ⟨σ, K₁, K₂, ?_⟩
  have e₁ : ((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β T h (σ ∘ Sum.inl) j b * U₁ (K₁ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  have e₂ : ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (Matrix.of fun k j => ((∑ b, covec β S h (σ ∘ Sum.inr) j b * U₂ (K₂ k) b : 𝓞_ℂ_[p]) : ℂ_[p])).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (Matrix.det _) = _
    rw [RingHom.map_det]
    rfl
  change (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) *
    ((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖
  rw [e₁, e₂]
  refine lt_norm_mul_of_close hK₂' hK₁'' hK₂'' hε1 hK₁' (hn.trans_le ?_)
  rw [pow_add, norm_mul, norm_pow, norm_pow]
  exact (mul_le_mul hK₁ hK₂ (by positivity) (norm_nonneg _)).trans_eq (norm_mul _ _).symm

end GlobalTheory.FlatModel
