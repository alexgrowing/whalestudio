import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointFrameMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointCompleteFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicOverInclusionStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace GlobalTheory.FlatModel

theorem norm_int_le_one {p : ℕ} [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  rw [← coe_valued]
  exact_mod_cast (Valuation.mem_valuationSubring_iff _ _).1 x.2

theorem norm_eq_of_norm_sub_lt {p : ℕ} [Fact p.Prime] {X A : ℂ_[p]} (h : ‖X - A‖ < ‖X‖) : ‖A‖ = ‖X‖ := by
  have h1 : ‖A‖ ≤ max ‖X‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max X (-(X - A))
    rwa [norm_neg, show X + -(X - A) = A by ring] at this
  have h2 : ‖X‖ ≤ max ‖A‖ ‖X - A‖ := by
    have := IsUltrametricDist.norm_add_le_max A (X - A)
    simpa using this
  rcases le_max_iff.1 h2 with h2 | h2
  · exact le_antisymm (h1.trans (max_le le_rfl h.le)) h2
  · exact absurd h (not_lt.2 h2)

theorem norm_quot_sub_lt {p : ℕ} [Fact p.Prime] (n : ℕ) (x y : 𝓞_ℂ_[p]) (A B κ q : ℂ_[p])
    (hbig : (p : ℝ)⁻¹ ^ n < ‖((x * y : 𝓞_ℂ_[p]) : ℂ_[p])‖)
    (hA : ‖(x : ℂ_[p]) - A‖ ≤ (p : ℝ)⁻¹ ^ n) (hB : ‖(y : ℂ_[p]) - B‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hq : q * A = κ * B) (hκ : κ ≠ 0) :
    ‖q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ‖ < ‖κ‖ := by
  have hX1 := norm_int_le_one x
  have hY1 := norm_int_le_one y
  have hbig' : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ * ‖(y : ℂ_[p])‖ := by
    rw [← norm_mul]; exact_mod_cast hbig
  have hXb : (p : ℝ)⁻¹ ^ n < ‖(x : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_right (norm_nonneg _) hY1)
  have hYb : (p : ℝ)⁻¹ ^ n < ‖(y : ℂ_[p])‖ :=
    hbig'.trans_le (mul_le_of_le_one_left (norm_nonneg _) hX1)
  have hXA : ‖(x : ℂ_[p]) - A‖ < ‖(x : ℂ_[p])‖ := hA.trans_lt hXb
  have hYB : ‖(y : ℂ_[p]) - B‖ < ‖(y : ℂ_[p])‖ := hB.trans_lt hYb
  have nA := norm_eq_of_norm_sub_lt hXA
  have nB := norm_eq_of_norm_sub_lt hYB
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ ^ n := by
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  have hA0 : A ≠ 0 := fun h0 => by rw [h0, norm_zero] at nA; linarith
  have hB0 : B ≠ 0 := fun h0 => by rw [h0, norm_zero] at nB; linarith
  have hY0 : (y : ℂ_[p]) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hYb; linarith
  have hq' : q = κ * B / A := by rw [eq_div_iff hA0, hq]
  have key : q * (x : ℂ_[p]) / (y : ℂ_[p]) - κ =
      κ * ((((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)) / (A * (y : ℂ_[p]))) := by
    rw [hq']; field_simp; ring
  rw [key, norm_mul]
  have hk : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  refine mul_lt_of_lt_one_right hk ?_
  have hden : 0 < ‖A * (y : ℂ_[p])‖ := norm_pos_iff.2 (mul_ne_zero hA0 hY0)
  rw [norm_div, div_lt_one hden]
  have e1 : ‖((x : ℂ_[p]) - A) * B‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul, nA, nB]
    exact mul_lt_mul_of_pos_right hXA (by linarith)
  have e2 : ‖A * ((y : ℂ_[p]) - B)‖ < ‖A * (y : ℂ_[p])‖ := by
    rw [norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hYB (by rw [nA]; linarith)
  calc ‖((x : ℂ_[p]) - A) * B - A * ((y : ℂ_[p]) - B)‖
      ≤ max ‖((x : ℂ_[p]) - A) * B‖ ‖A * ((y : ℂ_[p]) - B)‖ := by
        have := IsUltrametricDist.norm_add_le_max (((x : ℂ_[p]) - A) * B) (-(A * ((y : ℂ_[p]) - B)))
        rwa [norm_neg, ← sub_eq_add_neg] at this
    _ < ‖A * (y : ℂ_[p])‖ := max_lt e1 e2

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem norm_minor_sub_le {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : PtP E p)
    (n : ℕ) {V J : Type} [CommRing V] (β : V →+* 𝓞_ℂ_[p]) {N g m : ℕ} (T : J → Fin N → V)
    (h : Fin N → Fin g → 𝓞_ℂ_[p]) (ta : Fin N → P.T) (xb : Fin g → LieG P.Gt)
    (hh : ∀ a b, h a b - (P.al₀ (ta a)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n})
    (I : Fin m → J) (U : Fin m → Fin g → 𝓞_ℂ_[p]) :
    ‖((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) -
      (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  classical
  set Mex : Matrix (Fin m) (Fin m) 𝓞_ℂ_[p] :=
    Matrix.of fun k k' => ∑ b, (∑ a, β (T (I k') a) * (P.al₀ (ta a)).1 (xb b)) * U k b with hMex
  have h1 : pairDet (covec β T h I) U - Mex.det ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := by
    rw [← Ideal.Quotient.eq, pairDet, RingHom.map_det, RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, covec]
    rw [Ideal.Quotient.eq, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun b _ => ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
    refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun a _ => ?_)
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (hh a b)
  have e : ∀ (x : LieG P.Gt) (c : ℂ_[p]) (t : P.T),
      P.pairV (P.bLie x) (c ⊗ₜ[ℤ_[p]] t) = c * algebraMap 𝓞_ℂ_[p] ℂ_[p] ((P.al₀ t).1 x) := fun x c t => by
    rw [show (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : ℂ_[p]) ⊗ₜ[ℤ_[p]] t) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one], map_smul, P.pairV_bLie, smul_eq_mul]
  have h2 : ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) = (Matrix.of fun k k' => P.pairV (∑ b, (U k b : ℂ_[p]) • P.bLie (xb b))
        (∑ a, (β (T (I k') a) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta a)).det := by
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] Mex.det = _
    rw [RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hMex, map_sum, map_mul, map_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, e, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    change ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p])) * (U k b : ℂ_[p]) =
      (U k b : ℂ_[p]) * ((β (T (I k') a) : ℂ_[p]) * ((P.al₀ (ta a)).1 (xb b) : ℂ_[p]))
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
  rw [← h2]
  have h3 : ((pairDet (covec β T h I) U : 𝓞_ℂ_[p]) : ℂ_[p]) - ((Mex.det : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (c : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
    have := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hc
    rw [map_mul, map_pow, map_natCast, map_sub] at this
    exact this.symm
  rw [h3, norm_mul, norm_pow, GlobalTheory.PadicComplexHost.norm_p]
  exact mul_le_of_le_one_left (by positivity) (norm_int_le_one c)

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem kap_close : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → TateSt → ValueSt → BoundSt →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (τ : Psi H) (p : ℕ) [Fact p.Prime]
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ n : ℕ,
    ∀ (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle → l'.A = p ^ n →
    ∀ (N : ℕ) (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W), LatData Dw (embV c' W (conjEmb τ.1)) a T S →
    ∀ [Algebra c.F ℂ_[p]] (f : Rul Xo c) (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
      (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]), HTAt Y r ν yb yy P π ψ y →
      evR Xo c f y ≠ 0 → ∃ κ : ℂ_[p], ‖κ‖ = ‖evR Xo c f y‖ ∧
      ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
      ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
        (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ.1)) e U₁ →
        EigAt Y.t yb (β.comp (embV c' W (conjEmb τ.1))) e U₂ → HTApprox Y n yy P π ψ a e h →
        ∀ (σ : Equiv.Perm (Ind Dw τ.1)) (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g),
          ((p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) →
          ∀ fv : ℂ_[p], GVal Y r ν τ.1 f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
            (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
          ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
            (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖ := by
  classical
  intro hK hT hV _ E _ _ _ H Dw τ p _ _ hs n l l' Xo Xo' c c' W Y r ν hle hov hA N a T S hLD _ f yb yy P π ψ y hHT hev
  have inj : ∀ {A B : Type} [CommRing A] [CommRing B] (f f' : A →+* B), spMap f = spMap f' → f = f' := by
    intro A B _ _ f f' h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : c'.V W →+* 𝓞_ℂ_[p], yb ≫ Y.s = spMap β₀ :=
    ⟨(Spec.preimage (yb ≫ Y.s)).hom, by simp [spMap]⟩
  have hHT' := hHT
  obtain ⟨hPt, hTe, hF, z, gm, am, x, hFC, -, -, htie, hlat⟩ := hHT'
  obtain ⟨ta, u0, hlev, hDF⟩ :=
    hT E H Dw l' Xo' c' W Y p n hs hA yb yy P π ψ hPt β₀ (conjEmb τ.1) (Ind Dw τ.1) N a T S hLD
  rw [GlobalTheory.T.integral_model_p_adic_comparison E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT β₀ hβ₀] at hDF
  have heig : ∀ σ j, AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) (x σ j) := fun σ j =>
    GlobalTheory.T.p_adic_point_complete_field E H Dw l l' Xo Xo' c c' W Y r ν p yb yy P π ψ hPt σ (x σ j) (z.u σ j) (htie σ j) (z.eig σ j)
  have hmemE : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.eigV (embInt c P.integers σ) := fun σ k =>
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bLie_mem_eigV (heig σ j))
  have hKS := (hK p ℂ_[p] _ 𝓞_ℂ_[p] (𝓞 E) P).2.2.2
  have hmemW : ∀ σ k, ∑ j, gm σ k j • P.bLie (x σ j) ∈ P.W := fun σ k => by
    rw [hKS.2.2.2.2.2.2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  set w₁ : Fin (Dw.mult τ.1) → P.V := fun k => ∑ j, gm τ.1 k j • P.bLie (x τ.1 j) with hw₁
  set w₂ : Fin (Dw.mult (conjEmb τ.1)) → P.V := fun k => ∑ j, gm (conjEmb τ.1) k j • P.bLie (x (conjEmb τ.1) j)
    with hw₂
  have horth : ∀ k k', P.pairV (w₁ k) (w₂ k') = 0 := fun k k' =>
    (hKS.2.2.2.2.1 _).1 (hmemW _ k) _ (hmemW _ k')
  obtain ⟨lam, hlam, hlamσ, -⟩ :=
    hV E H Dw l c p hs P τ _ _ u0 hDF w₁ w₂ (hmemE _) (hmemE _) horth (hlat _) (hlat _)
  refine ⟨lam * evR Xo c f y, by rw [norm_mul, hlam, _root_.one_mul], ?_⟩
  intro β hβ g e U₁ U₂ h htb hE1 hE2 happ σ K₁ K₂ hbig fv hGV
  have hββ : β = β₀ := inj _ _ (hβ.symm.trans hβ₀)
  subst hββ
  choose xb hxb using fun b => GlobalTheory.T.p_adic_point_frame_map E H Dw l' Xo' c' W Y p yb yy P π ψ hPt (e b) (htb.1 b)
  have hh : ∀ m b, h m b - (P.al₀ (ta m)).1 (xb b) ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n} := fun m b =>
    happ m (ta m) (hlev m) b (xb b) (hxb b)
  have G1 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb τ.1 (U₁ (K₁ k)) (fun u hu => hE1.1 (K₁ k) u hu)
  have G2 := fun k => GlobalTheory.T.integral_model_p_adic_over_inclusion E H Dw l l' Xo Xo' c c' W Y r ν hle hov p yb yy P π ψ y hHT z gm am x hFC
    htie β hβ g e htb xb hxb (conjEmb τ.1) (U₂ (K₂ k)) (fun u hu => hE2.1 (K₂ k) u hu)
  choose v₁ cf₁ hv₁ hcf₁ hid₁ using G1
  choose v₂ cf₂ hv₂ hcf₂ hid₂ using G2
  have hfv := hGV y hTe hF v₁ v₂ (Matrix.of cf₁) (Matrix.of cf₂) hv₁ hv₂ hcf₁ hcf₂
  have fac : ∀ {m : ℕ} (cf : Fin m → Fin m → ℂ_[p]) (w : Fin m → P.V) (tt : Fin m → P.V)
      (L : Fin m → Fin g → 𝓞_ℂ_[p]), (∀ k, ∑ b, (L k b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf k j • w j) →
      (Matrix.of fun k k' => P.pairV (∑ b, (L k b : ℂ_[p]) • P.bLie (xb b)) (tt k')).det =
        (Matrix.of cf).det * (Matrix.of fun k k' => P.pairV (w k) (tt k')).det := by
    intro m cf w tt L hL
    rw [← Matrix.det_mul]
    congr 1
    ext k k'
    simp only [Matrix.of_apply, Matrix.mul_apply, hL, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  set M₁ := (Matrix.of fun k k' => P.pairV (w₁ k)
    ((fun i => ∑ m, (β (T i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inl k')))).det with hM₁
  set M₂ := (Matrix.of fun k k' => P.pairV (w₂ k)
    ((fun i => ∑ m, (β (S i m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (σ (Sum.inr k')))).det with hM₂
  have hl : ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁ = lam * M₂ := hlamσ σ
  have hA₁ : ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₁).det * M₁‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₁ w₁ (fun k' => ∑ m, (β (T (σ (Sum.inl k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₁ ∘ K₁) hid₁).symm).trans_le
      (norm_minor_sub_le P n β T h ta xb hh (σ ∘ Sum.inl) (U₁ ∘ K₁))
  have hB₁ : ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - (Matrix.of cf₂).det * M₂‖ ≤
      (p : ℝ)⁻¹ ^ n :=
    (congrArg (fun d => ‖((pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p]) - d‖)
      (fac cf₂ w₂ (fun k' => ∑ m, (β (S (σ (Sum.inr k')) m) : ℂ_[p]) ⊗ₜ[ℤ_[p]] ta m) (U₂ ∘ K₂) hid₂).symm).trans_le
      (norm_minor_sub_le P n β S h ta xb hh (σ ∘ Sum.inr) (U₂ ∘ K₂))
  have hlam0 : lam ≠ 0 := fun h0 => by rw [h0, norm_zero] at hlam; exact zero_ne_one hlam
  refine norm_quot_sub_lt n _ _ _ _ _ _ hbig hA₁ hB₁ ?_ (mul_ne_zero hlam0 hev)
  linear_combination (((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * M₁) * hfv + ((Matrix.of cf₂).det * evR Xo c f y) * hl

end GlobalTheory.FlatModel
