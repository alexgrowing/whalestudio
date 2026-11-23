import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LineDefect

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

section Alg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_aeval_int {σ R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') (a : σ → R)
    (s : MvPolynomial σ ℤ) : ψ (aeval a s) = aeval (fun p => ψ (a p)) s := by
  have := MvPolynomial.comp_aeval_apply (R := ℤ) a ψ.toIntAlgHom s
  simpa using this

theorem aeval_eq_eval₂ {σ R : Type} [CommRing R] [Algebra ℤ R] (a : σ → R) (s : MvPolynomial σ ℤ) :
    aeval a s = eval₂ (Int.castRingHom R) a s := by
  rw [aeval_def]
  congr 1
  exact Subsingleton.elim _ _

theorem prod_cross {F : Type} [Field F] (x : K → F) (hx : ∀ k, x k ≠ 0) {a b : K → ℤ} {α γ : K → ℕ}
    (hd : ∀ k, (α k : ℤ) - γ k = a k - b k) :
    (∏ k, x k ^ a k) * ∏ k, x k ^ γ k = (∏ k, x k ^ b k) * ∏ k, x k ^ α k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hx k), ← zpow_add₀ (hx k)]
  congr 1
  linarith [hd k]

variable {Ω : Type} [Field Ω]

theorem cone_of_form {R : Type} [CommRing R] (b : (Σ k, ι k) → R) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) :
    aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K R) * MvPolynomial.C (b p)) s =
      (∏ k, MvPolynomial.X k ^ d k) * MvPolynomial.C (aeval b s) := by
  have h := aeval_blockScale hs (fun k => (MvPolynomial.X k : MvPolynomial K R)) fun p => MvPolynomial.C (b p)
  rw [map_aeval_int MvPolynomial.C b s]
  simp only [aeval_eq_eval₂] at h ⊢
  exact h

theorem aeval_ne_zero_of_form {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (h : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  refine h ?_
  change mConeMap y s = 0
  have e : mConeMap y s = aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p)) s := by
    simp only [mConeMap, mul_comm]
  rw [e, cone_of_form y hs, h0, map_zero, mul_zero]

variable (S : Subring Ω) (φ : S →+* ℂ) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : (Σ k, ι k) → ℂ)
  (r : (Σ k, ι k) → S)

def coneS : MRing ι →ₐ[ℤ] MvPolynomial K S :=
  aeval fun p => MvPolynomial.X p.1 * MvPolynomial.C (r p)

def evS : MvPolynomial K S →+* ℂ := eval₂Hom φ fun k => w ⟨k, c k⟩

variable {S φ y c w r}

theorem coneS_eq_zero (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p) {s : MRing ι}
    (hs : s ∈ mCoordIdeal y) : coneS S r s = 0 := by
  have hJ : Function.Injective (MvPolynomial.map (σ := K) S.subtype) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  refine hJ ?_
  rw [map_zero]
  let Res : MvPolynomial K Ω →+* MvPolynomial K Ω :=
    eval₂Hom MvPolynomial.C fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * MvPolynomial.X k
  have e : (MvPolynomial.map (σ := K) S.subtype).comp (coneS S r).toRingHom = Res.comp (mConeMap y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    have h1 : ((r p : S) : Ω) = y p * (y ⟨p.1, c p.1⟩)⁻¹ := by
      rw [← hr p, mul_inv_cancel_right₀ (hy p.1)]
    simp [coneS, mConeMap, Res, h1]
    ring
  have h0 : mConeMap y s = 0 := hs
  have := RingHom.congr_fun e s
  simpa [h0] using this

theorem evS_coneS (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) (s : MRing ι) :
    evS S φ c w (coneS S r s) = evC w s := by
  have e : (evS S φ c w).comp (coneS S r).toRingHom =
      (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    simp [coneS, evS, hw p]
  exact RingHom.congr_fun e s

theorem core (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p)
    (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) {f g u v : MRing ι} {α γ : K → ℕ} (hf : IsMultiHomog f α)
    (hg : IsMultiHomog g γ) (hG : aeval r g ≠ 0) (huv : u * f - v * g ∈ mCoordIdeal y) {s₁ s₂ : S}
    (hs : s₂ * aeval r f = s₁ * aeval r g) :
    evC w u * φ s₁ * ∏ k, w ⟨k, c k⟩ ^ α k = evC w v * φ s₂ * ∏ k, w ⟨k, c k⟩ ^ γ k := by
  have h0 := coneS_eq_zero hy hr huv
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  have hcf : coneS S r f = (∏ k, MvPolynomial.X k ^ α k) * MvPolynomial.C (aeval r f) := cone_of_form r hf
  have hcg : coneS S r g = (∏ k, MvPolynomial.X k ^ γ k) * MvPolynomial.C (aeval r g) := cone_of_form r hg
  have hCG : (MvPolynomial.C (aeval r g) : MvPolynomial K S) ≠ 0 := by
    exact (map_ne_zero_iff (MvPolynomial.C : S →+* MvPolynomial K S) (MvPolynomial.C_injective K S)).2 hG
  have hcs : (MvPolynomial.C s₂ : MvPolynomial K S) * MvPolynomial.C (aeval r f) =
      MvPolynomial.C s₁ * MvPolynomial.C (aeval r g) := by
    rw [← map_mul, ← map_mul, hs]
  have key : coneS S r u * MvPolynomial.C s₁ * (∏ k, MvPolynomial.X k ^ α k) =
      coneS S r v * MvPolynomial.C s₂ * ∏ k, MvPolynomial.X k ^ γ k := by
    refine mul_left_cancel₀ hCG ?_
    rw [hcf, hcg] at h0
    linear_combination (MvPolynomial.C s₂) * h0 - (coneS S r u * ∏ k, MvPolynomial.X k ^ α k) * hcs
  have := congrArg (evS S φ c w) key
  rw [map_mul, map_mul, map_mul, map_mul, evS_coneS hw, evS_coneS hw] at this
  simpa [evS, map_prod] using this

end Alg

theorem norm_mul_h_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A B : HermLine ι) (e₀ ρ t : Ω) (f g u v : MRing ι) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, ι k) → ℂ) (ν : ℝ), IsCptGen ξ → CoordsAt ξ y z w → e₀ ≠ 0 → IsLineIso (mCoordIdeal y) A.a B.a f g → aeval y f = ρ * aeval y g → SecNorm ξ y A e₀ z w t ν → SecNorm ξ y B (ρ * e₀) z w t ν → 0 < ν → u * f - v * g ∈ mCoordIdeal y → evC w u ≠ 0 → ‖evC w v‖ * B.h w = ‖evC w u‖ * A.h w := by
  intro X Ω _ ξ K _ ι _ y A B e₀ ρ t f g u v z w ν hξ hw he hiso hρ hA hB hν huv _
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, -⟩ := hiso
  obtain ⟨c, hc⟩ := hA.exists_chart
  have hz := hA.specializes
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z hz hξ
  obtain ⟨a₁, ha₁, e₁⟩ := hA.2.2 c hc
  obtain ⟨a₂, ha₂, e₂⟩ := hB.2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  choose q hq hq' using fun p : Σ k, ι k => (hw.2 p.1 (c p.1) (IsUnit.mk0 _ (hc p.1))).2 p.2
  choose m hm using fun p => (hφ _ _).1 (hq p)
  obtain ⟨m₁, hm₁⟩ := (hφ _ _).1 ha₁
  obtain ⟨m₂, hm₂⟩ := (hφ _ _).1 ha₂
  set r : (Σ k, ι k) → regAt ξ ⟨centre z, hz⟩ := fun p => ⟨_, m p⟩ with hrdef
  have hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p := fun p => div_mul_cancel₀ _ (hy p.1)
  have hwr : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p := fun p => by
    rw [hm p, mul_comm]
    exact (hq' p).symm
  have hyf : aeval y f ≠ 0 := aeval_ne_zero_of_form hf hfP
  have hyg : aeval y g ≠ 0 := aeval_ne_zero_of_form hg hgP
  have hρ0 : ρ ≠ 0 := fun h => hyf (by rw [hρ, h, zero_mul])
  have hscale : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * (aeval r s : regAt ξ ⟨centre z, hz⟩) := by
    intro s d hs
    have h1 := aeval_blockScale hs (fun k => y ⟨k, c k⟩) fun p => (r p : Ω)
    have e : (fun p : Σ k, ι k => y ⟨p.1, c p.1⟩ * (r p : Ω)) = y :=
      funext fun p => (mul_comm _ _).trans (hr p)
    rw [e] at h1
    rw [h1]
    congr 1
    exact (map_aeval_int (regAt ξ ⟨centre z, hz⟩).subtype r s).symm
  have hF := hscale hf
  have hG := hscale hg
  have hQα : (∏ k, y ⟨k, c k⟩ ^ α k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hQγ : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hPA : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hPB : (∏ k, y ⟨k, c k⟩ ^ B.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hP := prod_cross (fun k => y ⟨k, c k⟩) hy hd
  have hGne : aeval r g ≠ 0 := fun h => hyg (by rw [hG, h]; simp)
  have hs : (⟨_, m₂⟩ : regAt ξ ⟨centre z, hz⟩) * aeval r f = ⟨_, m₁⟩ * aeval r g := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul]
    change t / ((∏ k, y ⟨k, c k⟩ ^ B.a k) * (ρ * e₀)) * _ = t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) * _
    have hFG := hρ
    rw [hF, hG] at hFG
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hPB (mul_ne_zero hρ0 he))
      (mul_ne_zero hPA he)]
    have key : ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ A.a k) =
        ((aeval r g : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ B.a k) * ρ :=
      mul_right_cancel₀ hQγ (by
        linear_combination ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * hP + (∏ k, y ⟨k, c k⟩ ^ B.a k) * hFG)
    linear_combination (t * e₀) * key
  have hcore := core (φ := φ) hy hr hwr hf hg hGne huv hs
  rw [hm₁, hm₂] at hcore
  have hn := congrArg norm hcore
  simp only [norm_mul, norm_prod, norm_pow] at hn
  have hNγ : (∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hN := prod_cross (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)) hd
  refine mul_right_cancel₀ hNγ (mul_left_cancel₀ hν.ne' ?_)
  linear_combination (‖evC w v‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₂ - (‖evC w u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₁ -
    (∏ k, ‖w ⟨k, c k⟩‖ ^ B.a k) * hn - (‖evC w u‖ * ‖a₁‖) * hN

end GlobalTheory.CompanionTheory.Ar.LineDefect
