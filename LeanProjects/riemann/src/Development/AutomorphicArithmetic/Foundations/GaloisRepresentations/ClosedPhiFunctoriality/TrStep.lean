import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem core {Z R B : Type} [CommRing Z] [CommRing R] [CommRing B] (f : R →+* B) (zc : Z →+* R) (zb : Z →+* B)
    (hz : ∀ x, f (zc x) = zb x) (n a s g : R) (nZ : Z) (hn : zc nZ = n) {d d' : ℕ}
    (V : Matrix (Fin d) (Fin d) R) (V' : Matrix (Fin d') (Fin d') R) (Pm : Matrix (Fin d) (Fin d') Z)
    (e : Fin d → Z) (e' : Fin d' → Z) (h3 : ∀ i j, n ∣ (V * Pm.map zc - Pm.map zc * V') i j)
    (h4 : ∀ i, nZ ∣ (Pm *ᵥ e' - e) i) (ui : Fin d → B) (vj : Fin d' → B) (w : B) (ai : Fin d → R) (bj : Fin d' → R)
    (ha : ∀ i, f (ai i) = f a * ui i) (hv : ∀ j, vj j = f n * f (bj j)) (hw : w = f n * f g) :
    ∃ Y : R, f a * (∑ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i * ui i +
      ∑ j, (V'.map f *ᵥ fun i => zb (e' i)) j * vj j - f s * w) = f (n * Y) := by
  choose W hW using h3
  choose r hr using h4
  have hPb : Pm.map zb = (Pm.map zc).map f := by
    ext i j; simp [hz]
  have hE : (fun j => zb (e' j)) = f ∘ (fun j => zc (e' j)) := by
    ext j; simp [hz]
  have hD : V * Pm.map zc - Pm.map zc * V' = n • Matrix.of W := by
    ext i j; simp [hW]
  have hM : V.map f * Pm.map zb - Pm.map zb * V'.map f = (n • Matrix.of W).map f := by
    rw [← hD, hPb, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul]
  have hq : (fun i => zb ((Pm *ᵥ e' - e) i)) = f ∘ (fun i => n * zc (r i)) := by
    ext i; simp only [Function.comp, hr i, map_mul, hz, ← hn]
  have h1 : ∀ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i =
      f n * f ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) := by
    intro i
    rw [hM, hE, hq, Pi.sub_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_mul, ← map_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ j, (V'.map f *ᵥ fun i => zb (e' i)) j = f ((V' *ᵥ fun i => zc (e' i)) j) := by
    intro j; rw [hE, ← RingHom.map_mulVec]
  refine ⟨∑ i, ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) * ai i +
    ∑ j, a * (V' *ᵥ fun i => zc (e' i)) j * bj j - a * s * g, ?_⟩
  simp only [h1, h2, hv, hw, map_mul, map_add, map_sub, map_sum, ha, Finset.mul_sum, mul_add, mul_sub]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

variable {l : ℕ} [Fact l.Prime]

private theorem u_alg {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l]) :
    uB T (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  show T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact T.zB z

private theorem iB_zC (z : ℤ_[l]) : iB l (zC l z) = Per.zB l z := rfl

private theorem exists_iB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (c : ↥(MaximalUnramifiedExtension l))
    (hc : ‖(c : Om l)‖ ≤ 1) : ∃ y : Per.Acris l, iB l y = uB T c := by
  obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T (adjExt (c : Om l)) ⟨c, mem_adjExt _, c.2⟩ hc
  refine ⟨iA l w, ?_⟩
  have h : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := hw
  show _ = T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c)
  rw [← h, T.ιA]
  rfl

private theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1

private theorem scale {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l)) (n : ℕ) (y : Om l) :
    uB T (lam ((n : Om l) * y)) = (n : Per.Bcris l) * uB T (lam y) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trStep_holds :
    Func → TrId → TrStep := by
  intro hF hI l _ P AI T s d d' m M c₁ c₂ t t' c pv p θ Pi e e' V V' h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := norm_l
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (l : Om l) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact (inv_pos.2 hlpos).ne hn
  have hlK : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg (fun x : ↥(MaximalUnramifiedExtension l) => (x : Om l)) h0
    simpa using this
  have hsmall : ∀ y : Om l, ‖y‖ ≤ ((l : ℝ) ^ M)⁻¹ → ‖y / (l : Om l) ^ M‖ ≤ 1 := by
    intro y hy
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ (by simpa using hy) (by positivity) |>.trans le_rfl
  let δ : Fin d' → Om l := fun j => ∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k
  let η : Om l := θ - ∑ k, c k * pv k
  let x : Fin d ⊕ Fin d' ⊕ Unit → Om l := Sum.elim (fun i => (l : Om l) ^ c₁ * t i)
    (Sum.elim (fun j => δ j / (l : Om l) ^ M) (fun _ => η / (l : Om l) ^ M))
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro (i | j | _)
    · exact h7 i
    · exact hsmall _ (h5 j)
    · exact hsmall _ h6
  obtain ⟨lam, hl1, hl2, hl3⟩ := hF l (MaximalUnramifiedExtension l) (Fin d ⊕ Fin d' ⊕ Unit) x ((l : Om l) ^ c₁ * (p - θ)) hx h8
  have hid := hI l (Per.Bcris l) (uB T) (Per.zB l) (u_alg T) (iB l s) d d' m t t' c pv p θ Pi e e'
    (V.map (iB l)) (V'.map (iB l)) h1 h2 lam
  choose ai hai using fun i => exists_iB T (lam (x (Sum.inl i))) (hl1 _)
  choose bj hbj using fun j => exists_iB T (lam (x (Sum.inr (Sum.inl j)))) (hl1 _)
  obtain ⟨g, hg⟩ := exists_iB T (lam (x (Sum.inr (Sum.inr ())))) (hl1 _)
  have hpow : ∀ (k : ℕ) (y : Om l), uB T (lam ((l : Om l) ^ k * y)) = (l : Per.Bcris l) ^ k * uB T (lam y) := by
    intro k y
    have := scale T lam (l ^ k) y
    push_cast at this
    exact this
  have hdiv : ∀ y : Om l, uB T (lam y) = (l : Per.Bcris l) ^ M * uB T (lam (y / (l : Om l) ^ M)) := by
    intro y
    rw [← hpow, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨Y, hY⟩ := core (iB l) (zC l) (Per.zB l) iB_zC ((l : Per.Acris l) ^ M) ((l : Per.Acris l) ^ c₁) s g
    ((l : ℤ_[l]) ^ M) (by simp) V V' Pi e e' h3 h4
    (fun i => uB T (lam (t i))) (fun j => uB T (lam (δ j))) (uB T (lam η)) ai bj
    (fun i => by
      rw [hai i]
      simp only [map_pow, map_natCast]
      exact hpow c₁ (t i))
    (fun j => by
      rw [hbj j]
      simp only [map_pow, map_natCast]
      exact hdiv (δ j))
    (by
      rw [hg]
      simp only [map_pow, map_natCast]
      exact hdiv η)
  rw [← hid] at hY
  set q : ↥(MaximalUnramifiedExtension l) := lam ((l : Om l) ^ c₁ * (p - θ)) with hq
  have huq : uB T q = (l : Per.Bcris l) ^ c₁ * uB T (lam (p - θ)) := hpow c₁ (p - θ)
  have hqn : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(q : Om l)‖ := h9.trans hl2
  have hq0 : q ≠ 0 := by
    intro h0
    have h00 : (0 : ℝ) < ((l : ℝ) ^ c₂)⁻¹ := by positivity
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hqn
    exact absurd hqn (not_le.2 h00)
  have hq' : ‖(((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ hqn (norm_nonneg _)
  obtain ⟨y', hy'⟩ := exists_iB T _ hq'
  refine ⟨Y * y', GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l ?_⟩
  have hqq : q * ((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q) = (l : ↥(MaximalUnramifiedExtension l)) ^ c₂ := mul_div_cancel₀ _ hq0
  have hu : uB T q * iB l y' = (l : Per.Bcris l) ^ c₂ := by
    rw [hy', ← map_mul, hqq, map_pow, map_natCast]
  show iB l _ = iB l _
  rw [← mul_assoc, map_mul (iB l) _ y', ← hY]
  simp only [map_mul, map_pow, map_natCast]
  rw [← hu, huq]
  ring
