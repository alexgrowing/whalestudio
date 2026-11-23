import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNearPowerExistsStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Glue

section Abs

variable {B : Type} [CommRing B]

def InMul (S : Subring B) (ϖ z : B) : Prop := ∃ s ∈ S, z = ϖ * s

theorem InMul.add {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z + w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s + t, S.add_mem hs ht, by ring⟩

theorem InMul.sub {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : InMul S ϖ w) :
    InMul S ϖ (z - w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  obtain ⟨t, ht, rfl⟩ := hw
  exact ⟨s - t, S.sub_mem hs ht, by ring⟩

theorem InMul.mul {S : Subring B} {ϖ z w : B} (hz : InMul S ϖ z) (hw : w ∈ S) :
    InMul S ϖ (z * w) := by
  obtain ⟨s, hs, rfl⟩ := hz
  exact ⟨s * w, S.mul_mem hs hw, by ring⟩

theorem inMul_zero (S : Subring B) (ϖ : B) : InMul S ϖ 0 :=
  ⟨0, S.zero_mem, by ring⟩

theorem pow_sub_pow_inMul {S : Subring B} {ϖ T f s : B} (hϖ : ϖ ∈ S) (hT : T ∈ S) (hs : s ∈ S)
    (h : T = ϖ * s + f) (k : ℕ) : InMul S ϖ (T ^ k - f ^ k) := by
  have hf : f ∈ S := by
    have : f = T - ϖ * s := by rw [h]; ring
    rw [this]
    exact S.sub_mem hT (S.mul_mem hϖ hs)
  induction k with
  | zero => simpa using inMul_zero S ϖ
  | succ k ih =>
    have e : T ^ (k + 1) - f ^ (k + 1) = (T ^ k - f ^ k) * T + (ϖ * s) * f ^ k := by
      rw [pow_succ, pow_succ]
      have : f ^ k * f = f ^ k * (T - ϖ * s) := by rw [h]; ring
      rw [this]; ring
    rw [e]
    exact (ih.mul hT).add ⟨s * f ^ k, S.mul_mem hs (S.pow_mem hf k), by ring⟩

theorem evalMod_of_lift {R T : Type} [CommRing R] [CommRing T] (S : Subring B) (F : ℕ → Ideal B)
    (ϖ : B) (h : R →+* B) (τ : T →* B) (r : R →+* T) (hτ0 : τ 0 = 0) (hτS : ∀ a, τ a ∈ S)
    (hϖ : ϖ ∈ S) (hadd : ∀ a b, InMul S ϖ (τ (a + b) - τ a - τ b))
    (hcoef : ∀ c, InMul S ϖ (h c - τ (r c))) (hF : ∀ k, ∀ f ∈ F 1, f ^ k ∈ F k)
    (x y : T) (φ : PowerSeries R)
    (hy : ∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)
    (M : ℕ) (s : B) (hs : s ∈ S) (hM : τ x ^ M - ϖ * s ∈ F 1) (k : ℕ) :
    ∃ D, ∀ D' ≥ D, Near S ϖ (F k) 1
      ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) - τ y) := by
  have hsum : ∀ D, InMul S ϖ ((∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) -
      τ (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i)) := by
    intro D
    induction D with
    | zero => simpa [hτ0] using inMul_zero S ϖ
    | succ D ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      generalize hA : (∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) = A at ih ⊢
      generalize hP : (∑ i ∈ Finset.range D, h (PowerSeries.coeff i φ) * τ x ^ i) = P at ih ⊢
      have e1 : P + h (PowerSeries.coeff D φ) * τ x ^ D -
          τ (A + r (PowerSeries.coeff D φ) * x ^ D) =
          (P - τ A) + (h (PowerSeries.coeff D φ) - τ (r (PowerSeries.coeff D φ))) * τ x ^ D -
          (τ (A + r (PowerSeries.coeff D φ) * x ^ D) - τ A -
            τ (r (PowerSeries.coeff D φ) * x ^ D)) := by
        rw [map_mul τ, map_pow τ]; ring
      rw [e1]
      exact (ih.add ((hcoef _).mul (S.pow_mem (hτS x) D))).sub (hadd _ _)
  refine ⟨M * k, fun D' hD' => ?_⟩
  obtain ⟨b, hb⟩ := hy D'
  have hP := hsum D'
  generalize (∑ i ∈ Finset.range D', r (PowerSeries.coeff i φ) * x ^ i) = A at hb hP
  generalize (∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * τ x ^ i) = P at hP ⊢
  have hyA : y = A + x ^ D' * b := by rw [← hb]; ring
  obtain ⟨a, ha, hT⟩ := pow_sub_pow_inMul hϖ (S.pow_mem (hτS x) M) hs
    (f := τ x ^ M - ϖ * s) (by ring) k
  obtain ⟨u, hu, hPu⟩ := hP
  obtain ⟨v, hv, hv'⟩ := hadd A (x ^ D' * b)
  have hg : (τ x ^ M - ϖ * s) ^ k ∈ F k := hF k _ hM
  set g := (τ x ^ M - ϖ * s) ^ k with hgdef
  have hpow : τ x ^ D' = (τ x ^ M) ^ k * τ x ^ (D' - M * k) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hw : τ x ^ (D' - M * k) * τ b ∈ S := S.mul_mem (S.pow_mem (hτS x) _) (hτS b)
  obtain ⟨w, hwdef⟩ : ∃ w, w = τ x ^ (D' - M * k) * τ b := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hC : τ (x ^ D' * b) = (τ x ^ M) ^ k * w := by
    rw [map_mul τ, map_pow τ, hpow, hwdef]; ring
  refine ⟨u - v - a * w, S.sub_mem (S.sub_mem hu hv) (S.mul_mem ha hw), ?_⟩
  have e : P - τ y - ϖ ^ 1 * (u - v - a * w) = -(g * w) := by
    rw [hyA]
    linear_combination hPu - hv' - hC - w * hT
  rw [e]
  exact (F k).neg_mem (Ideal.mul_mem_right w (F k) hg)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

def tchHom : Tl l →* Formalism.Per6.BdRp l :=
  ((wB l : Wl l →+* Formalism.Per6.BdRp l) : Wl l →* Formalism.Per6.BdRp l).comp (WittVector.teichmuller l)

theorem tchHom_apply (a : Tl l) : tchHom l a = tch l a := rfl

theorem tchHom_zero : tchHom l 0 = 0 := by
  simp [tchHom]

theorem teichmuller_add_sub (a b : Tl l) : ∃ w : Wl l,
    WittVector.teichmuller l (a + b) - WittVector.teichmuller l a - WittVector.teichmuller l b
      = w * (l : Wl l) := by
  set z : Wl l := WittVector.teichmuller l (a + b) - WittVector.teichmuller l a -
    WittVector.teichmuller l b with hz
  have h0 : z.coeff 0 = 0 := by
    have : WittVector.constantCoeff z = 0 := by
      simp [hz, map_sub]
    simpa using this
  have h1 : z = WittVector.verschiebung (z.shift 1) := by
    have := WittVector.eq_iterate_verschiebung (n := 1) (x := z) (by
      intro i hi
      obtain rfl : i = 0 := by omega
      exact h0)
    simpa using this
  obtain ⟨u, hu⟩ := (WittVector.frobenius_bijective l (Tl l)).2 (z.shift 1)
  refine ⟨u, ?_⟩
  rw [h1, ← hu, WittVector.verschiebung_frobenius]

end Conc

theorem evalMod_teichmuller : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (π : ↥(OL K)) (S : Subring (Formalism.Per6.BdRp l)),
    (∀ a, wB l a ∈ S) → (∀ c, oB K μ c ∈ S) → PerEnv S (FB l) (oB K μ π) → π ∣ (l : ↥(OL K)) →
    ∀ (r : ↥(OL K) →+* Tl l), (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) →
    ∀ (x y : Tl l), ‖thB l (tch l x)‖ < 1 → ∀ (φ : PowerSeries ↥(OL K)),
      (∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) →
      EvalMod S (FB l) (oB K μ π) (oB K μ) φ (tch l x) (tch l y) 1 := by
  intro l _ K μ π S hw ho env hπ r hr x y hx φ hy k
  obtain ⟨e, he⟩ := hπ
  have hl : ((l : ℕ) : Formalism.Per6.BdRp l) = oB K μ π * oB K μ e := by
    rw [← map_mul, ← he, map_natCast]
  have hadd : ∀ a b, InMul S (oB K μ π) (tchHom l (a + b) - tchHom l a - tchHom l b) := by
    intro a b
    obtain ⟨w, hw'⟩ := teichmuller_add_sub l a b
    refine ⟨wB l w * oB K μ e, S.mul_mem (hw _) (ho _), ?_⟩
    have := congrArg (wB l) hw'
    simp only [map_sub, map_mul, map_natCast] at this
    simp only [tchHom_apply, tch]
    rw [this, hl]; ring
  have hcoef : ∀ c, InMul S (oB K μ π) (oB K μ c - tchHom l (r c)) := by
    intro c
    obtain ⟨c', hc'⟩ := hr c
    refine ⟨- oB K μ c', S.neg_mem (ho _), ?_⟩
    rw [tchHom_apply, hc', map_add, map_mul]; ring
  have hϖ0 : thB l (oB K μ π) ≠ 0 := (env.unit.map (thB l)).ne_zero
  obtain ⟨M, -, s, hs, hM⟩ := GlobalTheory.T.teichmuller_near_power_exists S hw (oB K μ π) hϖ0 x hx
  rw [pow_one] at hM
  exact evalMod_of_lift S (FB l) (oB K μ π) (oB K μ) (tchHom l) r (tchHom_zero l)
    (fun a => hw _) env.mem hadd hcoef
    (fun k f hf => Ideal.pow_mem_pow (by simpa [FB] using hf) k) x y φ hy M s hs hM k

end GlobalTheory.CompanionTheory.LTPer.Glue
