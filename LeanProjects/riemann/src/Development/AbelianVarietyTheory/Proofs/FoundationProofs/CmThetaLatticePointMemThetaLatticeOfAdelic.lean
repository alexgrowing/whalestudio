import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.MovedLattice

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h] at h2
  simp at h2

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  unfold Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (halfDifferent_ne_bot D))

def ext (D : D7) (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem ext_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) : ext D cc ≠ 0 := by
  unfold ext
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact h
  · exact FaithfulSMul.algebraMap_injective _ _

theorem coe_alg (D : D7) (c : 𝓞 D.host.K) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) =
      ((c : D.host.K) : D.host.E) := rfl

theorem mem_ext (D : D7) {cc : Ideal (𝓞 D.host.K)} {c : 𝓞 D.host.K} (h : c ∈ cc) :
    ((c : D.host.K) : D.host.E) ∈ ext D cc := by
  rw [← coe_alg]
  exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ h)

theorem inc_mul_mem (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) {j : D.host.E}
    (hj : j ∈ (ext D cc * D.host.AA0)⁻¹) {y : AE D} (hy : y ∈ IhE D cc) : inc D j * y ∈ OhE D := by
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D h) (inverseHalfDifferent_ne_zero D)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    rw [← mul_assoc, ← map_mul]
    refine mul_mem ?_ hs
    have h1 := FractionalIdeal.mul_mem_mul hj (FractionalIdeal.mul_mem_mul (mem_ext D hc) ha)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at h1
    exact (AdLattice.incl_mem_iff (F := ℚ) _).2 h1
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem smul_mem_homL (D : D7) {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L₁) (h' : Moves D g' L₁') (z : Matrix (Fin N') (Fin N) D.host.E) (j : D.host.E)
    (hz : ∀ a b, inc D j * (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D))) a b ∈ OhE D) : j • z ∈ homL D L₁ L₁' := by
  refine Submodule.subset_span fun x hx => ?_
  rw [h] at hx
  rw [h']
  intro i
  have key : ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)).mulVec
      (fun k => inc D ((j • z).mulVec x k)) =
      (inc D j • (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D)))).mulVec
        (((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec (fun k => inc D (x k))) := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul _ (inc D j)]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      RingHom.map_mulVec]
    rfl
  rw [key]
  simp only [Matrix.mulVec, dotProduct] at hx ⊢
  exact sum_mem fun k _ => mul_mem (hz i k) (hx k)

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (y y' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (y + y') = pt D (tor0 D cc δ) δ y + pt D (tor0 D cc δ) δ y' := by
  funext τ a b
  simp [pt, embV, tor0, mul_add]

theorem pt_smul_mem (D : D7) (hD : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    {m : D.host.E} (hm : m ∈ ext D cc) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L₁ L₁') :
    pt D (tor0 D cc δ) δ (m • y) ∈ La D (tor0 D cc δ) L₁ L₁' := by
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
  clear hm
  induction hb using Submodule.span_induction generalizing y with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, y, hy, ?_⟩
    funext τ a b
    rw [coe_alg]
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hD τ, mul_assoc]
  | zero =>
    have : pt D (tor0 D cc δ) δ (algebraMap (𝓞 D.host.E) D.host.E 0 • y) = 0 := by
      funext τ a b
      simp [pt, embV, tor0]
    rw [this]; exact zero_mem _
  | add b b' _ _ hb hb' =>
    rw [map_add, add_smul, pt_add]
    exact add_mem (hb hy) (hb' hy)
  | smul r b _ hb =>
    have := hb ((YYl D L₁ L₁').smul_mem r hy)
    rwa [← algebraMap_smul D.host.E r y, smul_smul, ← map_mul, mul_comm] at this

end GlobalTheory.NormSum.MovedLattice

open GlobalTheory.NormSum.MovedLattice in

theorem GlobalTheory.NormSum.pt_mem_La_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D hD cc δ hcc N N' g g' L₁ L₁' h h' z hz
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)
  have hY : ∀ n ∈ D.host.AA0 * (ext D cc * D.host.AA0)⁻¹, n • z ∈ YYl D L₁ L₁' := by
    intro n hn
    refine FractionalIdeal.mul_induction_on hn (fun a ha j hj => ?_) (fun x y hx hy => ?_)
    · refine Submodule.subset_span ⟨a, ha, j • z, ?_, mul_smul _ _ _⟩
      exact smul_mem_homL D _ _ h h' z j fun a b => inc_mul_mem D hcc hj (hz a b)
    · rw [add_smul]; exact add_mem hx hy
  have h1 : (1 : D.host.E) ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have h2 : ∀ e ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹),
      pt D (tor0 D cc δ) δ (e • z) ∈ La D (tor0 D cc δ) L₁ L₁' := by
    intro e he
    refine FractionalIdeal.mul_induction_on he (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul]
      exact pt_smul_mem D hD.1 cc δ L₁ L₁' hm (hY n hn)
    · rw [add_smul, pt_add]; exact add_mem hx hy
  simpa using h2 1 h1
