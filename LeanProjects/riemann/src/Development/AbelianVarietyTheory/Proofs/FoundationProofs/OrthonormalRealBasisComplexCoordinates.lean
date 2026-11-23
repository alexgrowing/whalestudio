import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.OrthoCoord

variable {D : D7}

theorem emb_conj (φ : D.host.E →+* ℂ) (x : D.host.E) : φ (D.host.conj x) = starRingEnd ℂ (φ x) :=
  D.host.conjE_apply φ x

theorem embT_injective : Function.Injective (embT D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embT_indep (c : D.what₂.Tau → ℂ) (h : ∀ x, ∑ τ, c τ * embT D τ x = 0) (τ : D.what₂.Tau) : c τ = 0 := by
  have h1 := (linearIndependent_monoidHom D.host.E ℂ).comp
    (fun τ : D.what₂.Tau => ((embT D τ : D.host.E →+* ℂ) : D.host.E →* ℂ))
    (fun a b hab => embT_injective (RingHom.coe_monoidHom_injective hab))
  rw [Fintype.linearIndependent_iff] at h1
  refine h1 c ?_ τ
  funext x
  simpa [Finset.sum_apply] using h x

theorem coordB_embV (h : TraceMapNormalisation D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Orthonormal D b) (j k : Fin r) :
    coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) = if j = k then 1 else 0 := by
  have h1 := h (∑ i, ∑ i', b k i i' * D.host.conj (b j i i'))
  have h2 := hb k j
  unfold hYY at h2
  rw [h2] at h1
  have h3 : coordB D (tor0 D cc δ) b j (embV D (tor0 D cc δ) (b k)) =
      ∑ τ, embT D τ (∑ i, ∑ i', b k i i' * D.host.conj (b j i i')) := by
    simp only [coordB, embV, tor0, map_sum, map_mul, emb_conj]
  rw [h3, h1]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]

theorem coordB_sum (T : Tor D) {a d r : ℕ} (b : Fin r → Matrix (Fin d) (Fin a) D.host.E) (j : Fin r)
    (c : Fin r → ℂ) (v : Fin r → VC D a d) :
    coordB D T b j (∑ k, c k • v k) = ∑ k, c k * coordB D T b j (v k) := by
  let L : VC D a d →ₗ[ℂ] ℂ :=
    { toFun := coordB D T b j
      map_add' := fun x y => by simp [coordB, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [coordB, Finset.mul_sum, mul_assoc] }
  change L _ = ∑ k, c k * L (v k)
  simp [map_sum, map_smul]

theorem embV_mem_span (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤)
    (A : Matrix (Fin d) (Fin a) D.host.E) :
    embV D (tor0 D cc δ) A ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun k => D.host.φ₀ (c k : D.host.E), ?_⟩
  funext τ i j
  simp only [embV, tor0, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← h τ, ← map_mul]
  rfl

theorem span_eq_top (h : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {a d r : ℕ}
    {b : Fin r → Matrix (Fin d) (Fin a) D.host.E} (hb : Submodule.span D.host.K (Set.range b) = ⊤) :
    Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  let e : D.what₂.Tau → Fin d → Fin a → VC D a d := fun τ i j => Pi.single τ (Pi.single i (Pi.single j 1))
  have hz : ∀ z : VC D a d, z = ∑ τ, ∑ i, ∑ j, z τ i j • e τ i j := by
    intro z
    funext τ i j
    simp [e, Finset.sum_apply, Pi.single_apply, ite_apply]
  have he : ∀ τ i j, f (e τ i j) = 0 := by
    intro τ i j
    refine embT_indep (fun τ => f (e τ i j)) (fun x => ?_) τ
    have h1 : f (embV D (tor0 D cc δ) (Matrix.single i j x)) = 0 := hf (embV_mem_span h cc δ hb _)
    have h2 : embV D (tor0 D cc δ) (Matrix.single i j x) = ∑ τ, embT D τ x • e τ i j := by
      funext τ' i' j'
      simp only [e, embV, tor0, Matrix.single_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, ite_apply,
        smul_eq_mul]
      by_cases hi : i = i'
      · by_cases hj : j = j'
        · subst hi hj; simp
        · simp [hj, Ne.symm hj]
      · simp [hi, Ne.symm hi]
    rw [h2] at h1
    simpa [map_sum, map_smul, mul_comm] using h1
  refine LinearMap.ext fun z => ?_
  rw [hz z]
  simp [map_sum, map_smul, he]

theorem orthonormal_coord : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → (∀ i j, coordB D (tor0 D cc δ) b i (embV D (tor0 D cc δ) (b j)) = if i = j then 1 else 0) ∧ ∀ z : VC D N N', z = ∑ j, coordB D (tor0 D cc δ) b j z • embV D (tor0 D cc δ) (b j) := by
  intro D h cc δ N N' r b hb
  refine ⟨coordB_embV h.2 cc δ hb.1, fun z => ?_⟩
  have hz : z ∈ Submodule.span ℂ (Set.range fun k => embV D (tor0 D cc δ) (b k)) := by
    rw [span_eq_top h.1 cc δ hb.2]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordB_sum]
  simp [coordB_embV h.2 cc δ hb.1]

end GlobalTheory.OrthoCoord
