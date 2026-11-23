import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences

open idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem exists_trace_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (N : ℕ) : ∃ a : 𝓞 K, a + star a - 1 ∈ extP K 𝔭 ^ N := by
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  obtain ⟨e, he⟩ := exists_inv_theta hθ N
  refine ⟨θ * e, ?_⟩
  have hJ := conjO_mem_pow hF 𝔭 N
  have h1 : (conjO K θ - θ) * conjO K e - 1 ∈ extP K 𝔭 ^ N := by
    have h := hJ _ he
    simp only [map_sub, map_mul, map_one] at h
    rw [L3.conjO_conjO θ] at h
    exact h
  have h2 : (θ - conjO K θ) * (e + conjO K e) ∈ extP K 𝔭 ^ N := by
    have e2 : (θ - conjO K θ) * (e + conjO K e) =
        ((θ - conjO K θ) * e - 1) - ((conjO K θ - θ) * conjO K e - 1) := by ring
    rw [e2]
    exact Ideal.sub_mem _ he h1
  have h3 : e + conjO K e ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h2
  have e3 : θ * e + star (θ * e) - 1 =
      ((θ - conjO K θ) * e - 1) + conjO K θ * (e + conjO K e) := by
    rw [idealPowerSpanBounds.star_def, map_mul]
    ring
  rw [e3]
  exact Ideal.add_mem _ he (Ideal.mul_mem_left _ _ h3)

theorem exists_tr_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {N : ℕ} {z : 𝓞 K} (hz : z ∉ extP K 𝔭 ^ N) :
    ∃ b : 𝓞 K, trF hF (b * z) ∉ 𝔭 ^ N := by
  by_contra hall
  push_neg at hall
  obtain ⟨θ, hθ⟩ := exists_theta hK hF h𝔭
  have htr : ∀ b : 𝓞 K, b * z + conjO K (b * z) ∈ extP K 𝔭 ^ N := by
    intro b
    rw [← trF_spec hF]
    exact (mem_pow_iff 𝔭 N _).mpr (hall b)
  have h1 := htr 1
  have h2 := htr θ
  rw [one_mul] at h1
  rw [map_mul] at h2
  have h3 : (θ - conjO K θ) * conjO K z ∈ extP K 𝔭 ^ N := by
    have e : (θ - conjO K θ) * conjO K z =
        θ * (z + conjO K z) - (θ * z + conjO K θ * conjO K z) := by ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h1) h2
  have h4 : conjO K z ∈ extP K 𝔭 ^ N := mem_of_unit_mul_mem hθ h3
  apply hz
  have h5 := conjO_mem_pow hF 𝔭 N _ h4
  rwa [L3.conjO_conjO z] at h5

theorem exists_solve_scalar (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c ≤ k) {z₀ : 𝓞 K} (hz : z₀ ∉ extP K 𝔭 ^ (c + 1)) {s : 𝓞 K}
    (hs : s ∈ extP K 𝔭 ^ k) (hs' : star s - s ∈ extP K 𝔭 ^ (k + 1)) :
    ∃ r ∈ extP K 𝔭 ^ (k - c), z₀ * r + star (z₀ * r) - s ∈ extP K 𝔭 ^ (k + 1) := by
  obtain ⟨a, ha⟩ := exists_trace_one hK hF h𝔭 (k + 1)
  have has : a * s ∈ extP K 𝔭 ^ k := Ideal.mul_mem_left _ a hs
  have hσ : trF hF (a * s) ∈ 𝔭 ^ k := trF_mem_pow hF 𝔭 k has
  have hσs : ι (trF hF (a * s)) - s ∈ extP K 𝔭 ^ (k + 1) := by
    rw [trF_spec, map_mul]
    have e : a * s + conjO K a * conjO K s - s =
        (a + star a - 1) * s + conjO K a * (star s - s) := by
      rw [idealPowerSpanBounds.star_def, idealPowerSpanBounds.star_def]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hs')
  obtain ⟨b, hb⟩ := exists_tr_notMem hK hF h𝔭 hz
  obtain ⟨r', hr', hfill⟩ := idealPowerSpanBounds.exists_fill h𝔭.isPrime (idealPowerSpanBounds.ne_bot h𝔭) hb hck hσ
  refine ⟨b * ι r', Ideal.mul_mem_left _ b ((mem_pow_iff 𝔭 (k - c) r').mpr hr'), ?_⟩
  have hlin : trF hF (z₀ * (b * ι r')) = r' * trF hF (b * z₀) := by
    have e : z₀ * (b * ι r') = r' • (b * z₀) := by
      rw [Algebra.smul_def]
      ring
    rw [e, map_smul, smul_eq_mul]
  have hsum : z₀ * (b * ι r') + star (z₀ * (b * ι r')) = ι (r' * trF hF (b * z₀)) := by
    rw [← hlin, trF_spec, idealPowerSpanBounds.star_def]
  rw [hsum]
  have e2 : ι (r' * trF hF (b * z₀)) - s =
      -ι (trF hF (a * s) - trF hF (b * z₀) * r') + (ι (trF hF (a * s)) - s) := by
    simp only [map_sub, map_mul]
    ring
  rw [e2]
  exact Ideal.add_mem _ (neg_mem ((mem_pow_iff 𝔭 (k + 1) _).mpr hfill)) hσs

variable {m : Type} [Fintype m] [DecidableEq m]

theorem mul_entries_mem {r : Type} {J : Ideal (𝓞 K)} (M : Matrix m m (𝓞 K)) {R : Matrix m r (𝓞 K)}
    (hR : ∀ i j, R i j ∈ J) (i : m) (j : r) : (M * R) i j ∈ J := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ (hR l j))

theorem det_sub_mem {J : Ideal (𝓞 K)} {M N : Matrix m m (𝓞 K)} (h : ∀ i j, (M - N) i j ∈ J) :
    M.det - N.det ∈ J := by
  rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [Ideal.Quotient.eq]
  simpa [Matrix.sub_apply] using h i j

theorem exists_solve_matrix (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c k : ℕ} (hck : c + 1 ≤ k) {H X : Matrix m m (𝓞 K)} {D : 𝓞 F}
    (hD : H.det = ι D) (hDc : D ∉ 𝔭 ^ (c + 1)) (hX : ∀ i j, (Xᴴ * H * X - H) i j ∈ extP K 𝔭 ^ k)
    {W : Matrix m m (𝓞 K)} (hW : ∀ i j, W i j ∈ extP K 𝔭 ^ k) :
    ∃ Y : Matrix m m (𝓞 K), (∀ i j, Y i j ∈ extP K 𝔭 ^ (k - c)) ∧
      ∀ i j, (Xᴴ * H * Y - W) i j ∈ extP K 𝔭 ^ (k + 1) := by
  have hck' : c ≤ k := by omega
  have hfill := fun i j => exists_fillO (K := K) h𝔭 hDc hck' (hW i j)
  choose V hV hV' using hfill
  obtain ⟨R, hR⟩ : ∃ R : Matrix m m (𝓞 K), R = H.adjugate * Matrix.of V := ⟨_, rfl⟩
  have hRmem : ∀ i j, R i j ∈ extP K 𝔭 ^ (k - c) := by
    intro i j
    rw [hR]
    exact mul_entries_mem _ (fun a b => hV a b) i j
  refine ⟨X * R, fun i j => mul_entries_mem X hRmem i j, ?_⟩
  intro i j
  have e : Xᴴ * H * (X * R) - W = (Xᴴ * H * X - H) * R + (H * R - W) := by
    first
    | noncomm_ring
    | (simp only [Matrix.sub_mul, Matrix.mul_assoc]; abel)
  have e1 : H * R = H.det • Matrix.of V := by
    rw [hR, ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
  rw [e, Matrix.add_apply]
  refine Ideal.add_mem _ ?_ ?_
  · rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ (fun l _ => ?_)
    have h1 : (Xᴴ * H * X - H) i l * R l j ∈ extP K 𝔭 ^ (k + (k - c)) := by
      rw [pow_add]
      exact Ideal.mul_mem_mul (hX i l) (hRmem l j)
    exact Ideal.pow_le_pow_right (by omega) h1
  · rw [Matrix.sub_apply, e1, Matrix.smul_apply, Matrix.of_apply, hD, smul_eq_mul]
    have h2 := neg_mem (hV' i j)
    rw [neg_sub] at h2
    exact h2

end Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
