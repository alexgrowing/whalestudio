import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.GL2Classical.ExistsIntOfMemIntegralFiniteAdeles
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableLatticeWeightThreeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicColumnNormLowerStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicNormRatVectorBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatDoubleCosetEqOfRowDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNormDiagonalReductionStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing

namespace Ad3.GA

local notation "M3A" => Matrix (Fin 3) (Fin 3) 𝔸[ℚ]

namespace majorantEstimates

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

def F (M : ℕ) (p : ℚ × ℚ × ℚ) : ℝ :=
  if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then
    ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else 0

theorem F_nonneg (M : ℕ) (p : ℚ × ℚ × ℚ) : 0 ≤ F M p := by
  unfold F; split_ifs <;> positivity

theorem summable_F (M : ℕ) (hM : 0 < M) : Summable (F M) := GlobalTheory.T.summable_lattice_weight_three M hM

theorem real_bound {T L : ℕ} (hL : T + 3 ≤ L) {X Cg Ai α β ρ Y B Q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hρ : 0 ≤ ρ) (hY : 0 ≤ Y) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hAi0 : 0 ≤ Ai)
    (hX : X ≤ Cg * Ai ^ T / ((1 + α) * (1 + β)) ^ (3 * L))
    (hAi : Ai ≤ Q * ρ) (hρβ : ρ ≤ B * β) (hYαβ : Y ≤ B * (α * β ^ 2)) :
    X ≤ max Cg 0 * Q ^ T * (max 1 B) ^ (2 * L) * ((1 + ρ) ^ 3 * (1 + Y) ^ 2)⁻¹ := by
  set B1 := max 1 B
  have hB1 : 1 ≤ B1 := le_max_left _ _
  have hBB1 : B ≤ B1 := le_max_right _ _
  have hD : 1 ≤ (1 + α) * (1 + β) := by nlinarith
  have e1 : 1 + ρ ≤ B1 * (1 + β) := by nlinarith
  have e2 : 1 + Y ≤ B1 * ((1 + α) * (1 + β) ^ 2) := by
    have : α * β ^ 2 ≤ (1 + α) * (1 + β) ^ 2 - 1 := by nlinarith [sq_nonneg β, mul_nonneg hα hβ]
    have h0 : 0 ≤ α * β ^ 2 := by positivity
    nlinarith
  have e3 : (1 + ρ) * (1 + Y) ≤ B1 ^ 2 * ((1 + α) * (1 + β)) ^ 3 := by
    have h4 : (1 + α) * (1 + β) ^ 3 ≤ ((1 + α) * (1 + β)) ^ 3 := by
      have : (1 + α) ≤ (1 + α) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      have : (1 + α) * (1 + β) ^ 3 ≤ (1 + α) ^ 3 * (1 + β) ^ 3 :=
        mul_le_mul_of_nonneg_right this (by positivity)
      simpa [mul_pow] using this
    calc (1 + ρ) * (1 + Y) ≤ (B1 * (1 + β)) * (B1 * ((1 + α) * (1 + β) ^ 2)) :=
          mul_le_mul e1 e2 (by linarith) (by positivity)
      _ = B1 ^ 2 * ((1 + α) * (1 + β) ^ 3) := by ring
      _ ≤ B1 ^ 2 * ((1 + α) * (1 + β)) ^ 3 := mul_le_mul_of_nonneg_left h4 (by positivity)
  have e4 : ((1 + ρ) * (1 + Y)) ^ L ≤ B1 ^ (2 * L) * ((1 + α) * (1 + β)) ^ (3 * L) := by
    calc ((1 + ρ) * (1 + Y)) ^ L ≤ (B1 ^ 2 * ((1 + α) * (1 + β)) ^ 3) ^ L :=
          pow_le_pow_left₀ (by positivity) e3 L
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have e5 : Ai ^ T ≤ Q ^ T * (1 + ρ) ^ T := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hAi0 (hAi.trans (by nlinarith)) T
  have hDpos : 0 < ((1 + α) * (1 + β)) ^ (3 * L) := by positivity
  have e6 : (1 + ρ) ^ T * ((1 + ρ) ^ 3 * (1 + Y) ^ 2) ≤ ((1 + ρ) * (1 + Y)) ^ L := by
    rw [mul_pow]
    have h1 : (1 + ρ) ^ T * (1 + ρ) ^ 3 ≤ (1 + ρ) ^ L := by
      rw [← pow_add]; exact pow_le_pow_right₀ (by linarith) hL
    have h2 : (1 + Y) ^ 2 ≤ (1 + Y) ^ L := pow_le_pow_right₀ (by linarith) (by omega)
    calc (1 + ρ) ^ T * ((1 + ρ) ^ 3 * (1 + Y) ^ 2) = ((1 + ρ) ^ T * (1 + ρ) ^ 3) * (1 + Y) ^ 2 := by ring
      _ ≤ (1 + ρ) ^ L * (1 + Y) ^ L := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hP : 0 < (1 + ρ) ^ 3 * (1 + Y) ^ 2 := by positivity
  have hCg : Cg ≤ max Cg 0 := le_max_left _ _
  have hCg0 : 0 ≤ max Cg 0 := le_max_right _ _
  calc X ≤ Cg * Ai ^ T / ((1 + α) * (1 + β)) ^ (3 * L) := hX
    _ ≤ max Cg 0 * (Q ^ T * (1 + ρ) ^ T) / ((1 + α) * (1 + β)) ^ (3 * L) := by
        gcongr
    _ ≤ max Cg 0 * Q ^ T * (max 1 B) ^ (2 * L) * ((1 + ρ) ^ 3 * (1 + Y) ^ 2)⁻¹ := by
        rw [div_le_iff₀ hDpos]
        have key : (1 + ρ) ^ T ≤ B1 ^ (2 * L) * ((1 + α) * (1 + β)) ^ (3 * L) *
            ((1 + ρ) ^ 3 * (1 + Y) ^ 2)⁻¹ := by
          rw [le_mul_inv_iff₀ hP]; exact e6.trans e4
        calc max Cg 0 * (Q ^ T * (1 + ρ) ^ T) = max Cg 0 * Q ^ T * (1 + ρ) ^ T := by ring
          _ ≤ max Cg 0 * Q ^ T * (B1 ^ (2 * L) * ((1 + α) * (1 + β)) ^ (3 * L) *
              ((1 + ρ) ^ 3 * (1 + Y) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left key (by positivity)
          _ = _ := by ring

theorem lattice {Ω : Set 𝔸f} (hΩ : IsCompact Ω) {C : Set G3} (hC : IsCompact C)
    {Φ0 Φ1 Ψ : G3 → 𝔸[ℚ]} (h0 : Continuous Φ0) (h1 : Continuous Φ1) (hΨ : Continuous Ψ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (u v : (𝔸[ℚ])ˣ), (u : 𝔸[ℚ]).2 ∈ Ω → (v : 𝔸[ℚ]).2 ∈ Ω → ∀ m ∈ C,
      ∀ x0 x1 y : ℚ, algebraMap ℚ 𝔸[ℚ] x0 = v * Φ0 m → algebraMap ℚ 𝔸[ℚ] x1 = v * Φ1 m →
      algebraMap ℚ 𝔸[ℚ] y = u * v ^ 2 * Ψ m →
      ((M : ℚ) * x0).den = 1 ∧ ((M : ℚ) * x1).den = 1 ∧ ((M : ℚ) * y).den = 1 := by
  have hs : Continuous (Prod.snd : 𝔸[ℚ] → 𝔸f) := continuous_snd
  set D : Set 𝔸f := ((fun p : 𝔸f × G3 => p.1 * (Φ0 p.2).2) '' (Ω ×ˢ C)) ∪
    ((fun p : 𝔸f × G3 => p.1 * (Φ1 p.2).2) '' (Ω ×ˢ C)) ∪
    ((fun p : 𝔸f × 𝔸f × G3 => p.1 * p.2.1 ^ 2 * (Ψ p.2.2).2) '' (Ω ×ˢ Ω ×ˢ C)) with hDdef
  have hD : IsCompact D := by
    refine (((hΩ.prod hC).image ?_).union ((hΩ.prod hC).image ?_)).union
      ((hΩ.prod (hΩ.prod hC)).image ?_)
    · exact continuous_fst.mul (hs.comp (h0.comp continuous_snd))
    · exact continuous_fst.mul (hs.comp (h1.comp continuous_snd))
    · exact (continuous_fst.mul ((continuous_fst.comp continuous_snd).pow 2)).mul
        (hs.comp (hΨ.comp (continuous_snd.comp continuous_snd)))
  obtain ⟨d, hd0, hd⟩ := GroundTheory.Global.exists_mul_mem_integralFiniteAdeles_of_isCompact hD
  set n : ℤ := Rat.ringOfIntegersEquiv d with hn
  have hnr : (n : ℚ) = algebraMap (𝓞 ℚ) ℚ d := by rw [hn, Rat.ringOfIntegersEquiv_apply_coe]
  have hn0 : n ≠ 0 := by
    intro h
    apply hd0
    have : algebraMap (𝓞 ℚ) ℚ d = 0 := by rw [← hnr, h, Int.cast_zero]
    exact (map_eq_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).1 this
  have key : ∀ x : ℚ, algebraMap ℚ 𝔸f x ∈ D → ((n.natAbs : ℚ) * x).den = 1 := by
    intro x hx
    have hm := hd _ hx
    rw [← hnr, ← map_mul] at hm
    obtain ⟨z, hz⟩ := GroundTheory.Automorphic.GL2Classical.exists_int_of_mem_integralFiniteAdeles hm
    rcases Int.natAbs_eq n with h | h
    · have : ((n.natAbs : ℚ)) = (n : ℚ) := by
        conv_rhs => rw [h]
        simp
      rw [this, hz]; simp
    · have : ((n.natAbs : ℚ)) = -(n : ℚ) := by
        conv_rhs => rw [h]
        simp
      rw [this, neg_mul, hz, ← Int.cast_neg]; simp
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn0, fun u v hu hv m hm x0 x1 y e0 e1 ey => ⟨key _ ?_, key _ ?_, key _ ?_⟩⟩
  · refine Or.inl (Or.inl ⟨((v : 𝔸[ℚ]).2, m), ⟨hv, hm⟩, ?_⟩)
    have := congrArg Prod.snd e0
    simpa using this.symm
  · refine Or.inl (Or.inr ⟨((v : 𝔸[ℚ]).2, m), ⟨hv, hm⟩, ?_⟩)
    have := congrArg Prod.snd e1
    simpa using this.symm
  · refine Or.inr ⟨((u : 𝔸[ℚ]).2, (v : 𝔸[ℚ]).2, m), ⟨hu, hv, hm⟩, ?_⟩
    have := congrArg Prod.snd ey
    have h2 : ((v : 𝔸[ℚ]) ^ 2).2 = (v : 𝔸[ℚ]).2 ^ 2 := by rw [pow_two, pow_two]; rfl
    simpa [h2] using this.symm

theorem rat_inf (x : ℚ) : ‖(algebraMap ℚ 𝔸[ℚ] x).1 Rat.infinitePlace‖ = |(x : ℝ)| := by
  have := NumberField.InfinitePlace.Completion.Rat.norm_infinitePlace_completion Rat.infinitePlace x
  rw [Rat.cast_abs] at this
  have e : (algebraMap ℚ 𝔸[ℚ] x).1 Rat.infinitePlace = (x : Rat.infinitePlace.Completion) :=
    eq_ratCast ((Pi.evalRingHom _ Rat.infinitePlace).comp ((RingHom.fst _ _).comp (algebraMap ℚ 𝔸[ℚ]))) x
  rw [e]; exact this

theorem norm_inf_mul (a b : 𝔸[ℚ]) : ‖(a * b).1 Rat.infinitePlace‖ = ‖a.1 Rat.infinitePlace‖ * ‖b.1 Rat.infinitePlace‖ := by
  rw [show (a * b).1 Rat.infinitePlace = a.1 Rat.infinitePlace * b.1 Rat.infinitePlace from rfl, norm_mul]

theorem core {Ω : Set 𝔸f} (hΩ : IsCompact Ω) {C : Set G3} (hC : IsCompact C)
    {Φ0 Φ1 Ψ : G3 → 𝔸[ℚ]} (h0 : Continuous Φ0) (h1 : Continuous Φ1) (hΨ : Continuous Ψ)
    (T : ℕ) (Cg K0 : ℝ) (hK0 : 0 ≤ K0) :
    ∃ M : ℕ, 0 < M ∧ ∃ K : ℝ, ∀ (X : ℝ) (u v : (𝔸[ℚ])ˣ), ∀ m ∈ C, ∀ (x0 x1 y : ℚ) (z : Fin 3 → ℚ),
      algebraMap ℚ 𝔸[ℚ] x0 = v * Φ0 m → algebraMap ℚ 𝔸[ℚ] x1 = v * Φ1 m →
      algebraMap ℚ 𝔸[ℚ] y = u * v ^ 2 * Ψ m → (∀ i, z i = 0 ∨ z i = x0 ∨ z i = x1) →
      ((IdeleGroup.ideleModule ℚ u : ℝ) * IdeleGroup.ideleModule ℚ v)⁻¹ ≤
        K0 * Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) →
      X ≤ Cg / ((IdeleGroup.ideleModule ℚ u : ℝ) * IdeleGroup.ideleModule ℚ v) ^ T /
        ((1 + ‖(u : 𝔸[ℚ]).1 Rat.infinitePlace‖) * (1 + ‖(v : 𝔸[ℚ]).1 Rat.infinitePlace‖)) ^ (3 * (T + 3)) →
      (X ≠ 0 → (u : 𝔸[ℚ]).2 ∈ Ω ∧ (v : 𝔸[ℚ]).2 ∈ Ω) →
      X ≤ K * F M (x0, x1, y) := by
  obtain ⟨M, hM, hlat⟩ := lattice hΩ hC h0 h1 hΨ
  have hcf : ∀ f : G3 → 𝔸[ℚ], Continuous f → Continuous fun m => ‖(f m).1 Rat.infinitePlace‖ :=
    fun f hf => ((continuous_apply Rat.infinitePlace).comp (continuous_fst.comp hf)).norm
  obtain ⟨B0, hB0⟩ := hC.exists_bound_of_continuousOn
    (((hcf _ h0).add (hcf _ h1)).add (hcf _ hΨ)).continuousOn
  set B := max B0 0 with hBdef
  have hB : 0 ≤ B := le_max_right _ _
  have hbd : ∀ m ∈ C, ‖(Φ0 m).1 Rat.infinitePlace‖ ≤ B ∧ ‖(Φ1 m).1 Rat.infinitePlace‖ ≤ B ∧
      ‖(Ψ m).1 Rat.infinitePlace‖ ≤ B := by
    intro m hm
    have h := hB0 m hm
    have n0 := norm_nonneg ((Φ0 m).1 Rat.infinitePlace)
    have n1 := norm_nonneg ((Φ1 m).1 Rat.infinitePlace)
    have n2 := norm_nonneg ((Ψ m).1 Rat.infinitePlace)
    simp only [Pi.add_apply] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    have := le_max_left B0 0
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  set Q : ℝ := K0 * M * 3 with hQdef
  have hQ : 0 ≤ Q := by positivity
  refine ⟨M, hM, max Cg 0 * Q ^ T * (max 1 (2 * B)) ^ (2 * (T + 3)), ?_⟩
  intro X u v m hm x0 x1 y z e0 e1 ey hz hA hX hsupp
  have hF0 := F_nonneg M (x0, x1, y)
  have hK : 0 ≤ max Cg 0 * Q ^ T * (max 1 (2 * B)) ^ (2 * (T + 3)) := by
    have : 0 ≤ max Cg 0 := le_max_right _ _
    positivity
  by_cases hX0 : X = 0
  · rw [hX0]; exact mul_nonneg hK hF0
  obtain ⟨hu, hv⟩ := hsupp hX0
  obtain ⟨d0, d1, dy⟩ := hlat u v hu hv m hm x0 x1 y e0 e1 ey
  have hFe : F M (x0, x1, y) = ((1 + |(x0 : ℝ)| + |(x1 : ℝ)|) ^ 3 * (1 + |(y : ℝ)|) ^ 2)⁻¹ := by
    simp only [F]; rw [if_pos ⟨d0, d1, dy⟩]
  rw [hFe]
  have ninf : ∀ (s : ℚ) (a b : 𝔸[ℚ]), algebraMap ℚ 𝔸[ℚ] s = a * b →
      |(s : ℝ)| = ‖a.1 Rat.infinitePlace‖ * ‖b.1 Rat.infinitePlace‖ := by
    intro s a b h
    rw [← rat_inf, h, norm_inf_mul]
  set α := ‖(u : 𝔸[ℚ]).1 Rat.infinitePlace‖ with hαdef
  set β := ‖(v : 𝔸[ℚ]).1 Rat.infinitePlace‖ with hβdef
  have hα : 0 ≤ α := norm_nonneg _
  have hβ : 0 ≤ β := norm_nonneg _
  obtain ⟨b0, b1, b2⟩ := hbd m hm
  have hx0 : |(x0 : ℝ)| ≤ B * β := by
    rw [ninf _ _ _ e0]; nlinarith [norm_nonneg ((Φ0 m).1 Rat.infinitePlace)]
  have hx1 : |(x1 : ℝ)| ≤ B * β := by
    rw [ninf _ _ _ e1]; nlinarith [norm_nonneg ((Φ1 m).1 Rat.infinitePlace)]
  have hy : |(y : ℝ)| ≤ 2 * B * (α * β ^ 2) := by
    rw [ninf _ _ _ ey, norm_inf_mul, pow_two, norm_inf_mul]
    have h3 : 0 ≤ α * (β * β) := by positivity
    have h4 := norm_nonneg ((Ψ m).1 Rat.infinitePlace)
    nlinarith
  have hz' : ∀ i, ∃ k : ℤ, (M : ℚ) * z i = k := by
    intro i
    rcases hz i with h | h | h <;> rw [h]
    · exact ⟨0, by simp⟩
    · exact ⟨((M : ℚ) * x0).num, (Rat.coe_int_num_of_den_eq_one d0).symm⟩
    · exact ⟨((M : ℚ) * x1).num, (Rat.coe_int_num_of_den_eq_one d1).symm⟩
  have hH := GlobalTheory.T.adelic_norm_rat_vector_bound M hM z hz'
  have hzi : ∀ i, |((z i : ℚ) : ℝ)| ≤ |(x0 : ℝ)| + |(x1 : ℝ)| := by
    intro i
    have a0 := abs_nonneg (x0 : ℝ)
    have a1 := abs_nonneg (x1 : ℝ)
    rcases hz i with h | h | h <;> rw [h]
    · simp; positivity
    · linarith
    · linarith
  have hsum : ∑ i, |((z i : ℚ) : ℝ)| ≤ 3 * (|(x0 : ℝ)| + |(x1 : ℝ)|) := by
    rw [Fin.sum_univ_three]; linarith [hzi 0, hzi 1, hzi 2]
  set Ai := ((IdeleGroup.ideleModule ℚ u : ℝ) * IdeleGroup.ideleModule ℚ v)⁻¹ with hAidef
  have hAi0 : 0 ≤ Ai := by
    have := (IdeleGroup.ideleModule ℚ u).2
    have := (IdeleGroup.ideleModule ℚ v).2
    positivity
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hAi : Ai ≤ Q * (|(x0 : ℝ)| + |(x1 : ℝ)|) := by
    refine hA.trans ?_
    calc K0 * Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ])
        ≤ K0 * (M * ∑ i, |((z i : ℚ) : ℝ)|) := mul_le_mul_of_nonneg_left hH hK0
      _ ≤ K0 * (M * (3 * (|(x0 : ℝ)| + |(x1 : ℝ)|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hMr) hK0
      _ = Q * (|(x0 : ℝ)| + |(x1 : ℝ)|) := by rw [hQdef]; ring
  have hX' : X ≤ Cg * Ai ^ T / ((1 + α) * (1 + β)) ^ (3 * (T + 3)) := by
    rw [hAidef, inv_pow, ← div_eq_mul_inv]; exact hX
  have hρ : |(x0 : ℝ)| + |(x1 : ℝ)| ≤ 2 * B * β := by linarith
  have := real_bound (T := T) (L := T + 3) le_rfl hα hβ (by positivity) (abs_nonneg (y : ℝ))
    (by positivity : (0 : ℝ) ≤ 2 * B) hQ hAi0 hX' hAi hρ hy
  rwa [← add_assoc] at this

theorem dia_apply (ξ : GL (Fin 3) ℚ) (i j : Fin 3) :
    (dia ξ : M3A) i j = algebraMap ℚ 𝔸[ℚ] ((ξ : Matrix (Fin 3) (Fin 3) ℚ) i j) :=
  AdelicGLn.diagonal_apply ℚ 3 ξ i j

theorem dia_det (ξ : GL (Fin 3) ℚ) :
    (dia ξ : M3A).det = algebraMap ℚ 𝔸[ℚ] (ξ : Matrix (Fin 3) (Fin 3) ℚ).det := by
  rw [RingHom.map_det]
  congr 1

theorem upper_zero {β : G3} (hβ : β ∈ (Reduction.adelicBorel : Subgroup G3)) {i j : Fin 3} (h : j < i) :
    (β : M3A) i j = 0 :=
  (Reduction.mem_adelicBorel.1 hβ) h

theorem upper_det {β : G3} (hβ : β ∈ (Reduction.adelicBorel : Subgroup G3)) :
    (β : M3A).det = (β : M3A) 0 0 * (β : M3A) 1 1 * (β : M3A) 2 2 := by
  rw [Matrix.det_of_upperTriangular (Reduction.mem_adelicBorel.1 hβ), Fin.prod_univ_three]

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (γ : GL (Fin 2) ℚ) :
    ((e1 γ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![(γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1, 0;
        (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1, 0; 0, 0, 1] := rfl

theorem beta_apply {ξ : GL (Fin 3) ℚ} {m β : G3} (e : dia ξ * m = β) (i j : Fin 3) :
    (β : M3A) i j = algebraMap ℚ 𝔸[ℚ] ((ξ : Matrix (Fin 3) (Fin 3) ℚ) i 0) * (m : M3A) 0 j +
      algebraMap ℚ 𝔸[ℚ] ((ξ : Matrix (Fin 3) (Fin 3) ℚ) i 1) * (m : M3A) 1 j +
      algebraMap ℚ 𝔸[ℚ] ((ξ : Matrix (Fin 3) (Fin 3) ℚ) i 2) * (m : M3A) 2 j := by
  rw [← e, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, dia_apply, dia_apply, dia_apply]

theorem beta_det {ξ : GL (Fin 3) ℚ} {m β : G3} (e : dia ξ * m = β) :
    (β : M3A).det = algebraMap ℚ 𝔸[ℚ] (ξ : Matrix (Fin 3) (Fin 3) ℚ).det * (m : M3A).det := by
  rw [← e, Units.val_mul, Matrix.det_mul, dia_det]

theorem algU (γ : GL (Fin 2) ℚ) {m β : G3} (hβ : β ∈ (Reduction.adelicBorel : Subgroup G3))
    (e : dia (e1 γ) * m = β) (t1 t2 t3 : (𝔸[ℚ])ˣ) (h1 : (β : M3A) 0 0 = t1) (h2 : (β : M3A) 1 1 = t2)
    (h3 : (β : M3A) 2 2 = t3) :
    algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) =
        ((t2 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * ((m : M3A) 2 2 ^ 2 * (m : M3A) 0 0 *
          ((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ)) ∧
      algebraMap ℚ 𝔸[ℚ] (-(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) =
        ((t2 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * ((m : M3A) 2 2 ^ 2 * (m : M3A) 1 0 *
          ((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ)) ∧
      algebraMap ℚ 𝔸[ℚ] (γ : Matrix (Fin 2) (Fin 2) ℚ).det =
        ((t1 * t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * ((t2 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) ^ 2 *
          ((m : M3A) 2 2 ^ 3 * ((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ)) ∧
      (m : M3A) 2 0 = 0 ∧ (m : M3A) 2 1 = 0 ∧ (m : M3A) 2 2 = t3 ∧
      algebraMap ℚ 𝔸[ℚ] (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 0 0 =
        algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * t1 ∧
      algebraMap ℚ 𝔸[ℚ] (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 1 0 =
        -algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * t1 := by
  set A := algebraMap ℚ 𝔸[ℚ]
  have hb : ∀ i j, (β : M3A) i j = _ := beta_apply e
  have r20 : (m : M3A) 2 0 = 0 := by
    have x := hb 2 0; simp [orderedCechToCatCochainsOne_apply_valueAtSubset] at x; rw [← x]; exact upper_zero hβ (by decide)
  have r21 : (m : M3A) 2 1 = 0 := by
    have x := hb 2 1; simp [orderedCechToCatCochainsOne_apply_valueAtSubset] at x; rw [← x]; exact upper_zero hβ (by decide)
  have r22 : (m : M3A) 2 2 = t3 := by
    have x := hb 2 2; simp [orderedCechToCatCochainsOne_apply_valueAtSubset] at x; rw [← x]; exact h3
  have f10 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 0 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 1 0 = 0 := by
    have x := hb 1 0; simp [orderedCechToCatCochainsOne_apply_valueAtSubset] at x; rw [← x]; exact upper_zero hβ (by decide)
  have f00 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * (m : M3A) 0 0 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * (m : M3A) 1 0 = t1 := by
    have x := hb 0 0; simp [orderedCechToCatCochainsOne_apply_valueAtSubset] at x; rw [← x]; exact h1
  have hdγ : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det =
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) -
        A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) := by
    rw [Matrix.det_fin_two]; simp [A, map_sub, map_mul]
  have hdξ : ((e1 γ : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).det = (γ : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [orderedCechToCatCochainsOne_apply_valueAtSubset, Matrix.det_fin_three, Matrix.det_fin_two]; simp
  have hdet : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A).det = t1 * t2 * t3 := by
    rw [← hdξ, ← beta_det e, upper_det hβ, h1, h2, h3]
  have h00 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 0 0 = A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * t1 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * f00 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * f10
  have h10 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 1 0 = -A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * t1 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * f10 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * f00
  have i1 : (t1 : 𝔸[ℚ]) * ((t1⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := Units.mul_inv t1
  have i2 : (t2 : 𝔸[ℚ]) * ((t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := Units.mul_inv t2
  have i3 : (t3 : 𝔸[ℚ]) * ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := Units.mul_inv t3
  have iD : (m : M3A).det * (((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := by
    rw [← AdelicGLn.coe_det]; exact Units.mul_inv _
  set Dinv : 𝔸[ℚ] := (((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  set dm := (m : M3A).det
  set t1i : 𝔸[ℚ] := ((t1⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  set t2i : 𝔸[ℚ] := ((t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  set t3i : 𝔸[ℚ] := ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  refine ⟨?_, ?_, ?_, r20, r21, r22, h00, h10⟩
  · rw [r22, Units.val_mul]
    linear_combination (-(t1i * Dinv * dm)) * h00 + (t1i * Dinv * (m : M3A) 0 0) * hdet +
      ((t2 : 𝔸[ℚ]) * t3 * (m : M3A) 0 0 * Dinv - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * dm * Dinv) * i1 -
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * iD - ((t2 : 𝔸[ℚ]) * t3 * (m : M3A) 0 0 * Dinv) * i3
  · rw [r22, Units.val_mul, map_neg]
    linear_combination (-(t1i * Dinv * dm)) * h10 + (t1i * Dinv * (m : M3A) 1 0) * hdet +
      ((t2 : 𝔸[ℚ]) * t3 * (m : M3A) 1 0 * Dinv + A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * dm * Dinv) * i1 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * iD - ((t2 : 𝔸[ℚ]) * t3 * (m : M3A) 1 0 * Dinv) * i3
  · rw [r22, Units.val_mul, Units.val_mul]
    linear_combination (-A (γ : Matrix (Fin 2) (Fin 2) ℚ).det) * iD + Dinv * hdet -
      ((t1 : 𝔸[ℚ]) * t2 * t3 * Dinv * ((t3 : 𝔸[ℚ]) * t3i) ^ 2) * i2 -
      ((t1 : 𝔸[ℚ]) * t2 * t3 * Dinv * ((t3 : 𝔸[ℚ]) * t3i + 1)) * i3

theorem contEnt (i j : Fin 3) : Continuous fun m : G3 => (m : M3A) i j :=
  Reduction.continuous_GL_apply i j

theorem contDinv : Continuous fun m : G3 => (((AdelicGLn.det ℚ 3 m)⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) :=
  Units.continuous_coe_inv.comp (AdelicGLn.continuous_det ℚ 3)

theorem compact_C {Kc : Set G3} (hKc : IsCompact Kc) :
    IsCompact ((fun p : G3 × G3 => p.1 * p.2⁻¹) '' (Kc ×ˢ ((Reduction.maxCompact : Subgroup G3) : Set G3))) := by
  have := AdelicGLn.isTopologicalGroup ℚ 3
  exact (hKc.prod Reduction.isCompact_maxCompact).image (continuous_fst.mul continuous_snd.inv)

theorem poly_gen (t1 t2 t3 : (𝔸[ℚ])ˣ) {X1 X3 : ℝ} (hX1 : 0 < X1)
    (h1 : X1 ≤ (IdeleGroup.ideleModule ℚ t1 : ℝ)) (h3 : (IdeleGroup.ideleModule ℚ t3 : ℝ) ≤ X3) :
    ((IdeleGroup.ideleModule ℚ (t1 * t2⁻¹) : ℝ) * IdeleGroup.ideleModule ℚ (t2 * t3⁻¹))⁻¹ ≤ X3 / X1 := by
  have e : ((IdeleGroup.ideleModule ℚ (t1 * t2⁻¹) : ℝ) * IdeleGroup.ideleModule ℚ (t2 * t3⁻¹)) =
      (IdeleGroup.ideleModule ℚ t1 : ℝ) / IdeleGroup.ideleModule ℚ t3 := by
    have hg : t1 * t2⁻¹ * (t2 * t3⁻¹) = t1 * t3⁻¹ := by group
    have := congrArg (fun x => ((IdeleGroup.ideleModule ℚ x : ℝ))) hg
    simp only [map_mul, map_inv, Positive.val_mul, Positive.coe_inv] at this ⊢
    rw [div_eq_mul_inv]
    linear_combination this
  have p1 := (IdeleGroup.ideleModule ℚ t1).2
  have p3 := (IdeleGroup.ideleModule ℚ t3).2
  rw [e, inv_div]
  exact div_le_div₀ (by linarith) h3 hX1 h1

theorem adelicNorm_row (t : (𝔸[ℚ])ˣ) :
    Reduction.adelicNorm ((t : 𝔸[ℚ]) • (Pi.single 2 (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ])) = IdeleGroup.ideleModule ℚ t := by
  rw [Reduction.adelicNorm_smul (Reduction.hasFiniteContent_single_one 2), Reduction.adelicNorm_single_one, mul_one]

def ιU (q : NQ) : ℚ × ℚ × ℚ :=
  ((q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1, -(q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0,
    (q.out : Matrix (Fin 2) (Fin 2) ℚ).det)

theorem ιU_inj : Function.Injective ιU := by
  intro q q' h
  simp only [ιU, Prod.mk.injEq, neg_inj] at h
  exact GlobalTheory.T.rat_double_coset_eq_of_row_det q q' h.2.1 h.1 h.2.2

theorem det_ne_zero' (γ : GL (Fin 2) ℚ) : (γ : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

theorem row_two {m : G3} {t : (𝔸[ℚ])ˣ} (r20 : (m : M3A) 2 0 = 0) (r21 : (m : M3A) 2 1 = 0)
    (r22 : (m : M3A) 2 2 = t) :
    (Pi.single 2 (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ]) ᵥ* (m : M3A) = (t : 𝔸[ℚ]) • (Pi.single 2 (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ]) := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Pi.single_apply, r20, r21, r22]

theorem xiV_apply (γ : GL (Fin 2) ℚ) :
    ((e2 γ * sw : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ) =
      !![0, 1, 0; (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0, 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1;
        (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e2, b2M, sw, Matrix.mul_apply, Fin.sum_univ_three]

theorem algV (γ : GL (Fin 2) ℚ) {m β : G3} (hβ : β ∈ (Reduction.adelicBorel : Subgroup G3))
    (e : dia (e2 γ * sw) * m = β) (t1 t2 t3 : (𝔸[ℚ])ˣ) (h1 : (β : M3A) 0 0 = t1) (h2 : (β : M3A) 1 1 = t2)
    (h3 : (β : M3A) 2 2 = t3) :
    algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 / (γ : Matrix (Fin 2) (Fin 2) ℚ).det) =
        ((t1 * t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * (-(m : M3A) 2 1 * ((m⁻¹ : G3) : M3A) 0 1) ∧
      algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 / (γ : Matrix (Fin 2) (Fin 2) ℚ).det) =
        ((t1 * t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * ((m : M3A) 0 1 * ((m⁻¹ : G3) : M3A) 0 1) ∧
      algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ).det)⁻¹ =
        ((t2 * t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) * ((t1 * t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) ^ 2 *
          (-(m : M3A).det * ((m⁻¹ : G3) : M3A) 0 1 ^ 3) ∧
      (m : M3A) 0 0 = 0 ∧ (m : M3A) 1 0 = t1 ∧ (m : M3A) 2 0 = 0 ∧
      algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 1 +
        algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 2 1 = 0 ∧
      algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 2 +
        algebraMap ℚ 𝔸[ℚ] ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 2 2 = t3 := by
  set A := algebraMap ℚ 𝔸[ℚ]
  have hδ : (γ : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero
  have hi : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * A ((γ : Matrix (Fin 2) (Fin 2) ℚ).det)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  have hb : ∀ i j, (β : M3A) i j = _ := beta_apply e
  have f00 : (m : M3A) 1 0 = t1 := by
    have x := hb 0 0; rw [xiV_apply] at x; simp at x; rw [← x]; exact h1
  have f10 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * (m : M3A) 0 0 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * (m : M3A) 2 0 = 0 := by
    have x := hb 1 0; rw [xiV_apply] at x; simp at x; rw [← x]; exact upper_zero hβ (by decide)
  have f20 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 0 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 2 0 = 0 := by
    have x := hb 2 0; rw [xiV_apply] at x; simp at x; rw [← x]; exact upper_zero hβ (by decide)
  have f11 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * (m : M3A) 0 1 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * (m : M3A) 2 1 = t2 := by
    have x := hb 1 1; rw [xiV_apply] at x; simp at x; rw [← x]; exact h2
  have f21 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 1 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 2 1 = 0 := by
    have x := hb 2 1; rw [xiV_apply] at x; simp at x; rw [← x]; exact upper_zero hβ (by decide)
  have f22 : A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * (m : M3A) 0 2 +
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * (m : M3A) 2 2 = t3 := by
    have x := hb 2 2; rw [xiV_apply] at x; simp at x; rw [← x]; exact h3
  have hdγ : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det =
      A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) -
        A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) := by
    rw [Matrix.det_fin_two]; simp [A, map_sub, map_mul]
  have hdξ : ((e2 γ * sw : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).det = -(γ : Matrix (Fin 2) (Fin 2) ℚ).det := by
    rw [xiV_apply, Matrix.det_fin_three, Matrix.det_fin_two]; simp; ring
  have hdet : -A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A).det = t1 * t2 * t3 := by
    rw [← map_neg, ← hdξ, ← beta_det e, upper_det hβ, h1, h2, h3]
  have hm00 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 0 0 = 0 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * f10 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * f20
  have hm20 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 2 0 = 0 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * f20 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * f10
  have hm01 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 0 1 = A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * t2 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * f11 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 1) * f21
  have hm21 : A (γ : Matrix (Fin 2) (Fin 2) ℚ).det * (m : M3A) 2 1 = -A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * t2 := by
    rw [hdγ]; linear_combination A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 0 0) * f21 - A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * f11
  set Ai := A ((γ : Matrix (Fin 2) (Fin 2) ℚ).det)⁻¹
  have z00 : (m : M3A) 0 0 = 0 := by linear_combination Ai * hm00 - (m : M3A) 0 0 * hi
  have z20 : (m : M3A) 2 0 = 0 := by linear_combination Ai * hm20 - (m : M3A) 2 0 * hi
  have p : ((m⁻¹ : G3) : M3A) 0 1 * t1 = 1 := by
    have x : ((m⁻¹ * m : G3) : M3A) 0 0 = 1 := by rw [inv_mul_cancel]; simp
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, z00, z20, f00] at x
    simpa using x
  have i2 : (t2 : 𝔸[ℚ]) * ((t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := Units.mul_inv t2
  have i3 : (t3 : 𝔸[ℚ]) * ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]) = 1 := Units.mul_inv t3
  set mi := ((m⁻¹ : G3) : M3A) 0 1
  set t2i : 𝔸[ℚ] := ((t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  set t3i : 𝔸[ℚ] := ((t3⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ])
  set dm := (m : M3A).det
  refine ⟨?_, ?_, ?_, z00, f00, z20, f21, f22⟩
  · rw [div_eq_mul_inv, map_mul, Units.val_mul]
    linear_combination (-A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0) * Ai) * i2 + (t2i * Ai) * hm21 -
      ((m : M3A) 2 1 * t2i) * hi + ((m : M3A) 2 1 * t2i) * p
  · rw [div_eq_mul_inv, map_mul, Units.val_mul]
    linear_combination (-A ((γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1) * Ai) * i2 - (t2i * Ai) * hm01 +
      ((m : M3A) 0 1 * t2i) * hi - ((m : M3A) 0 1 * t2i) * p
  · rw [Units.val_mul, Units.val_mul]
    linear_combination (-Ai - (-dm * mi * t2i * t3i) * (mi * t1 + 1) * ((t2 : 𝔸[ℚ]) * t2i)) * p +
      (-Ai * (mi * t1) - (-dm * mi * t2i * t3i)) * i2 + (-Ai * (mi * t1) * ((t2 : 𝔸[ℚ]) * t2i)) * i3 +
      (-Ai * mi * t2i * t3i) * hdet + (-dm * mi * t2i * t3i) * hi

theorem adelicNorm_single_smul (i : Fin 3) (t : (𝔸[ℚ])ˣ) :
    Reduction.adelicNorm ((t : 𝔸[ℚ]) • (Pi.single i (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ])) = IdeleGroup.ideleModule ℚ t := by
  rw [Reduction.adelicNorm_smul (Reduction.hasFiniteContent_single_one i), Reduction.adelicNorm_single_one, mul_one]

def ιV (q : NQ) : ℚ × ℚ × ℚ :=
  ((q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 / (q.out : Matrix (Fin 2) (Fin 2) ℚ).det,
    (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 / (q.out : Matrix (Fin 2) (Fin 2) ℚ).det,
    ((q.out : Matrix (Fin 2) (Fin 2) ℚ).det)⁻¹)

theorem ιV_inj : Function.Injective ιV := by
  intro q q' h
  simp only [ιV, Prod.mk.injEq, _root_.inv_inj] at h
  obtain ⟨hc, hd, hδ⟩ := h
  rw [hδ] at hc hd
  have h0 := det_ne_zero' q'.out
  refine GlobalTheory.T.rat_double_coset_eq_of_row_det q q' ?_ ?_ hδ
  · exact (div_left_inj' h0).1 hc
  · exact (div_left_inj' h0).1 hd

theorem contMi : Continuous fun m : G3 => ((m⁻¹ : G3) : M3A) 0 1 := by
  have := AdelicGLn.isTopologicalGroup ℚ 3
  exact (Reduction.continuous_GL_apply 0 1).comp continuous_inv

theorem contDet : Continuous fun m : G3 => (m : M3A).det :=
  Continuous.matrix_det Units.continuous_val

end majorantEstimates

open majorantEstimates in
theorem majorant_first_holds : MajU := by
  intro V hV W hW Kc hKc
  obtain ⟨Ω, hΩ, T, hg⟩ := hV.gauge W hW
  obtain ⟨Cg, hCg⟩ := hg (3 * (T + 3))
  set C := (fun p : G3 × G3 => p.1 * p.2⁻¹) '' (Kc ×ˢ ((Reduction.maxCompact : Subgroup G3) : Set G3))
    with hCdef
  have hC : IsCompact C := compact_C hKc
  obtain ⟨P, hP, hPb⟩ := Reduction.exists_adelicNorm_vecMul_le_mul hC
  obtain ⟨ε, hε, hεb⟩ := GlobalTheory.T.compact_adelic_column_norm_lower C hC
  obtain ⟨M, hM, K, hK⟩ := core hΩ hC
    ((((contEnt 2 2).pow 2).mul (contEnt 0 0)).mul contDinv)
    ((((contEnt 2 2).pow 2).mul (contEnt 1 0)).mul contDinv)
    (((contEnt 2 2).pow 3).mul contDinv) T Cg (P / ε) (div_nonneg hP.le hε.le)
  refine ⟨fun q => K * F M (ιU q), ((summable_F M hM).comp_injective ιU_inj).mul_left K, ?_⟩
  intro q g hg
  obtain ⟨β, hβ, k, hk, hh⟩ := Reduction.exists_adelicBorel_mul_maxCompact (dia (e1 q.out) * g)
  set t1 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 0).unit with ht1
  set t2 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 1).unit with ht2
  set t3 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 2).unit with ht3
  have h1 : (β : M3A) 0 0 = t1 := (IsUnit.unit_spec _).symm
  have h2 : (β : M3A) 1 1 = t2 := (IsUnit.unit_spec _).symm
  have h3 : (β : M3A) 2 2 = t3 := (IsUnit.unit_spec _).symm
  have e : dia (e1 q.out) * (g * k⁻¹) = β := by rw [← mul_assoc, hh, mul_inv_cancel_right]
  have hmC : g * k⁻¹ ∈ C := ⟨(g, k), ⟨hg, hk⟩, rfl⟩
  obtain ⟨a0, a1, a2, r20, r21, r22, h00, h10⟩ := algU q.out hβ e t1 t2 t3 h1 h2 h3
  rw [hh, GlobalTheory.T.whittaker_norm_diagonal_reduction V hV W hW β hβ t1 t2 t3 h1 h2 h3 k]
  have hgau := hCg (t1 * t2⁻¹) (t2 * t3⁻¹) k hk Rat.infinitePlace
  set γ := q.out with hγ
  set m := g * k⁻¹ with hmdef
  set z : Fin 3 → ℚ := ![(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1, -(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, 0]
    with hzdef
  have hz : ∀ i, z i = 0 ∨ z i = (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 ∨
      z i = -(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 := by
    intro i; fin_cases i <;> simp [z]
  have hz0 : z ≠ 0 := by
    intro h0
    have c0 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
      have := congrFun h0 1; simpa [z] using this
    have d0 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 := by
      have := congrFun h0 0; simpa [z] using this
    exact det_ne_zero' γ (by rw [Matrix.det_fin_two, c0, d0]; ring)
  set δ := (γ : Matrix (Fin 2) (Fin 2) ℚ).det with hδdef
  have hδ : δ ≠ 0 := det_ne_zero' γ
  have hi : algebraMap ℚ 𝔸[ℚ] δ * algebraMap ℚ 𝔸[ℚ] δ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hδ, map_one]
  have hcol : (fun i => (m : M3A) i 0) = (t1 : 𝔸[ℚ]) • Reduction.ratVec (δ⁻¹ • z) := by
    ext i; fin_cases i
    · simp [Reduction.ratVec, z, map_mul]
      linear_combination (algebraMap ℚ 𝔸[ℚ] δ⁻¹) * h00 - (m : M3A) 0 0 * hi
    · simp [Reduction.ratVec, z, map_mul, map_neg]
      linear_combination (algebraMap ℚ 𝔸[ℚ] δ⁻¹) * h10 - (m : M3A) 1 0 * hi
    · simp [Reduction.ratVec, z, r20]
  have hz1 : δ⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero hδ) hz0
  set H := Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) with hHdef
  have hH1 : 1 ≤ H := Reduction.one_le_adelicNorm_ratVec hz0
  have hnorm : Reduction.adelicNorm (fun i => (m : M3A) i 0) = IdeleGroup.ideleModule ℚ t1 * H := by
    rw [hcol, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz1), Reduction.ratVec_smul,
      Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec hz0) (inv_ne_zero hδ)]
  have hε1 : ε / H ≤ IdeleGroup.ideleModule ℚ t1 := by
    rw [div_le_iff₀ (by linarith)]; rw [← hnorm]; exact (hεb m hmC 0).2
  have hP3 : (IdeleGroup.ideleModule ℚ t3 : ℝ) ≤ P := by
    have := hPb m hmC _ (Reduction.hasFiniteContent_single_one 2)
    rw [row_two r20 r21 r22, adelicNorm_row, Reduction.adelicNorm_single_one, mul_one] at this
    exact this
  have hpoly := poly_gen t1 t2 t3 (div_pos hε (by linarith)) hε1 hP3
  have hpoly' : ((IdeleGroup.ideleModule ℚ (t1 * t2⁻¹) : ℝ) * IdeleGroup.ideleModule ℚ (t2 * t3⁻¹))⁻¹ ≤
      P / ε * H := by
    refine hpoly.trans (le_of_eq ?_)
    field_simp
  exact hK _ (t1 * t2⁻¹) (t2 * t3⁻¹) m hmC _ _ _ z a0 a1 a2 hz hpoly' hgau.1
    (fun h => hgau.2 (fun h' => h (by rw [h', norm_zero])))

open majorantEstimates in
theorem majorant_second_holds : MajV := by
  intro V hV W hW Kc hKc
  obtain ⟨Ω, hΩ, T, hg⟩ := hV.gauge W hW
  obtain ⟨Cg, hCg⟩ := hg (3 * (T + 3))
  set C := (fun p : G3 × G3 => p.1 * p.2⁻¹) '' (Kc ×ˢ ((Reduction.maxCompact : Subgroup G3) : Set G3))
    with hCdef
  have hC : IsCompact C := compact_C hKc
  obtain ⟨P, hP, hPb⟩ := Reduction.exists_adelicNorm_vecMul_le_mul hC
  obtain ⟨ε, hε, hεb⟩ := GlobalTheory.T.compact_adelic_column_norm_lower C hC
  obtain ⟨M, hM, K, hK⟩ := core hΩ hC
    (((contEnt 2 1).neg).mul contMi) ((contEnt 0 1).mul contMi) ((contDet.neg).mul (contMi.pow 3))
    T Cg (P / ε) (div_nonneg hP.le hε.le)
  refine ⟨fun q => K * F M (ιV q), ((summable_F M hM).comp_injective ιV_inj).mul_left K, ?_⟩
  intro q g hg
  obtain ⟨β, hβ, k, hk, hh⟩ := Reduction.exists_adelicBorel_mul_maxCompact (dia (e2 q.out * sw) * g)
  set t1 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 0).unit with ht1
  set t2 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 1).unit with ht2
  set t3 := (Reduction.isUnit_apply_self_of_mem_adelicBorel hβ 2).unit with ht3
  have h1 : (β : M3A) 0 0 = t1 := (IsUnit.unit_spec _).symm
  have h2 : (β : M3A) 1 1 = t2 := (IsUnit.unit_spec _).symm
  have h3 : (β : M3A) 2 2 = t3 := (IsUnit.unit_spec _).symm
  have e : dia (e2 q.out * sw) * (g * k⁻¹) = β := by rw [← mul_assoc, hh, mul_inv_cancel_right]
  have hmC : g * k⁻¹ ∈ C := ⟨(g, k), ⟨hg, hk⟩, rfl⟩
  obtain ⟨v0, v1, v2, z00, f00, z20, g1, g2⟩ := algV q.out hβ e t1 t2 t3 h1 h2 h3
  rw [hh, GlobalTheory.T.whittaker_norm_diagonal_reduction V hV W hW β hβ t1 t2 t3 h1 h2 h3 k]
  have hgau := hCg (t1 * t2⁻¹) (t2 * t3⁻¹) k hk Rat.infinitePlace
  set γ := q.out with hγ
  set m := g * k⁻¹ with hmdef
  set δ := (γ : Matrix (Fin 2) (Fin 2) ℚ).det with hδdef
  have hδ : δ ≠ 0 := det_ne_zero' γ
  set z : Fin 3 → ℚ := ![(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 / δ, 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 / δ]
    with hzdef
  set y0 : Fin 3 → ℚ := ![(γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0, 0, (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1]
    with hy0def
  have hz : ∀ i, z i = 0 ∨ z i = (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 / δ ∨
      z i = (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 / δ := by
    intro i; fin_cases i <;> simp [z]
  have hy0 : y0 ≠ 0 := by
    intro h0
    have c0 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0 := by
      have := congrFun h0 0; simpa [y0] using this
    have d0 : (γ : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0 := by
      have := congrFun h0 2; simpa [y0] using this
    exact hδ (by rw [hδdef, Matrix.det_fin_two, c0, d0]; ring)
  have hzy : z = δ⁻¹ • y0 := by
    ext i; fin_cases i <;> simp [z, y0, div_eq_inv_mul]
  set H := Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) with hHdef
  have hH : H = Reduction.adelicNorm (Reduction.ratVec y0 : Fin 3 → 𝔸[ℚ]) := by
    rw [hHdef, hzy, Reduction.ratVec_smul,
      Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec hy0) (inv_ne_zero hδ)]
  have hcol : (fun i => (m : M3A) i 0) = (t1 : 𝔸[ℚ]) • (Pi.single 1 (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ]) := by
    ext i; fin_cases i <;> simp [z00, f00, z20]
  have hε1 : ε ≤ IdeleGroup.ideleModule ℚ t1 := by
    have := (hεb m hmC 0).2
    rwa [hcol, adelicNorm_single_smul] at this
  have hrow : Reduction.ratVec y0 ᵥ* (m : M3A) = (t3 : 𝔸[ℚ]) • (Pi.single 2 (1 : 𝔸[ℚ]) : Fin 3 → 𝔸[ℚ]) := by
    ext j
    fin_cases j
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Reduction.ratVec, y0, z00, z20]
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Reduction.ratVec, y0]
      linear_combination g1
    · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_three, Reduction.ratVec, y0]
      linear_combination g2
  have hP3 : (IdeleGroup.ideleModule ℚ t3 : ℝ) ≤ P * H := by
    have := hPb m hmC _ (Reduction.hasFiniteContent_ratVec hy0)
    rw [hrow, adelicNorm_single_smul, ← hH] at this
    exact this
  have hpoly := poly_gen t1 t2 t3 hε hε1 hP3
  have hpoly' : ((IdeleGroup.ideleModule ℚ (t2 * t3⁻¹) : ℝ) * IdeleGroup.ideleModule ℚ (t1 * t2⁻¹))⁻¹ ≤
      P / ε * H := by
    rw [mul_comm]
    refine hpoly.trans (le_of_eq ?_)
    ring
  have hg1 := hgau.1
  rw [mul_comm ((IdeleGroup.ideleModule ℚ (t1 * t2⁻¹) : ℝ)),
    mul_comm (1 + ‖((t1 * t2⁻¹ : (𝔸[ℚ])ˣ) : 𝔸[ℚ]).1 Rat.infinitePlace‖)] at hg1
  exact hK _ (t2 * t3⁻¹) (t1 * t2⁻¹) m hmC _ _ _ z v0 v1 v2 hz hpoly' hg1
    (fun h => (hgau.2 (fun h' => h (by rw [h', norm_zero]))).symm)

end Ad3.GA
