import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma Kset_sub {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]

lemma UJ_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

lemma symm_inter (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) :
    ∀ g ∈ UJset ε, ∀ v, T.symm (σ g v) = σ' g (T.symm v) := by
  intro g hg v
  apply T.injective
  rw [h g hg]; simp

lemma wt_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ' μ v) : IsWtOn (Kset ε) σ μ (T v) := by
  intro θ hθ
  rw [← h _ (Kset_sub hθ), hv θ hθ, map_smul]

lemma ktype_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : IsKTypeOf ε σ' Λ S) :
    IsKTypeOf ε σ Λ (S.map (T.toLinearEquiv : H →ₗ[ℂ] H)) := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ' g x, h2 g hg x hx, h g (Kset_sub hg) x⟩
  · intro S' hle hst
    rcases h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H)) (by
        intro x hx
        obtain ⟨y, hy, e⟩ := hle hx
        have : y = x := T.injective e
        exact this ▸ hy) (by
        intro g hg x hx
        show T (σ' g x) ∈ S'
        rw [h g (Kset_sub hg)]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T (T.symm x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← e] at hx
      exact hx
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hw
    have := wt_transfer T.symm (symm_inter T h) hw
    refine h5 μ x hx (by rintro rfl; simp at h0) ?_
    simpa using this

theorem isDS_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {lam : Fin n → ℝ}
    (hσ : IsDS ε lam σ) : IsDS ε lam σ' := by
  obtain ⟨c1, c2, ⟨⟨r1, r2⟩, r3, r4⟩, c4, c5, ⟨S, hS⟩, c7⟩ := hσ
  have h' := symm_inter T h
  have e : ∀ g ∈ UJset ε, ∀ v, σ' g v = T.symm (σ g (T v)) := by
    intro g hg v; rw [← h g hg]; simp
  have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨c1, c2, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, ktype_transfer T.symm h' hS⟩,
    fun μ S' hS' => c7 μ _ (ktype_transfer T h hS')⟩
  · ext v; rw [e 1 one, r1]; simp
  · intro a ha b hb
    ext v
    rw [ContinuousLinearMap.comp_apply, e _ (UJ_mul ha hb), e a ha, e b hb, r2 a ha b hb]; simp
  · intro g hg v
    rw [e g hg]; simp [r3 g hg]
  · intro v
    exact (T.symm.continuous.comp_continuousOn (r4 (T v))).congr fun g hg => e g hg v
  · intro S' hcl hst
    rcases c4 (S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H)) (hcl.preimage T.symm.continuous) (by
        intro g hg x hx
        show T.symm (σ g x) ∈ S'
        rw [h' g hg]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T.symm (T x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      rw [eq_top_iff]
      intro x _
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by rw [e]; trivial
      have h2 : T.symm (T x) ∈ S' := this
      simpa using h2
  · intro v w
    have : coefOn (ε := ε) σ' v w = coefOn (ε := ε) σ (T v) (T w) := by
      funext g
      show ⟪w, σ' (umat g) v⟫_ℂ = ⟪T w, σ (umat g) (T v)⟫_ℂ
      rw [← h _ g.2, T.inner_map_map]
    rw [this]; exact c5 _ _

theorem isDS_conj {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ UJset ε) (hu' : u' ∈ UJset ε) (h1 : u * u' = 1) :
    IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨⟨r1, r2⟩, r3, -⟩ := hσ.2.2.1
  have hs : ∀ v, σ u (σ u' v) = v := by
    intro v
    have := r2 u hu u' hu'
    rw [h1, r1] at this
    simpa using (congrArg (fun A : H →L[ℂ] H => A v) this).symm
  let T : H ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofSurjective
    { toLinearMap := (σ u : H →ₗ[ℂ] H), norm_map' := r3 u hu } (fun v => ⟨σ u' v, hs v⟩)
  refine isDS_transfer T ?_ hσ
  intro g hg v
  show σ u (σ (u' * g * u) v) = σ g (σ u v)
  rw [r2 _ (UJ_mul hu' hg) u hu, r2 u' hu' g hg]
  simp [hs]

lemma card_even (r : ℕ) : ((range (2 * r + 2)).filter fun m => m % 2 = 0).card = r + 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2 * (r + 1) + 2 = 2 * r + 2 + 1 + 1 by ring, range_add_one, range_add_one, filter_insert,
      filter_insert, if_neg (by omega), if_pos (by omega), card_insert_of_notMem (by simp), ih]

lemma card_signs (k r : ℕ) (hk : 1 ≤ k) :
    (univ.filter fun i => PI.BesselPeriodGGP.eps48 k r i = true).card = k + r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [card_filter]
  have h : ∀ i : Fin (2 * r + (j + 1) + 1), (if PI.BesselPeriodGGP.eps48 (j + 1) r i = true then 1 else 0) =
      (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0) i.val := by
    intro i
    by_cases h1 : i.val < j <;> simp [PI.BesselPeriodGGP.eps48, h1]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0),
    show 2 * r + (j + 1) + 1 = j + (2 * r + 2) by ring, sum_range_add]
  have a : ∑ m ∈ range j, (if m < j ∨ (m - j) % 2 = 0 then 1 else 0) = j := by
    rw [sum_congr rfl (g := fun _ => 1) (fun m hm => if_pos (Or.inl (mem_range.1 hm)))]; simp
  have b : ∑ m ∈ range (2 * r + 2), (if j + m < j ∨ (j + m - j) % 2 = 0 then 1 else 0) = r + 1 := by
    rw [← card_even r, card_filter]
    refine sum_congr rfl fun m _ => ?_
    simp
  rw [a, b]; ring

theorem cayley_exists_and_any : ∀ (k r : ℕ), (1 ≤ k → ∃ Q, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q) ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q, PI.UpqRep.IsCayleyU k r ε Q → PI.UpqRep.IsDS ε mu (fun g => R.σ (Q⁻¹ * g * Q)) := by
  intro k r
  refine ⟨fun hk => (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r _).2 (card_signs k r hk), ?_⟩
  rintro ε mu R ⟨-, ⟨P, ⟨⟨-, hP⟩, hPu⟩, hD⟩, -⟩ Q ⟨⟨-, hQ⟩, hQu⟩
  have p1 : Pᴴ * P = 1 := (Matrix.mem_unitaryGroup_iff').1 hPu
  have p2 : P * Pᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hPu
  have q1 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQu
  have q2 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hQu
  have pi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv p1
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have gen : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * Bᴴ = 1 →
      Aᴴ * Jm ε * A = Bᴴ * Jm ε * B → A * Bᴴ ∈ UJset ε := by
    intro A B hB hAB
    show (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = Jm ε
    calc (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = B * (Aᴴ * Jm ε * A) * Bᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (B * Bᴴ) * Jm ε * (B * Bᴴ) := by rw [hAB]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hB]; simp
  have key := isDS_conj hD (gen Q P p2 (hQ.trans hP.symm)) (gen P Q q2 (hP.trans hQ.symm)) (by
    calc Q * Pᴴ * (P * Qᴴ) = Q * (Pᴴ * P) * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p1, Matrix.mul_one, q2])
  have e : (fun g => R.σ (Q⁻¹ * g * Q)) = fun g => R.σ (P⁻¹ * (P * Qᴴ * g * (Q * Pᴴ)) * P) := by
    funext g
    congr 1
    rw [pi, qi]
    calc Qᴴ * g * Q = (Pᴴ * P) * Qᴴ * g * Q * (Pᴴ * P) := by rw [p1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact key

end GlobalTheory.CayleyChoice
