import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
theorem _root_.GlobalTheory.CayleyChoice.Kset_sub {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ _root_.PI.UpqRep.Kset ε) : g ∈ _root_.PI.UpqRep.UJset ε := by
  have hg' : g ∈ unitaryGroup (Fin n) ℂ ∧ g * _root_.PI.UpqRep.Jm ε = _root_.PI.UpqRep.Jm ε * g := hg
  obtain ⟨hu, hc⟩ := hg'
  show gᴴ * _root_.PI.UpqRep.Jm ε * g = _root_.PI.UpqRep.Jm ε
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← star_eq_conjTranspose,
    (mem_unitaryGroup_iff').mp hu, Matrix.one_mul]

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
private theorem mul_mem_UJset_jet_harmonics {a b : Matrix (Fin n) (Fin n) ℂ}
    (ha : a ∈ _root_.PI.UpqRep.UJset ε) (hb : b ∈ _root_.PI.UpqRep.UJset ε) : a * b ∈ _root_.PI.UpqRep.UJset ε := by
  have ha' : aᴴ * _root_.PI.UpqRep.Jm ε * a = _root_.PI.UpqRep.Jm ε := ha
  have hb' : bᴴ * _root_.PI.UpqRep.Jm ε * b = _root_.PI.UpqRep.Jm ε := hb
  show (a * b)ᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = _root_.PI.UpqRep.Jm ε
  rw [conjTranspose_mul, show bᴴ * aᴴ * _root_.PI.UpqRep.Jm ε * (a * b) = bᴴ * (aᴴ * _root_.PI.UpqRep.Jm ε * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in
private theorem isKTypeOf_map_of_intertwining {σ₁ σ₂ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (e : H ≃ₗ[ℂ] H)
    (he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ₂ k (e x) = e (σ₁ k x)) {μ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : _root_.PI.UpqRep.IsKTypeOf ε σ₁ μ S) : _root_.PI.UpqRep.IsKTypeOf ε σ₂ μ (S.map (e : H →ₗ[ℂ] H)) := by
  obtain ⟨hfin, hinv, hirr, ⟨v, hvS, hv0, hvw⟩, hmax⟩ := hS
  have inv_map : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₁ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₂ (T.map (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨σ₁ k x, hT k hk x hx, (he k hk x).symm⟩
  have inv_comap : ∀ T : Submodule ℂ H, _root_.PI.UpqRep.IsKStableOn ε σ₂ T →
      _root_.PI.UpqRep.IsKStableOn ε σ₁ (T.comap (e : H →ₗ[ℂ] H)) := by
    intro T hT k hk x hx
    show e (σ₁ k x) ∈ T
    rw [← he k hk x]
    exact hT k hk _ hx
  have wt : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) := by
    intro ν x hx θ hθ
    rw [he _ hθ, hx θ hθ, map_smul]
  have wt' : ∀ (ν : Fin n → ℝ) (x : H), _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₂ ν (e x) →
      _root_.PI.UpqRep.IsWtOn (_root_.PI.UpqRep.Kset ε) σ₁ ν x := by
    intro ν x hx θ hθ
    apply e.injective
    rw [← he _ hθ, hx θ hθ, map_smul]
  refine ⟨?_, inv_map S hinv, ?_, ⟨e v, ⟨v, hvS, rfl⟩, by simpa using hv0, wt μ v hvw⟩, ?_⟩
  · haveI := hfin
    infer_instance
  · intro T hT hTinv
    have hle : T.comap (e : H →ₗ[ℂ] H) ≤ S := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hT hx
      rwa [← e.injective hxy]
    rcases hirr _ hle (inv_comap T hTinv) with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hy' : e.symm y ∈ T.comap (e : H →ₗ[ℂ] H) := by simpa using hy
      rw [h, Submodule.mem_bot] at hy'
      simpa using congrArg e hy'
    · right
      refine le_antisymm hT ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← h] at hx
      exact hx
  · intro ν y hy hy0 hyw
    obtain ⟨x, hx, rfl⟩ := hy
    exact hmax ν x hx (by rintro rfl; simp at hy0) (wt' ν x hyw)

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} in

theorem _root_.GlobalTheory.CayleyChoice.isDS_conj {lam : Fin n → ℝ} (hσ : _root_.PI.UpqRep.IsDS ε lam σ)
    {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ _root_.PI.UpqRep.UJset ε) (hu' : u' ∈ _root_.PI.UpqRep.UJset ε) (h1 : u * u' = 1) :
    _root_.PI.UpqRep.IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨hc, hnt, ⟨⟨h1σ, hmul⟩, hiso, hcont⟩, hirr, hL2, ⟨S, hS⟩, hmin⟩ := hσ
  have hu'u : u' * u = 1 := mul_eq_one_comm.mp h1
  have conj_mem : ∀ {g}, g ∈ _root_.PI.UpqRep.UJset ε → u' * g * u ∈ _root_.PI.UpqRep.UJset ε := fun hg =>
    mul_mem_UJset_jet_harmonics (mul_mem_UJset_jet_harmonics hu' hg) hu
  have hAB : ∀ x, σ u (σ u' x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu _ hu', h1, h1σ]
    rfl
  have hBA : ∀ x, σ u' (σ u x) = x := by
    intro x
    rw [← ContinuousLinearMap.comp_apply, ← hmul _ hu' _ hu, hu'u, h1σ]
    rfl
  have hconj : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x, σ (u' * g * u) x = σ u' (σ g (σ u x)) := by
    intro g hg x
    rw [hmul _ (mul_mem_UJset_jet_harmonics hu' hg) _ hu, hmul _ hu' _ hg]
    rfl
  have hinner : ∀ x y, ⟪σ u x, σ u y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    let L : H →ₗᵢ[ℂ] H := ⟨(σ u : H →ₗ[ℂ] H), hiso u hu⟩
    exact L.inner_map_map x y
  let e : H ≃ₗ[ℂ] H :=
    { toLinearMap := (σ u' : H →ₗ[ℂ] H)
      invFun := σ u
      left_inv := hAB
      right_inv := hBA }
  have he : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ (u' * k * u) (e x) = e (σ k x) := by
    intro k hk x
    show σ (u' * k * u) (σ u' x) = σ u' (σ k x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  have he' : ∀ k ∈ _root_.PI.UpqRep.Kset ε, ∀ x, σ k (e.symm x) = e.symm (σ (u' * k * u) x) := by
    intro k hk x
    show σ k (σ u x) = σ u (σ (u' * k * u) x)
    rw [hconj k (_root_.GlobalTheory.CayleyChoice.Kset_sub hk), hAB]
  refine ⟨hc, hnt, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, isKTypeOf_map_of_intertwining e he hS⟩, ?_⟩
  · show σ (u' * 1 * u) = 1
    rw [Matrix.mul_one, hu'u, h1σ]
  · intro a ha b hb
    show σ (u' * (a * b) * u) = σ (u' * a * u) ∘SL σ (u' * b * u)
    rw [← hmul _ (conj_mem ha) _ (conj_mem hb)]
    congr 1
    rw [show u' * a * u * (u' * b * u) = u' * a * (u * u') * b * u by
      simp only [Matrix.mul_assoc], h1, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  · intro g hg v
    exact hiso _ (conj_mem hg) v
  · intro v
    exact (hcont v).comp ((continuous_const.mul continuous_id).mul continuous_const).continuousOn
      (fun g hg => conj_mem hg)
  · intro T hTc hTinv
    have hT'c : IsClosed (↑(T.comap (σ u' : H →ₗ[ℂ] H)) : Set H) :=
      hTc.preimage (σ u').continuous
    have hT'inv : ∀ g ∈ _root_.PI.UpqRep.UJset ε, ∀ x ∈ T.comap (σ u' : H →ₗ[ℂ] H),
        σ g x ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
      intro g hg x hx
      have hx' : σ u' x ∈ T := hx
      show σ u' (σ g x) ∈ T
      have := hTinv g hg (σ u' x) hx'
      rw [show σ u' (σ g x) = σ (u' * g * u) (σ u' x) by rw [hconj g hg, hAB]]
      exact this
    rcases hirr _ hT'c hT'inv with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        show σ u' (σ u y) ∈ T
        rwa [hBA]
      rw [h, Submodule.mem_bot] at hmem
      rw [Submodule.mem_bot, ← hBA y, hmem, map_zero]
    · right
      rw [eq_top_iff]
      intro y _
      have hmem : σ u y ∈ T.comap (σ u' : H →ₗ[ℂ] H) := by
        rw [h]
        exact Submodule.mem_top
      have hmem' : σ u' (σ u y) ∈ T := hmem
      rwa [hBA] at hmem'
  · intro v w
    have key := hL2 (σ u v) (σ u w)
    convert key using 1
    funext g
    have hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ _root_.PI.UpqRep.UJset ε := g.2
    show ⟪w, σ (u' * _ * u) v⟫_ℂ = ⟪σ u w, σ _ (σ u v)⟫_ℂ
    rw [hconj _ hg, ← hinner, hAB]
  · intro μ T hT
    exact hmin μ _ (isKTypeOf_map_of_intertwining e.symm he' hT)

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CayleyChoice.cayley_exists_and_any : ∀ (k r : ℕ),
    (1 ≤ k → ∃ Q, _root_.PI.UpqRep.IsCayleyU k r (_root_.PI.BesselPeriodGGP.eps48 k r) Q) ∧
    ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ)
      (R : _root_.BranchingSupport.Rep k r),
      R.IsDS ε mu → ∀ Q, _root_.PI.UpqRep.IsCayleyU k r ε Q →
        _root_.PI.UpqRep.IsDS ε mu (fun g => R.σ (Q⁻¹ * g * Q)) := by
  intro k r
  refine ⟨fun hk => ?_, ?_⟩
  · rw [_root_.GlobalTheory.UnitaryCayley.exists_isCayleyU_iff]
    have hcount : ∀ m : ℕ, (∑ x ∈ range (2 * m + 2), if x % 2 = 0 then 1 else 0) = m + 1 := by
      intro m
      induction m with
      | zero => decide
      | succ m ih =>
        rw [show 2 * (m + 1) + 2 = 2 * m + 2 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
        have h1 : (2 * m + 2) % 2 = 0 := by omega
        have h2 : (2 * m + 2 + 1) % 2 ≠ 0 := by omega
        simp [h1, h2]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [card_filter]
    simp only [_root_.PI.BesselPeriodGGP.eps48, Nat.add_sub_cancel]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => if (if i < j then true else decide ((i - j) % 2 = 0)) = true then 1 else 0)]
    rw [show 2 * r + (j + 1) + 1 = j + (2 * r + 2) by ring, sum_range_add]
    have e1 : (∑ x ∈ range j,
        if (if x < j then true else decide ((x - j) % 2 = 0)) = true then 1 else 0) = j := by
      rw [sum_congr rfl (g := fun _ => 1) (fun x hx => by simp [mem_range.mp hx])]
      simp
    have e2 : (∑ x ∈ range (2 * r + 2),
        if (if j + x < j then true else decide ((j + x - j) % 2 = 0)) = true then 1 else 0)
          = r + 1 := by
      rw [← hcount r]
      refine sum_congr rfl (fun x _ => ?_)
      simp
    rw [e1, e2]
    ring
  · intro ε mu R hR Q hQ
    obtain ⟨_, P, hP, hDS⟩ := hR
    have hPd : IsUnit P ∧ Pᴴ * _root_.PI.UpqRep.Jm ε * P = _root_.PI.UpqRep.Hpk k r := hP.1
    have hQd : IsUnit Q ∧ Qᴴ * _root_.PI.UpqRep.Jm ε * Q = _root_.PI.UpqRep.Hpk k r := hQ.1
    have hPi : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hPd.1)
    have hPi' : P⁻¹ * P = 1 := nonsing_inv_mul P ((isUnit_iff_isUnit_det P).mp hPd.1)
    have hQi : Q * Q⁻¹ = 1 := mul_nonsing_inv Q ((isUnit_iff_isUnit_det Q).mp hQd.1)
    have mem : ∀ {A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ},
        Aᴴ * _root_.PI.UpqRep.Jm ε * A = _root_.PI.UpqRep.Hpk k r → Bᴴ * _root_.PI.UpqRep.Jm ε * B = _root_.PI.UpqRep.Hpk k r →
          B * B⁻¹ = 1 → A * B⁻¹ ∈ _root_.PI.UpqRep.UJset ε := by
      intro A B hA hB hBB
      show (A * B⁻¹)ᴴ * _root_.PI.UpqRep.Jm ε * (A * B⁻¹) = _root_.PI.UpqRep.Jm ε
      rw [conjTranspose_mul, show (B⁻¹)ᴴ * Aᴴ * _root_.PI.UpqRep.Jm ε * (A * B⁻¹)
          = (B⁻¹)ᴴ * (Aᴴ * _root_.PI.UpqRep.Jm ε * A) * B⁻¹ by simp only [Matrix.mul_assoc], hA, ← hB,
        show (B⁻¹)ᴴ * (Bᴴ * _root_.PI.UpqRep.Jm ε * B) * B⁻¹ = (B * B⁻¹)ᴴ * _root_.PI.UpqRep.Jm ε * (B * B⁻¹) by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc],
        hBB, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have hprod : Q * P⁻¹ * (P * Q⁻¹) = 1 := by
      rw [show Q * P⁻¹ * (P * Q⁻¹) = Q * (P⁻¹ * P) * Q⁻¹ by simp only [Matrix.mul_assoc], hPi',
        Matrix.mul_one, hQi]
    have key := _root_.GlobalTheory.CayleyChoice.isDS_conj hDS (mem hQd.2 hPd.2 hPi)
      (mem hPd.2 hQd.2 hQi) hprod
    convert key using 2 with g
    rw [show P⁻¹ * (P * Q⁻¹ * g * (Q * P⁻¹)) * P = (P⁻¹ * P) * Q⁻¹ * g * Q * (P⁻¹ * P) by
      simp only [Matrix.mul_assoc], hPi', Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CayleyChoice
