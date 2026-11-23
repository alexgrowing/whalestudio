import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup PowerSeries

section PS

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {l : ℕ} [Fact l.Prime]

def residueConst : O⟦X⟧ →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O).comp (PowerSeries.constantCoeff (R := O))

theorem residueConst_apply (f : O⟦X⟧) :
    residueConst f = IsLocalRing.residue O (PowerSeries.constantCoeff f) := rfl

theorem residueConst_X_eq_zero : residueConst (X : O⟦X⟧) = 0 := by
  rw [residueConst_apply]
  simp

theorem residueConst_phi_eq (P : PhiData O l) (f : O⟦X⟧) : residueConst (P.φ f) = residueConst f := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hX : residueConst (P.φ X) = 0 := by
    have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
    rw [map_sub, hCa] at h6
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', map_add, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, zero_add,
      residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const f]
  rw [map_add, map_mul, map_add, map_mul, hX, mul_zero, zero_add, hCa]
  rw [residueConst_apply, residueConst_apply, PowerSeries.constantCoeff_C]

theorem residueConst_p1_eq_zero (P : PhiData O l) : residueConst (P.p 1) = 0 := by
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  unfold PhiData.p
  rw [Function.iterate_one]
  have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
  rw [map_sub, hCa] at h6
  have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
  rw [h6', map_add, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, zero_add,
    residueConst_apply, PowerSeries.constantCoeff_C]
  exact (IsLocalRing.residue_eq_zero_iff _).2 P.4

theorem level_poly_decomposition (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) :
    ∃ e h : O⟦X⟧, P.p s = C (l : O) * e + X ^ l * h ∧ residueConst e ≠ 0 := by
  unfold PhiData.p
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hCa : ∀ a : O, P.φ (C a) = C a := by
    intro a
    first
    | exact P.φ.commutes a
    | simpa using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply'] using P.φ.commutes a
    | simpa [PowerSeries.algebraMap_apply] using P.φ.commutes a
  have hκC : residueConst (C (l : O)) = 0 := by
    rw [residueConst_apply, PowerSeries.constantCoeff_C]
    exact (IsLocalRing.residue_eq_zero_iff _).2 P.4
  have hκXl : residueConst ((X : O⟦X⟧) ^ l) = 0 := by
    rw [map_pow, residueConst_X_eq_zero, zero_pow (by omega)]
  have hmul : ∀ a b a' b' : O⟦X⟧, ∃ a'' b'' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) * (C (l : O) * a' + X ^ l * b') = C (l : O) * a'' + X ^ l * b'' ∧
      residueConst a'' = 0 := by
    intro a b a' b'
    refine ⟨a * C (l : O) * a' + a * X ^ l * b' + X ^ l * b * a', X ^ l * b * b', by ring, ?_⟩
    simp only [map_add, map_mul, hκC, hκXl, mul_zero, zero_mul, add_zero]
  have hpow : ∀ a b : O⟦X⟧, ∀ m, 2 ≤ m → ∃ a' b' : O⟦X⟧,
      (C (l : O) * a + X ^ l * b) ^ m = C (l : O) * a' + X ^ l * b' ∧ residueConst a' = 0 := by
    intro a b m hm
    induction m, hm using Nat.le_induction with
    | base => rw [pow_two]; exact hmul a b a b
    | succ m hm ih =>
      obtain ⟨a', b', he, hk⟩ := ih
      obtain ⟨a'', b'', he', hk'⟩ := hmul a' b' a b
      exact ⟨a'', b'', by rw [pow_succ, he, he'], hk'⟩
  have hXl : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h6 : P.φ (X - C (l : O)) = P.u * (X - C (l : O)) * X ^ (l - 1) := P.6
  rw [map_sub, hCa] at h6
  have hφX : P.φ X = C (l : O) * (1 - P.u * X ^ (l - 1)) + X ^ l * P.u := by
    have h6' : P.φ X = P.u * (X - C (l : O)) * X ^ (l - 1) + C (l : O) := by rw [← h6]; ring
    rw [h6', hXl]
    ring
  induction s, hs using Nat.le_induction with
  | base =>
    refine ⟨1 - P.u * X ^ (l - 1), P.u, by rw [Function.iterate_one, hφX], ?_⟩
    rw [map_sub, map_one, map_mul, map_pow, residueConst_X_eq_zero, zero_pow (by omega), mul_zero, sub_zero]
    exact one_ne_zero
  | succ s hs ih =>
    obtain ⟨e, h, he, hk⟩ := ih
    obtain ⟨a', b', hab, hka⟩ := hpow (1 - P.u * X ^ (l - 1)) P.u l hl2
    refine ⟨P.φ e + a' * P.φ h, b' * P.φ h, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', he, map_add, map_mul, map_mul, hCa, map_pow, hφX, hab]
      ring
    · rw [map_add, map_mul, hka, zero_mul, add_zero, residueConst_phi_eq]
      exact hk

theorem isUnit_of_residueConst_ne_zero {e : O⟦X⟧} (hκ : residueConst e ≠ 0) : IsUnit e := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  rw [residueConst_apply] at hκ
  by_contra h
  exact hκ ((IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 h))

theorem l_pow_mem_span_level_X_pow (P : PhiData O l) (s : ℕ) (hs : 1 ≤ s) (B : ℕ) :
    ∃ a b : O⟦X⟧, C (l : O) ^ B = a * P.p s + b * X ^ B := by
  obtain ⟨e, h, hp, he⟩ := level_poly_decomposition P s hs
  obtain ⟨u, hu⟩ := isUnit_of_residueConst_ne_zero he
  obtain ⟨k, hk⟩ := sub_dvd_pow_sub_pow (C (l : O) * e) (-(X ^ l * h)) B
  rw [sub_neg_eq_add, ← hp] at hk
  have hl : B ≤ l * B := Nat.le_mul_of_pos_left B (Fact.out : l.Prime).pos
  refine ⟨k * (↑u⁻¹ : O⟦X⟧) ^ B, X ^ (l * B - B) * (-h) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B, ?_⟩
  have hy : (-(X ^ l * h) : O⟦X⟧) ^ B = X ^ (l * B - B) * (-h) ^ B * X ^ B := by
    rw [mul_assoc, mul_comm ((-h) ^ B), ← mul_assoc, ← pow_add, Nat.sub_add_cancel hl, pow_mul,
      ← mul_pow, neg_mul_eq_mul_neg]
  have hue : (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B = C (l : O) ^ B := by
    rw [← mul_pow, mul_assoc, ← hu, Units.mul_inv, mul_one]
  calc C (l : O) ^ B = (C (l : O) * e) ^ B * (↑u⁻¹ : O⟦X⟧) ^ B := hue.symm
    _ = (P.p s * k + (-(X ^ l * h)) ^ B) * (↑u⁻¹ : O⟦X⟧) ^ B := by rw [← hk, sub_add_cancel]
    _ = _ := by rw [hy]; ring

end PS

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}
    [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem powerSeriesConst_add {W : LocWach PD LL O v n} (Br : PhiBridge W) (F F' : PowerSeries O) :
    Br.cst (F + F') = Br.cst F + Br.cst F' := by
  unfold PhiBridge.cst
  funext x
  first
  | exact map_add Br.ι F F'
  | exact Br.ι.map_add F F'
  | simp

theorem l_pow_mem_levels_q_pow_ideal {W : LocWach PD LL O v n} (Br : PhiBridge W) (Bq : ℕ) {g : LetA O n}
    (hg : g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}) :
    g ∈ W.AΔ ∧ ∃ N : ℕ, ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ, lA W ^ N = a * g + b * qA W ^ Bq := by
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have key : ∃ F : PowerSeries O, g = Br.cst F ∧
      ∃ N : ℕ, ∃ a b : PowerSeries O, C ((PD.p : ℕ) : O) ^ N = a * F + b * X ^ Bq := by
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨a, b, hab⟩ := l_pow_mem_span_level_X_pow Br.P k hk Bq
      exact ⟨Br.P.p k, Br.ps_eq k, Bq, a, b, hab⟩
    | one =>
      exact ⟨1, Br.cst_one.symm, 0, 1, 0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨F₁, rfl, N₁, a₁, b₁, h₁⟩ := hx
      obtain ⟨F₂, rfl, N₂, a₂, b₂, h₂⟩ := hy
      refine ⟨F₁ * F₂, (Br.cst_mul F₁ F₂).symm, N₁ + N₂, a₁ * a₂,
        b₁ * a₂ * F₂ + a₁ * F₁ * b₂ + b₁ * b₂ * X ^ Bq, ?_⟩
      rw [pow_add, h₁, h₂]
      ring
  obtain ⟨F, rfl, N, a, b, h⟩ := key
  refine ⟨Br.cst_mem F, N, Br.cst a, Br.cst_mem a, Br.cst b, Br.cst_mem b, ?_⟩
  rw [Br.lA_eq, Br.qA_eq, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul,
    ← powerSeriesConst_add, h]

end Bridge

end Formalism.MainNotions.N.FrobeniusPowerSeries
