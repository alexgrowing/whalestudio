import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.PsCoprimeDvdSub

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G

section Alg

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

theorem combine_two (a b l u w : R) (k : ℕ) (hl : u * a + w * b = l ^ k) (y y₁ y₂ : V)
    (ha : y = a • y₁) (hb : y = b • y₂) :
    l ^ k • y = (a * b) • (u • y₂ + w • y₁) := by
  have e1 : (u * a) • y = (a * b * u) • y₂ := by
    rw [hb, smul_smul]
    congr 1
    ring
  have e2 : (w * b) • y = (a * b * w) • y₁ := by
    rw [ha, smul_smul]
    congr 1
    ring
  rw [← hl, add_smul, e1, e2, smul_add, smul_smul, smul_smul]

theorem combine_pow (l x y : R) (hl : l ∈ Ideal.span ({x, y} : Set R)) (a b : ℕ) :
    l ^ (a + b) ∈ Ideal.span ({x ^ a, y ^ b} : Set R) := by
  obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hl
  rw [← huw]
  refine Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := b) (k := a + b) _ ?_ ?_ (by omega)
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem combine_prod (l q : R) (a : ℕ → R) (m : ℕ)
    (h : ∀ s < m, ∃ j : ℕ, l ^ j ∈ Ideal.span ({a s, q} : Set R)) :
    ∃ j : ℕ, l ^ j ∈ Ideal.span ({∏ s ∈ Finset.range m, a s, q} : Set R) := by
  induction m with
  | zero =>
    refine ⟨0, Ideal.subset_span ?_⟩
    simp
  | succ m ih =>
    obtain ⟨j₁, h₁⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨j₂, h₂⟩ := h m (by omega)
    obtain ⟨u₁, w₁, e₁⟩ := Ideal.mem_span_pair.1 h₁
    obtain ⟨u₂, w₂, e₂⟩ := Ideal.mem_span_pair.1 h₂
    refine ⟨j₁ + j₂, Ideal.mem_span_pair.2 ⟨u₁ * u₂,
      u₁ * (∏ s ∈ Finset.range m, a s) * w₂ + w₁ * u₂ * a m + w₁ * w₂ * q, ?_⟩⟩
    rw [Finset.prod_range_succ, pow_add, ← e₁, ← e₂]
    ring

theorem combine_mod (N : Submodule R V) (l : R) (p : ℕ → R)
    (hcop : ∀ s s' : ℕ, s ≠ s' → l ∈ Ideal.span ({p s, p s'} : Set R)) (E : ℕ → ℕ) (y : V)
    (hy : y ∈ N) (ell : ℕ) (h : ∀ s < ell, ∃ y' ∈ N, y = p s ^ E s • y') :
    ∃ K : ℕ, ∃ z ∈ N, l ^ K • y = (∏ s ∈ Finset.range ell, p s ^ E s) • z := by
  induction ell with
  | zero => exact ⟨0, y, hy, by simp⟩
  | succ m ih =>
    obtain ⟨K, z, hz, hK⟩ := ih (fun s hs => h s (by omega))
    obtain ⟨y₂, hy₂, e₂⟩ := h m (by omega)
    obtain ⟨j, hj⟩ := combine_prod l (p m ^ E m) (fun s => p s ^ E s) m
      (fun s hs => ⟨E s + E m, combine_pow l (p s) (p m) (hcop s m (by omega)) (E s) (E m)⟩)
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.1 hj
    have e := combine_two (∏ s ∈ Finset.range m, p s ^ E s) (p m ^ E m) l u w j huw
      (l ^ K • y) z (l ^ K • y₂) hK (by rw [e₂, smul_comm])
    refine ⟨j + K, u • l ^ K • y₂ + w • z,
      N.add_mem (N.smul_mem _ (N.smul_mem _ hy₂)) (N.smul_mem _ hz), ?_⟩
    rw [Finset.prod_range_succ, pow_add, mul_smul, e]

end Alg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem combine_cop [IsDomain O] (hR : Ring9 W) (s s' : ℕ) (hss : s ≠ s') :
    PowerSeries.C (((PD.p : ℕ) : O)) ∈
      Ideal.span ({(baseIdOf hR).Bs.p s, (baseIdOf hR).Bs.p s'} : Set (PowerSeries O)) := by
  obtain ⟨u, hu⟩ := frobenius_uniformizer_identity hR
  have h2 := PD.hp.two_le
  have hℓ : (baseIdOf hR).Bs.ℓ = PD.p := rfl
  have hdvd : (PowerSeries.X * (PowerSeries.X + PowerSeries.C (((baseIdOf hR).Bs.ℓ : ℕ) : O)) :
      PowerSeries O) ∣ (baseIdOf hR).Bs.φ PowerSeries.X := by
    refine ⟨(u : PowerSeries O) * (baseIdOf hR).Bs.q ^ ((baseIdOf hR).Bs.ℓ - 2), ?_⟩
    rw [hu]
    have e : (baseIdOf hR).Bs.ℓ - 1 = ((baseIdOf hR).Bs.ℓ - 2) + 1 := by rw [hℓ]; omega
    rw [e, pow_succ]
    change _ = PowerSeries.X * (baseIdOf hR).Bs.q * _
    ring
  exact (LevelStatements.Lv.psCoprime O (baseIdOf hR).Bs.ℓ (baseIdOf hR).Bs.φ hdvd).2 s s' hss

theorem combine [IsDomain O] (hSat : Sat W) (hcrys : IsCrys PD T.ρ) (ell : ℕ) (E : ℕ → ℕ) (y : C.V)
    (hy : y ∈ (latOf C).N c)
    (h : ∀ s < ell, ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ E s • y') :
    ∃ y' ∈ (latOf C).N c, y = (∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s) • y' := by
  set κ : PowerSeries O := ∏ s ∈ Finset.range ell, (baseIdOf hR).Bs.p s ^ E s with hκ
  obtain ⟨K, z, hz, hK⟩ := combine_mod ((latOf C).N c) (PowerSeries.C (((PD.p : ℕ) : O)))
    (fun s => (baseIdOf hR).Bs.p s) (combine_cop hR) E y hy ell h
  have hd : (baseIdOf hR).d κ = ∏ s ∈ Finset.range ell, pS W s ^ E s := by
    rw [hκ, map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, BaseId.d_p]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O)) ^ K) =
      ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [map_pow, BaseId.d_C, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d κ) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d κ) 1 hcrys ⟨0, (baseIdOf hR).d κ, ⟨E, ell, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c z, hNΔ _ hz (fun δ hδ => C.t_Δ c z δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hK, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
