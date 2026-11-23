import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_triv (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) :
    ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1 := by
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  have hker : (μ.ker : Set kˣ) ∈ nhds (1 : kˣ) := hμ.mem_nhds (one_mem _)
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hker
  obtain ⟨U, hU, hUsub⟩ := hker
  rw [Units.val_one, IsValuativeTopology.mem_nhds_iff'] at hU
  obtain ⟨γ, hγ⟩ := hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hϖ1 : valuation k (ϖ : k) < 1 :=
    (Valuation.Integer.not_isUnit_iff_valuation_lt_one).mp hϖ.not_isUnit
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hϖ1 γ
  refine ⟨c, fun u hu => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨z, hz⟩ := hu
  have hz1 : valuation k (z : k) ≤ 1 := (Valuation.mem_integer_iff _ _).mp z.2
  have hv : valuation k (((unitIncl k u : kˣ) : k) - 1) < γ := by
    have h1 : ((unitIncl k u : kˣ) : k) - 1 = (ϖ : k) ^ c * (z : k) := by
      change ((u : 𝒪[k]) : k) - 1 = _
      have := congrArg (fun x : 𝒪[k] => (x : k)) hz
      push_cast at this
      exact this
    rw [h1, map_mul, map_pow]
    calc valuation k (ϖ : k) ^ c * valuation k (z : k) ≤ valuation k (ϖ : k) ^ c * 1 := by gcongr
      _ = valuation k (ϖ : k) ^ c := mul_one _
      _ < γ := hc
  exact hUsub (hγ hv)

theorem triv_cond (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (u : 𝒪[k]ˣ)
    (hu : (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res μ)) : res μ u = 1 := by
  obtain ⟨c, hc⟩ := exists_triv μ hμ
  exact Nat.sInf_mem (s := {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → res μ u = 1})
    ⟨c, hc⟩ u hu

theorem minor_unit {n r : ℕ} (hr : 1 ≤ r) {g : GL (Fin n) k} (hg : g ∈ KC k n r) {ι : Type} {_ : Fintype ι}
    {_ : DecidableEq ι} (f : ι → Fin n) (hf : Function.Injective f) :
    ∃ u : 𝒪[k]ˣ, ((g : Matrix (Fin n) (Fin n) k).submatrix f f).det = algebraMap 𝒪[k] k u ∧
      (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ r := by
  obtain ⟨⟨h, rfl⟩, hc⟩ := hg
  set I := IsLocalRing.maximalIdeal 𝒪[k] ^ r
  set M : Matrix ι ι 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix f f with hM
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hentry : ∀ i j, (M i j) - (if i = j then 1 else 0) ∈ I := by
    intro i j
    obtain ⟨y, hy, hyx⟩ := hc (f i) (f j)
    have : y = M i j - (if i = j then 1 else 0) := by
      apply hinj
      rw [hyx]
      simp only [hM, Matrix.submatrix_apply, map_sub, hf.eq_iff]
      split_ifs <;> simp [Matrix.GeneralLinearGroup.map]
    rw [← this]
    exact hy
  have hmk : M.map (Ideal.Quotient.mk I) = 1 := by
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply]
    have := Ideal.Quotient.eq.mpr (hentry i j)
    rw [this]
    split_ifs <;> simp
  have hD : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.mapMatrix_apply, hmk, Matrix.det_one, map_one]
  have hDm : M.det - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] := Ideal.pow_le_self (by omega) hD
  have hunit : IsUnit M.det := by
    by_contra hn
    have h1 : M.det ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have : (1 : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      have := Ideal.sub_mem _ h1 hDm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal 𝒪[k]).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  refine ⟨hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, RingHom.map_det]
    rfl
  · rw [IsUnit.unit_spec]
    exact hD

theorem chk_unit (μ : kˣ →* ℂˣ) (u : 𝒪[k]ˣ) : chk μ (algebraMap 𝒪[k] k u) = ((res μ u : ℂˣ) : ℂ) := by
  have h0 : algebraMap 𝒪[k] k u ≠ 0 := by
    intro h
    exact u.ne_zero (Subtype.val_injective (by simpa using h))
  rw [chk, dif_neg h0, show Units.mk0 _ h0 = unitIncl k u from Units.ext rfl]
  rfl

end UpperTheory.TNZ.Grp.P_lamBasic

namespace UpperTheory.TNZ.Grp

open UpperTheory.TNZ.Grp.P_lamBasic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_lamBasic {n : ℕ} (G : Grp k n) : LambdaBasicProp G := by
  intro hb
  obtain ⟨-, hlt, hcond, hq⟩ := hb
  have hlev : 1 ≤ G.lev := by unfold lev; omega
  have key : ∀ g ∈ KC k n G.lev, G.lam g = 1 := by
    intro g hg
    unfold lam
    refine Finset.prod_eq_one fun a _ => ?_
    obtain ⟨u, hu, hu1⟩ := minor_unit hlev hg (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n)
      Subtype.val_injective
    have hΔ : G.Δ a g = algebraMap 𝒪[k] k u := hu
    rw [hΔ, chk_unit]
    unfold μnext
    split_ifs with h
    · have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cc G.μ a ⟨a + 1, h⟩ :=
        Ideal.pow_le_pow_right (hlt a _).le
      rw [hq a ⟨a + 1, h⟩ u (hle hu1)]
      rfl
    · rw [div_one]
      have hle : IsLocalRing.maximalIdeal 𝒪[k] ^ G.lev ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ cond (res (G.μ a)) :=
        Ideal.pow_le_pow_right (hcond a).le
      rw [triv_cond (G.μ a) (G.smooth a) u (hle hu1)]
      rfl
  have hone : (1 : GL (Fin n) k) ∈ KC k n G.lev := by
    refine ⟨one_mem _, fun i j => ⟨0, zero_mem _, ?_⟩⟩
    simp [Matrix.one_apply]
  refine ⟨key 1 hone, fun g => ?_, key⟩
  unfold lam
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  unfold chk
  split_ifs
  · exact one_ne_zero
  · exact Units.ne_zero _

end UpperTheory.TNZ.Grp
