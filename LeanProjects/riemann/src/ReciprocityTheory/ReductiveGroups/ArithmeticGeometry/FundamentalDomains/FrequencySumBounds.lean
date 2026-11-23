import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealFlowPeriodsSpanEqTop

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FrequencySumBounds

open NumberField Complex Module
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}

def IsFreq (X : Data E r) (la : Wt X.Ψ r) (ν : X.Ψ → ℝ) : Prop :=
  (∀ τ, 0 ≤ ν τ) ∧ ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k

theorem freq_sum_bound (X : Data E r) (la : Wt X.Ψ r) (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, ∀ F : Finset (X.Ψ → ℝ), (∀ ν ∈ F, IsFreq X la ν) →
      ∑ ν ∈ F, Real.exp (-a * ∑ τ, ν τ) ≤ K := by
  classical
  have hsingle : ∀ τ : X.Ψ, ∃ T : Finset (X.Ψ → ℝ), (∀ p ∈ T, p ∈ X.periods la) ∧
      (Pi.single τ (1 : ℝ) : X.Ψ → ℝ) ∈ Submodule.span ℝ (T : Set (X.Ψ → ℝ)) := by
    intro τ
    have hmem : (Pi.single τ (1 : ℝ) : X.Ψ → ℝ) ∈ (⊤ : Submodule ℝ (X.Ψ → ℝ)) := Submodule.mem_top
    rw [← realFlowPeriods_span_eq_top X la] at hmem
    obtain ⟨T, hT, hT'⟩ := Submodule.mem_span_finite_of_mem_span hmem
    exact ⟨T, fun p hp => AddSubgroup.subset_closure (hT (Finset.mem_coe.mpr hp)), hT'⟩
  choose T hTsub hTmem using hsingle
  obtain ⟨U, hUdef⟩ : ∃ U : Finset (X.Ψ → ℝ), U = Finset.univ.biUnion T := ⟨_, rfl⟩
  have hUsub : ∀ p ∈ U, p ∈ X.periods la := by
    intro p hp
    rw [hUdef, Finset.mem_biUnion] at hp
    obtain ⟨τ, -, hp⟩ := hp
    exact hTsub τ p hp

  have hU_sep : ∀ d : X.Ψ → ℝ, (∀ p ∈ U, ∑ τ, d τ * p τ = 0) → d = 0 := by
    intro d hd
    funext τ
    let φ : (X.Ψ → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => ∑ σ, d σ * x σ
        map_add' := fun x y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := fun c x => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring }
    have hle : Submodule.span ℝ (T τ : Set (X.Ψ → ℝ)) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      intro p hp
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      exact hd p (by rw [hUdef]; exact Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ _, Finset.mem_coe.mp hp⟩)
    have h1 : φ (Pi.single τ (1 : ℝ)) = 0 := LinearMap.mem_ker.mp (hle (hTmem τ))
    have h2 : ∑ σ, d σ * (Pi.single τ (1 : ℝ) : X.Ψ → ℝ) σ = 0 := h1
    simpa [Pi.single_apply] using h2

  obtain ⟨g, hgdef⟩ : ∃ g : (X.Ψ → ℝ) → U → ℤ,
      g = fun (ν : X.Ψ → ℝ) (p : U) => round (2 * ∑ τ, ν τ * (p : X.Ψ → ℝ) τ) := ⟨_, rfl⟩
  have hg : ∀ ν, IsFreq X la ν → ∀ p (hp : p ∈ U),
      ((g ν ⟨p, hp⟩ : ℤ) : ℝ) = 2 * ∑ τ, ν τ * p τ := by
    intro ν hν p hp
    obtain ⟨k, hk⟩ := hν.2 p (hUsub p hp)
    rw [hgdef]
    show ((round (2 * ∑ τ, ν τ * p τ) : ℤ) : ℝ) = _
    rw [hk, round_intCast]
  have hinj : ∀ ν, IsFreq X la ν → ∀ ν', IsFreq X la ν' → g ν = g ν' → ν = ν' := by
    intro ν hν ν' hν' he
    have hd := hU_sep (ν - ν') (fun p hp => by
      have h1 := hg ν hν p hp
      have h2 := hg ν' hν' p hp
      rw [he] at h1
      have h3 : ∑ τ, ν τ * p τ = ∑ τ, ν' τ * p τ := by linarith
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, h3, sub_self])
    exact sub_eq_zero.mp hd

  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ p ∈ U, ∑ τ, |p τ| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun τ _ => abs_nonneg _
  have hM : ∀ p ∈ U, ∀ τ, |p τ| ≤ M := by
    intro p hp τ
    rw [hMdef]
    exact (Finset.single_le_sum (f := fun σ => |p σ|) (fun σ _ => abs_nonneg _)
      (Finset.mem_univ τ)).trans (Finset.single_le_sum (f := fun q => ∑ σ, |q σ|)
      (fun q _ => Finset.sum_nonneg fun σ _ => abs_nonneg _) hp)
  have hbd : ∀ ν, IsFreq X la ν → ∀ p (hp : p ∈ U),
      |((g ν ⟨p, hp⟩ : ℤ) : ℝ)| ≤ 2 * M * ∑ τ, ν τ := by
    intro ν hν p hp
    rw [hg ν hν p hp, abs_mul, abs_two]
    have h1 : |∑ τ, ν τ * p τ| ≤ ∑ τ, ν τ * M := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
      rw [abs_mul, abs_of_nonneg (hν.1 τ)]
      exact mul_le_mul_of_nonneg_left (hM p hp τ) (hν.1 τ)
    rw [← Finset.sum_mul] at h1
    nlinarith
  have hsumbd : ∀ ν, IsFreq X la ν →
      ∑ p : U, |((g ν p : ℤ) : ℝ)| ≤ (U.card : ℝ) * (2 * M * ∑ τ, ν τ) := by
    intro ν hν
    calc ∑ p : U, |((g ν p : ℤ) : ℝ)| ≤ ∑ _p : U, (2 * M * ∑ τ, ν τ) :=
          Finset.sum_le_sum fun p _ => hbd ν hν p.1 p.2
      _ = (U.card : ℝ) * (2 * M * ∑ τ, ν τ) := by simp
  have hc : 0 ≤ (U.card : ℝ) * (2 * M) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hB : 0 < (U.card : ℝ) * (2 * M) + 1 := by linarith
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = a / ((U.card : ℝ) * (2 * M) + 1) := ⟨_, rfl⟩
  have hb : 0 < b := by rw [hbdef]; exact div_pos ha hB

  obtain ⟨w, hwdef⟩ : ∃ w : ℤ → ℝ, w = fun (j : ℤ) => Real.exp (-b * |(j : ℝ)|) := ⟨_, rfl⟩
  have hw0 : ∀ j, 0 ≤ w j := fun j => by rw [hwdef]; exact (Real.exp_pos _).le
  have hgeo : Summable (fun n : ℕ => Real.exp (-b) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le ((Real.exp_lt_exp.mpr (by linarith : -b < 0)).trans_eq Real.exp_zero)
  have hw : Summable w := by
    rw [hwdef]
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hgeo.congr fun n => ?_
      show Real.exp (-b) ^ n = Real.exp (-b * |(((n : ℤ)) : ℝ)|)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      ring
    · refine hgeo.congr fun n => ?_
      show Real.exp (-b) ^ n = Real.exp (-b * |((-(n : ℤ) : ℤ) : ℝ)|)
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
      ring
  have hexp : ∀ ν, IsFreq X la ν → Real.exp (-a * ∑ τ, ν τ) ≤ ∏ p : U, w (g ν p) := by
    intro ν hν
    have hs : 0 ≤ ∑ τ, ν τ := Finset.sum_nonneg fun τ _ => hν.1 τ
    have h2 : b * ∑ p : U, |((g ν p : ℤ) : ℝ)| ≤ a * ∑ τ, ν τ := by
      calc b * ∑ p : U, |((g ν p : ℤ) : ℝ)| ≤ b * ((U.card : ℝ) * (2 * M * ∑ τ, ν τ)) :=
            mul_le_mul_of_nonneg_left (hsumbd ν hν) hb.le
        _ ≤ a * ∑ τ, ν τ := by
            rw [hbdef, div_mul_eq_mul_div, div_le_iff₀ hB]
            nlinarith [mul_nonneg ha.le hs, mul_nonneg hc hs]
    simp only [hwdef]
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.mpr
    rw [← Finset.mul_sum]
    linarith
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑' j : ℤ, w j := ⟨_, rfl⟩
  refine ⟨Z ^ U.card, fun F hF => ?_⟩
  have hinjF : Set.InjOn g (F : Set (X.Ψ → ℝ)) := by
    intro x hx y hy h
    exact hinj x (hF x hx) y (hF y hy) h
  obtain ⟨I, hIdef⟩ : ∃ I : Finset ℤ, I = (F.image g).biUnion (fun k => Finset.univ.image k) :=
    ⟨_, rfl⟩
  have hsub : F.image g ⊆ Fintype.piFinset (fun _ : U => I) := by
    intro k hk
    rw [Fintype.mem_piFinset]
    intro p
    rw [hIdef]
    exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_image_of_mem k (Finset.mem_univ p)⟩
  calc ∑ ν ∈ F, Real.exp (-a * ∑ τ, ν τ)
      ≤ ∑ ν ∈ F, ∏ p : U, w (g ν p) := Finset.sum_le_sum fun ν hν => hexp ν (hF ν hν)
    _ = ∑ k ∈ F.image g, ∏ p : U, w (k p) := by rw [Finset.sum_image hinjF]
    _ ≤ ∑ k ∈ Fintype.piFinset (fun _ : U => I), ∏ p : U, w (k p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => Finset.prod_nonneg fun p _ => hw0 _)
    _ = ∏ _p : U, ∑ j ∈ I, w j := (Finset.prod_univ_sum (fun _ : U => I) (fun _ j => w j)).symm
    _ ≤ ∏ _p : U, Z := Finset.prod_le_prod (fun _ _ => Finset.sum_nonneg fun j _ => hw0 j)
          (fun _ _ => hZ ▸ hw.sum_le_tsum I (fun j _ => hw0 j))
    _ = Z ^ U.card := by simp

end FrequencySumBounds

end ReciprocityTheory.ChartRestriction.G.FD
