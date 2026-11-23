import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem ratio_bound {m : ℕ} {f : Fin (m + 1) → ℝ} {c u : ℝ} (hf : ∀ i, 0 < f i) (hc : 0 ≤ c)
    (hu : ∀ i, f i ≤ u) (h1 : 1 ≤ c * ∏ i, f i) (i j : Fin (m + 1)) : f i / f j ≤ c * u ^ (m + 1) := by
  rw [Fin.prod_univ_succAbove _ j] at h1
  have h2 : ∏ k, f (j.succAbove k) ≤ u ^ m := by
    calc ∏ k, f (j.succAbove k) ≤ ∏ _k : Fin m, u := Finset.prod_le_prod (fun k _ => (hf _).le) fun k _ => hu _
      _ = u ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hu0 : 0 < u := (hf i).trans_le (hu i)
  have h3 : 1 ≤ c * (f j * u ^ m) :=
    h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (hf j).le) hc)
  rw [div_le_iff₀ (hf j)]
  calc f i ≤ u * 1 := by rw [mul_one]; exact hu i
    _ ≤ u * (c * (f j * u ^ m)) := mul_le_mul_of_nonneg_left h3 hu0.le
    _ = c * u ^ (m + 1) * f j := by ring

private theorem chain_first {m : ℕ} {r : Fin (m + 1) → ℝ} {t s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hst : s ≤ t) (hr : ∀ i, 0 < r i) (h : ∀ i j : Fin (m + 1), (j : ℕ) = i + 1 → t * r j ≤ r i)
    (i : Fin (m + 1)) : s ^ m * r i ≤ r 0 := by
  have h1 := Reduction.pow_mul_le_of_chain (r := fun j => (r j.rev)⁻¹) hs0 hs1 hst (fun j => inv_pos.2 (hr _))
    (fun p q hpq => by
      have h2 := h q.rev p.rev (by have := q.2; simp only [Fin.val_rev]; omega)
      rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)]
      exact h2) i.rev
  simp only [Fin.rev_last, Fin.rev_rev] at h1
  rw [← div_eq_mul_inv, div_le_iff₀ (hr _), ← div_eq_inv_mul, le_div_iff₀ (hr _)] at h1
  exact h1

private theorem le_of_pow_le {x c : ℝ} {d : ℕ} (hd : d ≠ 0) (hc : 1 ≤ c) (h : x ^ d ≤ c) : x ≤ c := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans hc
  · exact (le_self_pow₀ h1.le hd).trans h

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem qht_le_height (g : KernelIndexFullLattice.G1 E a) (γ : GL (Fin a) E) :
    qht (E := E) (a := a) g.1 ≤ height (AdelicGLn.diagonal E a γ * g.1) := by
  have h1 := ciInf_le (f := fun γ : GL (Fin a) E =>
    height (K := E) (ratGL E a γ * (retractOne g.1 : KernelIndexFullLattice.G1 E a).1))
    ⟨0, by rintro _ ⟨γ, rfl⟩; exact (height_pos _).le⟩ γ
  rw [retractOne_coe] at h1
  unfold qht
  rw [retractOne_coe]
  exact h1

omit [IsTotallyComplex E] in
private theorem prod_bound {ω : Set (AdelicGLn.AdelicGL E a)} (hω : IsCompact ω) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
      ∀ kk ∈ (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL E a)),
      b * Reduction.diagUnits a (fun i => Reduction.posIdele (K := E) (ρ i) (hρ i)) * kk ∈ Reduction.normOneGL E a →
      ∏ i, ρ i ≤ c ∧ (∏ i, ρ i)⁻¹ ≤ c := by
  have hdc : Continuous fun g : AdelicGLn.AdelicGL E a => (Reduction.detModule E a g : ℝ) :=
    continuous_subtype_val.comp Reduction.continuous_detModule
  obtain ⟨M₁, hM₁⟩ := hω.bddAbove_image hdc.continuousOn
  obtain ⟨M₂, hM₂⟩ := hω.bddAbove_image (hdc.inv₀ fun g => (Reduction.detModule E a g).2.ne').continuousOn
  refine ⟨max 1 (max M₁ M₂), le_max_left _ _, fun b hb ρ hρ kk hkk hx => ?_⟩
  have hd : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
  have h1 := Reduction.mem_normOneGL_iff_detModule.1 hx
  rw [map_mul, map_mul, Reduction.mem_normOneGL_iff_detModule.1 (Reduction.maxCompact_le_normOneGL hkk),
    mul_one] at h1
  have h2 := congrArg Subtype.val h1
  rw [Positive.val_mul, detModule_diagUnits_posIdele, Positive.val_one] at h2
  have h3 := eq_inv_of_mul_eq_one_right h2
  constructor
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [h3]
    exact (hM₂ ⟨b, hb, rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  · refine le_of_pow_le hd (le_max_left _ _) ?_
    rw [inv_pow, h3, inv_inv]
    exact (hM₁ ⟨b, hb, rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))

end

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.height_bound_of_quasiHeight_le :
    SiegelHt := by
  intro E _ _ _ a
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := Reduction.exists_siegelSet (K := E) a
  rcases a with _ | m
  · refine ⟨ω, 0, 0, hω, hωB, fun g => ?_⟩
    obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
    exact ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => i.elim0⟩
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := E) (n := m + 1) hω
  obtain ⟨c, hc, hcb⟩ := prod_bound hω
  have hc0 : 0 < c := one_pos.trans_le hc
  have hs0 : 0 < min t 1 := lt_min ht one_pos
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = (min t 1) ^ m := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ pow_pos hs0 m
  obtain ⟨e, he⟩ : ∃ e, e = Fintype.card (InfinitePlace E) := ⟨_, rfl⟩
  rw [← he] at hCh
  refine ⟨ω, Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)), (m + 1) * e, hω, hωB, fun g => ?_⟩
  obtain ⟨γ, b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hxe⟩ := hsieg g.1
  have hγx : AdelicGLn.diagonal E (m + 1) γ * g.1 ∈ Reduction.normOneGL E (m + 1) :=
    mul_mem (Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩) g.2
  obtain ⟨hP1, hP2⟩ := hcb b hb ρ hρ kk hkk (hxe ▸ hγx)
  have hP : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  have key : ∀ v : ℝ, (∀ i j, ρ i / ρ j ≤ c * (σ⁻¹ * v) ^ (m + 1)) →
      qht (E := E) (a := m + 1) g.1 ≤ Ch * c ^ (2 * e) * σ⁻¹ ^ (2 * ((m + 1) * e)) * v ^ (2 * ((m + 1) * e)) := by
    intro v hv
    have h1 : 1 ≤ c * (σ⁻¹ * v) ^ (m + 1) := by
      have := hv 0 0
      rwa [div_self (hρ 0).ne'] at this
    refine (qht_le_height g γ).trans ((hCh b hb ρ hρ kk hkk _ hγx hxe _ h1 hv).trans_eq ?_)
    simp only [mul_pow, ← pow_mul]
    rw [show (m + 1) * (2 * e) = 2 * ((m + 1) * e) by ring]
    ring
  refine ⟨γ, b, kk, ρ, hρ, hb, hkk, hxe, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    have h := key (ρ (Fin.last m))⁻¹ fun p q => by
      have h1 := ratio_bound (f := fun j => (ρ j)⁻¹) (u := σ⁻¹ * (ρ (Fin.last m))⁻¹) (fun j => inv_pos.2 (hρ j)) hc0.le
        (fun j => by
          rw [← mul_inv]
          refine inv_anti₀ (mul_pos hσ0 (hρ _)) ?_
          rw [hσ]
          exact Reduction.pow_mul_le_of_chain hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j)
        (by rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, one_le_div hP]; exact hP1) q p
      rwa [inv_div_inv] at h1
    rwa [inv_pow (ρ _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos (hρ _) _)] at h
  · obtain rfl : i = 0 := Fin.ext hi
    refine key (ρ 0) fun p q => ratio_bound hρ hc0.le (fun j => ?_) ?_ p q
    · rw [le_inv_mul_iff₀ hσ0, hσ]
      exact chain_first hs0.le (min_le_right _ _) (min_le_left _ _) hρ hs j
    · rwa [inv_le_iff_one_le_mul₀ hP] at hP2
