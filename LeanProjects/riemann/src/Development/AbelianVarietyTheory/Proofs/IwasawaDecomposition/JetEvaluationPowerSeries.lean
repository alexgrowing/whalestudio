import Mathlib
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.JetTruncNotInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RosLevel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR (pGl fGl)
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.RayEv.Transport
open GlobalTheory.TorusInvariance (wVal)
open GlobalTheory.EndRosati (push)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdicConverge

open MvPolynomial Formalism.L2.Pj

section Coef

variable {K : Type} [CommRing K] {ρ : Type} {m : ℕ}

def jetCoef (n : ρ →₀ ℕ) (j : Jet K ρ m) : K := (Ideal.Quotient.mk_surjective j).choose.coeff n

theorem jetCoef_mk {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (p : MvPolynomial ρ K) :
    jetCoef (m := m) n (Ideal.Quotient.mk _ p) = p.coeff n := by
  have hs := Ideal.Quotient.mk_surjective (I := orig K ρ ^ (m + 1)) (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) p)
  show hs.choose.coeff n = _
  have h2 : (Ideal.Quotient.mk (orig K ρ ^ (m + 1)) (hs.choose - p) : Jet K ρ m) = 0 := by
    rw [map_sub, hs.choose_spec, sub_self]
  have := (GlobalTheory.JetTest.mk_eq_zero_iff _).1 h2 n hn
  rwa [coeff_sub, sub_eq_zero] at this

theorem jetCoef_add {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (a b : Jet K ρ m) :
    jetCoef n (a + b) = jetCoef n a + jetCoef n b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_add, jetCoef_mk hn, jetCoef_mk hn, jetCoef_mk hn, coeff_add]

theorem jetCoef_smul {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (c : K) (a : Jet K ρ m) :
    jetCoef n (algebraMap K (Jet K ρ m) c * a) = c * jetCoef n a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have : algebraMap K (Jet K ρ m) c * Ideal.Quotient.mk _ p = Ideal.Quotient.mk _ (MvPolynomial.C c * p) := by
    rw [map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  rw [this, jetCoef_mk hn, jetCoef_mk hn, coeff_C_mul]

theorem jetCoef_psJet [Fintype ρ] [DecidableEq ρ] {n : ρ →₀ ℕ} (hn : n.degree ≤ m) (h : MvPowerSeries ρ K) :
    jetCoef n (psJet m h) = MvPowerSeries.coeff n h := by
  rw [psJet, jetCoef_mk hn, GlobalTheory.JetTest.coeff_psTrunc, if_pos hn]

theorem jet_ext (a b : Jet K ρ m) (h : ∀ n : ρ →₀ ℕ, n.degree ≤ m → jetCoef n a = jetCoef n b) : a = b := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← sub_eq_zero, ← map_sub, GlobalTheory.JetTest.mk_eq_zero_iff]
  intro e he
  rw [coeff_sub, ← jetCoef_mk he, ← jetCoef_mk he, h e he, sub_self]

end Coef

theorem exists_bound {α : Type} (S : Finset α) (φ : α → ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ (∀ x ∈ S, φ x ≤ q) ∧ (q = 0 ∨ ∃ x ∈ S, q = φ x) := by
  classical
  have hne : (insert 0 (S.image φ)).Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  refine ⟨(insert 0 (S.image φ)).max' hne, Finset.le_max' _ 0 (Finset.mem_insert_self _ _),
    fun x hx => Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem φ hx)), ?_⟩
  rcases Finset.mem_insert.1 (Finset.max'_mem _ hne) with h | h
  · exact Or.inl h
  · obtain ⟨x, hx, hq⟩ := Finset.mem_image.1 h
    exact Or.inr ⟨x, hx, hq.symm⟩

section Norms

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {R : Type} [CommRing R] (f : R →+* C)

def normIdeal (hf : ∀ r, ‖f r‖ ≤ 1) (c : ℝ) (hc : 0 ≤ c) : Ideal R where
  carrier := {a | ‖f a‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖f r‖ * ‖f a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem norm_le_of_mem_pow {I : Ideal R} (hI : I.FG) (hf1 : ∀ r, ‖f r‖ ≤ 1) (hfI : ∀ r ∈ I, ‖f r‖ < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k := by
  classical
  obtain ⟨G, hG⟩ := hI
  obtain ⟨q, hq0, hqG, hq⟩ := exists_bound G (fun x => ‖f x‖)
  have hq1 : q < 1 := by
    rcases hq with h | ⟨x, hx, h⟩
    · rw [h]; exact one_pos
    · rw [h]; exact hfI x (hG ▸ Ideal.subset_span hx)
  refine ⟨q, hq0, hq1, fun k => ?_⟩
  suffices h : I ^ k ≤ normIdeal f hf1 (q ^ k) (pow_nonneg hq0 k) from fun a ha => h ha
  induction k with
  | zero => intro a _; show ‖f a‖ ≤ q ^ 0; rw [pow_zero]; exact hf1 a
  | succ k ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun a ha b hb => ?_
    have ha' : ‖f a‖ ≤ q ^ k := ih ha
    have hspan : Ideal.span (G : Set R) ≤ normIdeal f hf1 (q ^ 1) (pow_nonneg hq0 1) :=
      Ideal.span_le.2 fun x hx => by show ‖f x‖ ≤ q ^ 1; rw [pow_one]; exact hqG x hx
    have hb' : ‖f b‖ ≤ q ^ 1 := hspan (hG.symm ▸ hb)
    show ‖f (a * b)‖ ≤ q ^ (k + 1)
    rw [map_mul, norm_mul, pow_succ]
    exact mul_le_mul ha' (by simpa using hb') (norm_nonneg _) (pow_nonneg hq0 k)

variable {W : Type} [CommRing W] [Algebra R W]

def normSub (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) (c : ℝ)
    (hc : 0 ≤ c) : Submodule R W where
  carrier := {w | ‖Λ w‖ ≤ c}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp [hc]
  smul_mem' := fun r a ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [hΛ, norm_mul]
    calc ‖f r‖ * ‖Λ a‖ ≤ 1 * c := mul_le_mul (hf r) ha (norm_nonneg _) zero_le_one
      _ = c := one_mul c

theorem bound_of_finite [Module.Finite R W] (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C)
    (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w, ‖Λ w‖ ≤ B := by
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := W)
  obtain ⟨B, hB0, hBT, -⟩ := exists_bound T (fun w => ‖Λ w‖)
  refine ⟨B, hB0, fun w => ?_⟩
  have h : (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ B hB0 := hT ▸ Submodule.span_le.2 (fun x hx => hBT x hx)
  exact h Submodule.mem_top

theorem bound_pow (hf : ∀ r, ‖f r‖ ≤ 1) (Λ : W →+ C) (hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w)
    {I : Ideal R} {q B : ℝ} (hq0 : 0 ≤ q) (hq : ∀ k : ℕ, ∀ a ∈ I ^ k, ‖f a‖ ≤ q ^ k) (hB : ∀ w, ‖Λ w‖ ≤ B)
    (e : ℕ) (x : W) (hx : x ∈ I.map (algebraMap R W) ^ e) : ‖Λ x‖ ≤ q ^ e * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [← Ideal.map_pow] at hx
  have hx' : x ∈ (I ^ e) • (⊤ : Submodule R W) := by
    rw [Ideal.smul_top_eq_map]; exact hx
  have hle : (I ^ e) • (⊤ : Submodule R W) ≤ normSub f hf Λ hΛ (q ^ e * B) (mul_nonneg (pow_nonneg hq0 e) hB0) :=
    Submodule.smul_le.2 fun a ha w _ => by
      show ‖Λ (a • w)‖ ≤ q ^ e * B
      rw [hΛ, norm_mul]
      exact mul_le_mul (hq e a ha) (hB w) (norm_nonneg _) (pow_nonneg hq0 e)
  exact hle hx'

theorem hasSum_of_adic (Λ : W →+ C) (J : Ideal W)
    (hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ J ^ (e + 1), ‖Λ x‖ < ε) {X : Type} (s : W) (t : X → W)
    (hst : ∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ J ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ J ^ (e + 1)) :
    HasSum (fun α => Λ (t α)) (Λ s) := by
  classical
  change Filter.Tendsto (fun S : Finset X => ∑ b ∈ S, Λ (t b)) Filter.atTop (nhds (Λ s))
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨e, he⟩ := hbound ε hε
  obtain ⟨S, hS1, hS2⟩ := hst e
  refine ⟨S, fun S' hS' => ?_⟩
  have hmem : s - ∑ α ∈ S', t α ∈ J ^ (e + 1) := by
    have h : s - ∑ α ∈ S', t α = (s - ∑ α ∈ S, t α) - ∑ α ∈ S' \ S, t α := by
      rw [← Finset.sum_sdiff hS']; abel
    rw [h]
    exact sub_mem hS2 (sum_mem fun α hα => hS1 α (Finset.mem_sdiff.1 hα).2)
  rw [dist_eq_norm, ← map_sum, ← map_sub, ← norm_neg, ← map_neg, neg_sub]
  exact he _ hmem

end Norms

theorem converge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (R : Type) [CommRing R] (I : Ideal R), I.FG → ∀ f : R →+* C, (∀ r, ‖f r‖ ≤ 1) → (∀ r ∈ I, ‖f r‖ < 1) → ∀ (W : Type) [CommRing W] [Algebra R W] [Module.Finite R W] (ρ : Type) [Fintype ρ] [DecidableEq ρ] (m : ℕ) (κ : W →+* Jet C ρ m), (∀ r, κ (algebraMap R W r) = algebraMap C (Jet C ρ m) (f r)) → ∀ (X : Type) (s : W) (t : X → W), (∀ e : ℕ, ∃ S : Finset X, (∀ α ∉ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ I.map (algebraMap R W) ^ (e + 1)) → ∀ (u : Jet C ρ m) (g : X → MvPowerSeries ρ C), (∀ α, psJet m (g α) = u * κ (t α)) → (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → Summable fun α => MvPowerSeries.coeff n (g α)) ∧ ∀ g₀ : MvPowerSeries ρ C, (∀ n : ρ →₀ ℕ, (n.sum fun _ k => k) ≤ m → HasSum (fun α => MvPowerSeries.coeff n (g α)) (MvPowerSeries.coeff n g₀)) → psJet m g₀ = u * κ s := by
  intro C _ _ _ R _ I hI f hf1 hfI W _ _ _ ρ _ _ m κ hκ X s t hst u g hg
  obtain ⟨q, hq0, hq1, hq⟩ := norm_le_of_mem_pow f hI hf1 hfI
  have key : ∀ n : ρ →₀ ℕ, n.degree ≤ m →
      HasSum (fun α => MvPowerSeries.coeff n (g α)) (jetCoef n (u * κ s)) := by
    intro n hn
    let Λ : W →+ C := AddMonoidHom.mk' (fun w => jetCoef n (u * κ w)) (fun a b => by
      simp only [map_add, mul_add]; exact jetCoef_add hn _ _)
    have hΛ : ∀ (r : R) (w : W), Λ (r • w) = f r * Λ w := by
      intro r w
      show jetCoef n (u * κ (r • w)) = f r * jetCoef n (u * κ w)
      rw [Algebra.smul_def, map_mul, hκ, mul_left_comm, jetCoef_smul hn]
    obtain ⟨B, hB0, hB⟩ := bound_of_finite f hf1 Λ hΛ
    have hcoef : ∀ α, MvPowerSeries.coeff n (g α) = Λ (t α) := fun α => by
      rw [← jetCoef_psJet hn, hg α]; rfl
    have hbound : ∀ ε > 0, ∃ e : ℕ, ∀ x ∈ I.map (algebraMap R W) ^ (e + 1), ‖Λ x‖ < ε := by
      intro ε hε
      have hB1 : (0 : ℝ) < B + 1 := by linarith
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hB1) hq1
      refine ⟨k, fun x hx => ?_⟩
      calc ‖Λ x‖ ≤ q ^ (k + 1) * B := bound_pow f hf1 Λ hΛ hq0 hq hB (k + 1) x hx
        _ ≤ q ^ k * (B + 1) :=
          mul_le_mul (pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ k)) (by linarith) hB0 (pow_nonneg hq0 k)
        _ < ε / (B + 1) * (B + 1) := mul_lt_mul_of_pos_right hk hB1
        _ = ε := div_mul_cancel₀ _ (ne_of_gt hB1)
    have h := hasSum_of_adic Λ (I.map (algebraMap R W)) hbound s t hst
    simp only [← hcoef] at h
    exact h
  refine ⟨fun n hn => (key n hn).summable, fun g₀ hg₀ => jet_ext _ _ fun n hn => ?_⟩
  rw [jetCoef_psJet hn]
  exact (hg₀ n hn).unique (key n hn)

end GlobalTheory.AdicConverge
