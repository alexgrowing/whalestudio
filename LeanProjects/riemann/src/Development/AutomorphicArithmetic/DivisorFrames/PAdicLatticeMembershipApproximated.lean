import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem lattice_membership_stable_under_approximation {K : Type} [NormedField K] [IsUltrametricDist K] {A : Type} {g : ℕ} (π : K) (q : ℝ) (hq : 1 < q)
    (hπ : ‖π‖ = q⁻¹) (n : ℕ) (hn : 2 ≤ n) (h k : A → Fin g → K) (Λ : Set (Fin g → K))
    (hk : ∀ a i, ‖h a i - k a i‖ ≤ q⁻¹ ^ n) (hΛ : ∀ cf, cf ∈ Λ ↔ ∀ a, ‖∑ i, h a i * cf i‖ ≤ 1)
    (hb : ∀ cf ∈ Λ, ∀ i, ‖π * cf i‖ ≤ 1) (cf : Fin g → K) : cf ∈ Λ ↔ ∀ a, ‖∑ i, k a i * cf i‖ ≤ 1 := by
  have hq0 : 0 < q := by linarith
  have hsm : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → ∀ a, ‖∑ i, (h a i - k a i) * cf i‖ ≤ 1 := by
    intro cf hc a
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    have h1 : q⁻¹ ^ n ≤ q⁻¹ ^ 2 :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hq.le) hn
    calc ‖h a i - k a i‖ * ‖cf i‖ ≤ q⁻¹ ^ 2 * q ^ 2 :=
          mul_le_mul ((hk a i).trans h1) (hc i) (norm_nonneg _) (by positivity)
      _ = 1 := by field_simp
  have key : ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ 2) → (cf ∈ Λ ↔ ∀ a, ‖∑ i, k a i * cf i‖ ≤ 1) := by
    intro cf hc
    rw [hΛ]
    refine forall_congr' fun a => ?_
    have e : ∑ i, (h a i - k a i) * cf i = ∑ i, h a i * cf i - ∑ i, k a i * cf i := by
      simp [sub_mul, Finset.sum_sub_distrib]
    have hs := hsm cf hc a
    rw [e] at hs
    constructor
    · intro h1
      have : ∑ i, k a i * cf i = ∑ i, h a i * cf i + -(∑ i, h a i * cf i - ∑ i, k a i * cf i) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (by rwa [norm_neg]))
    · intro h1
      have : ∑ i, h a i * cf i = ∑ i, k a i * cf i + (∑ i, h a i * cf i - ∑ i, k a i * cf i) := by ring
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 hs)
  have hb' : ∀ cf ∈ Λ, ∀ i, ‖cf i‖ ≤ q := by
    intro cf hc i
    have := hb cf hc i
    rwa [norm_mul, hπ, inv_mul_le_iff₀ hq0, _root_.mul_one] at this
  constructor
  · intro hc
    refine (key cf fun i => (hb' cf hc i).trans ?_).1 hc
    nlinarith
  · have ind : ∀ m : ℕ, ∀ cf : Fin g → K, (∀ i, ‖cf i‖ ≤ q ^ (m + 2)) → (∀ a, ‖∑ i, k a i * cf i‖ ≤ 1) → cf ∈ Λ := by
      intro m
      induction m with
      | zero => intro cf hc h1; exact (key cf (by simpa using hc)).2 h1
      | succ m ih =>
        intro cf hc h1
        have h2 : (fun i => π * cf i) ∈ Λ := by
          refine ih _ (fun i => ?_) fun a => ?_
          · rw [norm_mul, hπ, inv_mul_le_iff₀ hq0]
            calc ‖cf i‖ ≤ q ^ (m + 1 + 2) := hc i
              _ = q * q ^ (m + 2) := by ring
          · have : ∑ i, k a i * (π * cf i) = π * ∑ i, k a i * cf i := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
            rw [this, norm_mul, hπ, inv_mul_le_iff₀ hq0]
            exact (h1 a).trans (by linarith)
        refine (key cf fun i => ?_).2 h1
        have h3 := hb' _ h2 i
        rw [norm_mul, hπ, inv_mul_le_iff₀ hq0] at h3
        rwa [sq]
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖cf‖ hq
    refine ind m cf fun i => (norm_le_pi_norm cf i).trans (hm.le.trans ?_)
    exact pow_le_pow_right₀ hq.le (by omega)

theorem UpperTheory.p_adic_lattice_membership_approximated :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (n g : ℕ) (h : Dw.La → Fin g → ℂ_[p]) (b : (Fin g → ℂ_[p]) →ₗ[ℂ_[p]] ℂ_[p] ⊗[ℤ] Dw.La) (Λ : Set (Fin g → ℂ_[p])), 2 ≤ n → (∀ a i, ‖h a i - pr Dw (b (Pi.single i 1)) a‖ ≤ (p : ℝ)⁻¹ ^ n) → (∀ cf, cf ∈ Λ ↔ ∀ a, ‖∑ i, h a i * cf i‖ ≤ 1) → (∀ cf ∈ Λ, ∀ i, ‖(p : ℂ_[p]) * cf i‖ ≤ 1) → ∀ cf, cf ∈ Λ ↔ ∀ a, ‖pr Dw (b cf) a‖ ≤ 1 := by
  intro E _ _ _ H Dw p hp n g h b Λ hn hk hΛ hb cf
  have hnp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]
  have hq : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [lattice_membership_stable_under_approximation (p : ℂ_[p]) (p : ℝ) hq hnp n hn h (fun a i => pr Dw (b (Pi.single i 1)) a) Λ hk hΛ hb cf]
  refine forall_congr' fun a => ?_
  have e : pr Dw (b cf) a = ∑ i, pr Dw (b (Pi.single i 1)) a * cf i := by
    have : cf = ∑ i, cf i • (Pi.single i 1 : Fin g → ℂ_[p]) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp only [pr, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
