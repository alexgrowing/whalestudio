import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinrankOfPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_extend {M V E : Type} [AddCommGroup M] [AddCommGroup V] [AddCommGroup E] [Module ℚ E]
    (j : M →+ V) (hj : Function.Injective j) (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) (P : M →+ E) :
    ∃ Q : V →+ E, ∀ u, Q (j u) = P u := by
  choose m u hm h using hd
  have key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v →
      ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v := by
    intro w n v hn hv
    have h1 : n • u w = m w • v := hj (by
      rw [map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])
    have h2 : n • P (u w) = m w • P v := by rw [← map_nsmul, ← map_nsmul, h1]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hm' : (m w : ℚ) ≠ 0 := by exact_mod_cast hm w
    have h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]
    calc ((m w : ℚ)⁻¹) • P (u w) = ((m w : ℚ)⁻¹ * (n : ℚ)⁻¹) • ((n : ℚ) • P (u w)) := by
          rw [smul_smul]; congr 1; field_simp
      _ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp
  refine ⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩
  · intro a b
    have hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b) := by
      rw [map_add, map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul,
        smul_comm (m a) (m b) a]
    have hk := key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab
    have hma : (m a : ℚ) ≠ 0 := by exact_mod_cast hm a
    have hmb : (m b : ℚ) ≠ 0 := by exact_mod_cast hm b
    rw [hk, map_add, map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul]
    push_cast
    congr 2 <;> field_simp
  · intro v
    have hk := key (j v) 1 v one_ne_zero (by simp)
    simpa using hk

private theorem finrank_eq_of_place {M V : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [AddCommGroup V] [Module ℚ V] (j : M →+ V) (hj : Function.Injective j)
    (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) :
    Module.finrank ℤ M = Module.finrank ℚ V :=
  _root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd

private theorem period_of_basis {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {g : ℕ}
    (P : M →+ (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hc : Module.finrank ℤ M = 2 * g) :
    Function.Injective P ∧ DiscreteTopology P.range := by
  let b := Module.finBasis ℤ M
  let v : Fin (Module.finrank ℤ M) → (Fin g → ℂ) := fun i => P (b i)
  have hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [hPx]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Fintype.card_fin, hc, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have li : LinearIndependent ℝ v := linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr
  refine ⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩
  · have h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0 := by
      rw [← hx, hPx]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _
    have h1 := Fintype.linearIndependent_iff.mp li _ h0
    apply b.repr.injective
    ext i
    simpa using h1 i
  · let bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ) := Module.Basis.mk li hsp
    have hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)) := by
      have hb : Set.range bb = Set.range v := by
        rw [Module.Basis.coe_mk]
      rw [hb]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show P x ∈ Submodule.span ℤ (Set.range v)
        rw [hPx]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hy
        have hy' : y ∈ Submodule.span ℤ (Set.range v) := hy
        induction hy' using Submodule.span_induction with
        | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨b i, rfl⟩
        | zero => exact zero_mem P.range
        | add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))
        | smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r
    have hd : DiscreteTopology (Submodule.span ℤ (Set.range bb)) := inferInstance
    have hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))) := hd
    rw [← hset] at hd'
    exact hd'

private theorem herm_smul_mat {g : ℕ} (r : ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    hermForm (r • H) x y = r * hermForm H x y := by
  simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]

private theorem herm_nsmul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (m n : ℕ) (x y : Fin g → ℂ) :
    hermForm H (m • x) (n • y) = ((m : ℂ) * n) * hermForm H x y := by
  simp only [hermForm]
  rw [← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, star_natCast]
  ring

private theorem herm_scale {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) • Hm).IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm ((r : ℂ) • Hm) z z).re := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  · rw [herm_smul_mat, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)

theorem UpperTheory.Gal.W2.placePer_of :
    UpperTheory.Gal.W2.PlacePer := by
  intro p _ D G L β ρ D' j hpl
  obtain ⟨hinj, hact, hden, s, hs, hEF⟩ := hpl
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hform : ∀ (m n : ℕ) (u w : VQ D),
      formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w := by
    intro m n u w
    simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩
  · obtain ⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩ := hP
    obtain ⟨Q, hQ⟩ := exists_extend j hinj hden P
    have hsc := herm_scale hH hpos (inv_pos.mpr hsR)
    refine ⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩
    · obtain ⟨m, a, hm, h⟩ := hden w
      apply IsAddTorsionFree.nsmul_right_injective hm
      show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)
      have e1 : m • Q (actQ D c w) = P (c • a) := by
        rw [← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]
      have e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a := by
        rw [← hQ, ← h, map_nsmul, Matrix.mulVec_smul]
      rw [e1, e2, hPa]
    · rw [eq_top_iff, ← hPs]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, hQ x⟩
    · obtain ⟨m, a, hm, ha⟩ := hden u
      obtain ⟨n, b, hn, hb⟩ := hden w
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) =
          (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w) := by
        rw [← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]
        push_cast
        rfl
      have h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im =
          ((s : ℝ))⁻¹ * (D'.EF a b : ℝ) := by
        rw [herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]
      have h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ)) := by
        have h4 := hEF a b
        rw [← ha, ← hb, hform] at h4
        exact_mod_cast h4
      rw [h1, Complex.im_ofReal_mul, h3] at h2
      have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
      have h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im =
          ((m : ℝ) * n) * (formB L β u w : ℚ) := by
        rw [h2]
        field_simp
      exact mul_left_cancel₀ (mul_ne_zero hmR hnR) h5
  · obtain ⟨hQa, hQs, Hm, hH, hpos, hIm⟩ := hQ
    have hc : Module.finrank ℤ D'.La = 2 * D.g := by
      rw [finrank_eq_of_place j hinj hden, hrk]
      haveI : Module.Free ℤ D.La := D.freeLa
      exact Module.finrank_baseChange
    have hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤ := by
      rw [eq_top_iff, ← hQs]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, a, hm, h⟩ := hden w
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have e : Q w = (m : ℝ)⁻¹ • Q (j a) := by
        rw [← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨hi, hdisc⟩ := period_of_basis (Q.comp j) hs' hc
    have hsc := herm_scale hH hpos hsR
    refine ⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩
    · simp only [AddMonoidHom.comp_apply]
      rw [hact, hQa]
    · simp only [AddMonoidHom.comp_apply]
      rw [herm_smul_mat, Complex.im_ofReal_mul, hIm]
      have h4 := hEF x y
      exact_mod_cast h4.symm
