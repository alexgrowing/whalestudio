import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
open Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitSmooth

open GlobalTheory.CompanionTheory.SplitRep GlobalTheory.CompanionTheory.SplitPi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem modulus_near : ∀ᶠ x : Fˣ in 𝓝 1, modulus (x : F) = 1 := by
  have hs : IsOpen {x : Fˣ | (x : F) ∈ 𝒪[F] ∧ ((x⁻¹ : Fˣ) : F) ∈ 𝒪[F]} :=
    ((Valuation.isOpen_integer (R := F)).preimage Units.continuous_val).inter
      ((Valuation.isOpen_integer (R := F)).preimage Units.continuous_coe_inv)
  have h1 : (1 : Fˣ) ∈ {x : Fˣ | (x : F) ∈ 𝒪[F] ∧ ((x⁻¹ : Fˣ) : F) ∈ 𝒪[F]} := by
    simp [Valuation.mem_integer_iff]
  filter_upwards [hs.mem_nhds h1] with x hx
  have a : ValuativeRel.valuation F (x : F) ≤ 1 := hx.1
  have b : ValuativeRel.valuation F ((x⁻¹ : Fˣ) : F) ≤ 1 := hx.2
  have c : ValuativeRel.valuation F (x : F) = 1 := by
    refine le_antisymm a ?_
    calc (1 : ValuativeRel.ValueGroupWithZero F)
        = ValuativeRel.valuation F ((x : F) * ((x⁻¹ : Fˣ) : F)) := by simp
      _ = ValuativeRel.valuation F (x : F) * ValuativeRel.valuation F ((x⁻¹ : Fˣ) : F) := map_mul _ _ _
      _ ≤ ValuativeRel.valuation F (x : F) := mul_le_of_le_one_right' b
  exact modulus_eq_one_iff.2 ⟨x.ne_zero,
    mem_unitFiltrationUnits_zero_iff_ord.1 (mem_unitFiltrationUnits_zero_iff.2 c)⟩

theorem piS_one (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) :
    piS χ c₁ 1 Φ = Φ := by
  have e1 : one1 (1 : GL (Fin 2) F) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [one1]
  rw [piS_eq, e1]
  funext z
  rw [rWS_zero χ Matrix.det_one (by simp)]
  simp [cst, mp]
  congr 1
  ext <;> simp

theorem piS_uni (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (b : F) (Ψ : F × F → ℂ) (z : F × F) :
    piS χ c₁ (uni2 b) Ψ z = (χ (b * (z.1 * z.2)) : ℂ) * Ψ z := by
  have hdet : ((uni2 b : GL (Fin 2) F).val).det = 1 := by
    simp [uni2, Matrix.det_fin_two]
  have hd : GeneralLinearGroup.det (uni2 b : GL (Fin 2) F) = 1 := Units.ext (by simpa using hdet)
  rw [piS_eq]
  simp only []
  rw [rWS_zero χ (det_normalized_determinant_one _) (by simp [one1, uni2])]
  have e0 : one1 (uni2 b : GL (Fin 2) F) 0 0 = 1 := by simp [one1, hdet, uni2]
  have e1 : one1 (uni2 b : GL (Fin 2) F) 0 1 = b := by simp [one1, uni2]
  rw [e0, e1, hdet]
  have : (1 * z.1, 1 * z.2) * ((1 : F), (1 : F)) = z := by ext <;> simp
  rw [this]
  simp [cst, mp, hd]

theorem piS_dg (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (a d : Fˣ) (Ψ : F × F → ℂ) (z : F × F) :
    piS χ c₁ (dg2 a d) Ψ z = ((c₁ (a * d) : ℂˣ) : ℂ) * mp (a * d) (1 / 2) *
      ((modulus ((d⁻¹ : Fˣ) : F) : ℝ) : ℂ) * Ψ ((a : F) * z.1, ((d⁻¹ : Fˣ) : F) * z.2) := by
  have hdet : ((dg2 a d : GL (Fin 2) F).val).det = (a : F) * d := by
    simp [dg2, Matrix.det_fin_two]
  have hd : GeneralLinearGroup.det (dg2 a d : GL (Fin 2) F) = a * d := Units.ext (by simpa using hdet)
  rw [piS_eq]
  simp only []
  rw [rWS_zero χ (det_normalized_determinant_one _) (by simp [one1, dg2])]
  have e0 : one1 (dg2 a d : GL (Fin 2) F) 0 0 = ((d⁻¹ : Fˣ) : F) := by
    simp only [one1, hdet]
    simp [dg2]
    field_simp
  have e1 : one1 (dg2 a d : GL (Fin 2) F) 0 1 = 0 := by simp [one1, dg2]
  rw [e0, e1, hdet]
  have : (((d⁻¹ : Fˣ) : F) * z.1, ((d⁻¹ : Fˣ) : F) * z.2) * ((a : F) * d, (1 : F)) =
      ((a : F) * z.1, ((d⁻¹ : Fˣ) : F) * z.2) := by
    ext
    · simp
      field_simp
    · simp
  rw [this]
  simp [cst, hd]
  ring

theorem tube {Ψ : F × F → ℂ} (hΨ : Ψ ∈ SBE (F × F)) :
    ∀ᶠ p : Fˣ × Fˣ in 𝓝 1, ∀ z : F × F, Ψ ((p.1 : F) * z.1, ((p.2⁻¹ : Fˣ) : F) * z.2) = Ψ z := by
  have hc : Continuous (fun q : (Fˣ × Fˣ) × (F × F) =>
      (((q.1.1 : Fˣ) : F) * q.2.1, (((q.1.2)⁻¹ : Fˣ) : F) * q.2.2)) :=
    ((Units.continuous_val.comp (continuous_fst.comp continuous_fst)).mul
        (continuous_fst.comp continuous_snd)).prodMk
      ((Units.continuous_coe_inv.comp (continuous_snd.comp continuous_fst)).mul
        (continuous_snd.comp continuous_snd))
  have hK : IsCompact (tsupport Ψ) := hΨ.2
  have E : ∀ᶠ p : Fˣ × Fˣ in 𝓝 1, ∀ y ∈ tsupport Ψ,
      Ψ ((p.1 : F) * y.1, ((p.2⁻¹ : Fˣ) : F) * y.2) = Ψ y := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 := (hΨ.1.comp_continuous hc).eventually_eq ((1 : Fˣ × Fˣ), y)
    have h2 := (hΨ.1.comp_continuous (continuous_snd (X := Fˣ × Fˣ) (Y := F × F))).eventually_eq
      ((1 : Fˣ × Fˣ), y)
    filter_upwards [h1, h2] with q a b
    simp only [Function.comp] at a b
    rw [a, b]
    simp
  have E' : ∀ᶠ p : Fˣ × Fˣ in 𝓝 1, ∀ y ∈ tsupport Ψ,
      Ψ (((p⁻¹).1 : F) * y.1, ((((p⁻¹).2)⁻¹ : Fˣ) : F) * y.2) = Ψ y := by
    have ht : Tendsto (fun p : Fˣ × Fˣ => p⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv (G := Fˣ × Fˣ)).tendsto 1
    exact ht.eventually E
  filter_upwards [E, E'] with p a b z
  by_cases hz : z ∈ tsupport Ψ
  · exact a z hz
  · have hz0 : Ψ z = 0 := image_eq_zero_of_notMem_tsupport hz
    rw [hz0]
    by_contra hne
    have hy : ((p.1 : F) * z.1, ((p.2⁻¹ : Fˣ) : F) * z.2) ∈ tsupport Ψ :=
      subset_tsupport _ hne
    have := b _ hy
    have e : (((p⁻¹).1 : F) * ((p.1 : F) * z.1), ((((p⁻¹).2)⁻¹ : Fˣ) : F) * (((p.2⁻¹ : Fˣ) : F) * z.2)) = z := by
      ext <;> simp
    rw [e, hz0] at this
    exact hne this.symm

theorem uni_fix {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ : Fˣ →* ℂˣ)
    {Ψ : F × F → ℂ} (hΨ : Ψ ∈ SBE (F × F)) :
    ∀ᶠ b : F in 𝓝 0, piS χ c₁ (uni2 b) Ψ = Ψ := by
  have hK : IsCompact (tsupport Ψ) := hΨ.2
  have E : ∀ᶠ b : F in 𝓝 0, ∀ y ∈ tsupport Ψ, (χ (b * (y.1 * y.2)) : ℂ) = 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have hc : Continuous (fun q : F × (F × F) => q.1 * (q.2.1 * q.2.2)) := by fun_prop
    have h1 := ((isLC_char hχ hχ1).comp_continuous hc).eventually_eq ((0 : F), y)
    filter_upwards [h1] with q a
    simp only [Function.comp] at a
    rw [a]
    simp
  filter_upwards [E] with b hb
  funext z
  rw [piS_uni]
  by_cases hz : z ∈ tsupport Ψ
  · rw [hb z hz, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]

def lo (t : F) : GL (Fin 2) F := w0⁻¹ * uni2 (-t) * w0

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem lo_val (t : F) : (lo t : GL (Fin 2) F).val = !![1, 0; t, 1] := by
  have : ((w0⁻¹ : GL (Fin 2) F)).val = !![0, -1; 1, 0] := rfl
  simp only [lo, Units.val_mul, this]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, w0, Matrix.mul_apply, Fin.sum_univ_two]

theorem lo_fix [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ : Fˣ →* ℂˣ)
    {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    ∀ᶠ t : F in 𝓝 0, piS χ c₁ (lo t) Φ = Φ := by
  have hΨ := piS_mem hχ hχ1 c₁ hΦ (w0 : GL (Fin 2) F)
  have ht : Tendsto (fun t : F => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg (G := F)).tendsto 0
  filter_upwards [ht.eventually (uni_fix hχ hχ1 c₁ hΨ)] with t h
  rw [lo, piS_mul hχ hχ1 c₁ hΦ, piS_mul hχ hχ1 c₁ hΨ, h, ← piS_mul hχ hχ1 c₁ hΦ, inv_mul_cancel,
    piS_one]

theorem dg_fix {χ : AddChar F Circle} {c₁ : Fˣ →* ℂˣ} (hc : Continuous c₁)
    {Ψ : F × F → ℂ} (hΨ : Ψ ∈ SBE (F × F)) :
    ∀ᶠ p : Fˣ × Fˣ in 𝓝 1, piS χ c₁ (dg2 p.1 p.2) Ψ = Ψ := by
  have hker : ∀ᶠ x : Fˣ in 𝓝 1, c₁ x = 1 :=
    (GlobalTheory.RootEx.UniformLattices.isOpen_ker_of_continuous c₁ hc).mem_nhds (one_mem c₁.ker)
  have hA : ∀ᶠ x : Fˣ in 𝓝 1, c₁ x = 1 ∧ modulus (x : F) = 1 := hker.and modulus_near
  have t1 : Tendsto (fun p : Fˣ × Fˣ => p.1) (𝓝 1) (𝓝 1) := continuous_fst.tendsto 1
  have t2 : Tendsto (fun p : Fˣ × Fˣ => p.2) (𝓝 1) (𝓝 1) := continuous_snd.tendsto 1
  filter_upwards [t1.eventually hA, t2.eventually hA, tube hΨ] with p ha hd hT
  funext z
  rw [piS_dg, hT z]
  have m : modulus (((p.1 * p.2 : Fˣ)) : F) = 1 := by
    rw [Units.val_mul, modulus_mul, ha.2, hd.2, one_mul]
  have m' : modulus (((p.2⁻¹ : Fˣ)) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, modulus_inv, hd.2, inv_one]
  have m2 : modulus ((p.1 : F) * (p.2 : F)) = 1 := by simpa using m
  have m3 : modulus ((p.2 : F)⁻¹) = 1 := by simpa using m'
  simp [mp, m2, m3, ha.1, hd.1]

def toU (x : F) : Fˣ := by
  classical exact if h : x = 0 then 1 else Units.mk0 x h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
theorem toU_val {x : F} (h : x ≠ 0) : ((toU x : Fˣ) : F) = x := by
  simp [toU, h]

omit [MeasurableSpace F] [BorelSpace F] in
theorem toU_tendsto : Tendsto (toU : F → Fˣ) (𝓝 1) (𝓝 1) := by
  rw [Units.isEmbedding_val₀.isInducing.tendsto_nhds_iff]
  have : (Units.val ∘ toU : F → F) =ᶠ[𝓝 1] id := by
    filter_upwards [(continuous_id.tendsto (1 : F)).eventually_ne (one_ne_zero)] with x hx
    exact toU_val hx
  simpa using (tendsto_id (α := F) (x := 𝓝 1)).congr' this.symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in

theorem iwahori (u : GL (Fin 2) F) (a e : Fˣ) (ha : (a : F) = u.val 0 0)
    (he : (e : F) = u.val 1 1 - u.val 0 1 * u.val 1 0 / u.val 0 0) :
    u = lo (u.val 1 0 / u.val 0 0) * dg2 a e * uni2 (u.val 0 1 / u.val 0 0) := by
  have h0 : u.val 0 0 ≠ 0 := ha ▸ a.ne_zero
  apply Units.ext
  simp only [Units.val_mul, lo_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two, ha, he] <;> field_simp <;> ring

theorem stab_near [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    {c₁ : Fˣ →* ℂˣ} (hc : Continuous c₁) {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) :
    ∀ᶠ u : GL (Fin 2) F in 𝓝 1, piS χ c₁ u Φ = Φ := by
  have hent : ∀ i j, Continuous (fun u : GL (Fin 2) F => u.val i j) := fun i j =>
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) F)).matrix_elem i j
  have ta : Tendsto (fun u : GL (Fin 2) F => u.val 0 0) (𝓝 1) (𝓝 1) := by
    simpa using (hent 0 0).tendsto 1
  have tb : Tendsto (fun u : GL (Fin 2) F => u.val 0 1) (𝓝 1) (𝓝 0) := by
    simpa using (hent 0 1).tendsto 1
  have tc : Tendsto (fun u : GL (Fin 2) F => u.val 1 0) (𝓝 1) (𝓝 0) := by
    simpa using (hent 1 0).tendsto 1
  have td : Tendsto (fun u : GL (Fin 2) F => u.val 1 1) (𝓝 1) (𝓝 1) := by
    simpa using (hent 1 1).tendsto 1
  have tba : Tendsto (fun u : GL (Fin 2) F => u.val 0 1 / u.val 0 0) (𝓝 1) (𝓝 0) := by
    have h := tb.div ta one_ne_zero
    rw [zero_div] at h
    exact h
  have tca : Tendsto (fun u : GL (Fin 2) F => u.val 1 0 / u.val 0 0) (𝓝 1) (𝓝 0) := by
    have h := tc.div ta one_ne_zero
    rw [zero_div] at h
    exact h
  have te : Tendsto (fun u : GL (Fin 2) F => u.val 1 1 - u.val 0 1 * u.val 1 0 / u.val 0 0) (𝓝 1) (𝓝 1) := by
    simpa using td.sub ((tb.mul tc).div ta one_ne_zero)
  have tp : Tendsto (fun u : GL (Fin 2) F => ((toU (u.val 0 0), toU (u.val 1 1 - u.val 0 1 * u.val 1 0 / u.val 0 0)) :
      Fˣ × Fˣ)) (𝓝 1) (𝓝 1) := by
    exact (toU_tendsto.comp ta).prodMk_nhds (toU_tendsto.comp te)
  filter_upwards [ta.eventually_ne one_ne_zero, te.eventually_ne one_ne_zero,
    tba.eventually (uni_fix hχ hχ1 c₁ hΦ), tca.eventually (lo_fix hχ hχ1 c₁ hΦ),
    tp.eventually (dg_fix (χ := χ) hc hΦ)] with u h0 h1 hU hL hD
  rw [iwahori u _ _ (toU_val h0) (toU_val h1), piS_mul hχ hχ1 c₁ hΦ, hU,
    piS_mul hχ hχ1 c₁ hΦ, hD, hL]

def stab [CharZero F] {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ : Fˣ →* ℂˣ)
    {Φ : F × F → ℂ} (hΦ : Φ ∈ SBE (F × F)) : Subgroup (GL (Fin 2) F) where
  carrier := {h | piS χ c₁ h Φ = Φ}
  mul_mem' := fun {a b} ha hb => by
    change piS χ c₁ (a * b) Φ = Φ
    rw [piS_mul hχ hχ1 c₁ hΦ, show piS χ c₁ b Φ = Φ from hb, show piS χ c₁ a Φ = Φ from ha]
  one_mem' := piS_one χ c₁ Φ
  inv_mem' := fun {a} ha => by
    change piS χ c₁ a⁻¹ Φ = Φ
    have h := piS_mul hχ hχ1 c₁ hΦ a⁻¹ a
    rw [inv_mul_cancel, piS_one, show piS χ c₁ a Φ = Φ from ha] at h
    exact h.symm

end GlobalTheory.CompanionTheory.SplitSmooth
