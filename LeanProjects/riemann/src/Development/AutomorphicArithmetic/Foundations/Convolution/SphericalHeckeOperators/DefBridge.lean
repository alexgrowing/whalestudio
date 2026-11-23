import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
private theorem iw_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) := by
  ext g
  constructor
  · rintro ⟨⟨u, rfl⟩, hl⟩
    refine ⟨u, ?_, rfl⟩
    change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply]
    exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mpr (hl i j hij)
  · intro hg
    exact ⟨iwahori_le_integralGL F n hg, ((mem_iwahori_iff F n).1 hg).2.1⟩

open ValuativeRel in
private theorem unif (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    PositivityTheory.Rg.Tf.Loc.IsUniformiser ((uniformizerUnit F : Fˣ) : F) := by
  refine ⟨valuation_uniformizer_lt_one F, Units.ne_zero _, fun x hx => ?_⟩
  let y : 𝒪[F] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (residue_eq_zero_iff_valuation_lt_one F y).mpr hx
  have h1 := (mem_maximalIdeal_pow_iff F (m := 1) (y := y)).1 (by rwa [pow_one])
  simpa using h1

open ValuativeRel in
private theorem diag_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (t : Fin n → Fˣ) (ht : ∀ i, valuation F ((t i : Fˣ) : F) = 1) : diagGL F n t ∈ iwahori F n := by
  have he : ∀ i j, ((diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      Matrix.diagonal (fun i => ((t i : Fˣ) : F)) i j := fun i j => rfl
  refine (mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    by_cases h : i = j
    · subst h
      simp [ht]
    · simp [Matrix.diagonal_apply_ne _ h]
  · rw [he, Matrix.diagonal_apply_ne _ hij.ne']
    simp
  · rw [he]
    simp [ht]

theorem UpperTheory.ConvolutionTheory.H.defBridge :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
      PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) F = integralGL F n ∧
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) ∧
      (∃ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F)) ∧
      ∀ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ,
        PositivityTheory.Rg.Tf.Loc.iwahoriFn F (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) = uFn F a := by
  intro F _ _ _ _ n
  have hI := iw_eq F n
  refine ⟨rfl, hI, ⟨uniformizerUnit F, unif F⟩, fun ϖ hϖ a => ?_⟩
  have h0 := unif F
  have hv : ValuativeRel.valuation F (ϖ : F) = ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) :=
    le_antisymm (h0.2.2 _ hϖ.1) (hϖ.2.2 _ h0.1)
  set u : Fˣ := ϖ * (uniformizerUnit F)⁻¹ with hu
  have hu1 : ValuativeRel.valuation F (u : F) = 1 := by
    have hne : ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    rw [hu, Units.val_mul, map_mul, hv, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hne]
  have hd : diagGL F n (fun i => u ^ a i) ∈ iwahori F n := by
    refine diag_mem F n _ fun i => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu1, one_zpow]
  have hfac : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = torusPow F n a * diagGL F n (fun i => u ^ a i) := by
    have : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = diagGL F n (fun i => ϖ ^ a i) := Units.ext rfl
    rw [this, torusPow, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hu, ← mul_zpow]
    simp
  unfold PositivityTheory.Rg.Tf.Loc.iwahoriFn uFn dco
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, hI, SetLike.mem_coe, hfac]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _ * y, mul_mem hd hy, by simp only [mul_assoc]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, (diagGL F n (fun i => u ^ a i))⁻¹ * y, mul_mem (inv_mem hd) hy, by simp only [mul_assoc, mul_inv_cancel_left]⟩
