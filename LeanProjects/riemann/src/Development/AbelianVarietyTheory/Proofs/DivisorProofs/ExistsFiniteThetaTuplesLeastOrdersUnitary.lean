import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnitsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryComparisonLatticePeriodsAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.exists_uLocTuples_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → X₁.Ω₁), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁
  have hNodd : Odd X₁.S.N := by rw [X₁.ρ.N_eq]; exact (X₁.ρ.n_odd.pow).pow
  have hN2 := X₁.S.N_ge
  have hN3 : 3 ≤ X₁.S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero X₁.S.N := ⟨by omega⟩
  obtain ⟨m₁, m₂, hm₁, hm₂, hX⟩ := GlobalTheory.T.unitaryComparison_lattice_periods_at_point E H Dw hpq l Xo c C X₁
  obtain ⟨B, ι₀, 𝓛, hι₀, hT⟩ := GlobalTheory.T.least_intCombination_minimiserCell_unitary E H (min Dw.p Dw.q) φ hφ X₁.S.N hN3 hNodd
  haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup X₁.S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup X₁.S.Gam => (H : Set X₁.S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup X₁.S.Gam, Finite (T₀ →+ ZMod X₁.S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod X₁.S.N => (f : T₀ → ZMod X₁.S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup X₁.S.Gam, (T₀ →+ ZMod X₁.S.N) × (X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) × X₁.S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set X₁.Ω₁ := {v | v ≠ 0} ∩ Set.range (fun d : Dt => X₁.S.FF d.1 d.2.1 d.2.2.1 / X₁.S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let K := Σ n : Fin B, Σ _ : {L // L ∈ 𝓛 n.1}, ((Fin n.1 → ZMod X₁.S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → X₁.Ω₁ := fun k j => ∏ cl, ((k.2.2 cl : Es) : X₁.Ω₁) ^ ((m₁ : ℤ) * j.1 cl)
  refine ⟨m₂ * ι₀, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun cl _ => zpow_ne_zero _ (k.2.2 cl).2.1
  intro M U₀ EE out hAdm hEE x
  obtain ⟨X, _, _, _, _, n, eb, b₀, μ, e, hrank, hbal, hpos, hμ, hmin, he, htr⟩ := hX M U₀ EE out hAdm hEE x
  obtain ⟨hnB, hL⟩ := hT n X hrank eb
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hbal hpos μ hμ hmin
  have heE : ∀ cl, e cl ∈ Es := fun cl => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he cl
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨⟨n, hnB⟩, ⟨L, hLmem⟩, fun cl => ⟨e cl, heE cl⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  set b' : LinearMap.BilinForm ℤ X := pull π T.be with hb'
  have hbeBal : T.be ∈ balForms H.bar T.P.D.toPre.X := by rw [balForms_eq_levelForms]; exact T.lev
  have hb'bal : b' ∈ balForms H.bar X := pull_mem π hbeBal
  have hμ0 : μ 0 = 0 := by
    by_contra h0
    have h1 := hmin 0 0 (fun i => by simp)
    have h2 := hpos _ h0
    simp at h1
    omega
  have hb'psd : ∀ y, 0 ≤ b' y y := by
    intro y
    have h1 := hπmin 0 ((X₁.S.N : ℤ) • y) (fun i => by simp)
    have hNpos : (0 : ℤ) < X₁.S.N := by exact_mod_cast (show 0 < X₁.S.N by omega)
    have h2 : (0 : ℤ) ≤ (X₁.S.N : ℤ) * ((X₁.S.N : ℤ) * T.be (π y) (π y)) := by
      simpa [hμ0, map_zsmul, LinearMap.smul_apply, smul_eq_mul] using h1
    show 0 ≤ T.be (π y) (π y)
    exact (mul_nonneg_iff_of_pos_left hNpos).1 ((mul_nonneg_iff_of_pos_left hNpos).1 h2)
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'bal hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.be := evalZ_pull φ hπs T.be
  have hφ0 : 0 ≤ φ.evalZ b' := (hφ X hrank).evalZ_nonneg hb'bal hb'psd
  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    have hz : z₀ = (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) := by rw [hξ₀]
    rw [hz]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup X₁.S.Gam) c' κ, X₁.S.FF T₀ c' κ ∈ X₁.S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (X₁.S.ev_mem _ _))
  have hunit : ∀ cl, e cl ≠ 0 ∧ e cl ∈ M.O z₀ ∧ (e cl)⁻¹ ∈ M.O z₀ := by
    intro cl
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he cl
    rw [hc] at hne ⊢
    have hF : X₁.S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : X₁.S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (X₁.S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ cl, M.val y (e cl) ≠ 0 := by
    intro cl
    have h1 := RatModel.val_mul (M := M) hsp (hunit cl).2.1 (hunit cl).2.2
    rw [mul_inv_cancel₀ (hunit cl).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ cl, M.val y (e cl ^ m₁) = M.val y (e cl) ^ m₁ := by
    intro cl
    have := GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e cl) (fun _ => (m₁ : ℤ)) fun _ => hunit cl
    simpa using this
  choose v w hvw using fun cl => GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit T.irr (M.val y (e cl)) (hvne cl)
  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ cl, (m₁ : ℤ) * v cl = (m₂ : ℤ) * b' (μ cl) (μ cl) := by
    intro cl
    obtain ⟨w', hw'⟩ := hq cl
    have hq0 : 0 ≤ (m₂ : ℤ) * b' (μ cl) (μ cl) := mul_nonneg (by positivity) (hb'psd _)
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((m₁ : ℤ) * v cl) *
        algebraMap T.V (FractionRing T.V) ((w cl ^ (m₁ : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ ((((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (m₁ : ℤ) (v cl), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw cl]
      rw [show (((m₂ : ℤ) * b' (μ cl) (μ cl)).toNat) = (((m₂ : ℤ) * T.be (π (μ cl)) (π (μ cl))).toNat) from rfl]
      rw [hw', map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  let Ev : ((Fin n → ZMod X₁.S.N) → ℤ) → ℤ := fun ν => ∑ cl, v cl * ((m₁ : ℤ) * ν cl)
  have hE : ∀ ν, (Ev ν : ℝ) = (m₂ : ℝ) * ∑ cl, (ν cl : ℝ) * (b' (μ cl) (μ cl) : ℝ) := by
    intro ν
    have h1 : Ev ν = (m₂ : ℤ) * ∑ cl, ν cl * b' (μ cl) (μ cl) := by
      simp only [Ev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun cl _ => ?_
      have := hNv cl
      linear_combination (ν cl) * this
    rw [h1]; push_cast; ring
  have hzs : ∀ (f : (Fin n → ZMod X₁.S.N) → ℤ) (s : Finset (Fin n → ZMod X₁.S.N)),
      ∏ cl ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f cl = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ cl ∈ s, f cl := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ Ev ν *
      algebraMap T.V (FractionRing T.V) ((∏ cl, w cl ^ ((m₁ : ℤ) * ν cl) : T.Vˣ) : T.V) := by
    intro ν
    rw [GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp _ _ _ fun cl => hunit cl]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin n → ZMod X₁.S.N) → ℤ, (∏ cl, e cl ^ ((m₁ : ℤ) * ν cl)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun cl _ => ?_
    rcases Int.eq_nat_or_neg ((m₁ : ℤ) * ν cl) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit cl).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit cl).2.2 k
  have hge : ∀ ν ∈ L, ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be ≤ Ev ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) m₂)
    rw [hE ν, ← hφeq]; push_cast
    nlinarith
  have hE0 : ((Ev ν₀ : ℤ) : ℝ) = ((m₂ * ι₀ : ℕ) : ℝ) * φ.evalZ T.be := by
    rw [hE ν₀, ← heq, ← hφeq]; push_cast; ring
  have hEnn : 0 ≤ Ev ν₀ := by
    have : (0 : ℝ) ≤ (Ev ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(Ev ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show UOrdGe M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * j.1 cl)) _
    have hle' : Ev ν₀ ≤ Ev j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, Ev j.1 = ((Ev ν₀).toNat : ℤ) + d := ⟨(Ev j.1 - Ev ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ cl, w cl ^ ((m₁ : ℤ) * j.1 cl) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show UOrdEq M T ξ (∏ cl, e cl ^ ((m₁ : ℤ) * ν₀ cl)) _
    refine ⟨∏ cl, w cl ^ ((m₁ : ℤ) * ν₀ cl), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
