import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotOrdGeOfNotMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrdersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinFormPsdOfMinimalTupleModNStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingEqUniformiserZpowMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelValueProdZpowLocalUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.exists_locTuples_theta_of_adm : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a := by
  intro g n hg hn hodd F φ hφ W hW o' Ω _ _ _ _ S ρ u hBig hSharp hgen
  have hNodd : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN2 := S.N_ge
  have hN3 : 3 ≤ S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  have hn2 : ρ.n ≠ 2 := by
    intro h2; have := ρ.n_odd; rw [h2] at this; exact (Nat.not_odd_iff_even.2 even_two) this
  have hε : ∃ ε : Fin 8 → ℤ, Nat.Coprime S.N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
    rw [ρ.N_eq]; exact GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow W hW ρ.n ρ.k ρ.n_prime hn2
  have hC := GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations g φ hφ W hW.1 S.N hN3 hε
  choose ιf 𝓛f hιf using fun R : Fin (g + 1) => hC R.1 (Nat.lt_succ_iff.1 R.2)
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup S.Gam, (T₀ →+ ZMod S.N) × (S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) × S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set Ω := {v | v ≠ 0} ∩ Set.range (fun d : Dt => S.FF d.1 d.2.1 d.2.2.1 / S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let mult : Fin (g + 1) → ℕ := fun R => ∏ s ∈ Finset.univ.erase R, ιf s
  let K := Σ R : Fin (g + 1), Σ _ : {L // L ∈ 𝓛f R}, ((Fin 8 → Fin R.1 → ZMod S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → Ω := fun k j => ∏ c, ((k.2.2 c : Es) : Ω) ^ ((mult k.1 : ℤ) * j.1 c)
  refine ⟨∏ R, ιf R, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun R _ => by have := (hιf R).1; omega)
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (k.2.2 c).2.1
  intro M U₀ EE FinalForm hAdm hEE x
  obtain ⟨r, b₀, μ, e, hr, hsym, hpos, hμ, hmin, he, htr⟩ :=
    GlobalTheory.T.thetaModel_local_lattice_fourierParts_orders g n hg hn hodd F W hW o' Ω S ρ u hBig hSharp hgen hN0 M U₀ EE FinalForm hAdm hEE x
  let R : Fin (g + 1) := ⟨r, by omega⟩
  obtain ⟨hιR, hL⟩ := hιf R
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hsym hpos μ hμ hmin
  have heE : ∀ c, e c ∈ Es := fun c => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he c
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨R, ⟨L, hLmem⟩, fun c => ⟨e c, heE c⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec

  set b' := T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap with hb'
  have hb'sym : ∀ x y, b' x y = b' y x := fun x y => T.symm _ _
  have hb'psd : ∀ x, 0 ≤ b' x x := GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN (N := S.N) (by omega) W hW b' (μ 0) fun α hα =>
    hπmin 0 α fun u i => by obtain ⟨m, hm⟩ := hα u i; simp [hm, hμ]
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'sym hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.β := by
    have hpull : pull π.toIntLinearMap T.β = b' := LinearMap.ext₂ fun _ _ => rfl
    rw [← hpull]; exact evalZ_pull φ (r := π.toIntLinearMap) hπs T.β
  have hφ0 : 0 ≤ φ.evalZ b' :=
    (hφ (Fin r → ℤ) (by rw [Module.finrank_fin_fun]; exact hr)).evalZ_nonneg (mem_balForms_int.2 hb'sym) hb'psd

  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    rw [hz₀, hy, ← hξ₀]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup S.Gam) c' κ, S.FF T₀ c' κ ∈ S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))
  have hunit : ∀ c, e c ≠ 0 ∧ e c ∈ M.O z₀ ∧ (e c)⁻¹ ∈ M.O z₀ := by
    intro c
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he c
    rw [hc] at hne ⊢
    have hF : S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ c, M.val y (e c) ≠ 0 := by
    intro c
    have h1 := RatModel.val_mul (M := M) hsp (hunit c).2.1 (hunit c).2.2
    rw [mul_inv_cancel₀ (hunit c).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ c, M.val y (e c ^ S.N) = M.val y (e c) ^ S.N := by
    intro c
    have := GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e c) (fun _ => (S.N : ℤ)) fun _ => hunit c
    simpa using this
  choose v w hvw using fun c => GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit T.irr (M.val y (e c)) (hvne c)

  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ c, (S.N : ℤ) * v c = qW W b' (μ c) := by
    intro c
    obtain ⟨hq0, w', hw'⟩ := hq c
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((S.N : ℤ) * v c) *
        algebraMap T.V (FractionRing T.V) ((w c ^ (S.N : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ (((qW W b' (μ c)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (S.N : ℤ) (v c), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw c, hw',
        map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  have hmR : (∏ R', ιf R') = ιf R * mult R := (Finset.mul_prod_erase Finset.univ ιf (Finset.mem_univ R)).symm
  let E : ((Fin 8 → Fin r → ZMod S.N) → ℤ) → ℤ := fun ν => ∑ c, v c * ((mult R : ℤ) * ν c)
  have hE : ∀ ν, (S.N : ℝ) * (E ν : ℝ) = (mult R : ℝ) * ∑ c, (ν c : ℝ) * (qW W b' (μ c) : ℝ) := by
    intro ν
    simp only [E, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hNv c]; push_cast; ring
  have hzs : ∀ (f : (Fin 8 → Fin r → ZMod S.N) → ℤ) (s : Finset (Fin 8 → Fin r → ZMod S.N)),
      ∏ c ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f c = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ c ∈ s, f c := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ c, e c ^ ((mult R : ℤ) * ν c)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ E ν *
      algebraMap T.V (FractionRing T.V) ((∏ c, w c ^ ((mult R : ℤ) * ν c) : T.Vˣ) : T.V) := by
    intro ν
    rw [GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp _ _ _ fun c => hunit c]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin 8 → Fin r → ZMod S.N) → ℤ, (∏ c, e c ^ ((mult R : ℤ) * ν c)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun c _ => ?_
    rcases Int.eq_nat_or_neg ((mult R : ℤ) * ν c) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit c).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit c).2.2 k
  have hιeq : ((∏ R', ιf R' : ℕ) : ℝ) = (ιf R : ℝ) * mult R := by rw [hmR]; push_cast; ring
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast (show 0 < S.N by omega)
  have hge : ∀ ν ∈ L, ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β ≤ E ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) (mult R))
    rw [← hE ν] at h1
    rw [hιeq, ← hφeq]
    refine le_of_mul_le_mul_left ?_ hNpos
    nlinarith
  have hE0 : ((E ν₀ : ℤ) : ℝ) = ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β := by
    have h1 := congrArg (HMul.hMul (mult R : ℝ)) heq
    rw [← hE ν₀] at h1
    rw [hιeq, ← hφeq]
    refine mul_left_cancel₀ hNpos.ne' ?_
    nlinarith
  have hEnn : 0 ≤ E ν₀ := by
    have : (0 : ℝ) ≤ (E ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(E ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show GlobalTheory.Poinc.OrdGe M T ξ (∏ c, e c ^ ((mult R : ℤ) * j.1 c)) _
    have hle' : E ν₀ ≤ E j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, E j.1 = ((E ν₀).toNat : ℤ) + d := ⟨(E j.1 - E ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ c, w c ^ ((mult R : ℤ) * j.1 c) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show GlobalTheory.Poinc.OrdEq M T ξ (∏ c, e c ^ ((mult R : ℤ) * ν₀ c)) _
    refine ⟨∏ c, w c ^ ((mult R : ℤ) * ν₀ c), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
