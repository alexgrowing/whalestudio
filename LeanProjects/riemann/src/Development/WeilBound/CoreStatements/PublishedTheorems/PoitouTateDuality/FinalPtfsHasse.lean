import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmpA

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

section Hasse

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem urChar_mul (N : ℕ+) (g h : Gal(Ω/K)) :
    urChar K Ω N (g * h) = urChar K Ω N g + urChar K Ω N h := by
  simp only [urChar, map_mul, toAdd_mul, map_add]

theorem urChar_one (N : ℕ+) : urChar K Ω N 1 = 0 := by
  simp only [urChar, map_one, toAdd_one, map_zero]

theorem urChar_of_ker (N : ℕ+) {g : Gal(Ω/K)} (hg : unramifiedDegree K Ω g = 1) :
    urChar K Ω N g = 0 := by
  simp only [urChar, hg, toAdd_one, map_zero]

theorem urChar_of_deg_one (N : ℕ+) {g : Gal(Ω/K)}
    (hg : unramifiedDegree K Ω g = Multiplicative.ofAdd 1) : urChar K Ω N g = 1 := by
  simp only [urChar, hg, toAdd_ofAdd, map_one]

theorem continuous_urChar (N : ℕ+) : Continuous (urChar K Ω N) :=
  continuous_unramifiedCoord (K := K) (Ω := Ω) N

def urPsi (N : ℕ+) : Additive Gal(Ω/K) →ₜ+ QZ where
  toFun a := zmodToQZ (N : ℕ) (urChar K Ω N (Additive.toMul a))
  map_zero' := by simp only [toMul_zero, urChar_one, map_zero]
  map_add' a b := by simp only [toMul_add, urChar_mul, map_add]
  continuous_toFun :=
    (continuous_of_discreteTopology.comp (continuous_urChar (K := K) (Ω := Ω) N)).comp
      continuous_toMul

theorem reprIco_urPsi (N : ℕ+) (g : Gal(Ω/K)) :
    reprIco (charAdd (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g)) =
      ((urChar K Ω N g).val : ℚ) / (N : ℕ) := by
  rw [charAdd_apply]
  have h1 : (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) =
      QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ)) := by
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = _
    conv_lhs => rw [← ZMod.intCast_zmod_cast (urChar K Ω N g)]
    rw [zmodToQZ_intCast, ZMod.cast_eq_val]
    push_cast
    rfl
  rw [h1]
  have h2 : QZ.toAddCircle (QZ.mk (((urChar K Ω N g).val : ℤ) / ((N : ℕ) : ℤ))) =
      ((((urChar K Ω N g).val : ℚ) / (N : ℕ) : ℚ) : AddCircle (1 : ℚ)) := by
    simp [QZ.mk]
  rw [h2, reprIco_coe]
  have hN : (0 : ℚ) < (N : ℕ) := by exact_mod_cast N.pos
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one hN]
  exact_mod_cast ZMod.val_lt (urChar K Ω N g)

theorem charCocycle_urPsi (N : ℕ+) (g h : Gal(Ω/K)) :
    ((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) =
      ((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val := by
  have e := charCocycle_cast (charAdd (urPsi (K := K) (Ω := Ω) N)) g h
  rw [reprIco_urPsi, reprIco_urPsi, reprIco_urPsi] at e
  have hN : ((N : ℕ) : ℚ) ≠ 0 := by exact_mod_cast N.ne_zero
  have : (((N : ℕ) : ℤ) * charCocycle (charAdd (urPsi (K := K) (Ω := Ω) N)) (g, h) : ℚ) =
      (((urChar K Ω N g).val : ℤ) + (urChar K Ω N h).val - (urChar K Ω N (g * h)).val : ℤ) := by
    push_cast
    rw [e]
    field_simp
  exact_mod_cast this

end Hasse

section HasseC

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem brauerInv_galCupClass_urPsi (N : ℕ+) (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) :
    brauerInvZOfIsSepClosure K Ω (galCupClass K Ω (urPsi (K := K) (Ω := Ω) N) ϖ) =
      zmodToQZ (N : ℕ) 1 := by
  obtain ⟨σ, hσ⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) (Multiplicative.ofAdd 1)
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  have hψ : ∀ g ∈ (unramifiedDegree K Ω).ker,
      (urPsi (K := K) (Ω := Ω) N) (Additive.ofMul g) = 0 := by
    intro g hg
    show zmodToQZ (N : ℕ) (urChar K Ω N g) = 0
    rw [urChar_of_ker N (MonoidHom.mem_ker.1 hg), map_zero]
  have key := brauerInvZ_galCupClass_of_unramified (urPsi (K := K) (Ω := Ω) N) hψ hσ ϖ
  show brauerInvZ K Ω _ = _
  rw [key, hϖ, one_smul]
  show zmodToQZ (N : ℕ) (urChar K Ω N σ) = _
  rw [urChar_of_deg_one N hσ]

end HasseC

section HasseMain

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

theorem hasse_kummer_unram' (N : ℕ+)
    (ϖ : Kˣ) (hϖ : ord (ϖ : K) = 1) (Y : Ω) (hY : Y ^ (N : ℕ) = algebraMap K Ω ϖ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ N) (κ : Gal(Ω/K) → ZMod (N : ℕ))
    (hκ : ∀ g : Gal(Ω/K), g Y = ζ ^ (κ g).val * Y)
    (c : cocycles (galUnitsZ K Ω) 2)
    (hc : ∀ s : Fin 2 → Gal(Ω/K), ((Additive.toMul (cochainOf _ (cocycleι _ 2 c) s) : Ωˣ) : Ω) =
      ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val) :
    brauerInvZOfIsSepClosure K Ω (cohomologyπ _ 2 c) = - zmodToQZ (N : ℕ) 1 := by
  classical
  have hN0 : (N : ℕ) ≠ 0 := N.ne_zero
  have hϖ0 : algebraMap K Ω (ϖ : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K Ω).injective).2 ϖ.ne_zero
  have hY0 : Y ≠ 0 := by
    rintro rfl
    rw [zero_pow hN0] at hY
    exact hϖ0 hY.symm
  let ψ := urPsi (K := K) (Ω := Ω) N
  obtain ⟨w, hw, hwc⟩ := exists_cocycle_cupCharClassProf (galUnitsZ K Ω) ψ (unitsInvariant K Ω ϖ)
  let Yu : Ωˣ := Units.mk0 Y hY0
  let bf : Gal(Ω/K) → (galUnitsZ K Ω).V := fun h =>
    Additive.ofMul (Yu ^ (urChar K Ω N h).val)
  have hbf_lc : IsLocallyConstant fun t : Fin 1 → Gal(Ω/K) => bf (t 0) := by
    have h1 : IsLocallyConstant (urChar K Ω N) :=
      (IsLocallyConstant.iff_continuous _).2 (continuous_urChar (K := K) (Ω := Ω) N)
    exact (h1.comp fun u => Additive.ofMul (Yu ^ u.val)).comp_continuous (continuous_apply 0)
  have hsum : cohomologyπ _ 2 c + cohomologyπ _ 2 w = 0 := by
    rw [← map_add]
    refine (PositivityTheory.LocalTateOrthogonality.Gcoh.pi_succ_eq_zero_iff (galUnitsZ K Ω) 1 (c + w)).2
      ⟨fun t => bf (t 0), hbf_lc, ?_⟩
    have hd := PositivityTheory.LocalTateOrthogonality.Gcoh.d_comp (galUnitsZ K Ω).ρ (galUnitsZ K Ω) (AddEquiv.refl _)
      (fun _ _ => rfl) 1 (fun t => bf (t 0))
    simp only [AddEquiv.refl_apply] at hd
    rw [hd]
    funext s
    rw [PositivityTheory.LocalTateOrthogonality.Gcoh.dn_one, map_add, cochainOf_add, Pi.add_apply]
    have hwc' := hwc s
    have hc' := hc s
    set a0 := (urChar K Ω N (s 0)).val with ha0
    set a1 := (urChar K Ω N (s 1)).val with ha1
    set a01 := (urChar K Ω N (s 0 * s 1)).val with ha01
    set cc := charCocycle (charAdd ψ) (s 0, s 1) with hcc
    have hrel : ((N : ℕ) : ℤ) * cc = (a0 : ℤ) + a1 - a01 := charCocycle_urPsi N (s 0) (s 1)
    apply Additive.toMul.injective
    apply Units.ext
    rw [hwc']
    simp only [toMul_add, toMul_sub, toMul_zsmul, Units.val_mul, Units.val_div_eq_div_val,
      Units.val_zpow_eq_zpow_val, bf]
    rw [hc', coe_unitsInvariant]
    have hL : ((Additive.toMul (((zRepOfMonoidEnd (galUnitsHom K Ω)) (s 0))
          (Additive.ofMul (Yu ^ (urChar K Ω N (s 1)).val)) -
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0 * s 1)).val) +
          Additive.ofMul (Yu ^ (urChar K Ω N (s 0)).val)) : Ωˣ) : Ω) =
        (s 0) Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 := by
      show ((Additive.toMul ((Additive.ofMul (galUnitsHom K Ω (s 0) (Yu ^ a1)) : Additive Ωˣ) -
          Additive.ofMul (Yu ^ a01) + Additive.ofMul (Yu ^ a0)) : Ωˣ) : Ω) = _
      simp only [toMul_add, toMul_sub, toMul_ofMul, Units.val_mul, Units.val_div_eq_div_val,
        coe_galUnitsHom_apply, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Yu, Units.val_mk0,
        map_pow, div_eq_mul_inv]
    refine Eq.trans hL ?_
    rw [hκ (s 0), mul_pow]
    have hYz : Y ^ a1 * (Y ^ a01)⁻¹ * Y ^ a0 = (algebraMap K Ω (ϖ : K)) ^ cc := by
      rw [← hY, show (Y ^ (N : ℕ)) ^ cc = Y ^ (((N : ℕ) : ℤ) * cc) by rw [zpow_mul, zpow_natCast],
        hrel, zpow_sub₀ hY0, zpow_add₀ hY0, zpow_natCast, zpow_natCast, zpow_natCast]
      ring
    have hζN : ζ ^ (N : ℕ) = 1 := hζ.pow_eq_one
    have hzk : (ζ ^ (κ (s 0)).val) ^ a1 = ζ ^ (κ (s 0) * urChar K Ω N (s 1)).val := by
      rw [← pow_mul, ZMod.val_mul]
      conv_lhs => rw [← Nat.div_add_mod ((κ (s 0)).val * a1) (N : ℕ), pow_add, pow_mul, hζN,
        one_pow, one_mul]
    rw [← hzk, ← hYz]
    ring
  have hc0 : cohomologyπ _ 2 c = - cohomologyπ _ 2 w := eq_neg_of_add_eq_zero_left hsum
  rw [hc0, map_neg, hw]
  exact congrArg Neg.neg (brauerInv_galCupClass_urPsi (K := K) (Ω := Ω) N ϖ hϖ)

end HasseMain

end PositivityTheory.Lit1.PTN
