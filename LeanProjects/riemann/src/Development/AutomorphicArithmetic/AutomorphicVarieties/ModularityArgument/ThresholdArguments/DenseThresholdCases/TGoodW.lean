import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.AbsPowIntVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrinSeriesIrreducible
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharPolOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TEpsAway

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W.GoodWeilCharpoly
private theorem one_of_sq {a b : ℂ} (h : (X - 1 : ℂ[X]) ^ 2 = (X - C a) * (X - C b)) : a = 1 ∧ b = 1 := by
  have ha := congrArg (eval a) h
  have hb := congrArg (eval b) h
  simp only [eval_pow, eval_sub, eval_X, eval_one, eval_mul, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  exact ⟨sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 ha), sub_eq_zero.1 (pow_eq_zero_iff (two_ne_zero)|>.1 hb)⟩
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem absPow_int_val (m : ℤ) (x : kˣ) : (absPow k (m : ℂ) x : ℂ) = (absPow k 1 x : ℂ) ^ m := by
  rw [val_absPow, val_absPow, Complex.cpow_intCast, Complex.cpow_one]
end Loc
end UpperTheory.V.Z.Sym.W.GoodWeilCharpoly
theorem UpperTheory.V.Z.Sym.W.good_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.GoodWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι r w hlw hunr ⟨s, ⟨A, hA, hF⟩, hs⟩ τ hτ hPT
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN hA
  obtain ⟨a, ha, -⟩ := hrc
  obtain ⟨ψ, hψs, ⟨e⟩, -⟩ := _root_.UpperTheory.V.Z.Sym.W.principal_series_of_statement_w P.litN L 2 w τ hPT
  have hsub : IsSubquotient τ.ρ (prinSeries ψ) := by
    exact IsSubquotient.of_injective e.toIntertwiningMap e.toLinearEquiv.injective
  have hE := _root_.UpperTheory.V.Z.Sym.W.eigW_alt P L Ω l ι 2 r w hlw A hA a ha τ hτ hPT ψ hψs hsub
  let x : Fin 2 → Weil hA → ℂˣ := fun i t => ψ i (a t) * absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t)
  have hpol : ∀ t : Weil hA, (r (t : G L Ω)).val.charpoly.map ι.toRingHom = (X - C (x 0 t : ℂ)) * (X - C (x 1 t : ℂ)) := by
    intro t
    rw [hE t, psPol, Fin.prod_univ_two]
  have hUo : ∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1 := by
    intro i u hu
    obtain ⟨t, rfl⟩ := ha.surj u
    have hd : deg t = 0 := by
      have h0 := ha.ord_eq t
      rw [ord_eq_zero_iff.2 hu] at h0
      omega
    have hI : (t : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.1 hd
    have h1 := hpol t
    rw [hunr A hA _ hI] at h1
    have h2 : ((1 : GL (Fin 2) (Qbar l)).val.charpoly).map ι.toRingHom = (X - 1 : ℂ[X]) ^ 2 := by
      simp [Matrix.charpoly_one]
    rw [h2] at h1
    obtain ⟨h3, h4⟩ := GoodWeilCharpoly.one_of_sq h1
    have hv := isUnram_absPow (w.adicCompletion L) (-((((2 : ℕ) : ℂ) - 1) / 2)) (a t) hu
    have hx : ∀ j, x j t = ψ j (a t) := fun j => by
      show ψ j (a t) * _ = _
      rw [hv, mul_one]
    have e0 : ψ 0 (a t) = 1 := Units.ext (by rw [← hx 0]; exact h3)
    have e1 : ψ 1 (a t) = 1 := Units.ext (by rw [← hx 1]; exact h4)
    fin_cases i
    · exact e0
    · exact e1
  let s' : Weil hA := ⟨s, mem_Weil_of_isFrob hA hF⟩
  let al : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 0 s')
  let be : (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom (x 1 s')
  have hal : ι (al : Qbar l) = (x 0 s' : ℂ) := by simp [al]
  have hbe : ι (be : Qbar l) = (x 1 s' : ℂ) := by simp [be]
  have hc : (r s).val.charpoly = (X - C (al : Qbar l)) * (X - C (be : Qbar l)) := by
    apply Polynomial.map_injective ι.toRingHom ι.injective
    have h1 := hpol s'
    rw [show ((s' : G L Ω)) = s from rfl] at h1
    rw [h1, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_C]
    simp [hal, hbe]
  have H : ∀ m : ℤ, |m| ≤ 2 → (ψ 0 / ψ 1) ^ 2 ≠ absPow (Kw w) (m : ℂ) := by
    intro m hm he
    apply hs
    refine ⟨m, hm, ?_⟩
    have h1 := congrArg (fun f : (Kw w)ˣ →* ℂˣ => ((f (a s') : ℂˣ) : ℂ)) he
    have h2 := (_root_.UpperTheory.V.Z.Sym.Ga.cyc_char_eq_abs_pow_and_norm_pow_deg_away_l P L Ω l ι w hlw A hA a ha s').1
    have hq : (x 0 s' : ℂ) / (x 1 s' : ℂ) = (ψ 0 (a s') : ℂ) / (ψ 1 (a s') : ℂ) := by
      simp only [x, Units.val_mul]
      exact mul_div_mul_right _ _ (Units.ne_zero _)
    simp only [MonoidHom.pow_apply, MonoidHom.div_apply, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val,
      GoodWeilCharpoly.absPow_int_val, ← h2, ← hq, ← hal, ← hbe] at h1
    have h3 : ((al : Qbar l) / be) ^ 2 = Ga.ep l s ^ m := by
      apply ι.injective
      simpa [map_zpow₀] using h1
    have h4 := (Ga.ufFacts (Qbar l) (r s)).1 al be hc
    have hne : ((al : Qbar l) / be) ≠ 0 := div_ne_zero al.ne_zero be.ne_zero
    have h5 : ((al : Qbar l) / be)⁻¹ ^ 2 = Ga.ep l s ^ (-m) := by rw [inv_pow, h3, zpow_neg]
    rw [h4]
    simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val]
    rw [← h3, ← h5]
    field_simp
    ring
  exact ⟨ψ, hψs, ⟨e⟩, hUo, ⟨fun y hy => by simp [MonoidHom.div_apply, hUo 0 y hy, hUo 1 y hy], H⟩⟩
end
end
