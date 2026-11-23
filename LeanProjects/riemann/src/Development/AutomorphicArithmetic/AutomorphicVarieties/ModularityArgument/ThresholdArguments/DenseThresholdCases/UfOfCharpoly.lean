import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.UfOfCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TGalExW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CharPolOfChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRegElt

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
private theorem uf_of_charpoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (g : GL (Fin 2) (Qbar l)) (c : Fin 2 → ℂˣ)
    (h : g.val.charpoly.map ι.toRingHom = ∏ j, (X - C (c j : ℂ))) :
    ι (Ga.uf g) = ((c 0 / c 1 : ℂˣ) : ℂ) + (((c 0 / c 1 : ℂˣ)⁻¹ : ℂˣ) : ℂ) := by
  let e : ℂˣ →* (Qbar l)ˣ := Units.map ι.symm.toRingHom.toMonoidHom
  have he : ∀ x : ℂˣ, ι ((e x : (Qbar l)ˣ) : Qbar l) = (x : ℂ) := fun x => by simp [e]
  have hc : g.val.charpoly =
      (X - C ((e (c 0) : (Qbar l)ˣ) : Qbar l)) * (X - C ((e (c 1) : (Qbar l)ˣ) : Qbar l)) := by
    apply Polynomial.map_injective ι.toRingHom ι.injective
    rw [h, Fin.prod_univ_two]
    simp [Polynomial.map_mul, he]
  rw [(Ga.ufFacts _ g).1 _ _ hc]
  simp only [_root_.map_add, ← _root_.map_div, ← _root_.map_inv, he]
private theorem uf_of_pol {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (g : GL (Fin 2) (Qbar l)) (φ : Fin 2 → kˣ →* ℂˣ) (x : kˣ)
    (h : g.val.charpoly.map ι.toRingHom = UpperTheory.V.Z.Sym.W.psPol φ x) :
    ι (Ga.uf g) = (((φ 0 / φ 1) x : ℂˣ) : ℂ) + ((((φ 0 / φ 1) x)⁻¹ : ℂˣ) : ℂ) := by
  have e := uf_of_charpoly ι g (fun j => φ j x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) h
  have hx : (φ 0 x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) / (φ 1 x * absPow k (-((((2 : ℕ) : ℂ) - 1) / 2)) x) =
      (φ 0 / φ 1) x := by
    simp only [MonoidHom.div_apply, mul_div_mul_right_eq_div]
  simp only [hx] at e
  exact e
private theorem two_roots {K : Type} [Field K] (x : Kˣ) :
    (((x ^ 2 : Kˣ) : K) + (((x ^ 2)⁻¹ : Kˣ) : K)) = ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 := by
  have h0 : (x : K) ≠ 0 := x.ne_zero
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow]
  field_simp
  ring
private theorem two_ne {H : Type*} [CommGroup H] {p : H} (ψ : Fin 2 → H) (hp : p ≠ 1) (h0 : ψ 0 / ψ 1 ≠ p)
    (h1 : ψ 0 / ψ 1 ≠ p⁻¹) (i j : Fin 2) : ψ i ≠ ψ j * p := by
  intro e
  fin_cases i <;> fin_cases j
  · exact hp (by simpa using e)
  · exact h0 (by
      have e' : ψ 0 = ψ 1 * p := e
      rw [e', mul_div_cancel_left])
  · exact h1 (by
      have e' : ψ 1 = ψ 0 * p := e
      rw [e', div_mul_cancel_left])
  · exact hp (by simpa using e)
private theorem abs_ne_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro e
  have e' : absPow k (((1 : ℝ)) : ℂ) = absPow k (((0 : ℝ)) : ℂ) := by
    push_cast
    rw [absPow_zero]
    exact e
  exact one_ne_zero (GlobalTheory.TypeTwo.absPow_ofReal_injective k _ _ e')
private theorem reg_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (h : Reg (ψ 0 / ψ 1)) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  have two : absPow k 2 = absPow k 1 ^ 2 := by
    rw [pow_two, ← absPow_add]; norm_num
  refine two_ne ψ (abs_ne_one k) (fun e => h.2 2 (by norm_num) ?_) (fun e => h.2 (-2) (by norm_num) ?_) i j
  · rw [e]; push_cast; exact two.symm
  · rw [e]; push_cast; rw [absPow_neg, two, inv_pow]
private theorem reg_two {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : Fin 2 → kˣ →* ℂˣ) (a : kˣ →* ℂˣ) (h : Reg a) (e : ψ 0 / ψ 1 = a ^ 2) (i j : Fin 2) : ψ i ≠ ψ j * absPow k 1 := by
  refine two_ne ψ (abs_ne_one k) (fun e' => h.2 1 (by norm_num) ?_) (fun e' => h.2 (-1) (by norm_num) ?_) i j
  · rw [← e, e']; simp
  · rw [← e, e']; simp [absPow_neg]
theorem UpperTheory.V.Z.Sym.W.branch_two_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.Branch2WAlt := by
  intro Pw L Ω _ _ _ _ _ _ l _ ι hl hE M m hM r σ hAd hGal P ψ hGood hReg σ' hσ' hev
  obtain ⟨r', hGal', -⟩ := _root_.UpperTheory.V.Z.Sym.W.galois_exists_w_statement Pw L Ω l ι hl hE 2 (by norm_num) σ' hσ'
  have hr := Ga.badClosed L Ω l r hGal.cont
  have hr' := Ga.badClosed L Ω l r' hGal'.cont
  let E : Set (G L Ω) := {g | Ga.uf (r' g) = Ga.uf (r g) ^ 2 - 2}
  have hEc : IsClosed E := isClosed_eq hr'.1 ((hr.1.pow 2).sub continuous_const)
  have hstab : ∀ c : G (maximalRealSubfield L) Ω, IsConjEl c → ∀ s s' : G L Ω,
      s'.restrictScalars (maximalRealSubfield L) = c * s.restrictScalars (maximalRealSubfield L) * c⁻¹ →
      s' ∈ E → s ∈ E := by
    intro c hc s s' hss hs'
    obtain ⟨Q, hQ⟩ := hGal.pair c hc
    obtain ⟨Q', hQ'⟩ := hGal'.pair c hc
    have e1 := (Ga.ufFacts _ (r s)).2.2.2.1 (r s') Q _ (hQ s s' hss)
    have e2 := (Ga.ufFacts _ (r' s)).2.2.2.1 (r' s') Q' _ (hQ' s s' hss)
    change Ga.uf (r' s') = Ga.uf (r s') ^ 2 - 2 at hs'
    change Ga.uf (r' s) = Ga.uf (r s) ^ 2 - 2
    rw [← e1, ← e2]
    exact hs'
  have hfrob : ∀ᶠ w in Filter.cofinite, w ∈ P → ∀ s, Ga.FrobAt w s → s ∈ E := by
    refine hev.mono fun w hw hwP s hs => ?_
    obtain ⟨ψ', ⟨hsm', τ', hc', hq'⟩, hrat⟩ := hw hwP
    obtain ⟨hsp, hlw, hsm, τ, hc, ⟨eqv⟩⟩ := hGood.mem w hwP
    obtain ⟨A, hA, hF⟩ := hs
    obtain ⟨a, ha⟩ := GlobalTheory.localArtinExists_holds L Ω A w hA
    have hq : IsSubquotient τ.ρ (prinSeries (ψ w)) :=
      IsSubquotient.of_injective eqv.toIntertwiningMap eqv.toLinearEquiv.injective
    have hpt : UpperTheory.V.Z.Sym.W.PT τ :=
      _root_.UpperTheory.V.Z.Sym.W.plain_of_statement Pw.af.litN L 2 w τ (ψ w) hsm hq (reg_one (ψ w) (hReg w hwP))
    have hpt' : UpperTheory.V.Z.Sym.W.PT τ' :=
      _root_.UpperTheory.V.Z.Sym.W.plain_of_statement Pw.af.litN L 2 w τ' ψ' hsm' hq' (reg_two ψ' _ (hReg w hwP) hrat)
    let t : Weil hA := ⟨s, mem_Weil_of_isFrob hA hF⟩
    have c1 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt Pw.af L Ω l ι 2 r w hlw A hA a ha τ (hGal.loc w hsp τ hc) hpt (ψ w) hsm hq t
    have c2 := _root_.UpperTheory.V.Z.Sym.W.eigW_alt Pw.af L Ω l ι 2 r' w hlw A hA a ha τ' (hGal'.loc w hsp τ' hc') hpt' ψ' hsm' hq' t
    have u1 := uf_of_pol ι (r s) (ψ w) (a t) c1
    have u2 := uf_of_pol ι (r' s) ψ' (a t) c2
    rw [hrat] at u2
    apply ι.injective
    change ι (Ga.uf (r' s)) = ι (Ga.uf (r s) ^ 2 - 2)
    rw [u2, _root_.map_sub, _root_.map_pow, u1, _root_.map_ofNat]
    exact two_roots _
  have hsub := Ga.spread L Ω hE E (Ga.Bad r) hEc hr.2.2 hstab P M hM hGood.meets hfrob
  have hreg := _root_.UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order L Ω l ι M m r hAd.toIn_alt
  have hirr := Ga.sym4Irr l (G L Ω) r hGal.cont hAd.irr
    (fun H hH => let ⟨s, hs, _, a, b, h⟩ := hreg H hH; ⟨s, hs, a, b, h⟩)
  obtain ⟨s, -, hs, -⟩ := hreg ⊤ isOpen_univ
  exact Ga.noKappa l (G L Ω) r r' hirr (Ga.Bad r)ᶜ hr.2.2.isOpen_compl ⟨s, hs⟩ (fun g hg => hsub hg)
end
end
