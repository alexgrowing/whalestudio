import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecMemLev
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.AfFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExistsOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExtChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.UnrSmooth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalueSecond

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al

private theorem common_eig {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, Commute (f i) (f j)) :
    ∀ (n : ℕ) (W : Submodule ℂ M), Module.finrank ℂ W = n → W ≠ ⊥ → (∀ i, ∀ x ∈ W, f i x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i v = c • v :=
  _root_.UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig f hc

private theorem sdom_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : kˣ) (ht : valuation k (t : k) < 1) : Sig.SDom ![t, t⁻¹] := by
  intro i j hij
  have h0 : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  have h1 : valuation k (t : k) < (valuation k (t : k))⁻¹ :=
    ht.trans (one_lt_inv₀ (zero_lt_iff.2 h0) |>.2 ht)
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa using h1

private theorem dom_of_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d : Fin n → kˣ) (hd : Sig.SDom d) : AlgebraTools.Dom d := by
  intro i j hij
  rcases hij.lt_or_eq with h | rfl
  · exact (hd i j h).le
  · exact le_rfl

private theorem dom_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d d' : Fin n → kˣ) (h : AlgebraTools.Dom d) (h' : AlgebraTools.Dom d') : AlgebraTools.Dom (d * d') := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (h i j hij) (h' i j hij)

private theorem loc_char {k M : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup M] [Module ℂ M] (u : (Fin 2 → kˣ) → Module.End ℂ M) (b : kˣ →* ℂˣ) (v : M) (hv : v ≠ 0)
    (hmul : ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → u (d * d') = u d * u d')
    (hone : ∀ d, (∀ i, d i ∈ Hi.Uo k) → u d = 1)
    (hdomU : ∀ d : Fin 2 → kˣ, (∀ i, d i ∈ Hi.Uo k) → AlgebraTools.Dom d)
    (heig : ∀ d, AlgebraTools.Dom d → ∃ c : ℂ, u d v = c • v)
    (hb : ∀ t : kˣ, valuation k (t : k) < 1 → u ![t, t⁻¹] v = expo ![b, 1] ![t, t⁻¹] • v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, ∀ x ∈ Hi.Uo k, ψ i x = 1) ∧ ψ 0 / ψ 1 = b ∧
      ∀ d, Sig.SDom d → u d v = expo ψ d • v := by
  classical
  choose! χ hχ using heig
  have uniq : ∀ c c' : ℂ, c • v = c' • v → c = c' := fun c c' h => smul_left_injective ℂ hv h
  have hmulχ : ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → χ (d * d') = χ d * χ d' := by
    intro d d' h h'
    apply uniq
    rw [← hχ _ (dom_mul d d' h h'), hmul d d' h h', Module.End.mul_apply, hχ d' h', map_smul, hχ d h,
      smul_smul, mul_comm]
  have hunit : ∀ d, (∀ i, d i ∈ Hi.Uo k) → χ d = 1 := by
    intro d hd
    apply uniq
    rw [← hχ d (hdomU d hd), hone d hd, one_smul]
    rfl
  have hexpo : ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (d : Fin 2 → kˣ), expo ψ d ≠ 0 := fun ψ d => Units.ne_zero _
  have hχb : ∀ t : kˣ, valuation k (t : k) < 1 → χ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹] := by
    intro t ht
    apply uniq
    rw [← hχ _ (dom_of_sdom _ (sdom_pair t ht)), hb t ht]
  have hne : ∀ d, Sig.SDom d → χ d ≠ 0 := by
    intro d hd h0
    have hlt : valuation k (d 0 : k) < valuation k (d 1 : k) := hd 0 1 (by decide)
    let z : Fin 2 → kˣ := fun _ => d 0 * d 1
    have hz : AlgebraTools.Dom z := fun _ _ _ => le_rfl
    have hz' : AlgebraTools.Dom z⁻¹ := fun _ _ _ => le_rfl
    have hzz : χ z * χ z⁻¹ = 1 := by
      rw [← hmulχ _ _ hz hz', mul_inv_cancel]
      exact hunit 1 fun _ => one_mem _
    have hz0 : χ z ≠ 0 := left_ne_zero_of_mul_eq_one hzz
    let t : kˣ := d 0 / d 1
    have ht : valuation k (t : k) < 1 := by
      have h1 : valuation k (d 1 : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (d 1).ne_zero
      simp only [t, Units.val_div_eq_div_val, map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 h1)).2 hlt
    have hdd : d * d = z * ![t, t⁻¹] := by
      have e0 : d 0 * d 0 = d 0 * d 1 * (d 0 / d 1) := by rw [mul_assoc, mul_div_cancel]
      have e1 : d 1 * d 1 = d 0 * d 1 * (d 0 / d 1)⁻¹ := by
        rw [inv_div, mul_comm (d 0), mul_assoc, mul_div_cancel]
      funext i
      fin_cases i
      · exact e0
      · exact e1
    have hs := sdom_pair t ht
    have key : χ d * χ d = χ z * χ ![t, t⁻¹] := by
      rw [← hmulχ d d (dom_of_sdom d hd) (dom_of_sdom d hd), hdd, hmulχ _ _ hz (dom_of_sdom _ hs)]
    rw [h0, zero_mul, hχb t ht] at key
    exact mul_ne_zero hz0 (hexpo _ _) key.symm
  obtain ⟨ψ, hψ1, hψ2⟩ := extChar k 2 χ hne
    (fun d d' h h' => hmulχ d d' (dom_of_sdom d h) (dom_of_sdom d' h'))
    (fun d x h hx => by rw [hmulχ d x (dom_of_sdom d h) (hdomU x hx), hunit x hx, mul_one])
  refine ⟨ψ, hψ1, (unrSmooth k).2 ψ b fun t ht => ?_, fun d hd => ?_⟩
  · rw [← hψ2 _ (sdom_pair t ht), hχb t ht]
  · rw [hχ d (dom_of_sdom d hd), hψ2 d hd]

end UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.refine :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (U : Subgroup (UA L 2)), IsLevel U →
        ∀ S : Finset (Plc L), Places (S : Set (Plc L)) → (∀ w ∈ S, locU 2 w ⊓ Kall L 2 ≤ U) →
        ∀ (b : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (φ : UA L 2 → V), φ ≠ 0 → IsAF R (lev U S iw) φ → (∀ w ∈ S, EigS φ w (iw w) (b w)) →
        ∃ (φ' : UA L 2 → V) (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ), φ' ≠ 0 ∧ IsAF R (lev U S iw) φ' ∧
          ∀ w ∈ S, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ ψ w 0 / ψ w 1 = b w ∧ EigT φ' w (iw w) (ψ w) := by
  intro L _ _ _ V _ _ _ R U hU S hS hloc b φ hφ hAF hE
  classical
  obtain ⟨u, hu_op, hu_mul, hu_one, hu_comm⟩ := afOps L 2 V R U hU.1 S hS hloc
  haveI : FiniteDimensional ℂ (AF R (lev U S iw)) :=
    afFin L 2 V R (lev U S iw) ((cof L 2).2.2.1 U hU S iw)
  have hdomU : ∀ (w : Plc L) (d : Fin 2 → (Kw w)ˣ), (∀ i, d i ∈ Hi.Uo (Kw w)) → AlgebraTools.Dom d := by
    intro w d hd i j _
    exact ((hd i).trans (hd j).symm).le
  have hpair : ∀ (w : Plc L) (t : (Kw w)ˣ), valuation (Kw w) (t : Kw w) < 1 → AlgebraTools.Dom ![t, t⁻¹] :=
    fun w t ht => dom_of_sdom _ (sdom_pair t ht)

  have hcomm : ∀ w ∈ S, ∀ w' ∈ S, ∀ (d : Fin 2 → (Kw w)ˣ) (d' : Fin 2 → (Kw w')ˣ), AlgebraTools.Dom d → AlgebraTools.Dom d' →
      Commute (u w d) (u w' d') := by
    intro w hw w' hw' d d' hd hd'
    by_cases h : w = w'
    · subst h
      show u w d * u w d' = u w d' * u w d
      rw [← hu_mul w hw d d' hd hd', ← hu_mul w hw d' d hd' hd, mul_comm d d']
    · exact hu_comm w hw w' hw' h d d' hd hd'
  let E : Submodule ℂ (AF R (lev U S iw)) :=
    { carrier := {m | ∀ w ∈ S, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 →
        u w ![t, t⁻¹] m = expo ![b w, 1] ![t, t⁻¹] • m}
      add_mem' := fun {x y} hx hy w hw t ht => by rw [map_add, hx w hw t ht, hy w hw t ht, smul_add]
      zero_mem' := fun w _ t _ => by simp
      smul_mem' := fun c x hx w hw t ht => by rw [map_smul, hx w hw t ht, smul_comm] }
  have hmemE : ∀ m, m ∈ E ↔ ∀ w ∈ S, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 →
      u w ![t, t⁻¹] m = expo ![b w, 1] ![t, t⁻¹] • m := fun _ => Iff.rfl
  let φ₀ : AF R (lev U S iw) := ⟨φ, hAF⟩
  have hφ₀ : φ₀ ∈ E := by
    refine (hmemE _).2 fun w hw t ht => Subtype.ext ?_
    rw [hu_op w hw _ (hpair w t ht)]
    exact hE w hw t ht
  have hφ₀0 : φ₀ ≠ 0 := fun h => hφ (congrArg Subtype.val h)
  have hE0 : E ≠ ⊥ := fun h => hφ₀0 (by
    have := hφ₀
    rw [h] at this
    simpa using this)
  let ι : Type := Σ w : {w // w ∈ S}, {d : Fin 2 → (Kw w.1)ˣ // AlgebraTools.Dom d}
  let f : ι → Module.End ℂ (AF R (lev U S iw)) := fun i => u i.1.1 i.2.1
  obtain ⟨v, hvE, hv0, hveig⟩ := common_eig f
    (fun i j => hcomm i.1.1 i.1.2 j.1.1 j.1.2 i.2.1 j.2.1 i.2.2 j.2.2) _ E rfl hE0
    (fun i x hx => (hmemE _).2 fun w hw t ht => by
      have hc := (hcomm i.1.1 i.1.2 w hw i.2.1 ![t, t⁻¹] i.2.2 (hpair w t ht)).eq
      have := congrArg (fun g : Module.End ℂ (AF R (lev U S iw)) => g x) hc
      simp only [Module.End.mul_apply] at this
      show u w ![t, t⁻¹] (u i.1.1 i.2.1 x) = _
      rw [← this, (hmemE x).1 hx w hw t ht]
      exact map_smul _ _ _)
  have hloc' : ∀ w : Plc L, ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, w ∈ S →
      (∀ i, ∀ x ∈ Hi.Uo (Kw w), ψ i x = 1) ∧ ψ 0 / ψ 1 = b w ∧
        ∀ d, Sig.SDom d → u w d v = expo ψ d • v := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨ψ, h⟩ := loc_char (u w) (b w) v hv0 (hu_mul w hw) (hu_one w hw) (hdomU w)
        (fun d hd => hveig ⟨⟨w, hw⟩, ⟨d, hd⟩⟩) ((hmemE v).1 hvE w hw)
      exact ⟨ψ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose ψ hψ using hloc'
  refine ⟨(v : UA L 2 → V), ψ, fun h => hv0 (Subtype.ext h), v.2, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hψ w hw
  refine ⟨h1, h2, fun d hd => ?_⟩
  have := congrArg Subtype.val (h3 d hd)
  rw [hu_op w hw d (dom_of_sdom d hd) v] at this
  exact this
