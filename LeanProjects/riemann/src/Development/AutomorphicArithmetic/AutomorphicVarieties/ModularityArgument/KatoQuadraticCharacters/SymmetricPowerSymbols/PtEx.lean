import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.LocallyConstantFinite.KaU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.ptEx :
    UpperTheory.V.Z.Kato.Sym.PtEx := by
  intro Ω _ _ _ ε X m hm u v hu hv
  have LG := lgB Ω ε X m hm
  have KU := PE.kaU Ω ε X m hm
  have hu0 : u ≠ 0 := hu.1
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (io X u) hm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (io X v) hm
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne'] at ha
    exact hu0 ((map_eq_zero_iff _ (io X).injective).mp ha.symm)
  obtain ⟨η, hη, hlc, hunr⟩ := PE.etaEx Ω ε X m hm u v a b hu hv ha hb
  have hinU : ∀ g, InD X g → PE.InU X u v g := fun g hg => ⟨fun c => hg _, hg _, hg _, hg _⟩
  refine ⟨⟨a, b, η⟩, ⟨hu, hv, ha, hb, fun g h hg hh => hη g h (hinU g hg) (hinU h hh), hlc, hunr⟩, ?_⟩
  intro γ hu' hv'
  obtain ⟨σ, hσ⟩ := (admB Ω ε X).2.2.2.2.2.2.1 (slR X (ofSL γ))
  have hfix : ∀ f, X.sl (ofSL γ) f = f → σ (io X f) = io X f := fun f hf => by
    rw [hσ f]
    exact congrArg _ hf
  have hσU : PE.InU X u v σ :=
    ⟨fun c => hfix _ ((X.sl (ofSL γ)).commutes c), hfix _ (X.j_inv γ), hfix _ hu', hfix _ hv'⟩
  have hinv : ∀ x, σ x = x → σ⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hx]
    exact σ.symm_apply_apply x
  have hσiU : PE.InU X u v σ⁻¹ :=
    ⟨fun c => hinv _ (hσU.1 c), hinv _ hσU.2.1, hinv _ hσU.2.2.1, hinv _ hσU.2.2.2⟩
  have hz : ∀ g, PE.InU X u v g → g (zt X m) = zt X m := fun g hg => by
    unfold zt
    exact hg.1 _
  have hka1 : ka X m a 1 = 0 := by
    show lg X m a a = 0
    exact LG.2.2.1 a a 0 ha0 (by simp)
  have hk1 : ∀ g : RingAut (Kb X), ka X m 1 g = 0 := fun g => by
    show lg X m (g 1) 1 = 0
    rw [map_one]
    exact LG.2.2.1 1 1 0 one_ne_zero (by simp)
  have hcyc : cyc (Ω := Ω) m 1 = 1 := (LG.2.2.2.2.2.2 1 1).2.1
  have hη1 : η 1 = 0 := by
    have := hη 1 1 (hinU 1 (fun _ => rfl)) (hinU 1 (fun _ => rfl))
    rw [mul_one, hka1] at this
    linear_combination -this
  unfold Mv
  refine ⟨σ, hσ, ?_⟩
  simp only [IsKum, dif, Pt.mv]
  refine ⟨1, by simp, fun h hh => ?_⟩
  have hhU := hinU h hh
  have E1 := hη σ⁻¹ (h * σ) hσiU ⟨fun c => by show h (σ _) = _; rw [hσU.1 c, hhU.1 c], by show h (σ _) = _; rw [hσU.2.1, hhU.2.1], by show h (σ _) = _; rw [hσU.2.2.1, hhU.2.2.1], by show h (σ _) = _; rw [hσU.2.2.2, hhU.2.2.2]⟩
  have E2 := hη h σ hhU hσU
  have E3 := hη σ⁻¹ σ hσiU hσU
  rw [inv_mul_cancel, hη1] at E3
  have K1 := (KU b (by rintro rfl; rw [zero_pow hm.ne'] at hb; exact hv.1 ((map_eq_zero_iff _ (io X).injective).mp hb.symm)) h σ (hz h hhU) (hz σ hσU) (by rw [hb]; exact hhU.2.2.2) (by rw [hb]; exact hσU.2.2.2)).1
  have K2 := (KU a ha0 σ⁻¹ σ (hz _ hσiU) (hz σ hσU) (by rw [ha]; exact hσiU.2.2.1) (by rw [ha]; exact hσU.2.2.1)).1
  rw [inv_mul_cancel, hka1] at K2
  rw [hk1, hcyc, mul_assoc]
  show 0 = 1 ^ 2 * η (σ⁻¹ * (h * σ)) - η h + ka X m a h * ka X m b σ - ka X m a σ * ka X m b h
  linear_combination (-1 : ZMod m) * E1 - E2 + E3 + ka X m a σ⁻¹ * K1 - ka X m b h * K2
