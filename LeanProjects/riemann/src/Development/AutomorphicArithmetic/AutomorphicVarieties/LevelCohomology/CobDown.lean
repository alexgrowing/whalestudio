import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoAdicCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.FdAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem cob_up {l : ℕ} [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) {Γ : Type} [Group Γ]
    (θ : Γ →* Oˣ) (z : Γ → O) (D : Subgroup Γ) (h : CobOn θ z D) :
    ∃ m : PadicAlgCl l, ∀ g ∈ D, (z g : PadicAlgCl l) = ((θ g : O) : PadicAlgCl l) * m - m := by
  obtain ⟨a, ha, m, hm⟩ := h
  have ha' : (a : PadicAlgCl l) ≠ 0 := fun h => ha (Subtype.ext h)
  refine ⟨(m : PadicAlgCl l) / a, fun g hg => ?_⟩
  have h1 : (a : PadicAlgCl l) * z g = ((θ g : O) : PadicAlgCl l) * m - m := by
    exact_mod_cast congrArg Subtype.val (hm g hg)
  field_simp
  linear_combination h1

private theorem cob_down {l : ℕ} [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)) {Γ : Type} [Group Γ]
    (θ : Γ →* Oˣ) (z : Γ → O) (m : PadicAlgCl l)
    (hm : ∀ g, (z g : PadicAlgCl l) = ((θ g : O) : PadicAlgCl l) * m - m) : CobOn θ z ⊤ := by
  by_cases h : ∃ g₀, (θ g₀ : O) ≠ 1
  · obtain ⟨g₀, hg₀⟩ := h
    refine ⟨θ g₀ - 1, sub_ne_zero.2 hg₀, z g₀, fun g _ => Subtype.ext ?_⟩
    push_cast
    rw [hm g, hm g₀]
    ring
  · push Not at h
    refine cobOn_of_eq_zero θ fun g _ => Subtype.ext ?_
    rw [hm g, h g]
    simp

theorem UpperTheory.V.X.So.soCoc :
    ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (ψ : G k Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ z : G k Ω → c.O, Coc (Chr.Psi l e ψ)⁻¹ z → Alg.AdicCont (maximalIdeal c.O) z → (∀ A : ValuationSubring Ω, CobOn (Chr.Psi l e ψ)⁻¹ z (Ine (F := k) A)) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A)) → CobOn (Chr.Psi l e ψ)⁻¹ z ⊤ := by
  intro CK hK hPT hLF hLT k Ω _ _ _ _ _ l _ c ψ hψ e he z hz hc h1 h2
  let ψ' : G k Ω →* (PadicAlgCl l)ˣ := (Units.map c.O.val.toMonoidHom).comp ψ
  have hψ' : IsOpen (ψ'.ker : Set (G k Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => ?_) hψ
    have : ψ g = 1 := hg
    show Units.map c.O.val.toMonoidHom (ψ g) = 1
    rw [this, map_one]
  have hcz : Continuous z := ((UpperTheory.V.X.So.adicCont l c).2 _ z).1 hc
  obtain ⟨m, hm⟩ := UpperTheory.V.X.soBar CK hK hPT hLF hLT k Ω l ψ' hψ' e he
    (fun g => (((Chr.Psi l e ψ)⁻¹ g : c.O) : PadicAlgCl l)) (fun g => by
      have h0 : (((Chr.Psi l e ψ)⁻¹ g : c.Oˣ) : c.O) * (ψ g : c.O) * algebraMap ℤ_[l] c.O (cycZ k Ω l g : ℤ_[l]) ^ e = 1 := by
        have e1 : algebraMap ℤ_[l] c.O (cycZ k Ω l g : ℤ_[l]) = (chiO k Ω l c.O g : c.O) := rfl
        rw [e1, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul, Units.val_eq_one]
        show (chiO k Ω l c.O g ^ (e : ℤ) * ψ g)⁻¹ * ψ g * chiO k Ω l c.O g ^ e = 1
        rw [zpow_natCast, mul_assoc, mul_comm (ψ g), inv_mul_cancel]
      have h3 := congrArg c.O.val h0
      rw [map_mul, map_mul, map_pow, map_one, AlgHom.commutes] at h3
      exact h3)
    (fun g => (z g : PadicAlgCl l)) (continuous_subtype_val.comp hcz)
    (fun g h => by exact_mod_cast congrArg Subtype.val (hz g h))
    (fun A => cob_up c.O _ z _ (h1 A)) (fun A hA => cob_up c.O _ z _ (h2 A hA))
  exact cob_down c.O _ z m hm
