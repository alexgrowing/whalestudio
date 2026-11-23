import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga

private theorem cyc_eq_of_pow {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal)
    (h : IsPlaceOver A w) {σ : G L Ω} {q : ℕ}
    (hσ : ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1) :
    (cycBar L Ω l σ : Qbar l) = (q : Qbar l) := by
  have h1 : ((cycZ L Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp (cycZ_toZModPow_eq hl h hσ)
  simp [cycBar, h1]

end UpperTheory.V.Z.Sym.Ga

theorem UpperTheory.V.Z.Sym.Ga.epsAway :
    Af.Hypotheses₂ → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ s : Weil h, ι (Ga.ep l (s : G L Ω)) = (absPow (w.adicCompletion L) 1 (a s) : ℂ) ∧ ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
  intro _ L Ω _ _ _ _ _ l _ ι w hl A h a ha s
  have hfrob : (cycBar L Ω l ((frob h : Weil h) : G L Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) :=
    Ga.cyc_eq_of_pow hl h (isFrob_frob (h := h)).2
  set t : Weil h := s * (frob h) ^ (-deg s) with ht
  have hdt : deg t = 0 := by
    rw [ht, deg_mul, deg_zpow, deg_frob]
    ring
  have hI : (t : G L Ω) ∈ Ine (F := L) A :=
    actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hdt))
  have hine : (cycBar L Ω l (t : G L Ω) : Qbar l) = 1 := by
    have := Ga.cyc_eq_of_pow (σ := (t : G L Ω)) (q := 1) hl h (fun x hx => by simpa using hI.2 x hx)
    simpa using this
  have hs : s = t * (frob h) ^ (deg s) := by
    rw [ht, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hε : Ga.ep l (s : G L Ω) = ((normV w : ℕ) : Qbar l) ^ deg s := by
    show (cycBar L Ω l (s : G L Ω) : Qbar l) = _
    conv_lhs => rw [hs]
    rw [Subgroup.coe_mul, map_mul, Units.val_mul, hine, one_mul, Subgroup.coe_zpow, map_zpow,
      Units.val_zpow_eq_zpow_val, hfrob]
  have hq : ι (Ga.ep l (s : G L Ω)) = ((normV w : ℕ) : ℂ) ^ deg s := by
    rw [hε, map_zpow₀, map_natCast]
  refine ⟨?_, hq⟩
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [hq, ← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val]
  simp
