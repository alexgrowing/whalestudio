import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Gu.FrobTwTAux

open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem tw_diag (X : ExtraV) {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (t : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw t = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w t) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc H
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    L.sat (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  rw [cl, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_tw (t : ℝ) (x : ℂˣ) :
    (((x⁻¹ * qPow w t : ℂˣ) : ℂ)) ^ (-1 : ℤ) = (x : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(t : ℂ)) := by
  rw [zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv, coe_qPow, ← Complex.cpow_neg]

end UpperTheory.V.Z.Win.Gu.FrobTwTAux

open UpperTheory.V.Z.Win.Gu.FrobTwTAux in
theorem UpperTheory.V.Z.Win.Gu.frobTwT :
    ExtraV → GdLaws → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ t : ℝ, (ParAtT ι r w fun _ _ rc => (rc (cl σ)).lpTw t) → FrobEig ι r w (B.map fun α : ℂˣ => (α : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(t : ℂ))) := by
  intro X hG E Ω _ _ _ _ _ l _ ι a r w hl σ B hB t H A h
  obtain ⟨rc, hrec⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
  obtain ⟨α, rfl, e⟩ := tw_diag X hrec σ B hB t
  have hu : (WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w t)).unr := (WD.unr_mk _).2 (WDRep.unr_diag _)
  have hg : UpperTheory.V.Z.Win.Gd ((rc (cl σ)).lpTw t) := by
    rw [e]
    exact (hG E Ω A w h).2.2.2 _ hu
  have hk : WDT ι r ((rc (cl σ)).lpTw t) := (H A h rc hrec).1 hl
  have hx := hk.isWDOf hg
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t', ht, φ, hφ, N, b, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact hu), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_tw, Multiset.map_map]
  rfl
