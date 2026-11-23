import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenScal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverComponentOverBaseRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChangesStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsPullOfMoveInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedBlockSelfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevOfLiftsOfEqOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.LevDegree

theorem card_lifts_const : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ σ₂, GoodEmb d.c₂ σ₂ → letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra; ∀ y y' : FrPt Xo c (CAt σ₂), Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} = Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y'} := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd σ₂ _ y y'
  letI : Algebra c.F (CAt σ₂) := (σ₂.comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  letI : Field (CAt σ₂) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ₂) := inferInstanceAs (IsAlgClosed ℂ)
  have hA : l.A = 1 := hL.levA
  have hA₂ : d.l₂.A = 1 := hL₂.levA
  have hpq : Dw.p ≠ Dw.q ∧ 1 ≤ Dw.p + Dw.q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hL.inR
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hk : ∀ a : c.F, algebraMap d.c₂.F (CAt σ₂) (d.eF a) = algebraMap c.F (CAt σ₂) a := fun _ => rfl
  obtain ⟨lift, hlift⟩ := GlobalTheory.LevPullModel.exists_isLift (Dw := Dw) (l := d.l₂)
  have hov : ∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ spMap (IntermediateField.inclusion h).toRingHom :=
    GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hA d
  have L := GlobalTheory.LevelActionOfLifts.actLev_of_lifts_of_eq_one D H Dw d.l₂ d.Xo₂ d.c₂ (Gam Dw d.l₂) lift hpq.2 hA₂
    (fun a => (Submodule.Quotient.eq _).1 ((GlobalTheory.LevPullModel.lift_mk hlift 1 a).trans rfl))
    (fun g h a => (Submodule.Quotient.eq _).1 (by
      rw [GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift, GlobalTheory.LevPullModel.lift_mk hlift]; rfl))
  have key : ∀ y : FrPt Xo c (CAt σ₂),
      Nat.card {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} =
        Nat.card {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} := by
    intro y
    obtain ⟨y₀, hy₀⟩ := hd.2.2.2.2.2.2.1 (CAt σ₂) hk y
    have T := GlobalTheory.T.levelCover_fibre_torsor_trivial_level_changes D.host.E H Dw l Xo c d hpq.2 hd hA₂ hov lift hlift (CAt σ₂) hk y₀
    have hA₂' : d.l₂.A.Coprime d.l₂.M := by rw [hA₂]; exact Nat.coprime_one_left _
    have hex : ∀ γ : Gam Dw d.l₂, ∃ y₂', levR (lift γ, (LinearMap.id : Dw.La →ₗ[𝓞 D.host.E] Dw.La)) y₀ y₂' :=
      fun γ => L.total γ (CAt σ₂) y₀
    choose g hg using hex
    let f : {γ : Gam Dw d.l₂ // CongMod l.Mb (lift γ) LinearMap.id} →
        {y₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) // FrOver d y₂ y} :=
      fun γ => ⟨g γ.1, ((T (g γ.1) y hy₀).1).2 ⟨γ.1, γ.2, hg γ.1⟩⟩
    refine (Nat.card_eq_of_bijective f ⟨fun γ γ' e => Subtype.ext ?_, fun z => ?_⟩).symm
    · have e' : g γ.1 = g γ'.1 := congrArg Subtype.val e
      exact (T (g γ.1) y hy₀).2 γ.1 γ'.1 (hg γ.1) (e' ▸ hg γ'.1)
    · obtain ⟨γ, hγ, hl⟩ := ((T z.1 y hy₀).1).1 z.2
      exact ⟨⟨γ, hγ⟩, Subtype.ext (GlobalTheory.LevelSpanCompare.levR_unique hpq.2 hA₂' (lift γ) (hg γ) hl)⟩
  exact (key y).trans (key y').symm

end GlobalTheory.LevDegree
