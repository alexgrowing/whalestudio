import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftExistsUniqueGlobal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsUniqueIsTwistPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HasGenPull

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

namespace TransPullEx

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (L : RigLB A)

theorem exists_isNormPull (φ : A ⟶ A) [IsMonHom φ] (a b : ℤ)
    (β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b])) (hβ : β.IsGen)
    {T : Over S} (s : LB.Sec (LPow A L.L b T)) : ∃ s', IsNormPull A L φ a b s s' := by
  have hL := L.isLB
  have ha : eSec A ≫ φ.left = eSec A := by simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  obtain ⟨α₀, hα₀, hv₀⟩ := exists_gen hL (φ' := ![𝟙 A.left, φ.left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, ha, Category.comp_id]
      rw [← zpow_add, ← zpow_add, ← zpow_add, show -a + - -b + (a + -b) = 0 by ring, zpow_zero,
        _root_.mul_one])
    (LB.mulGen L.L _ _ _ _ β (LB.pullGen L.L _ _ (LB.mulGen L.L _ _ _ _
      (LB.invGen L.L _ _ (LB.pullGen L.L _ _ β (eSec A)))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hβ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (NormMulUniv.rigPow_isGen L.rigGen _)
        (NormMulUniv.rigPow_isGen L.rigGen _))) _))
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ φ).left]) (ε' := ![a, -b])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ a) (Category.comp_id _)
      · rfl)
    (LB.pullGen L.L ![𝟙 A.left, φ.left] ![a, -b] α₀ (snd T A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨s', hs', -⟩ := existsUnique_isTwistPull S A L.L hL T (endOver A T φ) (snd T A ≫ φ) (lift_snd _ _) a b α hα s
  refine ⟨s', α₀, α, hα₀, corr_of_val hL fun y J hJ => ?_, corr_of_val hL fun y J hJ => hv _ _ y J hJ, hs'⟩
  rw [val_pull hJ, hv₀ _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormMulUniv.eSec_hom, Category.comp_id,
    val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]

end TransPullEx

theorem exists_isTransPull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] (xF : Sp F ⟶ Xo.X) (α : 𝓞 E) (N : ℕ), Odd N → α * star α = (N : 𝓞 E) → ∀ (s : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L 1 (ptO Xo xF))) (b : ptO Xo xF ⟶ Xo.univ.t.G), b ^ N = 1 → ∃ hh, IsTransPull Xo.univ.t.G Xo.univ.t.PP (Xo.univ.t.act.act α) N s b hh := by
  intro E _ _ _ H Dw l Xo c F _ _ xF α N hN hα s b hb
  letI := H.starRing
  have hLaw : Laws := firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have := Xo.univ.t.act.hom α
  have hL := Xo.univ.t.PP.isLB
  have h := PullGenG.hasGen_pull Xo.univ.t.PP Xo.univ.t.cub Xo.univ.t.act.toRingAct H.w0 α N hα (Xo.univ.t.adj α)
    Xo.univ.t.prim 1
  rw [Nat.one_mul] at h
  obtain ⟨β, hβ⟩ := h.gen hL (K' := Fin 2) ![𝟙 Xo.univ.t.G.left, (Xo.univ.t.act.act α).left] ![(N : ℤ), -1] rfl
  obtain ⟨h₁, hh₁⟩ := TransPullEx.exists_isNormPull Xo.univ.t.PP (Xo.univ.t.act.act α) (N : ℤ) 1 β hβ s
  obtain ⟨⟨U, hU⟩, -⟩ := symLift_exists_unique_of_cast hLaw Xo.X (UnivPol.pol Xo) N hN
    (UnivPol.isUnit_natCast Xo _ hN.pos) (N : ℤ) rfl (ptO Xo xF) b hb
  obtain ⟨hh, hhh, -⟩ := existsUnique_isTwistPull Xo.X Xo.univ.t.G Xo.univ.t.PP.L hL (ptO Xo xF)
    (translT _ U.pt) (translPt _ U.pt) (lift_snd _ _) (N : ℤ) (N : ℤ) U.φ U.isGen h₁
  exact ⟨hh, h₁, hh₁, hb, U, hU, hhh⟩

end GlobalTheory
