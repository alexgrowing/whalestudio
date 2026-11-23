import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.Ar.Rec.ReadEx
attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {SS : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem ModelDimension.geo_core (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c)
    (hZ : GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z)) :
    letI := Small.cstAlg Or
    ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧
      (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  letI algΩ := Small.cstAlg Or
  obtain ⟨ψ, hψ, hc⟩ := GlobalTheory.T.root_origin_component_generic_point E H Dw l Xo c Y SS RM Sys Fx Or Z hZ
  obtain ⟨hgx, y₀, hy₀, hy₀c⟩ := isGenFr_genFr h Z
  obtain ⟨N, ec, hx, hb, hj, hli₀, hli, hmem⟩ := flags_setup Or Fr Z ψ hψ hc y₀ hy₀
  letI algfn : Algebra Or.𝔐.Ω₀ RM.Ω := Or.𝔐.fn.toAlgebra
  have hg' := generic_cast Or.Fl.j (labelRk Dw) (fun s => Dw.mult (Small.labelC s)) (Small.mult_labelC Dw) Or.Fl.V₀
    Or.Fl.b Or.Fl.deg Or.Fl.generic
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hbT, hT0, hTd⟩ := lin_core Or.Fl.j Or.Fl.V₀ _ Or.Fl.deg hg'
    (fun s => ec (Small.labelC s)) (fun s => hli₀ _) hmem (fun s => hli _)
  obtain ⟨T, hTi, hTr, hTv⟩ := exists_strictHenselian_absolutely_closed_local_ring v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := exists_lift ψ T hTi
  have hφk : ∀ x, φ (algebraMap (kap Z) (Om Z) x) = Or.𝔐.fn (ψ x) := fun x => by
    rw [IsScalarTower.algebraMap_apply (kap Z) (MvPolynomial (FlagVar Dw) (kap Z)) (Om Z) x]
    exact hφC x
  have hφc : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [gfp_tower Z a, hφk, hc]
  let φA : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφc }
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  obtain ⟨y₃, h₃⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c _ _ φA (genFr h Z)
  have hk : φ.comp (algebraMap (kap Z) (Om Z)) = Or.𝔐.fn.comp ψ.toRingHom := RingHom.ext hφk
  have hbase : spMap φ ≫ (genFr h Z).x = Fr.y₀.x := by
    rw [hgx, ← Category.assoc, spc, hk, ← hy₀]
    exact hx
  have hx₃ : y₃.x = Fr.y₀.x := h₃.1.trans hbase
  have hcoef : ∀ s (i j : Fin (Dw.mult (Small.labelC s))), φ (genCoef Z (Small.labelC s) i j) = v s j i := by
    intro s i j
    unfold genCoef
    split_ifs with h1 h2
    · rw [hφX]
      exact hTv s i j h1
    · subst h2
      rw [map_one, hv1]
    · rw [map_zero, hv0 s j i (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))]
  have hy3 : ∀ s, y₃.u (Small.labelC s) = fun m =>
      (N.pt (∑ l, v s l m • Or.Fl.j (ec (Small.labelC s) l))).left := by
    intro s
    funext i
    have h1 := GlobalTheory.T.is_comb_base_change E H Dw l Xo _ _ φ (genFr h Z).x _ _ _ _ (hy₀c (Small.labelC s) i)
    have hv : (fun j => spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j) = fun j => (N.pt (Or.Fl.j (ec (Small.labelC s) j))).left := by
      funext j
      rw [hj, ← Category.assoc, spc, ← dualMap_comp₂, hk]
    rw [hbase, hv, comb_iff N] at h1
    rw [h₃.2.1]
    refine h1.trans ?_
    simp only [hcoef]
  obtain ⟨t, ht⟩ : ∃ t, FrBor t y₃ Fr.y₀ := frBor_of_comb y₃ Fr.y₀ hx₃.symm (fun τ i => by
    obtain ⟨s, rfl⟩ := (Small.labelC_bijective H).2 τ
    refine ⟨Tm s i, isUnit_iff_ne_zero.2 (hTd s i), fun j hij => hT0 s i j hij, ?_⟩
    rw [hx₃, hy3 s, comb_iff N]
    exact (hb s i).symm.trans (congrArg (fun e => (N.pt e).left) (hbT s i)))
  refine ⟨φA, y₃, t, h₃, ht, hφd.trans ?_⟩
  rw [hTr, ← adjoin_all_eq_strict v hv1 hv0]
  exact hvd

end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace ModelDimension

theorem component_laws_unif_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (Fr : Small.GenFrame Or) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → letI := Small.cstAlg Or; ∃ (φ : Om Z →ₐ[c.F] RM.Ω) (P : FrPt Xo c RM.Ω) (t : Ix Dw → (RM.Ω)ˣ), FrMap φ (genFr h Z) P ∧ FrBor t P Fr.y₀ ∧ (letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) := by
  intro E _ _ _ H Dw l Xo c r U h e _ Y S RM Sys Fx Or Fr Z hZ
  exact geo_core Or Fr h Z hZ

end ModelDimension
