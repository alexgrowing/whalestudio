import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagVariablesAlgIndepStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentIsoRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameConstantsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginConstantAlgebraPointsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.RdEx

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (Formalism.L2.Pj.dualMap g) ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap (Formalism.L2.Pj.dualMap (g.comp f)) := by
  rw [spMap_comp']
  congr 1
  refine RingHom.ext fun t => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

set_option maxHeartbeats 1000000 in

theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → ∃ Rd : Reading Fr h Z, GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Fr h Z hcomp hgt hWD
  letI := Small.cstAlg Or
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv E H Dw l Xo c Y SS RM Sys Fx Or Z hcomp
  obtain ⟨hyx, y₀, hy₀, hcomb⟩ := isGenFr_genFr h Z
  let χ : kap Z →ₐ[c.F] RM.Ω := { Or.𝔐.fn.comp ψ.toRingHom with commutes' := hψ2 }
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.FrameNorm.exists_frMap_along χ y₀
  obtain ⟨hpt₂, hlie⟩ := GlobalTheory.T.root_origin_component_iso_relay E H Dw l Xo c Y SS RM Sys Fx Or Z ψ hψ1 y₀ hy₀ χ y₂ rfl hy₂
  choose e he hi hev using hlie
  letI fa := Or.𝔐.fn.toAlgebra
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hb, hT0, hTd⟩ := GlobalTheory.T.generic_flag_triangular_relay Or.𝔐.Ω₀ RM.Ω Or.Fl.Li₀ Or.𝔐.Li Or.Fl.j
    (CMType H ⊕ CMType H) (labelRk Dw) Or.Fl.V₀ Or.Fl.b Or.Fl.deg Or.Fl.generic e he hi
  obtain ⟨T, hTi, hTr, hTv⟩ := GlobalTheory.T.flag_variables_alg_indep E H Dw Or.𝔐.Ω₀ RM.Ω v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := GlobalTheory.T.polynomial_field_extension_degree (kap Z) Or.𝔐.Ω₀ RM.Ω (FlagVar Dw) ψ T hTi
  have hφk : ∀ a : kap Z, φ (algebraMap (kap Z) (Om Z) a) = Or.𝔐.fn (ψ a) := fun a => hφC a
  have hφcst : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [← hψ2 a, ← hφk]
    rfl
  let φa : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφcst }
  obtain ⟨y', hy'⟩ := GlobalTheory.FrameNorm.exists_frMap_along φa (genFr h Z)
  have hφχ : φ.comp (algebraMap (kap Z) (Om Z)) = χ.toRingHom := RingHom.ext hφk
  have hxx : y'.x = y₂.x := by
    rw [hy'.1, hy₂.1, hyx, hy₀]
    show spMap φ ≫ spMap _ ≫ _ = spMap χ.toRingHom ≫ _
    rw [← Category.assoc, spMap_comp', hφχ]
  have hptF : Small.ptF y' = Small.ptF y₂ := pullback.hom_ext (by rw [Small.ptF_fst, Small.ptF_fst, hxx])
    (by rw [Small.ptF_snd, Small.ptF_snd])
  have hpt' : Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f := by
    rw [← hpt₂, Small.ptY, Small.ptY, hptF]
  have hcoef : ∀ (s : CMType H ⊕ CMType H) (k m : Fin (labelRk Dw s)),
      φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) (Small.labelFin Dw s m)) = v s m k := by
    intro s k m
    unfold genCoef
    split_ifs with h1 h2
    · have := hφX ⟨Small.labelC s, ⟨(Small.labelFin Dw s k, Small.labelFin Dw s m), h1⟩⟩
      refine this.trans ((hTv s _ _ h1).trans ?_)
      rfl
    · have : k = m := Fin.ext (show (k : ℕ) = m from congrArg (fun x : Fin (Dw.mult (Small.labelC s)) => (x : ℕ)) h2)
      subst this
      rw [map_one, hv1]
    · have : m < k := by
        have h3 : ¬ (k : ℕ) < m := h1
        have h4 : (k : ℕ) ≠ m := fun e' => h2 (Fin.ext e')
        exact Fin.lt_def.2 (by omega)
      rw [map_zero, hv0 s m k this]
  have hc : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk Dw s)),
      IsCombAt y₂.x (y₂.u (Small.labelC s))
        (fun j => φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) j))
        (y'.u (Small.labelC s) (Small.labelFin Dw s k)) := by
    intro s k
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isCombAt_bc (ψ := φ) (x0 := (genFr h Z).x) (x0' := y'.x) hy'.1
      (hcomb (Small.labelC s) (Small.labelFin Dw s k))
    have h2 : ∀ j, spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j = y₂.u (Small.labelC s) j := fun j => by
      rw [hy₂.2.1, ← Category.assoc, spMap_dual_comp', hφχ]
    have h3 : y'.u (Small.labelC s) (Small.labelFin Dw s k) = spMap (Formalism.L2.Pj.dualMap φ) ≫ (genFr h Z).u (Small.labelC s) (Small.labelFin Dw s k) := hy'.2.1 _ _
    rw [h3, ← hxx]
    simpa only [h2] using h1
  let Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li := fun s m => ∑ k, v s k m • Or.Fl.j (e s k)
  have hW : ∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
    intro s k
    have := GlobalTheory.T.root_origin_constant_algebra_points E H Dw l Xo c Y SS RM Sys Fx Or y₂ y' hpt₂ hxx s (fun m => Or.Fl.j (e s m)) (hev s) _ k (hc s k)
    simpa only [hcoef] using this
  obtain ⟨t, hbor⟩ := GlobalTheory.T.root_origin_generic_frame_constants E H Dw l Xo c Y SS RM Sys Fx Or Fr y' hpt' Wv Tm hW hb hT0 hTd
  refine ⟨⟨φ, hφcst, t, fun a f hf => ?_, ?_⟩, y', hy', hbor⟩
  · have h1 := GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field E H Dw l Xo c a f RM.Ω t y' Fr.y₀ hf hbor
    obtain ⟨p, ψ₁, z, hz⟩ := hgt
    have key : ∀ {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ' : p.R →ₐ[c.F] S), FrMap ψ' z w →
        evR Xo c f w = ψ' (f p z) := by
      intro S _ _ w ψ' hw
      have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, ψ', z, hw⟩
      show evalAt _ _ f w = _
      unfold evalAt
      rw [dif_pos hft]
      exact hWD f hf.1 S _ p _ ψ' _ z w hft.choose_spec.choose_spec.choose_spec hw
    have h2 : evC h Z f = ψ₁ (f p z) := key _ _ hz
    have h3 : evR Xo c f y' = φ (evC h Z f) := by
      rw [key y' (φa.comp ψ₁) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ₁ φa hz hy'), h2]
      rfl
    show evR Xo c f Fr.y₀ = _
    rw [h1, h3]
  · have h1 := hφd
    rw [hTr, hvd] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.Plug.RdEx

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem exists_geoRead : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ (Fr : Small.GenFrame (o.Or B (κ Z))) (Rd : Reading Fr h Z), GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c r U h e hl Y T o κ hκ B Z
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z))
    (o.Or B (κ Z))
  obtain ⟨Rd, hR⟩ := RdEx.core E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z)) (o.Or B (κ Z)) Fr h Z
    (hκ Z) (hl.genT Z) hl.evalWD
  exact ⟨Fr, Rd, hR⟩

end GlobalTheory.CompanionTheory.Ar.Plug
