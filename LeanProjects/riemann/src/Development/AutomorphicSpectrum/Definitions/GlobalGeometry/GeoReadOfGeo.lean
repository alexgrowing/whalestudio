import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameSectionBound
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FrBorDiagUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.GeoReadModel

open CategoryTheory NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar.Rec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}
  {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

theorem evR_of_geo {K L : Type} [Field K] [Algebra c.F K] [Field L] [Algebra c.F L] (φ : K →ₐ[c.F] L)
    {y : FrPt Xo c K} {y' y'' : FrPt Xo c L} {t : Ix Dw → Lˣ} (hm : FrMap φ y y') (hb : FrBor t y' y'')
    (a : WZ E) (f : Rul Xo c) (hf : f ∈ secZ Xo c a) :
    evR Xo c f y'' = ((∏ i, t i ^ exZ Dw a i : Lˣ) : L) * φ (evR Xo c f y) := by
  obtain ⟨⟨-, hC, hB, -, hA, -⟩, -⟩ := GlobalTheory.Exist.frame_laws_of_moduli E H Dw l Xo c
  have hWD := evalWD_fr hC
  have key : ∀ {T : Type} [Field T] [Algebra c.F T] (p : TRing c.F) (ψ : p.R →ₐ[c.F] T) (u : FrPt Xo c p.R)
      (z : FrPt Xo c T), FrMap ψ u z → evR Xo c f z = ψ (f p u) := by
    intro T _ _ p ψ u z hz
    have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, u, hz⟩
    unfold evR evalAt
    rw [dif_pos hft]
    exact hWD f hf.1 T _ p _ ψ _ u z hft.choose_spec.choose_spec.choose_spec hz
  obtain ⟨p, ψ, u, hu⟩ := hA K y
  have e1 : evR Xo c f y' = φ (evR Xo c f y) := by
    rw [key p ψ u y hu, key p (φ.comp ψ) u y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ φ hu hm)]
    rfl
  rw [← e1]
  exact FinRd.evalAt_bor_zpow hB (exZ Dw a) hf.1
    (fun p t y y' hb => by rw [hf.2 p t y y' hb, Units.coe_prod]) L t y' y'' (hA L y') (hA L y'') hb

def ofGeo (φ : letI := Small.cstAlg Or; Om Z →ₐ[c.F] RM.Ω) (t : Ix Dw → (RM.Ω)ˣ)
    (hg : letI := Small.cstAlg Or; ∃ y' : FrPt Xo c RM.Ω, FrMap φ (genFr h Z) y' ∧ FrBor t y' Fr.y₀)
    (hd : letI := Small.cstAlg Or; letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) :
    Reading Fr h Z :=
  letI := Small.cstAlg Or
  { φ := φ.toRingHom
    φ_cst := φ.commutes
    t := t
    rd_eq := fun a f hf => by
      obtain ⟨y', hm, hb⟩ := hg
      exact evR_of_geo φ hm hb a f hf
    deg := hd }

theorem geoRead_ofGeo (φ : letI := Small.cstAlg Or; Om Z →ₐ[c.F] RM.Ω) (t : Ix Dw → (RM.Ω)ˣ)
    (hg : letI := Small.cstAlg Or; ∃ y' : FrPt Xo c RM.Ω, FrMap φ (genFr h Z) y' ∧ FrBor t y' Fr.y₀)
    (hd : letI := Small.cstAlg Or; letI := φ.toRingHom.toAlgebra; Module.finrank (Om Z) RM.Ω = Or.Fl.deg) :
    GeoRead (ofGeo (Fr := Fr) φ t hg hd) := hg

theorem comp_eq {Z' : Comp Xo c} {R : Reading Fr h Z} {R' : Reading Fr h Z'} (g : GeoRead R) (g' : GeoRead R') :
    Z = Z' ∧ HEq R.φ R'.φ := by
  letI := Small.cstAlg Or
  obtain ⟨y, hm, hb⟩ := g
  obtain ⟨y', hm', hb'⟩ := g'
  have hi := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω y' Fr.y₀ y').2.2.2 _ hb'
  have hc := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω y Fr.y₀ y').2.2.1 _ _ hb hi
  obtain ⟨rfl, he⟩ := GlobalTheory.Reg.GenericFlagInj.eq_of_frBor h Z Z' _ _ y y' _ hm hm' hc
  exact ⟨rfl, heq_of_eq (congrArg AlgHom.toRingHom (eq_of_heq he))⟩

theorem unique {R R' : Reading Fr h Z} (g : GeoRead R) (g' : GeoRead R') : R = R' := by
  letI := Small.cstAlg Or
  have hφ : R.φ = R'.φ := eq_of_heq (comp_eq g g').2
  obtain ⟨φ, hc, t, hr, hd⟩ := R
  obtain ⟨φ', hc', t', hr', hd'⟩ := R'
  obtain rfl : φ = φ' := hφ
  obtain ⟨y, hm, hb⟩ := g
  obtain ⟨y', hm', hb'⟩ := g'
  obtain rfl : y = y' := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ (genFr h Z)).1 _ _ hm hm'
  obtain rfl : t = t' := GlobalTheory.FrameRelCheck.frBor_diag_unique _ _ _ _ hb hb'
  rfl

open Classical in

def flip (R : Reading Fr h Z) : Reading Fr h Z where
  φ := R.φ
  φ_cst := R.φ_cst
  t := Function.update R.t none (-R.t none)
  rd_eq a f hf := by
    rw [R.rd_eq a f hf]
    congr 2
    refine Finset.prod_congr rfl fun i _ => ?_
    cases i with
    | none => simp [Rec.exZ]
    | some x => simp
  deg := R.deg

theorem not_both (R : Reading Fr h Z) : ¬ (GeoRead R ∧ GeoRead (flip R)) := by
  rintro ⟨g, g'⟩
  have e := congrFun (congrArg Reading.t (unique g g')) none
  simp only [flip, Function.update_self] at e
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom Or.𝔐.cst.injective
  have e2 : ((R.t none : (RM.Ω)ˣ) : RM.Ω) = -(R.t none : (RM.Ω)ˣ) := by
    have := congrArg Units.val e
    rwa [Units.val_neg] at this
  exact (R.t none).ne_zero (by linear_combination (1 / 2 : RM.Ω) * e2)

theorem pt_over {R : Reading Fr h Z} (g : GeoRead R) :
    Or.𝔐.ξ ≫ Or.𝔐.f = spMap R.φ ≫ Small.ptY Y (genFr h Z) := by
  letI := Small.cstAlg Or
  obtain ⟨y, hm, hb⟩ := g
  have e := Small.ptY_map Y hm
  have e2 : Small.ptY Y Fr.y₀ = Small.ptY Y y := by
    unfold Small.ptY
    congr 1
    apply CategoryTheory.Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hb.1]
    · rw [Small.ptF_snd, Small.ptF_snd]
  rw [← Fr.pt_eq, e2, e]

theorem transport {R : Reading Fr h Z} (g : GeoRead R) (Fr' : Small.GenFrame Or) :
    ∃ R' : Reading Fr' h Z, GeoRead R' ∧ R'.φ = R.φ := by
  letI := Small.cstAlg Or
  obtain ⟨y, hm, hb⟩ := g
  have hx : Fr'.y₀.x = Fr.y₀.x := Fr'.x_eq Fr
  have hrefl := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω y Fr.y₀ Fr.y₀).2.2.2 _ hb
  have h1 := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω Fr.y₀ y Fr.y₀).2.2.1 _ _ hrefl hb
  have hu : ∀ τ i, Fr'.y₀.u τ i = Fr.y₀.u τ i := by
    intro τ i
    obtain ⟨s, k, e⟩ := Small.exists_labelFin Dw τ i
    cases e
    exact Small.u_eq_of_tanY_eq Y (Fr'.pt_eq.trans Fr.pt_eq.symm) ((Fr'.tan_eq s k).trans (Fr.tan_eq s k).symm)
  obtain ⟨t, ht⟩ := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω Fr.y₀ Fr'.y₀ Fr.y₀).2.1 hx (fun τ i => by
    obtain ⟨cf, h2, h3, h4⟩ := h1.2.1 τ i
    exact ⟨cf, h2 ▸ Units.isUnit _, h3, by rw [hu]; exact h4⟩)
  have hb' := (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c RM.Ω y Fr.y₀ Fr'.y₀).2.2.1 _ _ hb ht
  exact ⟨ofGeo _ _ ⟨y, hm, hb'⟩ R.deg, geoRead_ofGeo _ _ ⟨y, hm, hb'⟩ R.deg, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Plug.GeoReadModel
