import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianMapModelOfIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFrameChangeDiagonalUnitsIntegralFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IntFrameSat

theorem tanPull_frac_injective {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) (T : CDVR) (xV : Sp T.V ⟶ X) :
    Function.Injective (GlobalTheory.FlagMod.tanPull (G := t.G) (algebraMap T.V T.Fr)
      (rfl : spMap (algebraMap T.V T.Fr) ≫ xV = spMap (algebraMap T.V T.Fr) ≫ xV)) := by
  rw [injective_iff_map_eq_zero]
  intro D hD
  obtain ⟨n, Dv, hDt, hst⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t T.V xV
  have hid : spMap (algebraMap T.V T.V) = 𝟙 _ := Spec.map_id _
  have hdid : spMap (dualMap (algebraMap T.V T.V)) = 𝟙 _ := by
    have : dualMap (algebraMap T.V T.V) = RingHom.id _ := by
      apply RingHom.ext
      intro z
      ext <;> simp [dualMap]
    rw [this]
    exact Spec.map_id _
  have h1 := hst T.V (algebraMap T.V T.V) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv D).left (by rw [hid, Category.id_comp]; exact isTan_tv D)
  simp only [hid, hdid, Category.id_comp] at h1
  obtain ⟨a, ha, -⟩ := h1
  let d : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM xV t.G := fun e => tanOf (hDt e)
  have hDs : D = ∑ e, a e • d e := (GlobalTheory.LieMet.isComb_iff d a D).1 ha
  have h0 : (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (algebraMap T.V T.Fr) ≫ xV) t.G) =
      ∑ e, algebraMap T.V T.Fr (a e) • GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) rfl (d e) := by
    rw [← hD, hDs, map_sum]
    simp only [map_smulₛₗ]
  obtain ⟨b, -, hb⟩ := hst T.Fr (algebraMap T.V T.Fr) (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (0 : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap (algebraMap T.V T.Fr) ≫ xV) t.G)).left
    (isTan_tv _)
  have hc1 := hb (fun e => algebraMap T.V T.Fr (a e))
    ((GlobalTheory.LieMet.isComb_iff (fun e => GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) rfl (d e)) _ _).2 h0)
  have hc2 := hb 0
    ((GlobalTheory.LieMet.isComb_iff (fun e => GlobalTheory.FlagMod.tanPull (algebraMap T.V T.Fr) rfl (d e)) _ _).2 (by simp))
  have ha0 : a = 0 := by
    funext e
    have := congrFun (hc1.trans hc2.symm) e
    exact IsFractionRing.injective T.V T.Fr (by simpa using this)
  rw [hDs, ha0]
  simp

end GlobalTheory.IntFrameSat

namespace GlobalTheory.IntFrameSat

set_option maxHeartbeats 1000000 in

theorem intFrame_model_sat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (xV : Sp T.V ⟶ Z.X), letI := io.toAlgebra; spMap (algebraMap T.V T.Fr) ≫ xV = AllWt.ptF y.1 ≫ Z.jQ ≫ genι Z → ∀ τ : E →+* ℂ, ∃ v : Fin (Dw.mult τ) → (Sp (DualNumber T.V) ⟶ Z.t.G.left), (∀ i, IsTanAtG Z.t xV (v i)) ∧ (∀ i, ∃ w : Sp (DualNumber T.Fr) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ AllWt.ptF y.1 ∧ w ≫ Z.m0.toSABMap.φ = y.1.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ v i) ∧ ∀ (cf : Fin (Dw.mult τ) → T.Fr) (u : Sp (DualNumber T.V) ⟶ Z.t.G.left), IsTanAtG Z.t xV u → IsCombAtG Z.t (spMap (algebraMap T.V T.Fr) ≫ xV) (fun i => spMap (dualMap (algebraMap T.V T.Fr)) ≫ v i) cf (spMap (dualMap (algebraMap T.V T.Fr)) ≫ u) → ∀ i, ∃ a : T.V, algebraMap T.V T.Fr a = cf i := by
  intro E _ _ _ H Dw l Xo c O _ β Z T io y xV
  letI := io.toAlgebra
  intro hxV τ
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbas, hu⟩, -⟩ := y.2.2
  obtain ⟨ψ, ρ, h1, h2, h3⟩ := GlobalTheory.exists_sabMap_model_of_integral_frPt Z T io y.1 xV hxV G t' m1 m2
  have hmono : Mono (spMap (algebraMap T.V T.Fr)) := by
    have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) := IsLocalization.epi (nonZeroDivisors T.V) T.Fr
    exact Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hbase : spMap (dualMap (algebraMap T.V T.Fr)) ≫ (epsOver T.V T.V).hom =
      spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ spMap (algebraMap T.V T.Fr) := by
    show spMap (dualMap (algebraMap T.V T.Fr)) ≫ spMap ((algebraMap T.V (DualNumber T.V)).comp (algebraMap T.V T.V)) = _
    rw [GlobalTheory.ShFam.OpenReg.spMap_comp, GlobalTheory.ShFam.OpenReg.spMap_comp]
    congr 1
    ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

  have hw : ∀ i, ∃ w : Sp (DualNumber T.Fr) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) ≫ AllWt.ptF y.1 ∧
      w ≫ Z.m0.toSABMap.φ = y.1.u τ i ∧
      w ≫ Z.m.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ ((ub τ i).left ≫ ψ.φ) := by
    intro i
    obtain ⟨u', hu1, hu2⟩ := hu τ i
    have hut : u' ≫ t'.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      apply (cancel_mono (spMap (algebraMap T.V T.Fr))).1
      rw [Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu2, Category.assoc, Over.w (ub τ i), hbase]
    refine ⟨u' ≫ ρ, ?_, ?_, ?_⟩
    · rw [Category.assoc, h2, ← Category.assoc, hut]
      rfl
    · rw [Category.assoc, h1, hu1]
    · rw [Category.assoc, h3, ← Category.assoc, hu2, Category.assoc]

  let f := GlobalTheory.ShFam.EigFrame.ofFrPt Z y.1 hxV.symm
  have hfv : ∀ i, f.v τ i = spMap (dualMap (algebraMap T.V T.Fr)) ≫ ((ub τ i).left ≫ ψ.φ) := by
    intro i
    obtain ⟨w0, hw0t, hw0a, hw0b⟩ := GlobalTheory.ShFam.EigFrame.ofFrPt_v Z y.1 hxV.symm τ i
    obtain ⟨w, hwa, hwb, hwc⟩ := hw i
    have : w0 = w := by
      apply Z.m0.toSABMap.cart.1.hom_ext
      · rw [hw0a, hwb]
      · rw [hw0t.1, hwa]
    rw [← hw0b, this, hwc]
  refine ⟨fun i => (ub τ i).left ≫ ψ.φ, fun i => ?_, hw, ?_⟩
  · obtain ⟨v, hv⟩ := GlobalTheory.T.exists_modelTangent_of_pullback_tangent xV G ψ (ub τ i) (htan τ i)
    have hv' := isTan_tv v
    rw [hv] at hv'
    exact hv'
  · intro cf u hu0 hc
    have hinj := tanPull_frac_injective Z.t T xV
    obtain ⟨ub', hub', hsp⟩ := GlobalTheory.IntFrameDiag.integralFrame_transport T io xV _ rfl hinj G ψ τ (ub τ)
      (htan τ) (hbas τ)
    let U : TanM xV Z.t.G := tanOf hu0
    have hvec : ∀ i, GlobalTheory.FlagMod.tanPull (G := Z.t.G) (algebraMap T.V T.Fr) rfl (ub' i) = f.vec τ i := by
      intro i
      apply tan_ext
      rw [GlobalTheory.FlagMod.tanPull_left, hub' i]
      exact (hfv i).symm
    have hU : GlobalTheory.FlagMod.tanPull (G := Z.t.G) (algebraMap T.V T.Fr) rfl U = ∑ i, cf i • f.vec τ i := by
      refine (GlobalTheory.LieMet.isComb_iff (f.vec τ) cf _).1 ?_
      have e1 : (fun i => (tv (f.vec τ i)).left) = fun i => spMap (dualMap (algebraMap T.V T.Fr)) ≫ ((ub τ i).left ≫ ψ.φ) :=
        funext hfv
      rw [e1]
      exact hc
    have hmem : GlobalTheory.FlagMod.tanPull (G := Z.t.G) (algebraMap T.V T.Fr) rfl U ∈ GlobalTheory.FlagMod.eigLie c (spMap (algebraMap T.V T.Fr) ≫ xV) τ := by
      rw [hU]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      exact fun a => f.act_vec τ i a
    obtain ⟨a, ha⟩ := hsp U hmem
    have h2' : GlobalTheory.FlagMod.tanPull (G := Z.t.G) (algebraMap T.V T.Fr) rfl U = ∑ i, algebraMap T.V T.Fr (a i) • f.vec τ i := by
      rw [← ha, map_sum]
      simp only [map_smulₛₗ, hvec]
    have hli := Fintype.linearIndependent_iff.1 (f.linearIndependent_vec τ) (fun i => cf i - algebraMap T.V T.Fr (a i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, ← hU, ← h2', sub_self])
    intro i
    exact ⟨a i, (sub_eq_zero.1 (hli i)).symm⟩

end GlobalTheory.IntFrameSat
