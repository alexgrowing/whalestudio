import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSecPullNonzeroOnFibres
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPolAVGenericFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtEx

theorem nonempty_basis_of_isLieBasis {X : Scheme.{0}} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G : Over X} [GrpObj G]
    [IsCommMonObj G] {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G x Φ) {n : ℕ} {v : Fin n → (epsR R ⟶ G')} (hb : IsLieBasis v) :
    Nonempty (Module.Basis (Fin n) R (TanM x G)) := by
  let u : Fin n → TanM x G := fun j => mkT (pushHom h (epsR R) (v j)) ((PullbackSections.isTangent_iff h _).1 (hb.1 j))
  have hcomb : ∀ (a : Fin n → R) (w : epsR R ⟶ G'), IsLieComb a v w ↔
      pushHom h (epsR R) w = tv (∑ i, a i • u i) := fun a w => by
    rw [PullbackSections.isLieComb_iff h, GlobalTheory.FlagMod.tv_sum']
    rfl
  have hbij : Function.Bijective (Fintype.linearCombination R u) := by
    rw [Function.bijective_iff_existsUnique]
    intro W
    obtain ⟨p, hp⟩ := PullbackSections.push_surj h (tv W)
    have ht : IsTangent p := (PullbackSections.isTangent_iff h p).2 (by rw [hp]; exact tv_mem W)
    refine (existsUnique_congr fun a => ?_).1 (hb.2 p ht)
    rw [hcomb, hp, Fintype.linearCombination_apply]
    exact ⟨fun e => (tanM_ext e).symm, fun e => by rw [e]⟩
  exact ⟨(Pi.basisFun R (Fin n)).map (LinearEquiv.ofBijective _ hbij)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_keyAt_of_sabMap (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hg : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, th, ⟨hw, hr⟩, hth, hne⟩ :=
    GlobalTheory.exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  obtain ⟨m', hm'⟩ : ∃ m' : SABMap t Y.t (spMap (ev z M.U hz) ≫ M.hU.fromSpec), m'.φ = m.φ := by
    rw [GlobalTheory.FlagMod.spMap_ev z M.hU hz]
    exact ⟨m, rfl⟩
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec Y.t.G) m.base)
  have hrig : m.cm.rigPull Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ z he Y.t.PP.L Y.t.PP.rig := by
    have key : ∀ (a b : Sp R ⟶ Y.X) (_ : a = b) ha hb,
        rigPullOf (G' := t.G) m.φ a ha Y.t.PP.L Y.t.PP.rig = rigPullOf m.φ b hb Y.t.PP.L Y.t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  refine ⟨⟨GlobalTheory.GenericPol.toPolAV t M.n hg hp hA hK, hn, t.PP.rig, t.PP.rigGen, th, fun s => ?_, v, hb⟩, rfl,
    m.φ, he, w, rfl, m.cart, hw, hrig ▸ hr, fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, h₁, h₂⟩ := hne s
    exact ⟨g, h₁, Opens.mem_iSup.2 ⟨i, h₂⟩⟩
  · refine (hth (j PUnit.unit) i _ h le_rfl).trans ?_
    exact congrArg (· * _) (GlobalTheory.LB.resG_self _ _)
  · exact hm' ▸ hv i

theorem smoothOfRelativeDimension_fibre {K : Type} [Field K] {z : Sp K ⟶ Y.X} {t : SAB H (Sp K)} (m : SABMap t Y.t z)
    (h : Set.range z ⊆ Set.range Y.j) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t.G.hom := by
  obtain ⟨K', _, i, y, e⟩ := GlobalTheory.GenericPol.exists_lift z Y.j h
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull Out.CubePf.cubePull (Out.specOf i) t
  generalize (⟨(Over.pullback (Out.specOf i)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
    Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t' at m₁
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m₁
  obtain ⟨m', -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t t' Y.j y Y.m (e ▸ n)
  have h₁ : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m'.cart.1
      (GlobalTheory.ObjDim.smoothOfRelativeDimension Y.oF)
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace ↥t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (Classical.arbitrary _)
  have h₂ : SmoothOfRelativeDimension d t'.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback m₁.cart.1 hd
  rw [← H1.dim_unique _ h₂ h₁ (eSec t'.G (default : PrimeSpectrum K'))]
  exact hd

theorem exists_keyAt_model (M : GChart Y) {K : Type} [Field K] (z : Sp K ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    (h : Set.range z ⊆ Set.range Y.j) (hpos : 1 ≤ Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) :
    ∃ x : KeyIn K, x.P.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) ∧ KeyAt M z hz x := by
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull z Y.t
  generalize (⟨(Over.pullback z).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    Geo.Tor.OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩ : SAB H _) = t at m
  obtain ⟨hp, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv m h
  have hg := smoothOfRelativeDimension_fibre m h
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis t.G hg
  obtain ⟨b⟩ := nonempty_basis_of_isLieBasis m.cart hv
  have hn : Module.finrank ℚ E / 2 * (Dw.p + Dw.q) = M.n := by
    simpa using Fintype.card_congr (b.indexEquiv (GlobalTheory.FlagMod.lieBasis M.toMChart z hz))
  rw [hn] at hg hpos ⊢
  exact exists_keyAt_of_sabMap M z hz m hp hA hK hg hpos

theorem exists_keyAt : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (M : ct.KeyChart) (K : Type) [Field K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U), Set.range z ⊆ ct.Xm.opn → ∃ x : KeyIn K, x.P.g = D.R.f * N ∧ KeyAt M z hz x := by
  intro D A N j S κ p ct M K _ z hz h
  have hd : Module.finrank ℚ D.host.E / 2 * (S.Dw.p + S.Dw.q) = D.R.f * N := by
    rw [GlobalTheory.PinNum.finrank_host, S.rank_eq, Nat.mul_div_cancel_left _ two_pos]
  have hf : 1 ≤ D.R.f := by
    have h₁ : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [GlobalTheory.PinNum.finrank_host] at h₁
    omega
  have hN := S.two_le
  rw [← hd]
  exact exists_keyAt_model (Y := ct.base) M z hz (ct.range_base_j ▸ h)
    (hd ▸ Nat.mul_pos hf (by omega))

end GlobalTheory.KeyAtEx
