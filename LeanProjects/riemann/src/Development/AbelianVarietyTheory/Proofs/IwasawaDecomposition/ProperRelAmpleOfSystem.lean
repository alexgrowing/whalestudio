import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeyInputAtChartPoint
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSecPullNonzeroOnFibres

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtFam

open GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem relAmple_iff_of_cls {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) : Out.RelAmple A M ↔ Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hL, relAmple_iff_isAmpleLB A hM]
  refine forall_congr' fun U => forall_congr' fun hU => ?_
  refine Iff.trans (isAmpleLB_congr (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)
    ((cls_eq_iff (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)).1 ?_)) (isAmpleLB_pow_iff (pull_isLB hL _) hd)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

section OneModel

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

theorem exists_keyAt (M : GChart Y) {R : Type} [CommRing R] {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hd : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, θ, ⟨hw, hr⟩, hθ, hne⟩ :=
    exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  have cast : ∀ (p q : Sp R ⟶ Y.X) (_ : p = q) (n : SABMap t Y.t p), ∃ n' : SABMap t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ _ (FlagMod.spMap_ev z M.hU hz).symm m
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp R) :=
    { A := t.G, g := M.n, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK
      isAb := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ _) m.base)
  have hrig : ∀ (e : Sp R ⟶ Y.X) (_ : m.cm.e = e) (he : eSec t.G ≫ m.φ = e ≫ eSec Y.t.G),
      rigPullOf m.φ e he Y.t.PP.L Y.t.PP.rig = m.cm.rigPull Y.t.PP.L Y.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨⟨P, hn, t.PP.rig, t.PP.rigGen, θ, fun s => ?_, v, hb⟩, rfl, m.φ, he, w, rfl, m.cart, hw, ?_,
    fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hne s
    exact ⟨g, hg, Opens.mem_iSup.2 ⟨i, hi⟩⟩
  · rw [hrig z m.base he]
    exact hr
  · exact (hθ (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))
  · rw [← hm']
    exact hv i

theorem exists_keyAt_of_point (M : GChart Y) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U) {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) {K : Type} [Field K] [CharZero K] (f : R →+* K) {x₀ : KeyIn K}
    (h₀ : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x₀) :
    ∃ x : KeyIn R, x.P.g = x₀.P.g ∧ KeyAt M z hz x := by
  obtain ⟨φ, -, w, hg, hc, hw, -⟩ := h₀
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : x₀.P.A.left ⟶ t.G.left, ψ ≫ m.φ = φ ∧ ψ ≫ t.G.hom = x₀.P.A.hom ≫ spMap f :=
    ⟨m.cart.1.lift φ (x₀.P.A.hom ≫ spMap f) (by rw [hc.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _,
      m.cart.1.lift_snd _ _ _⟩
  subst h₁
  have g : IsGrpPullback x₀.P.A t.G (spMap f) ψ := m.cart.cancel hc h₂
  have e : LBIso x₀.P.L (t.PP.L.pull ψ) :=
    LBIso.trans x₀.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB t.PP.isLB _) ⟨w, hw⟩
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl).symm
  have hG : IsAbelianScheme t.G := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
  have q : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hK⟩ := KTrivGlob.exists_open t.PP.isLB x₀.P.isLB hG hA g e x₀.P.ktriv q
  have : CharZero R := f.charZero
  have : CharZero Γ(Sp R, ⊤) := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have kt := KTrivSpread.kTriv_of_open_integral GlobalTheory.firstFiveLaws.1 (Sp R) (fun n hn => Nat.cast_ne_zero.2 hn) U
    ⟨_, hU⟩ t.G t.PP t.cub hG hA hK
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (spMap f q))
  obtain rfl : d = M.n := (H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g.1 hd)
    x₀.P.smoothDim (eSec x₀.P.A q)).trans hg
  obtain ⟨x, hx, h⟩ := exists_keyAt M hz m hp hA kt hd (hg ▸ x₀.g_pos)
  exact ⟨x, hx.trans hg.symm, h⟩

end OneModel

end GlobalTheory.KeyAtFam
