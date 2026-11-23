import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLawsOfSignature
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FieldTwistConditions

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT.AnyLev

theorem at_one (hP : GlobalTheory.CovTop.Hypotheses2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hg : ∀ q : ℕ, q.Prime → l.GoodAt q) (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0)
    (hC : GlobalTheory.CompRat.CurveOver H c.F l.M') (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H) :
    ∃ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0),
      ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal) := by
  have hF : FnAlgClosed Xo c := GlobalTheory.ShFam.GeomComp.fnAlgClosed_of_curveOver Xo c hpq h1 hC
  obtain ⟨U, hL⟩ := GlobalTheory.FlatCore.Model.exists_laws Dw l Xo c hpq hA hg hF h1
  obtain ⟨s⟩ := GlobalTheory.FlatCore.archEx_always E H Dw l Xo c _ U _ hL Zc τ
  refine ⟨s.sig, s.sig_mem, fun la => ?_⟩
  exact GlobalTheory.FlatCore.htConst_always hP hP.q2 hP.q3 hP.q4 E H Dw l Xo c _ U _ hL Zc τ s la

section Down

open GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem pullRule_mem_secZ (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) : pullRule d f ∈ secZ d.Xo₂ d.c₂ e := by
  refine ⟨fun p q φ u u' hm => ?_, fun p t u u' hb => ?_⟩
  · letI := algDn d p.R
    letI := algDn d q.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := q.R) (fun _ => rfl) u'
    let φc : p.R →ₐ[c.F] q.R := ⟨φ.toRingHom, fun a => φ.commutes (d.eF a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R q.R φc y
    have hw' : FrOver d u' w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hy hw hm
    obtain rfl : y' = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy' hw'
    show pullRule d f q u' = φ (pullRule d f p u)
    rw [pullRule_eq d f q u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc y
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R y) y' hw
  · letI := algDn d p.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u'
    show pullRule d f p u' = _ * pullRule d f p u
    rw [pullRule_eq d f p u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Xo c e hf p.R t y y' (frBor_down d hy hy' hb)

theorem evR_pullRule_nat (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hc : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k)
    (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ (pullRule d f) y₂ = evR Xo c f y := by
  have key : ∀ (p : TRing d.c₂.F) (φ : p.R →ₐ[d.c₂.F] k) (u : FrPt d.Xo₂ d.c₂ p.R), FrMap φ u y₂ →
      φ (pullRule d f p u) = evR Xo c f y := by
    intro p φ u hu
    letI := algDn d p.R
    obtain ⟨z, hz⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    let φc : p.R →ₐ[c.F] k := ⟨φ.toRingHom, fun a => (φ.commutes (d.eF a)).trans (hc a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R k φc z
    have hw' : FrOver d y₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hz hw hu
    obtain rfl : y = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy hw'
    rw [pullRule_eq d f p u z hz]
    exact (GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf φc z
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R z) y hw).symm
  have hT := GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂
  have e : evR d.Xo₂ d.c₂ (pullRule d f) y₂ =
      hT.choose_spec.choose (pullRule d f hT.choose hT.choose_spec.choose_spec.choose) := by
    unfold evR evalAt
    rw [dif_pos hT]
  rw [e]
  exact key _ _ _ hT.choose_spec.choose_spec.choose_spec

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [StarRing (𝓞 E)]

theorem pointOver_down {P : Point p v O (𝓞 E)} {V F : Type} [CommRing V] [Field F] [Algebra V F]
    {x₂ : Sp F ⟶ d.Xo₂.X} {x : Sp F ⟶ Xo.X} (e : x₂ ≫ d.r = x) {k : F →+* C} {kO : V →+* O}
    {ψ : P.A.A.left ⟶ d.Xo₂.univ.t.G.left} (h : PointOver P x₂ k kO ψ) : PointOver P x k kO (ψ ≫ d.m.φ) := by
  obtain ⟨h0, G, t', m₁, m₂, π, φ, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨m', e₁⟩ := LiftBaseChange.exists_comp' d.m m₁ x e.symm
  refine ⟨h0, G, t', m', m₂, π, φ, h1, h2, h3, h4, by rw [e₁, ← Category.assoc, h5], ?_⟩
  obtain ⟨w, hw, -⟩ := d.m.lin
  have i : LBIso (d.Xo₂.univ.t.PP.L.pull ψ) (Xo.univ.t.PP.L.pull (ψ ≫ d.m.φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ ψ ψ rfl)
      (chartPullSame Xo.univ.t.PP.L _ _ _ ψ fun _ => rfl) (⟨w, hw⟩ : LBIso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ))
  exact LBIso.trans P.A.isLB (LB.isLB_pull d.Xo₂.univ.t.PP.isLB _) (LB.isLB_pull Xo.univ.t.PP.isLB _) h6 i

variable [Algebra c.F C] [Algebra d.c₂.F C] [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem htLat_eq (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) (P : Point p v O (𝓞 E))
    (τ : E →+* ℂ) : htLat d.c₂ P τ = htLat c P τ := by
  have e : embAt d.c₂ C τ = embAt c C τ := RingHom.ext fun a => by
    unfold embAt
    rw [RingHom.comp_apply, RingHom.comp_apply, ← hc]
    exact congrArg _ (Subtype.ext rfl)
  unfold htLat embInt
  rw [e]

theorem isHTChange_down (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) {P : Point p v O (𝓞 E)}
    {ψ : P.A.A.left ⟶ d.Xo₂.univ.t.G.left} {z₂ y₂ : FrPt d.Xo₂ d.c₂ C} {z y : FrPt Xo c C} (hz : FrOver d z₂ z)
    (hy : FrOver d y₂ y) (h : IsHTChange P ψ z₂ y₂) : IsHTChange P (ψ ≫ d.m.φ) z y := by
  obtain ⟨t, hb, ht⟩ := h.exists_frBor
  obtain ⟨ex, -, pm, q₁, q₂, q₃⟩ := frBor_down d hz hy hb
  obtain ⟨g, a, x, ⟨h1, h2, -⟩, hg, -, hL, hB⟩ := h
  refine ⟨g, t none, x, ⟨ex, fun τ i => ?_, pm, q₁, ?_, q₃⟩, hg, ht, fun τ j => ?_, fun τ => ?_⟩
  · have := (GlobalTheory.FrameLift.comb_iff d.m hz.1 (fun j => (z₂.tan τ j).1) (g τ i) (h1 ▸ (y₂.tan τ i).1)).1 (h2 τ i)
    rw [funext (hz.2.1 τ), hy.2.1] at this
    exact this
  · rw [q₂, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact (Category.comp_id _).symm
  · obtain ⟨xG, u', k₁, k₂, k₃⟩ := hL τ j
    exact ⟨xG, u', k₁, by rw [← Category.assoc, k₂, hz.2.1], k₃⟩
  · rw [← htLat_eq d hc]
    exact hB τ

theorem isHTFrame_down (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂)
    (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) {T : CDVR} {io : c.F →+* T.Fr}
    {io₂ : d.c₂.F →+* T.Fr} {b₂ : IntFr d.Xo₂ d.c₂ T io₂} {b : IntFr Xo c T io}
    (hb : letI := io.toAlgebra; letI := io₂.toAlgebra; FrOver d b₂.1 b.1)
    {k₂ : letI := io₂.toAlgebra; T.Fr →ₐ[d.c₂.F] C} {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C}
    (hk : letI := io.toAlgebra; letI := io₂.toAlgebra; k₂.toRingHom = k.toRingHom) {y₂ : FrPt d.Xo₂ d.c₂ C}
    (h : IsHTFrame p v O b₂ k₂ y₂) : ∃ y : FrPt Xo c C, FrOver d y₂ y ∧ IsHTFrame p v O b k y := by
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨-, kO, P, ψ, z₂, h1, h2, h3⟩ := h
  obtain ⟨y, hy⟩ := below_exists d hO hK hc y₂
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c T.Fr C k b.1
  have hz' : FrOver d z₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := k) (ψ₂ := k₂) hk hb hz h2
  refine ⟨y, hy, GlobalTheory.TransferCompare.allTest_framed Xo c C y, kO, P, ψ ≫ d.m.φ, z, ?_, hz,
    isHTChange_down d hc hz' hy h3⟩
  rw [← hk]
  exact pointOver_down d hb.1 h1

end Down

section Transfer

open GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem liesOn_down (rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c)
    (e₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r)
    (e₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (d.eF : c.F →+* d.c₂.F))
    {Z₂ : Formalism.L2.Pj.Comp d.Xo₂ d.c₂} {Z : Formalism.L2.Pj.Comp Xo c} (hZ : rF '' (Z₂ : Set (d.Xo₂.XF d.c₂)) ⊆ (Z : Set (Xo.XF c)))
    {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) {y₂ : FrPt d.Xo₂ d.c₂ S} {y : FrPt Xo c S}
    (hy : FrOver d y₂ y) (h : LiesOn Z₂ y₂) : LiesOn Z y := by
  have e : ptF y = ptF y₂ ≫ rF := by
    apply pullback.hom_ext
    · rw [Category.assoc, e₁, ptF, ptF, pullback.lift_fst, pullback.lift_fst_assoc, hy.1]
    · rw [Category.assoc, e₂, ptF, ptF, pullback.lift_snd, pullback.lift_snd_assoc,
        ← LiftBaseChange.spMap_comp']
      exact congrArg spMap (RingHom.ext fun a => (hc a).symm)
  intro s
  rw [e]
  exact hZ ⟨_, h s, rfl⟩

theorem htValOn_down (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) (rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c)
    (e₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r)
    (e₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (d.eF : c.F →+* d.c₂.F))
    {Z₂ : Formalism.L2.Pj.Comp d.Xo₂ d.c₂} {Z : Formalism.L2.Pj.Comp Xo c} (hZ : rF '' (Z₂ : Set (d.Xo₂.XF d.c₂)) ⊆ (Z : Set (Xo.XF c)))
    {la₂ : HeightOneSpectrum (𝓞 d.c₂.F)} {la : HeightOneSpectrum (𝓞 c.F)} (hla : ∀ a : c.F, vLa la₂ (d.eF a) = vLa la a)
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) :
    ∀ w₂ ∈ htValOn Z₂ la₂, ∃ w ∈ htValOn Z la, w₂ (pullRule d f) = w f := by
  rintro _ ⟨T, io₂, e, b₂, ho, ⟨halg, hon⟩, p, hp, ha₂, k₂, y₂, hy₂, rfl⟩
  letI := io₂.toAlgebra
  let io : c.F →+* T.Fr := io₂.comp (d.eF : c.F →+* d.c₂.F)
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := algDn d ℂ_[p]
  obtain ⟨b, hb⟩ := below_exists d hO hK (S := T.Fr) (fun _ => rfl) b₂.1
  let bI : IntFr Xo c T io := ⟨b, GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr b,
    GlobalTheory.CoverDown.integral_below d T _ io₂ (fun _ => rfl) b b₂.1 hb b₂.2.2⟩
  let k : T.Fr →ₐ[c.F] ℂ_[p] := ⟨k₂.toRingHom, fun a => k₂.commutes (d.eF a)⟩
  letI := H.starRing
  obtain ⟨y, hy, hF⟩ := isHTFrame_down d hO hK (C := ℂ_[p]) (fun _ => rfl) (b := bI) (k := k) hb rfl hy₂
  refine ⟨_, ⟨T, io, e, bI, ⟨ho.1, fun a => (ho.2 (d.eF a)).trans (by rw [hla])⟩,
    ⟨halg, liesOn_down d rF e₁ e₂ hZ (fun _ => rfl) hb hon⟩, p, hp, inferInstance, k, y, hF, rfl⟩, ?_⟩
  show val_vw la₂ p _ _ = val_vw la p _ _
  rw [evR_pullRule_nat d hO hK hf (fun _ => rfl) y₂ y hy]
  have hp' : vLa la₂ (p : d.c₂.F) = vLa la (p : c.F) := by rw [← hla, map_natCast]
  unfold val_vw
  rw [hp']

end Transfer

theorem anyLev (hP : GlobalTheory.CovTop.Hypotheses2) : AnyLevSt := by
  intro E _ _ _ H Dw l Xo c hpq hg h1 hC Zc τ
  let l₀ : Level H := { l with A := 1, A_pos := Nat.one_pos }
  have hd : l₀.Dvd l := ⟨dvd_rfl, le_rfl, one_dvd _⟩
  have hM : l₀.M' ∣ l.M' := Nat.lcm_dvd (Nat.dvd_lcm_left _ _) (one_dvd _)
  have hK : KA l₀ ≤ KA l := GlobalTheory.Models.RankZero.KA_le_of_eq_one rfl l
  have hpos : 0 < l.M' := GlobalTheory.LevelExist.M'_pos l
  let c₀ : Coeff l₀ :=
    { F := c.F
      fin := c.fin
      conj := c.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd hpos hM
        rw [he]
        exact pow_mem c.zeta_mem e
      le := hK.trans c.le }
  have hC₀ : GlobalTheory.CompRat.CurveOver H c₀.F l₀.M' := by
    obtain ⟨k, hk⟩ := hM
    refine GlobalTheory.IndefiniteRowSideFullHecke.FieldTwistConditions.curveOver_of_mul (k := k) ?_ (hk ▸ hC)
    rintro rfl
    omega
  obtain ⟨Xo₀⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₀ hpq
  obtain ⟨r, jK, m, hj, hr, -, -, -, hcF⟩ := (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l₀ l Xo₀ Xo hd
  obtain ⟨rF, e₁, e₂, -⟩ := hcF c₀ c rfl
  let d : DeltaDat Xo₀ c₀ 0 := ⟨1, ⊤, l, Xo, c, rfl, r, m, fun _ _ _ _ => 0, 0, 0⟩
  have hO : GlobalTheory.ClsVal.Cmp.OverBase d := fun h => by
    rw [← GlobalTheory.ClsVal.Cmp.eq_incl h jK hj]
    exact hr
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (Zc.2.1.image rF rF.continuous.continuousOn)
  obtain ⟨f, hf, hρ⟩ := at_one hP E H Dw l₀ Xo₀ c₀ hpq rfl hg h1 hC₀ ⟨Z₀, hZ₀⟩ τ
  refine ⟨GlobalTheory.CovPull.pullRule d f, pullRule_mem_secZ d hO hK hf, fun la => ?_⟩
  obtain ⟨ρ, hρ⟩ := hρ la
  refine ⟨ρ, fun w hw => ?_⟩
  obtain ⟨w₀, hw₀, e⟩ := htValOn_down d hO hK rF e₁ e₂ (Z₂ := Zc) (Z := ⟨Z₀, hZ₀⟩) hZ (la₂ := la) (la := la)
    (fun _ => rfl) hf.1 w hw
  exact e.trans (hρ w₀ hw₀)

end GlobalTheory.DetHT.AnyLev

end
