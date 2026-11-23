import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusRankEqRankThetaGroupOfPointPerpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupOfPointEqAlongModelHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryEndomorphismsTorsionExtendSemiAbelianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeUnitaryClassicalTraitCentreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIsoStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.Poinc.FibLat

namespace GlobalTheory.UPoinc.GFib

theorem TT_le_HH_of_uIsLab {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {cf : Coeff l} {C : UCompact Xo cf} (X : USetup C) {p : ℕ} [Fact p.Prime]
    {z : X.M.Z} (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (h : UIsLab X ct yy)
    (hker : yy.ker = X.S.HH X.M z) : X.S.TT X.M z ≤ X.S.HH X.M z := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, -, G, _, α, β, -, -, -, y₀, -, u, lb, j, -, hlab, -⟩ := h
  have hk : lb.yy.ker ≤ yy.ker := fun a ha => by
    have h0 : lb.yy a = QuotientAddGroup.mk 0 := by rw [AddMonoidHom.mem_ker.1 ha]; rfl
    have := hlab a 0 h0
    rw [map_zero] at this
    exact AddMonoidHom.mem_ker.2 this
  intro t ht
  rw [← hker]
  refine hk ?_
  have h1 : t ∈ (X.S.rechart c₀ hc R' fg frac hth hev).perp lb.yy.ker := fun h hh => ht h (hker ▸ hk hh)
  have h2 := lb.isoFree.1 h1
  rwa [ThetaSys.perp_perp] at h2

end GlobalTheory.UPoinc.GFib

theorem GlobalTheory.UPoinc.GFib.labelled_lattices_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X) (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ → X.S.IsEE Y U₀ EE → IsProper q → Y.pt ≫ q = X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → ∀ (ct ct' : UCTrait X p z) (y y' : Sp (OO p) ⟶ Y.Z), y ≫ q = ct.y → y' ≫ q = ct'.y → ∀ (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ θ : ct.T.P.D.toPre.X ≃+ ct'.T.P.D.toPre.X, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (θ μ)) ∧ ∀ (a : 𝓞 E) v, θ (a • v) = a • θ v := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p _ z hz ct ct' y y' hy hy' yy yy' hl hl'
  have hker := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct yy hl.uIsLab
  have hker' := GlobalTheory.T.unitaryTraitLabels_surjective_kernel E H Dw hpq l Xo cf C X p z ct' yy' hl'.uIsLab
  have hTH := GlobalTheory.UPoinc.GFib.TT_le_HH_of_uIsLab X ct yy hl.uIsLab hker.2
  obtain ⟨f, gγ, hf, hg⟩ := GlobalTheory.T.unitaryEndomorphisms_torsion_extend_semiAbelian E H Dw l Xo cf C X wi Y U₀ EE FinalForm q hO hE hpt z hTH
  have hL : 0 < X.S.r * X.S.N := Nat.mul_pos (by have := X.S.r_pos; omega) (by have := X.S.N_ge; omega)
  have hprim : IsPrimitiveRoot (X.S.ζ ^ (X.S.r * X.S.N)) (X.S.r * X.S.N) :=
    X.S.prim.pow (by positivity) (by ring)
  let ζ : X.o₁ˣ := (hprim.isUnit hL.ne').unit
  have hζ : IsPrimitiveRoot (ζ : X.o₁) (X.S.r * X.S.N) := hprim
  obtain ⟨s, σ, hs, hσ, hc⟩ :=
    GlobalTheory.T.characterLattice_unitaryClassicalTrait_centre E H Dw hpq l Xo cf C X wi Y U₀ EE FinalForm q hO hE hP hpt p z f gγ hf hg ζ hζ
  obtain ⟨c, hc1, hc2⟩ := hc ct y hy yy hl
  obtain ⟨c', hc1', hc2'⟩ := hc ct' y' hy' yy' hl'
  have hx : q.base (y (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy, ct.cen]
  have hx' : q.base (y' (cPt p)) = z := by
    rw [← Scheme.Hom.comp_apply, hy', ct'.cen]

  have hrk : ∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt FinalForm.G w r₀ := by
    obtain ⟨r₀, -, ⟨e₀⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE (y (cPt p))
    refine ⟨r₀, fun w hw => ?_⟩
    obtain ⟨r, hr, ⟨e⟩⟩ := GlobalTheory.T.torusRank_eq_rank_thetaGroupOfPoint_perp X.o₁ X.Ω₁ X.S X.ρ Y U₀ EE FinalForm X.big hO hE w
    have hT : X.S.TT Y w = X.S.TT Y (y (cPt p)) := by
      simp only [ThetaSys.TT]
      rw [GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv w,
        GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom X.o₁ X.Ω₁ X.S X.M Y q hpt X.hasDiv (y (cPt p))]
      simp only [hw, hx]
    have e₁ : (Fin r → ZMod (X.S.r * X.S.N)) ≃ (Fin r₀ → ZMod (X.S.r * X.S.N)) :=
      (e.symm.toEquiv.trans (Equiv.setCongr (congrArg (fun H : AddSubgroup X.S.Gam => (H : Set X.S.Gam)) hT))).trans
        e₀.toEquiv
    haveI : NeZero (X.S.r * X.S.N) := ⟨hL.ne'⟩
    have hcard := Fintype.card_congr e₁
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
    have h2 : 2 ≤ X.S.r * X.S.N := by
      have := X.S.r_pos; have := X.S.N_ge; nlinarith
    rwa [Nat.pow_right_injective h2 hcard] at hr
  have hmove := GlobalTheory.T.characterLatticeAtFibre_const_preconnected X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi _ q z hz hrk (𝓞 E) _ f (fun a => (hf a).1) gγ ζ
    (X.S.r * X.S.N) hL (Units.ext (by simpa using hζ.pow_eq_one)) X.S.unit (fun t => (hg t).1)
    (fun t w hw => (hg t).2.2 w hw) ct.T.P.D.toPre.X _ c _ _ hx hx' hc1
  haveI : IsDomain X.o₁ := (inferInstance : GlobalTheory.ZH.ArithBase X.o₁ X.Ω₁).ded.toIsDomain
  obtain ⟨θ, hθm, hθc⟩ := GlobalTheory.T.characterLatticeAtFibre_unique_up_to_iso X.o₁ X.Ω₁ Y FinalForm.G FinalForm.semi (𝓞 E) _ f gγ ζ (X.S.r * X.S.N) hL hζ
    X.S.unit ct.T.P.D.toPre.X ct'.T.P.D.toPre.X _ c _ c' _ hmove hc1'
  refine ⟨θ, fun a v hv => ?_, fun a v => ?_⟩
  · obtain ⟨a', ha'⟩ := hker'.1 (QuotientAddGroup.mk (θ v))
    have hd : a' - a ∈ X.S.HH X.M z := by
      rw [← ThetaSys.perp_TT]
      refine ThetaSys.mem_perp'.2 fun t ht => ?_
      have e1 := hc2' a' (θ v) ⟨t, ht⟩ ha'
      rw [hθc, hc2 a v ⟨t, ht⟩ hv] at e1
      have e2 := hs.mul_left_cancel e1
      rw [sub_eq_add_neg, eStd_add_right, eStd_neg_right, ← e2]
      exact add_neg_cancel _
    rw [← hker'.2, AddMonoidHom.mem_ker, map_sub, sub_eq_zero] at hd
    rw [← hd, ha']
  · obtain ⟨b, rfl⟩ := hσ a
    exact hθm b v
