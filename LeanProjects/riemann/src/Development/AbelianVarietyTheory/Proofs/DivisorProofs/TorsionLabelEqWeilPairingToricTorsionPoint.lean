import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteLocalBaseAtClosedPointGroupImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

namespace GlobalTheory.Poinc.UTestLabel

theorem char_eq_weil_of_label : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  intro o Ω _ _ _ S ρ
  refine ⟨1, ?_⟩
  intro p _ y₀ u l τ' b hτ hb a β hβ
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ S.r * S.N :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  haveI : CharZero u.V := CharZero.mk (fun m n hmn => by
    have e0 := congrArg ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))) hmn
    simpa only [map_natCast, Nat.cast_inj] using e0)
  obtain ⟨f, hf1, -, -, -, hfW⟩ := GlobalTheory.ZH.uTors_closed u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨pk, x, hpkx, hxo⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest o Ω S ρ p y₀ u a
  obtain ⟨q, hqy, hqt⟩ := exists_qkPt_tor u.D.tau_bimult τ' hτ
  have hqx : QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (f q) := (hf1 q (f q)).2 rfl
  have hqo := hb q (f q) hqy hqt hqx
  have hpk : x = f pk := (hf1 pk x).1 hpkx
  have W₁ := weilQkIs_tor hG q pk hqy hqt
  have W₂ := (hfW q pk (τ' (Multiplicative.ofAdd pk.y))).1 W₁
  have := ρ.P.isAb.comm
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    have e1 : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK =
        spMap ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp u.yK) := (spMap_comp _ _).symm
    rw [e1, u.fac]
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) :=
    S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h
    (ρ.weil b a (c₀ ^ (eStd S.g _ b a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (f q) (f pk) (h ≫ ρ.pt b) (h ≫ ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB W₂ W₃)
    have e' := congrArg Units.val e
    simp only [MonoidHom.coe_coe, Units.coe_map, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec,
      RingHom.toMonoidHom_eq_coe] at e'
    have hq : (QuotientAddGroup.mk β : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk pk.y := hβ.symm.trans (l.yy_eq a pk x hpkx hxo)
    obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.1 (QuotientAddGroup.eq.1 hq)
    have hpy : pk.y = β + (S.r * S.N) • m := by
      rw [nsmulAddMonoidHom_apply] at hm
      rw [hm]; abel
    have hτm : τ' (Multiplicative.ofAdd ((S.r * S.N) • m)) = 1 := by
      rw [ofAdd_nsmul, map_pow, ← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    rw [hpy, ofAdd_add, map_mul, hτm, _root_.mul_one] at e'
    rw [e', Units.val_one, one_smul, ← map_pow, ← pow_mul]
  · show h.left ≫ (ρ.pt b).left = _
    rw [hh, hqo]
  · show h.left ≫ (ρ.pt a).left = _
    rw [hh, ← hxo, hpk]

end GlobalTheory.Poinc.UTestLabel
