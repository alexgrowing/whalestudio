import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusSpreadOverTraitSpecialisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSpreadLatticeMapCommutesEndomorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToricTorsionPointOfLatticeCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackSemiAbelianOverNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalNoetherianStalkFactorOfFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianEndExtendingAbelianSchemeEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricTorsionPointMemberHasLabelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.GSep.Spz
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem exists_eq_nsmul_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L : ℕ) (x : X)
    (h : ∀ c : X →+ ℤ, (L : ℤ) ∣ c x) : ∃ w, x = L • w := by
  let b := Module.Free.chooseBasis ℤ X
  choose w hw using fun k => h (b.coord k).toAddMonoidHom
  refine ⟨∑ k, w k • b k, ?_⟩
  rw [Finset.smul_sum, ← b.sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : b.repr x k = L * w k := hw k
  rw [this, mul_smul, natCast_zsmul]

theorem injective_of_ker_le {X Y : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y]
    [Module.Free ℤ Y] (ρ : X →+ Y) (L : ℕ) (hL : 2 ≤ L) (h : ∀ x, ρ x = 0 → ∃ w, x = L • w) : Function.Injective ρ := by
  refine (injective_iff_map_eq_zero ρ).2 fun x hx => ?_
  have key : ∀ k : ℕ, ∃ w, ρ w = 0 ∧ x = L ^ k • w := by
    intro k
    induction k with
    | zero => exact ⟨x, hx, by simp⟩
    | succ k ih =>
      obtain ⟨w, hw, rfl⟩ := ih
      obtain ⟨w', rfl⟩ := h w hw
      refine ⟨w', ?_, by rw [smul_smul, pow_succ]⟩
      rw [map_nsmul, ← natCast_zsmul] at hw
      exact (smul_eq_zero.1 hw).resolve_left (by omega)
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun k => ?_)
  obtain ⟨w, -, hw⟩ := key (b.repr x k).natAbs
  rw [map_zero, Finsupp.zero_apply]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((L ^ (b.repr x k).natAbs : ℕ) : ℤ)) ⟨b.repr w k, ?_⟩ ?_
  · conv_lhs => rw [hw]
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self (by omega)

theorem isPrimitiveRoot_map_of_isUnit_order {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K] (φ : o →+* K)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem intCast_eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) {a : ℤ}
    {b : ZMod m} (h : z ^ a = z ^ (b.val : ℤ)) : (a : ZMod m) = b := by
  have hz0 : z ≠ 0 := hz.ne_zero (NeZero.ne m)
  have h1 : z ^ (a - (b.val : ℤ)) = 1 := by rw [zpow_sub₀ hz0, h, div_self (zpow_ne_zero _ hz0)]
  have h2 := (hz.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ((a - (b.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  exact h3

variable {I : Type} {X₁ : GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {t : X → V} {δ : I → X → X}

theorem torAt_char_eq_weil (𝔪 : GMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ)
    (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A)
    (hT : TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V)
      (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x)
    (hxo : x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
      (X₁.ρ.pt τ).left) (a : X₁.S.Gam) (mu : X) (hY : 𝔪.YY a mu) :
    ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = eStd X₁.S.g _ τ a := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  obtain ⟨τ', q, hτv, hqy, hqt, hqx⟩ := hT
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  have W₁ := weilQkIs_tor hG q p' hqy hqt
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk q p' x x' hqx hp'x (τ' (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    x x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [hτv] at e'
    haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
    haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨by omega⟩
    have hzp := isPrimitiveRoot_map_of_isUnit_order ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R))) (by omega) hζ X₁.S.unit
    refine intCast_eq_of_zpow_eq hzp ?_
    rw [zpow_natCast]
    simp only [RingHom.coe_comp, Function.comp_apply, map_pow] at e' ⊢
    exact e'
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [hh, hxo]
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

variable {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} {U₀ : Y.Z.Opens} {EE : Y.Lat X₁.S.J} (FinalForm : ZHOut X₁.ρ Y U₀ EE)
  (𝔫 : GMem X₁ z₁ act V ev X t δ) {ξ : Sp V ⟶ Y.Z}

include 𝔫 in

theorem base_of_gMem : GlobalTheory.Mum.Base V :=
  ⟨⟨𝔫.cn.1, inferInstance, 𝔫.cn.2.1, 𝔫.cn.2.2.1⟩, 𝔫.cn.2.2.2⟩

theorem exists_link (hO : X₁.S.Over₀ Y U₀) (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ β : 𝔫.G.left ⟶ FinalForm.G.left, IsGrpPullback 𝔫.G FinalForm.G ξ β ∧
      Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β) ∧
      ∀ (f : X₁.ρ.P.A ⟶ X₁.ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ E : EndU 𝔫.U.toUnifPre,
        E.aA.left ≫ 𝔫.φ = 𝔫.φ ≫ f.left → E.aG.left ≫ β = β ≫ Fm.left := by
  have e : (jK V ≫ ξ) ≫ πY = jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by rw [Category.assoc, hξ]
  have hreg : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (πY ((jK V ≫ ξ) (closedPoint (FractionRing V)))) := fun a ha => by
    have := 𝔫.reg a ha
    rw [← e] at this
    exact this
  obtain ⟨O, _, _, _, _, _, _, xO, u, v, h₁, h₂, h₃, h₄⟩ := exists_stalk_factor X₁.o₁ X₁.Ω₁ Y hO.normal X₁.S.R
    (FractionRing V) (jK V ≫ ξ) 𝔫.yK (fun a ha => hπ.map_mem_O (hreg a ha)) (fun a => by
      rw [𝔫.yK_eq, ← e]
      exact hπ.val_comp _ _ (hreg a a.2))
  obtain ⟨gm, hgm⟩ := link_of_normal X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne O xO u h₁ h₂
  have e₂ : spMap v ≫ spMap u = spMap 𝔫.yK := (GlobalTheory.SpreadTrait.spMap_comp' u v).trans (congrArg spMap h₄)
  obtain ⟨w, hw, hwφ⟩ := GlobalTheory.SpreadTrait.pull_cancel (isGrpPullback_pullback X₁.ρ.P.A (spMap u)) (spMap v)
    (𝔫.cart.congr e₂.symm rfl)
  have hl := hgm.pull FinalForm hw
  rw [h₃, e₂, hwφ] at hl
  obtain ⟨β, hβ, hβg, hE⟩ := exists_ext Y.Z FinalForm.G FinalForm.semi V (base_of_gMem 𝔫) 𝔫.G 𝔫.semi 𝔫.D 𝔫.A 𝔫.U ξ _ hl.1
  refine ⟨β, hβ, hβg ▸ hl, fun f Fm hf E h => hE E Fm ?_⟩
  have := hl.2.1 f Fm hf _ (𝟙 _) E.aA.left ((Over.w E.aA).trans (Category.id_comp _).symm)
    (h.trans (Category.id_comp _).symm)
  exact this.trans (Category.id_comp _)

theorem yK_algebraMap (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ oV : X₁.o₁ →+* V, ξ ≫ Y.s = spMap oV ∧
      ∀ a, 𝔫.yK (algebraMap X₁.o₁ X₁.S.R a) = algebraMap V (FractionRing V) (oV a) := by
  have h : ξ ≫ Y.s = spMap (Spec.preimage (ξ ≫ Y.s)).hom := (Spec.map_preimage _).symm
  refine ⟨_, h, fun a => ?_⟩
  rw [𝔫.yK_eq, ← hξ]
  refine RatModel.val_algebraMap (σ := (algebraMap V (FractionRing V)).comp (Spec.preimage (ξ ≫ Y.s)).hom) ?_ a
  rw [Category.assoc, Category.assoc, hπ.inducedModelMorphism_comp_structureMap]
  exact (congrArg (jK V ≫ ·) h).trans (GlobalTheory.SpreadTrait.spMap_comp' _ _)

theorem pow_eq_one_of_qkToAkU {K : Type} [Field K] [Algebra (FractionRing V) K] {k : ℕ} {q : QkPt 𝔫.D.toPre K k}
    {x : TFK (R := V) K ⟶ 𝔫.A.A} (h : QkToAkU 𝔫.U.toUnifPre K k q x) : x ^ k = 1 := by
  obtain ⟨w, hw⟩ := 𝔫.U.ext
  exact (h w hw).1

theorem pt_eq_sec {β : 𝔫.G.left ⟶ FinalForm.G.left}
    (hl : Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β)) {a : X₁.S.Gam} {Wo : Y.Z.Opens}
    {h : Wo.toScheme ⟶ FinalForm.G.left} (hs : SecOn FinalForm a Wo h) {ξ' : Sp V ⟶ Wo.toScheme} (hξ' : ξ' ≫ Wo.ι = ξ)
    (K : Type) [Field K] [Algebra (FractionRing V) K] (x : TFK (R := V) K ⟶ 𝔫.A.A)
    (hx : x.left ≫ 𝔫.φ = spMap ((algebraMap (FractionRing V) K).comp 𝔫.yK) ≫ (X₁.ρ.pt a).left) :
    x.left ≫ genMap 𝔫.U ≫ β = spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ' ≫ h := by
  have e : x.left ≫ 𝔫.A.A.hom = spMap (algebraMap (FractionRing V) K) := Over.w x
  have := hl.2.2 a Wo h hs _ x.left (spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ') (by
    rw [reassoc_of% e]
    simp only [Category.assoc, hξ']) (by
    rw [reassoc_of% e, hx, ← GlobalTheory.SpreadTrait.spMap_comp', Category.assoc])
  simpa only [Category.assoc] using this

end GlobalTheory.GSep.Spz

theorem GlobalTheory.GSep.Spz.latTo_of_specializes : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), GlobalTheory.GSep.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (t₁ : X₀ → V₁) (δ₁ : I → X₀ → X₀) (𝔫₁ : GlobalTheory.GSep.GMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (t₂ : X → V₂) (δ₂ : I → X → X) (𝔫₂ : GlobalTheory.GSep.GMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → GlobalTheory.GSep.GMem.LatTo 𝔫₁ 𝔫₂ := by
  intro I X₁ z₁ act hact Y πY hZ V₁ _ _ _ _ ev₁ X₀ _ t₁ δ₁ 𝔫₁ ξ₁ V₂ _ _ _ _ ev₂ X _ t₂ δ₂ 𝔫₂ ξ₂ hξ₁ hξ₂ hsp
  obtain ⟨U₀, EE, ⟨FinalForm⟩, hO, -, hπ, -⟩ := hZ
  obtain ⟨β₁, hβ₁, hl₁, hE₁⟩ := GlobalTheory.GSep.Spz.exists_link FinalForm 𝔫₁ hO hπ hξ₁
  obtain ⟨β₂, hβ₂, hl₂, hE₂⟩ := GlobalTheory.GSep.Spz.exists_link FinalForm 𝔫₂ hO hπ hξ₂
  obtain ⟨o₁, ho₁, hy₁⟩ := GlobalTheory.GSep.Spz.yK_algebraMap 𝔫₁ hπ hξ₁
  obtain ⟨o₂, ho₂, hy₂⟩ := GlobalTheory.GSep.Spz.yK_algebraMap 𝔫₂ hπ hξ₂
  have b₁ := GlobalTheory.GSep.Spz.base_of_gMem 𝔫₁
  have b₂ := GlobalTheory.GSep.Spz.base_of_gMem 𝔫₂
  obtain ⟨ρ, hρ⟩ := exists_spread₂ Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ inferInstance (by
      haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
      haveI := Y.lft
      exact LocallyOfFiniteType.isLocallyNoetherian Y.s) hsp
  have onto := spread₂_surjective Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have eqv := spread₂_endU_comm Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have tor := GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ X₁.o₁ Y.s o₁ o₂ ho₁ ho₂
  obtain ⟨tot₁, sur₁, cong₁, -⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁ 𝔫₁
  obtain ⟨tot₂, sur₂, cong₂, -⟩ := GlobalTheory.T.thetaLabels_surjective_hom_lattice_mod_level I X₁ z₁ act V₂ ev₂ X t₂ δ₂ 𝔫₂
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have int₁ := GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hx₀ V₁ ev₁ X₀ t₁ δ₁ 𝔫₁
  have int₂ := GlobalTheory.T.mem_dividingLabels_iff_class_zero I X₁ z₁ act x₀ hx₀ V₂ ev₂ X t₂ δ₂ 𝔫₂
  have hL : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hζ : (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (X₁.S.r * X₁.S.N) = 1 := by
    rw [← pow_mul, ← sq]; exact X₁.S.prim.pow_eq_one

  have hy : πY (ξ₂ (closedPoint V₂)) = z₁ := by
    haveI := 𝔫₂.loc
    have : (ξ₂ ≫ πY) (closedPoint V₂) = z₁ := by
      rw [hξ₂]
      exact (congrArg (X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.comap_closedPoint ev₂)).trans
        Scheme.fromSpecStalk_closedPoint
    exact this
  have hHH : X₁.S.HH X₁.M z₁ ≤ X₁.S.HH Y (ξ₂ (closedPoint V₂)) :=
    AddSubgroup.closure_mono fun a ha => hπ.div (t := X₁.S.th) (hy.symm ▸ ha)

  have lab : ∀ a mu₁ mu₂, 𝔫₁.YY a mu₁ → 𝔫₂.YY a mu₂ →
      ∃ w, 𝔫₁.e₈ mu₁ - ρ (𝔫₂.e₈ mu₂) = (X₁.S.r * X₁.S.N) • w := by
    intro a mu₁ mu₂ h₁ h₂
    refine GlobalTheory.GSep.Spz.exists_eq_nsmul_of_forall_dvd _ _ fun c => ?_
    obtain ⟨x₁, hx₁⟩ := exists_torAt V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U (AlgebraicClosure (FractionRing V₁))
      (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V₁) _ (algebraMap V₁ _ (o₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) (by omega)
      (by rw [← map_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, map_one]) c
    obtain ⟨τ', q, hτ', hq, hq', hQ⟩ := id hx₁
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.geometricTorsionPoint_member_has_label I X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁ 𝔫₁ x₁ (GlobalTheory.GSep.Spz.pow_eq_one_of_qkToAkU 𝔫₁ hQ)
    have hH : τ ∈ X₁.S.HH X₁.M z₁ := (int₁ τ).2 ⟨q, x₁, hq.trans (map_zero _).symm, hQ, hτ⟩
    obtain ⟨Wo, h, hW, hs⟩ := FinalForm.sec _ τ (hHH hH)
    have lift : ∀ {V : Type} [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ Y.Z), ξ (closedPoint V) ∈ Wo →
        ∃ ξ' : Sp V ⟶ Wo.toScheme, ξ' ≫ Wo.ι = ξ := fun ξ hξ =>
      ⟨IsOpenImmersion.lift Wo.ι ξ (by
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ((IsLocalRing.specializes_closedPoint w).map ξ.continuous).mem_open Wo.isOpen hξ),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨ξ₁', hξ₁'⟩ := lift ξ₁ (hsp.mem_open Wo.isOpen hW)
    obtain ⟨ξ₂', hξ₂'⟩ := lift ξ₂ hW
    obtain ⟨-, q₂, x₂, -, hQ₂, hx₂'⟩ := tot₂ τ
    have hx₂ := GlobalTheory.GSep.Spz.pow_eq_one_of_qkToAkU 𝔫₂ hQ₂
    have ht := tor _ _ (by omega) X₁.S.unit hζ Wo h ξ₁' ξ₂' hs.1 hξ₁' hξ₂' _ _ c x₁ x₂ hx₁
      (GlobalTheory.GSep.Spz.pt_eq_sec FinalForm 𝔫₁ hl₁ hs hξ₁' _ x₁ hτ) hx₂ (GlobalTheory.GSep.Spz.pt_eq_sec FinalForm 𝔫₂ hl₂ hs hξ₂' _ x₂ hx₂')
    rw [← hy₁] at hx₁
    rw [← hy₂] at ht
    have w₁ := GlobalTheory.GSep.Spz.torAt_char_eq_weil 𝔫₁ τ c x₁ hx₁ hτ a mu₁ h₁
    have w₂ := GlobalTheory.GSep.Spz.torAt_char_eq_weil 𝔫₂ τ _ x₂ ht hx₂' a mu₂ h₂
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, map_sub, Int.cast_sub, w₁, sub_eq_zero]
    exact w₂.symm
  have inj : Function.Injective ρ := by
    refine GlobalTheory.GSep.Spz.injective_of_ker_le ρ _ hL fun y hy0 => ?_
    obtain ⟨mu, rfl⟩ := 𝔫₂.e₈.surjective y
    obtain ⟨a, ha⟩ := sur₂ mu
    obtain ⟨mu₁, h₁⟩ := tot₁ a
    obtain ⟨w, hw⟩ := lab a mu₁ mu h₁ ha
    have h0 : 𝔫₁.YY a 0 := (cong₁ a mu₁ 0 h₁).2 ⟨-𝔫₁.e₈.symm w, 𝔫₁.e₈.injective (by
      rw [hy0, sub_zero] at hw
      simp [hw])⟩
    obtain ⟨w', hw'⟩ := (cong₂ a 0 mu ((int₂ a).1 ((int₁ a).2 h0))).1 ha
    exact ⟨𝔫₂.e₈ w', by rw [← map_nsmul, hw', zero_add]⟩
  let e := AddEquiv.ofBijective ρ ⟨inj, onto⟩
  let K : X₀ ≃+ X := (𝔫₁.e₈.trans e.symm).trans 𝔫₂.e₈.symm
  have hK : ∀ mu, ρ (𝔫₂.e₈ (K mu)) = 𝔫₁.e₈ mu := fun mu => by
    simp only [K, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    exact e.apply_symm_apply _
  refine ⟨K, fun a mu => ?_, fun a mu h₁ => ?_⟩
  · obtain ⟨E₁, h₁, h₁'⟩ := 𝔫₁.equiv a
    obtain ⟨E₂, h₂, h₂'⟩ := 𝔫₂.equiv a
    obtain ⟨Fm, hF⟩ := endOn_exists X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne _ (hact a)
    apply 𝔫₂.e₈.injective
    apply inj
    rw [hK, ← h₂', eqv Fm E₁ E₂ (hE₁ _ Fm hF E₁ h₁) (hE₂ _ Fm hF E₂ h₂), hK, h₁']
  · obtain ⟨mu₂, h₂⟩ := tot₂ a
    obtain ⟨w, hw⟩ := lab a mu mu₂ h₁ h₂
    obtain ⟨w', rfl⟩ := onto w
    refine (cong₂ a mu₂ _ h₂).2 ⟨𝔫₂.e₈.symm w', 𝔫₂.e₈.injective (inj ?_)⟩
    rw [hK, map_add, map_add, map_nsmul, map_nsmul, AddEquiv.apply_symm_apply, ← hw, add_sub_cancel]
