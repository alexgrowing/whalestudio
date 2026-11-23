import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulOfValLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFrameOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JKCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbFractionRingOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupIClosedPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPerpKerEquivHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrCentre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureEqKerOfMeetsTorsionCosets
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsValuationClosure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaDvr.TorRank

section Least
open GlobalTheory.UT

theorem closure_least_val : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (yK : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left), IsGrpPullback A.A ρ.P.A (spMap yK) φ → LBIso A.L (ρ.P.L.pull φ) → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), IsSemiAbelian G → (∀ a : o, yK (algebraMap o S.R a) ∈ (algebraMap V (FractionRing V)).range) → ∀ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A), QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x → x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → AddSubgroup.closure {a | yK ⟨S.th a, S.th_mem a⟩ ≠ 0 ∧ ∀ b, ∃ v : V, yK ⟨S.th b, S.th_mem b⟩ = algebraMap V (FractionRing V) v * yK ⟨S.th a, S.th_mem a⟩} = yy.ker := by
  intro o Ω _ _ _ _ S ρ V _ _ _ _ hc yK A φ hcart hlb G _ _ D U hG hy yy hyy hyq
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  obtain ⟨s, hs, hcos⟩ := GlobalTheory.ThetaDvr.Scale.exists_scale hL hL₂ o Ω S ρ V hc yK A φ hcart hlb G D U hG hy yy hyy hyq ϖ hϖ v hv
  haveI : CharZero (FractionRing V) := charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.ThetaGeneric.exists_th_ne_zero hL hL₂ o Ω S ρ (FractionRing V) yK
  set iK := algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) with hiK
  have hiKinj : Function.Injective iK := iK.injective
  have inj := IsFractionRing.injective V (FractionRing V)
  have hs₀ : s ≠ ⊤ := fun h => by
    have := (hs a₀).1
    rw [h, top_le_iff, AddValuation.top_iff] at this
    exact ha₀ (hiKinj (this.trans (map_zero iK).symm))
  have ne0 : ∀ a, v (iK (yK ⟨S.th a, S.th_mem a⟩)) = s → yK ⟨S.th a, S.th_mem a⟩ ≠ 0 := fun a ha h0 => by
    rw [h0, map_zero, AddValuation.map_zero] at ha
    exact hs₀ ha.symm
  have min : ∀ a, v (iK (yK ⟨S.th a, S.th_mem a⟩)) = s → ∀ b, ∃ w : V,
      yK ⟨S.th b, S.th_mem b⟩ = algebraMap V (FractionRing V) w * yK ⟨S.th a, S.th_mem a⟩ := fun a ha b =>
    (exists_mul_of_val_le hϖ hv (ne0 a ha) (ha.symm ▸ (hs b).1)).imp fun _ h => h.1
  obtain ⟨j, hj, hr⟩ := ρ.r_eq
  have hM : S.r * S.N = ρ.n ^ (j + ρ.k * 2) := by rw [hr, ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + ρ.k * 2 := by have := ρ.two_le; omega
  have hnd : ρ.n ∣ S.r * S.N := by rw [hM]; exact dvd_pow_self _ (by omega)
  refine GlobalTheory.closure_eq_ker_of_meets_torsion_cosets _ _ ρ.n _ _ ρ.n_prime.ne_zero hJ hM yy hyy _ ?_ fun a ha => ?_
  · rintro a ⟨h0, hb⟩
    by_contra hne
    obtain ⟨c, hc0, -, hcs⟩ := hcos ρ.n ρ.n_prime.two_le hnd 0 (map_zero yy)
    have hlt : v (iK (yK ⟨S.th c, S.th_mem c⟩)) < v (iK (yK ⟨S.th a, S.th_mem a⟩)) := hcs ▸ (hs a).2 hne h0
    obtain ⟨w, hw, hwm⟩ := exists_mul_of_val_le hϖ hv (ne0 c hcs) hlt.le
    obtain ⟨w', hw'⟩ := hb c
    have e : yK ⟨S.th a, S.th_mem a⟩ * (algebraMap V (FractionRing V) (w * w') - 1) = 0 := by
      rw [map_mul]; linear_combination -hw - (algebraMap V (FractionRing V) w) * hw'
    have e' : w * w' = 1 := by
      have := (mul_eq_zero.1 e).resolve_left h0
      exact inj (by rw [map_one]; exact sub_eq_zero.1 this)
    exact (IsLocalRing.mem_maximalIdeal _).1 (hwm hlt) (IsUnit.of_mul_eq_one w' e')
  · obtain ⟨a', ha', hn, hs'⟩ := hcos ρ.n ρ.n_prime.two_le hnd a ha
    refine ⟨a' - a, hn, ?_⟩
    rw [add_sub_cancel]
    exact ⟨ne0 a' hs', min a' hs'⟩

end Least

theorem labelMap : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (yK : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left), IsGrpPullback A.A ρ.P.A (spMap yK) φ → LBIso A.L (ρ.P.L.pull φ) → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A), QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x → x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro o Ω _ _ _ _ S ρ V _ _ _ _ hV yK A φ cart _ G _ _ D U
  have L := GlobalTheory.allSixLaws.1
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := uTors_closed V hV A G D U (AlgebraicClosure (FractionRing V)) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := LabelMap.exists_lift_points cart (TFK (R := V) (AlgebraicClosure (FractionRing V))) ρ.pt ρ.pt_add
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := D.tau_bimult
  have wd : ∀ q q' : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range) = QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := LabelMap.pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (TorusExt.qkAdd hB (P a) (P b)) (by
      rw [hadd _ _ _ (TorusExt.qkAdd_qkAdd hB _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := AlgebraicClosure (FractionRing V)) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

theorem isoFree_perp : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (yK : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left), IsGrpPullback A.A ρ.P.A (spMap yK) φ → LBIso A.L (ρ.P.L.pull φ) → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A), QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x → x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK) ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) := by
  intro o Ω _ _ _ hA S ρ V _ _ _ _ hV yK A φ cart lb G _ _ D U yy hs hyy
  have hL := GlobalTheory.allSixLaws.1
  have hG := hL.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have := ρ.P.isAb.comm
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := uTors_closed V hV A G D U (AlgebraicClosure (FractionRing V)) (S.r * S.N) hn.pos
  set y₀ : S.R →+* AlgebraicClosure (FractionRing V) := (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp yK with hy₀
  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (AlgebraicClosure (FractionRing V))ˣ := Units.map y₀.toMonoidHom c₀
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : AlgebraicClosure (FractionRing V)) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact (hζ.isRoot_cyclotomic hn.pos).map
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK = spMap y₀ :=
    (Spec.map_comp (CommRingCat.ofHom yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := TorusPerp.ptHom cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
  have hΦ : Function.Bijective Φ := TorusPerp.ptHom_bijective _ _
  have lab : ∀ a q, Φ (f q) = h ≫ ρ.pt a → yy a = QuotientAddGroup.mk q.y := fun a q e =>
    hyy a q _ ((f₁ _ _).2 rfl) ((congrArg (fun z => z.left) e).trans (by rw [← hh]; rfl))
  let pt : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) := MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun _ _ => ρ.pt_add _ _
  have onto : ∀ b, ∃ q, Φ (f q) = h ≫ ρ.pt b := fun b => by
    obtain ⟨x, hx⟩ := hΦ.2 (h ≫ ρ.pt b)
    obtain ⟨q, rfl⟩ := f₂ x (hΦ.1 (by
      have e : ρ.pt b ^ (S.r * S.N) = 1 := by
        refine (map_pow pt (Multiplicative.ofAdd b) _).symm.trans ?_
        rw [← ofAdd_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul, ofAdd_zero, map_one]
      rw [map_pow, hx, map_one, ← MonObj.comp_pow, e, MonObj.comp_one]))
    exact ⟨q, hx⟩
  have weil : ∀ a b q q', Φ (f q) = h ≫ ρ.pt a → Φ (f q') = h ≫ ρ.pt b →
      WeilIs A.A A.L (S.r * S.N : ℕ) (f q) (f q') (unitOn (ω ^ (eStd S.g _ a b).val)) := fun a b q q' e e' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil a b (c₀ ^ (eStd S.g _ a b).val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← e, ← e'] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB A.isLB cart lb _ _ _ _
      (Φ (f q)) (Φ (f q')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← TorusPerp.map_unitOn, ← hh]
  refine (TorusPerp.isoFree_perp_ker S yy hs fun l => ?_).1
  let χ := AddChar.zmodChar (S.r * S.N) hω.pow_eq_one
  let τ : Multiplicative D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ := χ.toMonoidHom.comp l.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (l α).val := fun _ => rfl
  obtain ⟨q, hq, hqτ⟩ := TorusPerp.exists_qkPt_tor (F := AlgebraicClosure (FractionRing V)) (k := S.r * S.N) D.tau_bimult τ (MonoidHom.ext fun α => by
    show (ω ^ (l α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow])
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (AlgebraicClosure (FractionRing V)) _ (Φ (f q)) (by rw [← map_pow, hq1, map_one])
  refine ⟨a, (lab a q ha.symm).trans (by rw [hq]; rfl), fun b α e => ?_⟩
  obtain ⟨q', hq'⟩ := onto b
  have e₁ := TorusPerp.unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG A.isAb A.isLB (weil a b q q' ha.symm hq')
    ((f₅ q q' _).1 (TorusPerp.weilQkIs_tor hG q q' hq hqτ)))
  rw [hτ] at e₁
  rw [ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)]
  obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 ((lab b q' hq').symm.trans e)
  have hz' : (S.r * S.N) • z = -q'.y + α := hz
  have := congrArg l hz'
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_add, map_neg] at this
  exact neg_add_eq_zero.1 this.symm

theorem leastValuation_labels : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE), S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∀ [IsCommMonObj ((Over.pullback ξ).obj Zh.G)] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (IsLocalRing.maximalIdeal V) D A ((Over.pullback ξ).obj Zh.G)), LBIso U.LG.L (Zh.L.L.pull (pullback.fst Zh.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Zh.G)) → ∀ (emb : Ω →+* FractionRing V), (∀ (W : M.Z.Opens) (f : Γ(M.Z, W)), ξ (IsLocalRing.closedPoint V) ∈ W → emb (valF M.pt W f) = algebraMap V (FractionRing V) (valR ξ W f)) → ∃ yy : S.Gam →+ D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : D.toPre.X →+ D.toPre.X).range, Function.Surjective yy ∧ S.IsoFree (S.perp yy.ker) ∧ AddSubgroup.closure {a | S.th a ≠ 0 ∧ ∀ b, ∃ v : V, emb (S.th b) = algebraMap V (FractionRing V) v * emb (S.th a)} = yy.ker := by
  have geo := @GlobalTheory.GenFibre.genFibre
  have clos := closure_least_val
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh _ hO _ V _ _ _ _ hV ξ hξ _ D A U hLB _ emb hemb
  obtain ⟨φ, cart, lb⟩ := geo o Ω S ρ M U₀ EE Zh hO V ξ hξ D A U hLB emb hemb
  have semi : IsSemiAbelian ((Over.pullback ξ).obj Zh.G) := IsSemiAbelian.pullback ξ Zh.G Zh.semi
  have hy : ∀ a : o, (emb.comp (algebraMap S.R Ω)) (algebraMap o S.R a) ∈ (algebraMap V (FractionRing V)).range :=
    fun a => ⟨valR ξ ⊤ (constFn M.s ⊤ a), by
      rw [← hemb ⊤ _ trivial, M.valF_constFn (U := ⊤) ⟨ξ (IsLocalRing.closedPoint V), trivial⟩ a]; rfl⟩
  obtain ⟨yy, hs, he⟩ := labelMap o Ω S ρ V hV (emb.comp (algebraMap S.R Ω)) A φ cart lb _ D U
  refine ⟨yy, hs, isoFree_perp o Ω S ρ V hV _ A φ cart lb _ D U yy hs he, ?_⟩
  rw [← clos o Ω S ρ V hV _ A φ cart lb _ D U semi hy yy hs he]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, RingHom.comp_apply, map_ne_zero]
  rfl

theorem tt_equiv_fin_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE), S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∀ [IsCommMonObj ((Over.pullback ξ).obj Zh.G)] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (IsLocalRing.maximalIdeal V) D A ((Over.pullback ξ).obj Zh.G)), LBIso U.LG.L (Zh.L.L.pull (pullback.fst Zh.G.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus Zh.G)) → Nonempty (S.TT M (ξ (IsLocalRing.closedPoint V)) ≃+ (Fin (Module.finrank ℤ D.toPre.X) → ZMod (S.r * S.N))) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hBig hOv hEE V _ _ _ _ hc ξ hgen _ D A U hLB hPsi
  obtain ⟨emb, hemb⟩ := GlobalTheory.ZH.RatModel.exists_emb_fractionRing_of_dominant o Ω M V ξ hgen
  have h2 := GlobalTheory.ZH.ThetaSys.supI_closedPoint_eq o Ω S M hOv.div V ξ emb hemb
  obtain ⟨yy, hon, hiso, hcl⟩ := leastValuation_labels o Ω S ρ M U₀ EE Zh hBig hOv hEE V hc ξ hgen D A U hLB hPsi emb hemb
  have hTT : S.TT M (ξ (IsLocalRing.closedPoint V)) = S.perp yy.ker := by
    rw [ThetaSys.TT, ThetaSys.HH, h2, hcl]
  rw [hTT]
  exact GlobalTheory.ZH.PerpKerRank.perp_ker_equiv o Ω S D.toPre.X yy hon hiso

end GlobalTheory.ThetaDvr.TorRank

end

section Main
open IsLocalRing ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open GlobalTheory.Poinc GlobalTheory.TorusPart
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

theorem GlobalTheory.ThetaDvr.TorRank.rkAt_tt_equiv : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Big → S.Over₀ M U₀ → S.IsEE M U₀ EE → ∀ w : M.Z, ∃ r : ℕ, RkAt FinalForm.G w r ∧ Nonempty (S.TT M w ≃+ (Fin r → ZMod (S.r * S.N))) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE FinalForm hB hO hE w
  obtain ⟨V, _, _, _, _, ξ, hc, hξ, w', hw'⟩ := GlobalTheory.DvrCentre.exists_complete_dvr_centre o Ω M w
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := ⟨w', by
    show ξ w' ∈ abLocus FinalForm.G
    rw [hw', FinalForm.ab]
    exact ThetaSys.TT_genericPoint S M⟩
  have : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif V inferInstance inferInstance hc ξ hne
  have hT := GlobalTheory.ThetaDvr.TorRank.tt_equiv_fin_of_unif o Ω S ρ M U₀ EE FinalForm hB hO hE V hc ξ ⟨w', hw'⟩ D A U hL hP
  rw [hξ] at hT
  refine ⟨Module.finrank ℤ D.toPre.X, ?_, hT⟩
  have h₁ : IsGrpPullback ((Over.pullback ξ).obj FinalForm.G) FinalForm.G ξ (pullback.fst FinalForm.G.hom ξ) :=
    isGrpPullback_pullback _ _
  have h₀ : IsGrpPullback ((Over.pullback (spMap (residue V))).obj ((Over.pullback ξ).obj FinalForm.G))
      ((Over.pullback ξ).obj FinalForm.G) (spMap (residue V)) (pullback.fst _ _) := isGrpPullback_pullback _ _
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 :=
    GlobalTheory.TorusPart.map_pow_one_eq_zero fun x hx => (residue_eq_zero_iff x).2 hx
  refine ⟨D.toPre.X, inferInstance, inferInstance, inferInstance, ResidueField V, inferInstance,
    spMap (residue V) ≫ ξ, _, inferInstance, _, gtTorus (U.gt 0) hρ h₀, ?_, h₀.comp h₁, isTorPart_gtTorus (U.gt 0) hρ h₀, rfl⟩
  have hcl : spMap (residue V) (closedPoint (ResidueField V)) = closedPoint V :=
    haveI : (closedPoint (ResidueField V)).asIdeal.IsMaximal := maximalIdeal.isMaximal _
    PrimeSpectrum.ext (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ residue_surjective))
  rw [← hξ, ← hcl]
  rfl

end Main
