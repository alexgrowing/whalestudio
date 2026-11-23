import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.PolarizedAbelianVarieties
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.PolCompare

open GlobalTheory.CechPic GlobalTheory.HermTensorKernel

section Ample

variable {X : Scheme.{0}} {L : LB X}

theorem powLB_eq_pw (L : LB X) (n : ℕ) : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.powLB L n = AbLaw.pw L n := by
  unfold IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.powLB AbLaw.pw
  simp only [zpow_natCast]

theorem isLB_powLB (hL : L.IsLB) (n : ℕ) : (IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.powLB L n).IsLB :=
  powLB_eq_pw L n ▸ AbLaw.isLB_pw hL n

theorem lbIso_powLB (hL : L.IsLB) (n : ℕ) : LBIso (IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.powLB L n) (lbPow L n) := by
  refine (cls_eq_iff (isLB_powLB hL n) (isLB_lbPow hL n)).1 ?_
  rw [cls_lbPow hL, ← natCast_zsmul, ← AmpleStabFinite.cls_pw hL]
  simp only [powLB_eq_pw]

theorem isAmpleLB_iff (hL : L.IsLB) : GlobalTheory.IsAmpleLB L ↔ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsAmpleLB L := by
  refine ⟨fun h => ⟨h.compactSpace, fun x => ?_⟩, fun h => ⟨hL, h.1, fun x => ?_⟩⟩
  · obtain ⟨n, hn, s, hs, ha⟩ := h.exists_affine x
    obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_powLB hL n) (isLB_lbPow hL n) (lbIso_powLB hL n) s
    exact ⟨n, hn, t, ht.ge hs, (congrArg IsAffineOpen ht).mpr ha⟩
  · obtain ⟨n, hn, s, hs, ha⟩ := h.2 x
    obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_lbPow hL n) (isLB_powLB hL n)
      (lbIso_powLB hL n).symm s
    exact ⟨n, hn, t, ht.ge hs, ht ▸ ha⟩

end Ample

section Conditions

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

theorem rigidified_iff (L : LB A.left) : Out.Rigidified A L ↔ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsRigidified A L := Iff.rfl

theorem sym_iff_locZero (hL : L.IsLB) :
    Out.Sym A L ↔ ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) = 0 := by
  refine forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
      (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = 0 ↔ _
  rw [one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]

theorem isSymmetric_iff_cls (hL : L.IsLB) :
    IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsSymmetric A L ↔ pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL = 0 :=
  (cls_eq_iff (pull_isLB hL _) hL).symm.trans sub_eq_zero.symm

theorem sym_of_isSymmetric (hL : L.IsLB) (h : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsSymmetric A L) : Out.Sym A L :=
  (sym_iff_locZero A hL).2 fun _ => ⟨⊤, trivial, by rw [(isSymmetric_iff_cls A hL).1 h, map_zero]⟩

theorem sym_iff (hA : IsAbelianScheme A) (hL : L.IsLB) : Out.Sym A L ↔ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsSymmetric A L := by
  refine ⟨fun h => (isSymmetric_iff_cls A hL).2 ?_, sym_of_isSymmetric A hL⟩
  have e : eSec A ≫ (GrpObj.inv : A ⟶ A).left = eSec A := congrArg (fun q => q.left) (GrpObj.one_inv (G := A))
  have key := AmpleStabFinite.eq_pull_of_local A.hom (eSec A) (Over.w η[A])
    (fun V => AmpleStabFinite.surj_of_isPullback globalFns_holds hA (IsPullback.of_hasPullback _ _)) _
    ((sym_iff_locZero A hL).1 h)
  rw [key, pull_comp, map_sub, ← pull_comp (eSec A), e, sub_self, map_zero]

theorem relAmple_iff_isProper_and (hL : L.IsLB) :
    Out.RelAmple A L ↔ IsProper A.hom ∧ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsRelAmple A L := by
  constructor
  · intro h
    have := ZH.isProper_hom_of_relAmple h
    exact ⟨this, inferInstance, fun V hV =>
      (isAmpleLB_iff (LB.isLB_pull hL _)).1 (isAmpleLB_of_relAmple A hL h V hV)⟩
  · rintro ⟨_, -, h⟩
    exact relAmple_of_isAmpleLB A hL fun V hV => (isAmpleLB_iff (LB.isLB_pull hL _)).2 (h V hV)

theorem relAmple_iff (hA : IsProper A.hom) (hL : L.IsLB) : Out.RelAmple A L ↔ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.IsRelAmple A L :=
  (relAmple_iff_isProper_and A hL).trans (and_iff_right hA)

theorem memK_iff_cls (hL : L.IsLB) {T : Over S} (x : T ⟶ A) :
    IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.MemK A L x ↔ lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hΛ _)).symm.trans ?_
  have e : cls _ hΛ = lam (cls L hL) (fst A A) (snd A A) := cls_cube_two hL _ _ hΛ
  rw [cls_pull hΛ, e, pull_lam, whiskerRight_fst, whiskerRight_snd]

theorem inK_of_memK (hL : L.IsLB) {T : Over S} {x : T ⟶ A} (h : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.MemK A L x) : UU.InK A L x :=
  (translDiff_iff hL x).2 fun _ => ⟨⊤, trivial, fun _ _ _ => by rw [(memK_iff_cls A hL x).1 h, map_zero]⟩

theorem exists_memK_of_inK (hL : L.IsLB) {T : Over S} {x : T ⟶ A} (h : UU.InK A L x) (p : T.left) :
    ∃ V : T.left.Opens, p ∈ V ∧
      IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.MemK A L ((Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T) ≫ x) := by
  obtain ⟨V, hV, H⟩ := (translDiff_iff hL x).1 h p
  refine ⟨V, hV, (memK_iff_cls A hL _).2 ?_⟩
  let i : Over.mk (V.ι ≫ T.hom) ⟶ T := Over.homMk V.ι rfl
  have H' := H _ (i ▷ A).left fun y => by
    have e := congrArg (fun q => q.left y) (whiskerRight_fst i A)
    exact (congrArg (· ∈ V) e).mpr ((fst _ A).left y).2
  rwa [pull_lam, whiskerRight_fst_assoc, whiskerRight_snd] at H'

theorem kTriv_iff (hL : L.IsLB) : Out.KTriv A L ↔ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.KTrivial A L := by
  rw [UU.kTriv_iff_forall]
  refine ⟨fun h T x hx => h T x (inK_of_memK A hL hx), fun h T x hx => ?_⟩
  refine Over.OverMorphism.ext (Scheme.hom_ext_of_forall x.left (1 : T ⟶ A).left fun p => ?_)
  obtain ⟨V, hV, H⟩ := exists_memK_of_inK A hL hx p
  exact ⟨V, hV, congrArg (fun q => q.left) ((h _ _ H).trans
    (MonObj.comp_one (Over.homMk V.ι rfl : Over.mk (V.ι ≫ T.hom) ⟶ T)).symm)⟩

end Conditions

variable {S : Scheme.{0}}

def toIndefiniteRowSideFullHecke (P : Out.PolAV S) : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.PolAV S P.g where
  A := P.A
  isAbelian := P.isAb
  relDim := P.smoothDim
  L := P.L
  isLB := P.isLB
  rigidified := (rigidified_iff P.A P.L).1 P.rigid
  symmetric := (sym_iff P.A P.isAb P.isLB).1 P.sym
  relAmple := (relAmple_iff P.A P.isAb.proper P.isLB).1 P.ample
  kTrivial := (kTriv_iff P.A P.isLB).1 P.ktriv

def split_model_to_place_model {g : ℕ} (Q : IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.PolAV S g) : Out.PolAV S where
  A := Q.A
  isAb := Q.isAbelian
  g := g
  smoothDim := Q.relDim
  L := Q.L
  isLB := Q.isLB
  rigid := (rigidified_iff Q.A Q.L).2 Q.rigidified
  sym := (sym_iff Q.A Q.isAbelian Q.isLB).2 Q.symmetric
  ample := (relAmple_iff Q.A Q.isAbelian.proper Q.isLB).2 Q.relAmple
  ktriv := (kTriv_iff Q.A Q.isLB).2 Q.kTrivial

def polAVEquiv (S : Scheme.{0}) : Out.PolAV S ≃ Σ g : ℕ, IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.PolAV S g where
  toFun P := ⟨P.g, toIndefiniteRowSideFullHecke P⟩
  invFun Q := split_model_to_place_model Q.2
  left_inv _ := rfl
  right_inv _ := rfl

def polAVEquivDim (S : Scheme.{0}) (g : ℕ) : {P : Out.PolAV S // P.g = g} ≃ IndefiniteRowSideFullHecke.PolarizedAbelianVarieties.PolAV S g where
  toFun P := P.2 ▸ toIndefiniteRowSideFullHecke P.1
  invFun Q := ⟨split_model_to_place_model Q, rfl⟩
  left_inv := by rintro ⟨P, rfl⟩; rfl
  right_inv _ := rfl

end GlobalTheory.PolCompare
