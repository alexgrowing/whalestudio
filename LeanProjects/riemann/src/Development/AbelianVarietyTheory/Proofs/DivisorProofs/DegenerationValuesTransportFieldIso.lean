import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.FieldIso

open GlobalTheory.TorusExt GlobalTheory.ArcExt GlobalTheory.FormalValue GlobalTheory.ExpansionTotal

section Local

variable {A A' : Type} [CommRing A] [IsLocalRing A] [CommRing A'] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
  {φ : K → (Y ⟶ X)} {ε : K → ℤ}

def vL {A : Type} [CommRing A] (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) (J : (Sp A ⟶ X) → L.ι) : A :=
  valR r (LB.wchart L φ fun k => J (r ≫ φ k)) (t.s fun k => J (r ≫ φ k)).val

def sL {A : Type} [CommRing A] (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) (J : (Sp A ⟶ X) → L.ι) : A :=
  valR r (LB.wchart L φ fun k => J (r ≫ φ k)) (s.f fun k => J (r ≫ φ k))

variable {J : (Sp A ⟶ X) → L.ι} (hJ : Good L (cpt A) J)
include hJ

theorem stalk_vL (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) :
    toStkA (cpt A) (vL t r J) = (val t r (cpt A) J).val :=
  toStkA_valR r _ _ ((top_le_iff_cpt _ _).2 (hJ.mem φ r)) _

theorem stalk_sL (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) :
    toStkA (cpt A) (sL s r J) = sval s r (cpt A) J :=
  toStkA_valR_eq_gs r _ _ ((top_le_iff_cpt _ _).2 (hJ.mem φ r)) _

variable (ρ : A →+* A') {J' : (Sp A' ⟶ X) → L.ι} (hJ' : ∀ ψ, J' (spMap ρ ≫ ψ) = J ψ)
include hJ'

theorem vL_ext (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) : vL t (spMap ρ ≫ r) J' = ρ (vL t r J) := by
  have e : (fun k => J' ((spMap ρ ≫ r) ≫ φ k)) = fun k => J (r ≫ φ k) := funext fun k => by
    rw [Category.assoc, hJ']
  have k : ∀ j j' : K → L.ι, j = j' → valR (spMap ρ ≫ r) (LB.wchart L φ j) (t.s j).val =
      valR (spMap ρ ≫ r) (LB.wchart L φ j') (t.s j').val := by rintro _ _ rfl; rfl
  exact (k _ _ e).trans (valR_spMap ρ r _ ((top_le_iff_cpt _ _).2 (hJ.mem φ r)) _)

theorem sL_ext (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp A ⟶ Y) : sL s (spMap ρ ≫ r) J' = ρ (sL s r J) := by
  have e : (fun k => J' ((spMap ρ ≫ r) ≫ φ k)) = fun k => J (r ≫ φ k) := funext fun k => by
    rw [Category.assoc, hJ']
  have k : ∀ j j' : K → L.ι, j = j' → valR (spMap ρ ≫ r) (LB.wchart L φ j) (s.f j) =
      valR (spMap ρ ≫ r) (LB.wchart L φ j') (s.f j') := by rintro _ _ rfl; rfl
  exact (k _ _ e).trans (valR_spMap ρ r _ ((top_le_iff_cpt _ _).2 (hJ.mem φ r)) _)

end Local

section Dual

variable {F F' : Type} [Field F] [Field F'] {X : Scheme.{0}} {L : LB X}

theorem redE_cpt : redE F (cpt F) = cpt (DualNumber F) := by
  haveI : IsLocalHom (TrivSqZeroExt.fstHom F F F).toRingHom :=
    ⟨fun a h => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 h⟩
  exact IsLocalRing.comap_closedPoint (TrivSqZeroExt.fstHom F F F).toRingHom

theorem good_field {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) : Good L (cpt F) J :=
  fun ψ => hJ ψ trivial

theorem good_dual {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) :
    Good L (cpt (DualNumber F)) (fun ψ => J (redE F ≫ ψ)) := fun ψ => by
  rw [← redE_cpt]
  exact good_field hJ (redE F ≫ ψ)

theorem redE_dualMap (f : F →+* F') : redE F' ≫ spMap (dualMap f) = spMap f ≫ redE F := by
  rw [← spMap_comp', ← spMap_comp']
  refine congrArg spMap ?_
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem inl_dualMap (f : F →+* F') : spMap (dualMap f) ≫ spMap (algebraMap F (DualNumber F)) =
    spMap (algebraMap F' (DualNumber F')) ≫ spMap f := by
  rw [← spMap_comp', ← spMap_comp']
  refine congrArg spMap ?_
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end Dual

def mapNum {O O' : Type} [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) : NumD O' where
  A := N.A
  θ x y z := Units.map f.toMonoidHom (N.θ x y z)
  cub := ⟨fun x y => by rw [N.cub.face, map_one], fun x y z => by rw [N.cub.s01], fun x y z => by rw [N.cub.s12],
    fun x x' x'' y => by rw [← map_mul, ← map_mul, N.cub.coc]⟩
  σ x := Units.map f.toMonoidHom (N.σ x)
  σ_one := by rw [N.σ_one, map_one]
  σ_mul x y := by rw [← map_mul, ← map_mul, ← map_mul, N.σ_mul]
  th x := f (N.th x)
  X := N.X
  c := N.c
  c_add := N.c_add
  ψ χ := Units.map f.toMonoidHom (N.ψ χ)
  even χ := by rw [← map_mul, N.even]
  bimult a a' b := by simpa only [map_mul, map_div] using congrArg (Units.map f.toMonoidHom) (N.bimult a a' b)

def mapHom {O O' : Type} [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) : NumD.Hom f N (mapNum f N) where
  φ := MonoidHom.id N.A
  h _ := 1
  h_one := rfl
  θ_eq x y u := by simp only [_root_.mul_one]; rfl
  σ_eq x := rfl
  lam := 1
  th_eq x := by simp only [_root_.mul_one, Units.val_one, _root_.one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq χ := _root_.mul_one _

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F F' : Type} [Field F] [Field F']
  [Algebra (FractionRing R) F] [Algebra (FractionRing R) F']

section Ext

variable (f : F →+* F') (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
  {J : (Sp F ⟶ D.P.A.left) → D.P.L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ))
  {J' : (Sp F' ⟶ D.P.A.left) → D.P.L.ι} (hg : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J' ψ)) (hJ' : ∀ ψ, J' (spMap f ≫ ψ) = J ψ)
include hJ hg hJ'

omit hJ hg in
theorem gauge_dual (ψ : Sp (DualNumber F) ⟶ D.P.A.left) :
    J' (redE F' ≫ spMap (dualMap f) ≫ ψ) = J (redE F ≫ ψ) := by
  rw [← Category.assoc, redE_dualMap, Category.assoc, hJ']

theorem vE_pull {gm : GtPt D (TE R F)} {gm' : GtPt D (TE R F')} (h : GtPt.IsPull (spMap (dualMap f)) gm gm') (χ : D.X) :
    vE (gm'.s χ) (𝟙 _) J' = dualMap f (vE (gm.s χ) (𝟙 _) J) := by
  have g' := good_dual hg
  refine Eq.trans ?_ (vL_ext (good_dual hJ) (dualMap f) (J' := fun ψ => J' (redE F' ≫ ψ))
    (gauge_dual f hJ') (gm.s χ) (𝟙 _))
  refine toStkA_injective ((stalk_vL g' _ _).trans (Eq.trans ?_ (stalk_vL g' _ _).symm))
  rw [val_corr g' (h.2 χ), val_pull g', Category.id_comp, Category.comp_id]

theorem exists_fam (k : ℕ) (s : Fam D F k) : ∃ s' : Fam D F' k,
    (∀ α (x : TF (R := R) F ⟶ D.P.A), sF (s'.s α) (lift (𝟙 (TF (R := R) F')) (extMap f hf ≫ x)).left J' =
      f (sF (s.s α) (lift (𝟙 (TF (R := R) F)) x).left J)) ∧
    ∀ α (b : TE R F ⟶ D.P.A) (b' : TE R F' ⟶ D.P.A), b'.left = spMap (dualMap f) ≫ b.left →
      sE (s'.s α) (lift (Over.homMk (spMap (algebraMap F' (DualNumber F'))) rfl : TE R F' ⟶ TF (R := R) F') b').left J' =
      dualMap f (sE (s.s α)
        (lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl : TE R F ⟶ TF (R := R) F) b).left J) := by
  obtain ⟨s', hs⟩ := exists_famPull (extMap (R := R) f hf) D ((extMap_jFK f hf).trans (Category.id_comp _)) k s
  refine ⟨s', fun α x => ?_, fun α b b' hb => ?_⟩
  · have g' := good_field hg
    refine Eq.trans ?_ (sL_ext (good_field hJ) f hJ' (s.s α) _)
    refine toStkA_injective ((stalk_sL g' _ _).trans (Eq.trans ?_ (stalk_sL g' _ _).symm))
    refine (hs α _ _ _ _ g').trans (congrArg (fun r => sval (s.s α) r (cpt F') J') ?_)
    refine congrArg (fun q : TF (R := R) F' ⟶ DegPre.BF D F => q.left)
      (show lift (𝟙 _) (extMap f hf ≫ x) ≫ toBK (extMap f hf) D = extMap f hf ≫ lift (𝟙 _) x from ?_)
    apply CartesianMonoidalCategory.hom_ext <;> simp [toBK]
  · have g' := good_dual hg
    refine Eq.trans ?_ (sL_ext (good_dual hJ) (dualMap f) (J' := fun ψ => J' (redE F' ≫ ψ))
      (gauge_dual f hJ') (s.s α) _)
    refine toStkA_injective ((stalk_sL g' _ _).trans (Eq.trans ?_ (stalk_sL g' _ _).symm))
    refine (hs α _ _ _ _ g').trans (congrArg (fun r => sval (s.s α) r (cpt _) fun ψ => J' (redE F' ≫ ψ)) ?_)
    let u : TE R F' ⟶ TE R F := Over.homMk (spMap (dualMap f)) (by
      change spMap (dualMap f) ≫ spMap (algebraMap F (DualNumber F)) ≫ (TF (R := R) F).hom =
        spMap (algebraMap F' (DualNumber F')) ≫ (TF (R := R) F').hom
      rw [← Category.assoc, inl_dualMap, Category.assoc]
      exact congrArg (_ ≫ ·) (Over.w (extMap (R := R) f hf)))
    refine congrArg (fun q : TE R F' ⟶ DegPre.BF D F => q.left)
      (show lift (Over.homMk (spMap (algebraMap F' (DualNumber F'))) rfl : TE R F' ⟶ TF (R := R) F') b' ≫
        toBK (extMap f hf) D = u ≫ lift (Over.homMk (spMap (algebraMap F (DualNumber F))) rfl :
          TE R F ⟶ TF (R := R) F) b from ?_)
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, toBK_fst, lift_fst_assoc, Category.assoc, lift_fst]
      exact Over.OverMorphism.ext (inl_dualMap f).symm
    · rw [Category.assoc, toBK, lift_snd, lift_snd, Category.assoc, lift_snd]
      exact Over.OverMorphism.ext hb

end Ext

section Iso

variable (e : F ≃+* F') (he : (e : F →+* F').comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')

theorem sp_symm : spMap (e.symm : F' →+* F) ≫ spMap (e : F →+* F') = 𝟙 _ := by
  rw [← spMap_comp', show (e.symm : F' →+* F).comp (e : F →+* F') = RingHom.id F from RingHom.ext e.symm_apply_apply]
  exact Spec.map_id _

include he in
theorem symm_comp : (e.symm : F' →+* F).comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F :=
  RingHom.ext fun x => e.symm_apply_eq.2 (RingHom.congr_fun he x).symm

def ptEquiv : (TF (R := R) F ⟶ D.P.A) ≃* (TF (R := R) F' ⟶ D.P.A) where
  toFun x := extMap (e : F →+* F') he ≫ x
  invFun x := extMap (e.symm : F' →+* F) (symm_comp e he) ≫ x
  left_inv x := Over.OverMorphism.ext (by
    change spMap (e.symm : F' →+* F) ≫ spMap (e : F →+* F') ≫ x.left = x.left
    rw [← Category.assoc, sp_symm, Category.id_comp])
  right_inv x := Over.OverMorphism.ext (by
    change spMap (e.symm.symm : F →+* F') ≫ spMap (e.symm : F' →+* F) ≫ x.left = x.left
    rw [← Category.assoc, sp_symm, Category.id_comp])
  map_mul' x y := MonObj.comp_mul _ _ _

variable {N : NumD F} (ν : NumOf D F N)

theorem gauge_iso (ψ : Sp F ⟶ D.P.A.left) : ν.J (spMap (e.symm : F' →+* F) ≫ spMap (e : F →+* F') ≫ ψ) = ν.J ψ := by
  rw [← Category.assoc, sp_symm, Category.id_comp]

include he in
theorem rig_iso : vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F').hom
    (fun ψ => ν.J (spMap (e.symm : F' →+* F) ≫ ψ)) = e ν.rg :=
  (congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r
    (fun ψ => ν.J (spMap (e.symm : F' →+* F) ≫ ψ))) (Over.w (extMap (R := R) (e : F →+* F') he)).symm).trans
    (vF_ext (e : F →+* F') ν.good (gauge_iso e ν) _ _)

def mapNumOf : NumOf D F' (mapNum (e : F →+* F') N) where
  J ψ := ν.J (spMap (e.symm : F' →+* F) ≫ ψ)
  good ψ z _ := (Subsingleton.elim (α := PrimeSpectrum F') (spMap (e.symm : F' →+* F) (cpt F)) z) ▸
    ν.good (spMap (e.symm : F' →+* F) ≫ ψ) (Set.mem_univ (cpt F))
  th := ν.th
  th_gen := ν.th_gen
  eA := ν.eA.trans (ptEquiv e he)
  eX := ν.eX
  c_eq (χ : N.X) := by
    change extMap (e : F →+* F') he ≫ ν.eA (N.c χ) = _
    rw [ν.c_eq]
    exact DVR.comp_cP D (extMap _ he) _
  θ_eq (x y u : N.A) := by
    change (e : F →+* F') (N.θ x y u : F) = vF _ (lift (extMap (e : F →+* F') he ≫ ν.eA x)
      (lift (extMap (e : F →+* F') he ≫ ν.eA y) (extMap (e : F →+* F') he ≫ ν.eA u))).left _
    rw [ν.θ_eq, ← comp_lift, ← comp_lift]
    exact (vF_ext _ ν.good (gauge_iso e ν) _ _).symm
  σ_eq x := (congrArg (e : F →+* F') (ν.σ_eq x)).trans (vF_ext _ ν.good (gauge_iso e ν) _ _).symm
  th_eq x := by
    rw [rig_iso e he ν]
    exact (map_mul e _ _).symm.trans ((congrArg e (ν.th_eq x)).trans
      (sF_ext (e : F →+* F') ν.good (gauge_iso e ν) _ _).symm)
  ψ_eq χ := by
    rw [rig_iso e he ν]
    refine (congrArg e (ν.ψ_eq χ)).trans ((map_mul e _ _).trans (congrArg (· * e ν.rg) ?_))
    exact (vF_ext (e : F →+* F') ν.good (gauge_iso e ν) _ _).symm.trans
      (congrArg (fun r => vF (D.psi (ν.eX χ)) r _) ((extMap_jFK (e : F →+* F') he).trans (Category.id_comp _)))

end Iso

theorem transport_iso : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (e : F ≃+* F'), (∀ x, e (algebraMap (FractionRing R) F x) = algebraMap (FractionRing R) F' x) → ∀ (N : NumD F) (ν : NumOf D F N), ∃ (N' : NumD F') (ν' : NumOf D F' N') (I : NumD.Hom (e : F →+* F') N N'), Function.Bijective I.φ ∧ (∀ x, I.h x = 1) ∧ I.lam = 1 ∧ (∀ χ, ν'.eX (I.e χ) = ν.eX χ) ∧ ν'.th = ν.th ∧ ν'.rg = e ν.rg ∧ (∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ χ, vE (gm'.s χ) (𝟙 _) ν'.J = dualMap (e : F →+* F') (vE (gm.s χ) (𝟙 _) ν.J)) ∧ ∀ (k : ℕ) (s : Fam D F k), ∃ s' : Fam D F' k, (∀ f, ν.FamV s f → ∃ f', ν'.FamV s' f' ∧ ∀ α x, f' (I.e α) (I.φ x) = e (f α x)) ∧ ∀ (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')), GtPt.IsPull (spMap (dualMap (e : F →+* F'))) gm gm' → ∀ α, jc ν' s' gm' (I.e α) = dualMap (e : F →+* F') (jc ν s gm α) := by
  intro R _ _ D F F' _ _ _ _ e he N ν
  have hf : (e : F →+* F').comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := RingHom.ext he
  have hr : (mapNumOf e hf ν).rg = e ν.rg := rig_iso e hf ν
  have hv := fun (gm : GtPt D (TE R F)) (gm' : GtPt D (TE R F')) h =>
    vE_pull (gm := gm) (gm' := gm') (e : F →+* F') ν.good (mapNumOf e hf ν).good (gauge_iso e ν) h
  refine ⟨mapNum (e : F →+* F') N, mapNumOf e hf ν, mapHom _ N, Function.bijective_id, fun _ => rfl, rfl,
    fun _ => rfl, rfl, hr, hv, fun k s => ?_⟩
  obtain ⟨s', h₁, h₂⟩ := exists_fam (e : F →+* F') hf ν.good (mapNumOf e hf ν).good (gauge_iso e ν) k s
  refine ⟨s', fun f h => ⟨fun α x => e (f α x), fun α x => ?_, fun _ _ => rfl⟩, fun gm gm' h α => ?_⟩
  · rw [hr, ← map_pow, ← map_mul, h α x]
    exact (h₁ _ _).symm
  · exact (congrArg₂ (· * ·) (h₂ _ _ _ h.1) (hv gm gm' h _)).trans (map_mul _ _ _).symm

end GlobalTheory.MBLow.FieldIso

end
