import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.RigidTranslate

open GlobalTheory.CoordToExt GlobalTheory.PolTranslate

section Calculus

variable {X Y Z : Scheme.{0}}

theorem lbIso_of_refines {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem gen_of_lbIso {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B) (t : LB.Gen A) (ht : t.IsGen) :
    ∃ s : LB.Gen B, s.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId A) (chartPullPull B (𝟙 X) (𝟙 X) rfl)
  obtain ⟨c, hc⟩ := gen_chartPull (chartPullPull A (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c', hc', -⟩ := exists_up ((isGen_iff w).1 hw) hB hA c hc
  exact gen_chartPull (chartPullUnpull B _ (Category.id_comp _)) c' hc'

abbrev diff (L : LB X) (u v : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]

theorem lbIso_diff_diff {L : LB X} (hL : L.IsLB) (u v : Y ⟶ X) (a b : Z ⟶ Y) (e : a ≫ v = b ≫ v) :
    LBIso (diff (diff L u v) a b) (diff (L.pull u) a b) := by
  refine lbIso_of_refines hL ((refines_self _ _).linComb _ _) ((refines_self _ _).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, e, mul_comm (f (b ≫ u))⁻¹, mul_assoc]

theorem lbIso_diff_pull {L : LB X} (hL : L.IsLB) (u v : Y ⟶ X) (a : Z ⟶ Y) (i : L.ι) (h : ∀ z, (a ≫ v) z ∈ L.U i) :
    LBIso ((diff L u v).pull a) (L.pull (a ≫ u)) := by
  obtain ⟨c, hc⟩ := IsoExtend.exists_gen_of_chart hL (a ≫ v) i h
  refine lbIso_of_refines hL ((refines_self _ _).linComb _ _) (refines_self _ _) c hc fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, mul_left_comm]

end Calculus

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

abbrev rigTransl (L : LB A.left) (t : 𝟙_ (Over S) ⟶ A) : LB A.left := diff L (transl t).left (toUnit A ≫ t).left

theorem comp_const {T : Over S} (y : T ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    y.left ≫ (toUnit A ≫ t).left = (toUnit T ≫ t).left := by
  rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

theorem comp_transl_left {T : Over S} (y : T ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    y.left ≫ (transl t).left = (y * (toUnit T ≫ t)).left := by
  rw [← Over.comp_left, comp_transl]

variable {L : LB A.left} {t : 𝟙_ (Over S) ⟶ A}

theorem rigidified_rigTransl (hL : L.IsLB) : Out.Rigidified A (rigTransl L t) := by
  refine ((refines_self _ _).linComb _ _).exists_gen hL (fun U _ f => ?_) _ isGen_one
  have e : eSec A ≫ (transl t).left = eSec A ≫ (toUnit A ≫ t).left := by
    rw [eSec, comp_const, comp_transl_left]
    have : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [this, _root_.one_mul]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two, Fintype.prod_unique, Fintype.prod_empty,
    Matrix.cons_val_zero, Matrix.cons_val_one, e, _root_.mul_one, zpow_neg, mul_inv_cancel]

theorem sym_rigTransl [IsCommMonObj A] (ht : t * t = 1) (hL : L.IsLB) (h : Out.Sym A L) :
    Out.Sym A (rigTransl L t) := by
  intro s
  obtain ⟨U, hU, c, hc⟩ := sym_transl ht h s
  refine ⟨U, hU, gen_of_lbIso (DVR.linComb_isLB _ (pull_isLB hL _) _ _)
    (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) (lbIso_diff_diff hL _ _ _ _ ?_).symm c hc⟩
  rw [Category.assoc, comp_const]

theorem kTriv_rigTransl (ht : t * t = 1) (hL : L.IsLB) (h : Out.KTriv A L) : Out.KTriv A (rigTransl L t) := by
  intro R _ s y hy
  refine kTriv_transl ht hL h R s y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, gen_of_lbIso (pull_isLB (DVR.linComb_isLB _ (DVR.linComb_isLB _ hL _ _) _ _) _)
    (pull_isLB (DVR.linComb_isLB _ (pull_isLB hL _) _ _) _)
    (LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) (lbIso_diff_diff hL _ _ _ _ ?_)) c hc⟩
  rw [comp_const, comp_const]

theorem relAmple_rigTransl [IsAffine S] [IsProper A.hom] (ht : t * t = 1) (hL : L.IsLB) (h : Out.RelAmple A L) :
    Out.RelAmple A (rigTransl L t) := by
  have hL' : (rigTransl L t).IsLB := DVR.linComb_isLB _ hL _ _
  refine AmpleLocal.relAmple_of_locally S A _ hL' inferInstance inferInstance fun s => ?_
  let t₀ : S ⟶ A.left := t.left
  obtain ⟨i, hi⟩ := exists_chart hL (t₀ s)
  let U : S.Opens := t₀ ⁻¹ᵁ L.U i
  refine ⟨U, hi, ?_⟩
  have e : (transl t).left ≫ (transl t).left = 𝟙 _ := congrArg (fun q => q.left) (transl_transl ht)
  have : IsIso (transl t).left := ⟨⟨(transl t).left, e, e⟩⟩
  have hp : IsPullback (transl t).left A.hom A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  have H := (isPullback_morphismRestrict A.hom U).flip.paste_horiz hp
  have k : (toUnit A ≫ t).left = A.hom ≫ t₀ := rfl
  obtain ⟨w, hw⟩ := lbIso_diff_pull hL (transl t).left (toUnit A ≫ t).left (A.hom ⁻¹ᵁ U).ι i fun z => by
    rw [k]; exact z.2
  exact relAmple_pull (A' := Over.mk (A.hom ∣_ U)) H hL (pull_isLB hL' _) ((isGen_iff w).1 hw) ⊤
    (isAffineOpen_top _) (fun _ => trivial) h

theorem lam_rigTransl [IsCommMonObj A] (hL : L.IsLB) (c : LB.Gen (Theta A L)) (hc : c.IsGen) :
    LBIso (abelian₂ A (rigTransl L t)) ((abelian₂ A L).pull (𝟙 _)) := by
  refine LBIso.symm (LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullId _) ?_)
  refine lbIso_of_refines hL (refines_self _ _) ((refines_self _ _).linComb _ _) _
    (DVR.pullGen_isGen _ _ _ _ hc (lift (x2 A 0) (lift (x2 A 1) (toUnit _ ≫ t))).left) fun U _ f => ?_
  rw [Fintype.prod_prod_type]
  simp only [zpow_mul, Finset.prod_zpow, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    comp_const, comp_transl_left]
  refine (congrArg₂ (· * ·) (prod_cub (x2 A 0) (x2 A 1) (toUnit _ ≫ t) f)
    (prod_square (x2 A) fun x => f x.left)).trans (Eq.symm ((prod_square (x2 A) fun x =>
      f (x * (toUnit _ ≫ t)).left ^ (1 : ℤ) * f (toUnit (G2 A) ≫ t).left ^ (-1 : ℤ)).trans ?_))
  simp only [zpow_neg, zpow_one, _root_.one_mul, _root_.mul_assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_rigid_translate : Out.Laws → ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (t : 𝟙_ (Over (Sp R)) ⟶ P.A), t ^ 2 = 1 → ∃ (P' : Out.PolAV (Sp R)) (e : P'.A ≅ P.A), IsMonHom e.hom ∧ P'.g = P.g ∧ LamIs P'.A P'.L P.A (abelian₂ P.A P.L) e.hom.left ∧ LBIso P'.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ ((toUnit P.A ≫ t) * 𝟙 P.A)).left, (toUnit P'.A ≫ t).left] ![1, -1]) := by
  intro _ R _ P t ht
  rw [sq] at ht
  have := P.isAb.comm
  have := P.isAb.proper
  obtain ⟨c, hc⟩ := Moduli.cube_of_isLB _ P P.L P.isLB
  refine ⟨{ A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := rigTransl P.L t
            isLB := DVR.linComb_isLB _ P.isLB _ _
            rigid := rigidified_rigTransl P.isLB
            sym := sym_rigTransl ht P.isLB P.sym
            ample := relAmple_rigTransl ht P.isLB P.ample
            ktriv := kTriv_rigTransl ht P.isLB P.ktriv },
    Iso.refl _, inferInstanceAs (IsMonHom (𝟙 _)), rfl,
    ⟨𝟙 _, ⟨(Category.id_comp _).trans (Category.comp_id _).symm, (Category.id_comp _).trans (Category.comp_id _).symm⟩,
      lam_rigTransl P.isLB c hc⟩, exists_iso P.isLB ?_ _⟩
  have e : transl t = 𝟙 P.A ≫ ((toUnit P.A ≫ t) * 𝟙 P.A) := by
    rw [Category.id_comp, transl, _root_.mul_comm]
  exact congrArg (fun q : P.A ⟶ P.A => ![q.left, (toUnit P.A ≫ t).left]) e

end GlobalTheory.RigidTranslate
