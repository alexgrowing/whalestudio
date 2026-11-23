import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.VB (IsVB)

namespace GlobalTheory.Vert.Check

open Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Z : Model O}

theorem not_isEff_neg_div {g : O} (hg : g ≠ 0) (hm : g ∈ maximalIdeal O) :
    ¬ IsEff (-Z.div g hg) := by
  rintro ⟨I, hI⟩
  have h : ofEff (I * Z.effConst g hg) = ofEff 1 := by
    rw [ofEff_mul, hI, ofEff_one]; exact neg_add_cancel _
  have h' := congrArg Subtype.val (ofEff_injective h)
  obtain ⟨x, hx⟩ := Z.exists_notMem_gen
  have hx' : x ∈ (Z.effConst g hg).1.support :=
    ((EffCartierData.principal (Z.const g) (Z.isRegularFn_const hg)).mem_support_iff ⟨⟩
      (show x ∈ (⊤ : Z.X.Opens) from trivial)).2 (Z.gen_eq_basicOpen hg hm ▸ hx)
  have hx'' : x ∈ (I * Z.effConst g hg).1.support := Or.inr hx'
  rw [h', Submonoid.coe_one, Scheme.IdealSheafData.one_eq_top,
    Scheme.IdealSheafData.support_top] at hx''
  exact hx''.elim

theorem div_ne_zero {g : O} (hg : g ≠ 0) (hm : g ∈ maximalIdeal O) : Z.div g hg ≠ 0 := fun h =>
  not_isEff_neg_div (Z := Z) hg hm ⟨1, by rw [h, ofEff_one, neg_zero]⟩

theorem chiLenPic_mul (I J : Z.effVert) (c : Pic Z.X) : chiLenPic O (divMod (I * J).1) c =
    chiLenPic O (divMod I.1) (c - effCls J) + chiLenPic O (divMod J.1) c := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_shortExact_add (effData I) (effData J)
  simp only [idealSheaf_effData] at e₁ e₂ e₃
  have hM := Twist.isLB_lbZPow (effData J).isLB_lb (-1)
  have := chiLenPic_shortExact hS (((isVertical_divMod I).finiteLenTwists.twist hM).of_iso e₁.symm)
    ((isVertical_divMod J).finiteLenTwists.of_iso e₃.symm)
  rw [chiLenPic_congr O e₁, chiLenPic_congr O e₂, chiLenPic_congr O e₃] at this
  refine (congrFun this c).trans (congrArg (· + _) ((chiLenPic_twist O _ hM c).trans ?_))
  rw [cls_lbZPow (effData J).isLB_lb, neg_one_zsmul, neg_add_eq_sub]
  rfl

theorem effDeg_symm (I J : Z.effVert) (Q : PicSym Z.X) :
    effDeg I (firstChernPic (effCls J) * Q) = effDeg J (firstChernPic (effCls I) * Q) := by
  refine LinearMap.congr_fun (picSym_linearMap_ext
    (l := effDeg I ∘ₗ LinearMap.mulLeft ℚ (firstChernPic (effCls J)))
    (l' := effDeg J ∘ₗ LinearMap.mulLeft ℚ (firstChernPic (effCls I))) fun n g => ?_) Q
  have key (a : Pic Z.X) : firstChernPic a * ∏ i, firstChernPic (g i) =
      ∏ i : Fin (n + 1), firstChernPic ((Fin.cons a g : Fin (n + 1) → Pic Z.X) i) := by
    rw [Fin.prod_univ_succ]; rfl
  have e : bwdDiff (effCls J) (chiLenPic O (divMod I.1)) =
      bwdDiff (effCls I) (chiLenPic O (divMod J.1)) := funext fun c => by
    have h₁ := chiLenPic_mul I J c
    have h₂ := chiLenPic_mul J I c
    rw [mul_comm J I] at h₂
    rw [bwdDiff_apply, bwdDiff_apply]
    omega
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, key, effDeg, IsVertical.deg,
    picForm_prod, multiDiff_cons', e]

theorem vDeg_symm (D D' : Z.VDivZ) (Q : PicSym Z.X) :
    Z.vDeg D (firstChernPic (Z.vCls D') * Q) = Z.vDeg D' (firstChernPic (Z.vCls D) * Q) := by
  obtain ⟨I, J, rfl⟩ := exists_eq_ofEff_sub D
  obtain ⟨I', J', rfl⟩ := exists_eq_ofEff_sub D'
  simp only [map_sub, sub_mul, vDeg_ofEff, vCls_ofEff, LinearMap.sub_apply]
  rw [effDeg_symm I I', effDeg_symm I J', effDeg_symm J I', effDeg_symm J J']
  ring

section Theory

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

theorem capDeg_symm (D D' : (Z.toITh p).VDiv) (Q : (Z.toITh p).Ch) :
    (Z.toITh p).capDeg D ((Z.toITh p).cD D' * Q) = (Z.toITh p).capDeg D' ((Z.toITh p).cD D * Q) := by
  change Z.capDeg_vp p D (Z.cDQ D' * Q) = Z.capDeg_vp p D' (Z.cDQ D * Q)
  induction D using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, LinearMap.add_apply, ha, hb]
  | tmul a D =>
    induction D' using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_mul, LinearMap.add_apply, ha, hb]
    | tmul b D' =>
      have h (a : ℚ) (D : Z.VDivZ) : (a ⊗ₜ[ℤ] D : Z.VDivQ) = a • toQ D := by
        simp [toQ, TensorProduct.smul_tmul']
      simp only [h, map_smul, smul_mul_assoc, LinearMap.smul_apply, cDQ_toQ, capDeg_vp_toQ,
        vDeg_symm D D', smul_eq_mul]
      ring

theorem capDeg_divP_cD (D : (Z.toITh p).VDiv) (Q : (Z.toITh p).Ch) :
    (Z.toITh p).capDeg (Z.toITh p).divP ((Z.toITh p).cD D * Q) = 0 := by
  rw [capDeg_symm, (Z.toITh p).cD_divP, zero_mul, map_zero]

end Theory

theorem cls_div_symm {E E' : Z.X.Modules} {r : ℕ} (φ : Z.GenIso E E') (hE : IsVB E r)
    (hE' : IsVB E' r) : (GenIso.div φ.symm hE' hE).cls = -(φ.div hE hE').cls := by
  have h0 : (GenIso.div (Iso.refl _ : Z.GenIso E E) hE hE).cls = 0 := by
    have := GenIso.cls_div_trans (Iso.refl _ : Z.GenIso E E) hE hE hE (Iso.refl _)
    rw [Iso.trans_refl] at this
    simpa using this
  have := GenIso.cls_div_trans φ hE hE' hE φ.symm
  rw [Iso.self_symm_id, h0] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem not_isEff_smul_symm {E : Z.X.Modules} (hE : IsVB E 1) {g : O} (hg : g ≠ 0)
    (hm : g ∈ maximalIdeal O) : ¬ IsEff (GenIso.div (GenIso.smul E g hg).symm hE hE).cls := by
  rw [cls_div_symm, GenIso.cls_div_of_smul hE hg rfl, one_nsmul]
  exact not_isEff_neg_div hg hm

theorem nonempty_coh_base :
    Nonempty (O ≃ₗ[O] coh (twist (structureModule (base O).X) (LB.triv _)) 0) := by
  have hb : Function.Bijective (algebraMap O Γ((base O).X, ⊤)) :=
    (Scheme.ΓSpecIso (.of O)).symm.commRingCatIsoToRingEquiv.bijective
  let l : sectionsOn (structureModule (base O).X) ⊤ ≃ₗ[O] Γ((base O).X, ⊤) :=
    { sectionsOn.toΓ (structureModule (base O).X) ⊤ with
      map_smul' := fun r s => by
        refine (sectionsOn.toΓ_smul r s).trans ?_
        rw [restrictGlobal_top, Algebra.smul_def]; rfl }
  exact ⟨(LinearEquiv.ofBijective (Algebra.linearMap O _) hb).trans (l.symm.trans
    ((cohOn.zeroEquiv O _ ⊤).symm.trans (cohOn.mapIso O ⊤ 0 (Twist.trivIso _))))⟩

theorem vDeg_div_base {g : O} (hg : g ≠ 0) :
    (base O).vDeg ((base O).div g hg) 1 = (IsDiscreteValuationRing.addVal O g).toNat := by
  have h := vDeg_ofEff_prod ((base O).effConst g hg) (ι := Fin 0) (L := finZeroElim) (fun i => i.elim0)
  rw [Fin.prod_univ_zero, if_pos (by simp), interLen_eq_multiDiff O _ (fun i => i.elim0),
    multiDiff_of_isEmpty] at h
  obtain ⟨e⟩ := nonempty_coh_base (O := O)
  have : Module.Free O (coh (twist (structureModule (base O).X) (LB.triv _)) 0) := .of_equiv e
  have : IsAffine (base O).X := inferInstanceAs (IsAffine (Spec _))
  have := Twist.isQuasicoherent_twist (F := structureModule (base O).X) (LB.isLB_triv _)
  have k := chiLen_twist_effConst (Z := base O) hg (LB.isLB_triv _)
    fun n hn => coh.subsingleton_of_isAffine _ hn
  rw [← e.finrank_eq, Module.finrank_self] at k
  refine h.trans ?_
  have k' : chiLenPic O (divMod ((base O).effConst g hg).1) 0 = _ := k
  rw [k']; simp

theorem capDeg_divP_base (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] :
    ((base O).toITh p).capDeg ((base O).toITh p).divP 1 = 1 := by
  rw [capDeg_vp_toQ, divP, vDeg_div_base]
  exact div_self (Nat.cast_ne_zero.2 (ramIdx_ne_zero O p))

theorem capDeg_uniformiser_line (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]
    {ϖ : O} (hϖ : Irreducible ϖ) : ((projSpace O 1).toITh p).capDeg
      (toQ ((projSpace O 1).div ϖ hϖ.ne_zero)) (c1 (formalTwistingSheaf O 1) (ProjSpace.O1_isLB O 1)) =
      1 / ramIdx O p := by
  have := vDeg_div_projSpace 0 hϖ.ne_zero
  rw [IsDiscreteValuationRing.addVal_uniformizer hϖ] at this
  rw [capDeg_vp_toQ, ← pow_one (c1 _ _)]
  exact congrArg (· / _) (this.trans (by simp))

example : haveI := charP_residueField_padicInt 2
    ((base ℤ_[2]).toITh 2).capDeg ((base ℤ_[2]).toITh 2).divP 1 = 1 :=
  haveI := charP_residueField_padicInt 2
  capDeg_divP_base 2

section Mixed

variable {L M : Z.X.Modules} (hL : IsVB L 1) (hM : IsVB M 1) (g g' : O) (hg : g ≠ 0) (hg' : g' ≠ 0)

include hg hg' in

theorem isIso_diag : IsIso (Z.genRes.map
    (biprod.map (smulHom L (Z.const g)) (smulHom M (Z.const g')))) := by
  have := isIso_genRes_map_smulHom L hg
  have := isIso_genRes_map_smulHom M hg'
  have := preservesBinaryBiproduct_of_preservesBinaryCoproduct Z.genRes (X := L) (Y := M)
  have e : Z.genRes.map (biprod.map (smulHom L (Z.const g)) (smulHom M (Z.const g'))) =
      (Z.genRes.mapBiprod L M).hom ≫ (biprod.mapIso (asIso (Z.genRes.map (smulHom L (Z.const g))))
        (asIso (Z.genRes.map (smulHom M (Z.const g'))))).hom ≫ (Z.genRes.mapBiprod L M).inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    apply biprod.hom_ext <;> simp [← Functor.map_comp]
  rw [e]; infer_instance

def diagIso : Z.GenIso (L ⊞ M) (L ⊞ M) :=
  haveI := isIso_diag (L := L) (M := M) g g' hg hg'
  GenIso.ofHom (biprod.map (smulHom L (Z.const g)) (smulHom M (Z.const g')))

def diagPair : FlagPair (diagIso (L := L) (M := M) g g' hg hg') 2 where
  fl := .ofBiprod hL hM
  fl' := .ofBiprod hL hM
  gen := Fin.cons (Iso.refl _) (Fin.cons (GenIso.smul L g hg)
    (Fin.cons (diagIso g g' hg hg') finZeroElim))
  gen_ι := Fin.cons ((Z.genRes.map_isZero (isZero_zero _)).eq_of_src _ _)
    (Fin.cons (by
      change (GenIso.smul L g hg).hom ≫ Z.genRes.map biprod.inl =
        Z.genRes.map biprod.inl ≫ (diagIso g g' hg hg').hom
      rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq, GenIso.smul_inv]
      change _ ≫ Z.genRes.map _ = _
      rw [← Functor.map_comp, ← Functor.map_comp, biprod.inl_map])
    (Fin.cons (by
      change (diagIso g g' hg hg').hom ≫ Z.genRes.map (𝟙 _) =
        Z.genRes.map (𝟙 _) ≫ (diagIso g g' hg hg').hom
      simp) finZeroElim))

theorem cls_div_diagPair : ((diagPair hL hM g g' hg hg').div 0).cls = Z.div g hg ∧
    ((diagPair hL hM g g' hg hg').div 1).cls = Z.div g' hg' := by
  constructor
  · refine (GenIso.cls_div_of_smul ((Flag.ofBiprod hL hM).isVB_gr 0) hg ?_).trans (one_nsmul _)
    have h := (diagPair hL hM g g' hg hg').π_grIso_hom 0
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
    rw [← cancel_epi (Z.genRes.map ((Flag.ofBiprod hL hM).π 0)), ← Functor.map_comp,
      ← smulHom_comp, Functor.map_comp]
    exact h.symm
  · refine (GenIso.cls_div_of_smul ((Flag.ofBiprod hL hM).isVB_gr 1) hg' ?_).trans (one_nsmul _)
    have h := (diagPair hL hM g g' hg hg').π_grIso_hom 1
    rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv] at h
    rw [← cancel_epi (Z.genRes.map ((Flag.ofBiprod hL hM).π 1)), ← Functor.map_comp]
    refine h.symm.trans ?_
    change Z.genRes.map (biprod.map (smulHom L (Z.const g)) (smulHom M (Z.const g'))) ≫
      Z.genRes.map (cokernel.π biprod.inl) = Z.genRes.map (cokernel.π biprod.inl ≫ _)
    rw [← Functor.map_comp]
    congr 1
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, cokernel.condition_assoc, cokernel.condition, comp_zero, zero_comp]
    · rw [biprod.inr_map_assoc, smulHom_comp, Category.assoc]
      rfl

end Mixed

example (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] :
    Formalism.BasicNotions.DV.ck ((diagPair (Z := projSpace O 1) (VB.isVB_structureModule _)
      (VB.isVB_structureModule _) p 1 (natCast_ne_zero O p) one_ne_zero).toFPair p) 1
      (c1 (formalTwistingSheaf O 1) (ProjSpace.O1_isLB O 1)) = 1 := by
  obtain ⟨h₀, h₁⟩ := cls_div_diagPair (Z := projSpace O 1) (VB.isVB_structureModule _)
    (VB.isVB_structureModule _) (p : O) 1 (natCast_ne_zero O p) one_ne_zero
  rw [div_of_isUnit _ isUnit_one] at h₁
  simp only [Formalism.BasicNotions.DV.ck, Formalism.BasicNotions.DV.Gk, Fin.sum_univ_two, FlagPair.toFPair, h₀, h₁,
    Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.sub_self, one_mul, zero_add,
    map_zero, LinearMap.zero_apply, add_zero]
  exact capDeg_divP_line O p

end GlobalTheory.Vert.Check
