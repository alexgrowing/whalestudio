import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.ExactTerm
open TWM TWO

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem comp_generic_injective :
    Function.Injective fun q : (TO hϖ hv).left ⟶ D.toPre.P.A.left => (ιS hϖ hv).left ≫ q := fun f g h => by
  have : IsProper D.toPre.P.A.hom := D.toPre.P.isAb.proper
  have e : f ≫ D.toPre.P.A.hom = g ≫ D.toPre.P.A.hom := by
    obtain ⟨a, ha⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (f ≫ D.toPre.P.A.hom)
    obtain ⟨b, hb⟩ := Spec.map_surjective (R := CommRingCat.of V) (S := CommRingCat.of (Ov v)) (g ≫ D.toPre.P.A.hom)
    have e₁ : a ≫ CommRingCat.ofHom (algebraMap (Ov v) F) = b ≫ CommRingCat.ofHom (algebraMap (Ov v) F) :=
      Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_comp, ha, hb]
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ D.toPre.P.A.hom) h).trans (Category.assoc _ _ _)))
    have e₂ : a = b := CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
      (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x))
    exact ha.symm.trans ((congrArg Spec.map e₂).trans hb)
  have hU : ValuativeCriterion.Uniqueness D.toPre.P.A.hom := IsSeparated.valuativeCriterion _
  let S : ValuativeCommSq D.toPre.P.A.hom :=
    { R := Ov v, K := F, i₁ := (ιS hϖ hv).left ≫ f, i₂ := f ≫ D.toPre.P.A.hom, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((hU S).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

theorem exists_unit_const {K : Type} [Fintype K] {φ : K → ((TO hϖ hv).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U),
      ∏ k, h ((ιS hϖ hv).left ≫ φ k) ^ ε k = 1) :
    ∃ u : F, v u = 0 ∧ ∀ z J, Good D.toPre.P.L z J → (val t (ιS hϖ hv).left z J).val = cst F z u := by
  have hI : IsIso (Scheme.Hom.appTop (𝟙 (TO hϖ hv).left)) :=
    inferInstanceAs (IsIso (Scheme.Hom.app (𝟙 (TO hϖ hv).left) ⊤))
  obtain ⟨a, ha⟩ := H1.exists_const D.toPre.P.L D.toPre.P.isLB (𝟙 _) (ConcreteCategory.bijective_of_isIso _).2 t ht
    (fun U _ h => by
      have := hf U (Function.extend (fun q => (ιS hϖ hv).left ≫ q) h 1)
      simpa only [(comp_generic_injective hϖ hv).extend_apply] using this)
  have hu : IsUnit a := (TO hϖ hv).left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' D.toPre.P.isLB y
    have q := ha _ (𝟙 _) y J hJ
    rw [Category.comp_id] at q
    exact (congrArg IsUnit (q.trans (gs_eq (𝟙 _) y ⊤ trivial a))).mp (Units.isUnit _)
  refine ⟨ιr (v := v) a, v_unit v (hu.map (Scheme.ΓSpecIso (CommRingCat.of (Ov v))).hom.hom).unit, fun z J hJ => ?_⟩
  rw [ha _ _ z J hJ, Category.comp_id, ← Category.id_comp (ιS hϖ hv).left]
  exact (gs_pull (𝟙 _) (ιS hϖ hv).left z ⊤ trivial a).symm.trans (congrArg (gs (𝟙 _) z ⊤) (appTop_specMap _ a))

theorem cst_gF {Z : Scheme.{0}} (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (c : V) :
    Geo.Tor.cst ((ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom) z c = gs ρ z ⊤ (gF D.toPre F (algVF c)) := by
  have e : (ρ ≫ (DegPre.prB D.toPre F).left) ≫ D.toPre.P.A.hom =
      (ρ ≫ (fst (TF (R := V) F) D.toPre.P.A).left) ≫ Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V))) := by
    rw [← TF_hom, Category.assoc, Category.assoc, Over.w, Over.w]
  rw [e]
  refine (gs_pull _ _ z ⊤ trivial _).symm.trans (Eq.trans ?_ (gs_pull ρ _ z ⊤ trivial _).symm)
  refine congrArg (gs _ z ⊤) ((appTop_specMap _ _).trans ?_)
  simp

include hϖ hv in

theorem vge_iff {k : ℕ} {χ : D.toPre.X} (b : D.toPre.SecB k χ)
    (hb : ∀ σ : D.toPre.SecB k χ, ∃ c : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ D.toPre.P.A.left) (z : Z) (J),
      Good D.toPre.P.L z J → sval σ r z J = Geo.Tor.cst (r ≫ D.toPre.P.A.hom) z c * sval b r z J)
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k))) {r : ℚ} (hs : VGe D F v k χ s r) :
    ∃ a : F, (r : WithTop ℚ) ≤ v a ∧ (∀ r' : ℚ, (r' : WithTop ℚ) ≤ v a → VGe D F v k χ s r') ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval s ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := by
  have hL := D.toPre.P.isLB
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := hs
  choose c hc using fun i => hb (σ i)
  have key : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s ρ z J = gs ρ z ⊤ (gF D.toPre F (∑ i, a i * algVF (c i))) *
        sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J := fun Z ρ z J hJ => by
    rw [SectionScalarValuation.sval_lin (fun i => gF D.toPre F (a i)) σF (fun j => hsum j) ρ z hJ, map_sum,
      SectionScalarValuation.gs_sum ρ z ⊤ trivial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← SectionScalarValuation.secScal_sval (hscal i) ρ z hJ, hc i _ _ z J hJ, cst_gF, map_mul, gs_mul ρ z ⊤ trivial, _root_.mul_assoc]
  refine ⟨∑ i, a i * algVF (c i), AddValuation.map_le_sum v fun i _ => ?_, fun r' hr' => ?_, key⟩
  · rw [AddValuation.map_mul]
    exact le_add_of_le_of_nonneg (hva i) (v_of_V v hϖ hv (c i)).1
  · let bF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F χ) (DegPre.famε k)) :=
      VVRank.pullTo b (DegPre.prB D.toPre F).left fun i => (GC.famφ_eq _ _ _ i).symm
    refine ⟨1, fun _ => _, fun _ => b, fun _ => bF, fun _ => SectionScalarValuation.secScal_of_sval hL fun y J hJ =>
      (VVRank.sval_pullTo _ _ _ _ y hJ).symm, fun _ => hr', fun j => ?_⟩
    rw [Fin.sum_univ_one]
    refine sec_ext_val hL (s' := SecOps.secScale (gF D.toPre F _) bF) (fun y J hJ => ?_) j
    have hm := hJ.mem (DegPre.famφ D.toPre F χ) (𝟙 _)
    exact (key _ _ y J hJ).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) (gs_res _ y le_top hm _)
      (VVRank.sval_pullTo _ _ _ _ y hJ))).symm

theorem v_coef {χ : D.toPre.X} (b : D.toPre.SecB 1 χ) (s : Fam D.toPre F 1) (a : F)
    (hs : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J), Good D.toPre.P.L z J →
        sval (s.s χ) ρ z J = gs ρ z ⊤ (gF D.toPre F a) * sval b (ρ ≫ (DegPre.prB D.toPre F).left) z J)
    (g : GtPtF D.toPre F) (m : TO hϖ hv ⟶ D.toPre.P.A) (hm : ιS hϖ hv ≫ m = g.b)
    (hu : ∀ z J, Good D.toPre.P.L z J → IsUnit (sval b (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ m.left) z J))
    (w : Frm D.toPre F 1 g.b) (hw : w.IsGen) {l ω : ℚ} (hl : GenV hϖ hv (g.s χ) l) (hω : GenV hϖ hv w ω) :
    v (coef s g w χ) = v a + l + ω := by
  have hL := D.toPre.P.isLB
  obtain ⟨t₀, h₀, v₀⟩ := exists_gen_of_isUnit hL b m.left hu
  obtain ⟨φ₁, e₁, t₁, h₁, x₁, hx₁, v₁⟩ := hl
  obtain ⟨φ₂, e₂, t₂, h₂, x₂, hx₂, v₂⟩ := hω
  have hm' : (ιS hϖ hv).left ≫ m.left = g.b.left := congrArg (fun q => q.left) hm
  obtain ⟨u, hu₀, vu⟩ := exists_unit_const hϖ hv
    (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ (LB.mulGen _ _ _ _ _ t₀ t₁) t₂) (LB.invGen _ _ _
      (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig (TO hϖ hv).hom)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ h₀ h₁) h₂)
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.toPre.rig_gen _))) (fun U _ h => by
      have p₀ := SectionScalarValuation.prod_famB D.toPre g.b χ 1 h
      have p₁ := prod_gt g.b χ h
      have p₂ := CoefBasic.prod_line 1 g.b h
      have p₃ : (ιS hϖ hv).left ≫ (TO hϖ hv).hom ≫ eSec D.toPre.P.A = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Category.assoc, Over.w]; rfl
      simp only [e₁] at p₁
      simp only [e₂] at p₂
      simp only [← hm', Category.assoc] at p₀
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, p₀, p₁, p₂, p₃]
      rw [mul_comm g.b, hm']
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one, SectionScalarValuation.cQ, cP]
      module)
  have e : coef s g w χ = a * x₁ * x₂ * u := CoefBasic.coef_eq fun z J hJ => by
    have q := vu z J hJ
    rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, Over.w, Units.val_mul, Units.val_mul, Units.val_mul,
      v₀ _ _ z J hJ, hm', Units.mul_inv_eq_iff_eq_mul] at q
    replace q : _ = _ * (rigV D.toPre (TF (R := V) F).hom z J).val := q
    have q₁ : gs (lift (𝟙 (TF (R := V) F)) g.b).left z ⊤ (gF D.toPre F a) = cst F z a := by
      refine (gs_pull _ (fst (TF (R := V) F) D.toPre.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    rw [hs _ _ z J hJ, v₁ z J hJ, v₂ z J hJ, q₁, ← Over.comp_left, lift_snd, pow_one]
    simp only [CoefBasic.cst_eq, map_mul] at q ⊢
    exact Eq.symm (by linear_combination (CoefBasic.cstH z a * CoefBasic.cstH z x₁ * CoefBasic.cstH z x₂) * q)
  rw [e, AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_mul, hx₁, hx₂, hu₀, add_zero]

theorem exact_term_after_torsion : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  intro hL _ _ _ _ V _ _ _ _ _ ϖ hϖ D Q hQ F _ _ _ v hv ϑ hϑ n hn hnV g χ
  obtain ⟨b, hb, hb'⟩ := exists_secB_good hL.1 D.toPre χ
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := vge_iff hϖ hv b hb (ϑ.s χ) (hϑ.1 χ)
  have ha : v a = ((Q χ : ℚ) : WithTop ℚ) := by
    simp only [Nat.cast_one, div_one, zero_add] at ha₁
    refine le_antisymm (not_lt.1 fun h => ?_) ha₁
    obtain ⟨q, hq₁, hq₂⟩ := WithTop.lt_iff_exists_coe_btwn.1 h
    refine hϑ.2 (q - Q χ) (sub_pos.2 (WithTop.coe_lt_coe.1 hq₁)) ((n1a V ϖ hϖ D Q hQ F v hv 1 le_rfl {χ}
      (fun χ' => ⟨χ, Finset.mem_singleton_self _, χ' - χ, by simp⟩) ϑ _).2 fun α hα => ?_)
    rw [Finset.mem_singleton] at hα
    subst hα
    refine ha₂ _ ?_
    simpa using hq₂.le
  have : IsAlgClosed (ResidueField (Ov v)) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (Ov v) F
  obtain ⟨m, hm⟩ := exists_liftO hϖ hv g.b
  let ρ : Over.mk (Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ (TO hϖ hv).hom) ⟶ TO hϖ hv := Over.homMk _ rfl
  have hK : (n : ResidueField (Ov v)) ≠ 0 := by
    have := (hnV.map ((residue (Ov v)).comp (fO v hϖ hv))).ne_zero
    rwa [map_natCast] at this
  obtain ⟨x₀, hx₀, hu⟩ := hb' (ResidueField (Ov v)) _ n hn hK (ρ ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.1.mulN _ D.toPre.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : TO hϖ hv ⟶ D.toPre.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue (Ov v))) ≫ x.left = x₀.left :=
    exists_torsion_lift (Ov v) D.toPre.P.A n (TO hϖ hv).hom x₀ hx₀
  have ex' : ρ ≫ x = x₀ := Over.OverMorphism.ext ex
  letI := TorusExt.gtGroup D.toPre F
  obtain ⟨h, hh₁, hh₂⟩ := TorusExt.exists_nsmul_eq_of_pow_eq (n := n) (by omega) (0 : GtPtF D.toPre F)
    (b := ιS hϖ hv ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one, TorusExt.zero_b])
  refine ⟨h, 0, g + h, (TorusExt.isZero_iff_eq _).2 rfl, (TorusExt.isNsmul_iff_eq _ _ _).2 hh₂.symm,
    (TorusExt.isAdd_iff_eq _ _ _).2 rfl, fun w l ω hw hl hω => ?_⟩
  rw [v_coef hϖ hv b ϑ a ha₃ (g + h) (m * x) (by rw [MonObj.comp_mul, hm, TorusExt.add_b, hh₁]) (fun z J hJ => by
    have q := hu z J hJ
    rw [← ex', ← MonObj.comp_mul] at q
    exact q) w hw (hl χ) hω, ha]
  rfl

end GlobalTheory.UT.ExactTerm
end
