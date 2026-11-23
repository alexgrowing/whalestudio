import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermuteStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClosedImmersionDensePointsStatement
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionSection

theorem exists_field_point {X : Scheme.{0}} (w : X) :
    ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply w _⟩

def trivSec {X : Scheme.{0}} {W : X.Opens} (f : Γ(X, W)) : LB.Sec (Inh.trivLB W.toScheme) where
  f := fun _ => (W.ι.appLE W ⊤ W.ι_preimage_self.ge).hom f
  compat := fun _ _ => (_root_.one_mul _).symm

theorem crd_trivSec {X : Scheme.{0}} {W : X.Opens} {J : Type} (f : J → Γ(X, W)) {R : Type} [CommRing R]
    (y : Sp R ⟶ W.toScheme) :
    Crd (Inh.trivLB W.toScheme) (fun j => trivSec (f j)) y (fun j => valR (y ≫ W.ι) W (f j)) :=
  ⟨PUnit.unit, 1, GlobalTheory.Points.le_preimage_top y, fun j =>
    (GlobalTheory.Points.valR_appLE y W.ι _ (GlobalTheory.Points.le_preimage_top y) (f j)).symm.trans (_root_.one_mul _).symm⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_closed (hj : JacobsonSpace M.Z) (z : M.Z) :
    ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ z ⤳ z' ∧ S.HH M z' = S.HH M z := by
  obtain ⟨z', ⟨h1, h2⟩, h3⟩ := nonempty_inter_closedPoints
    (Z := {z' | S.supI M z ⊆ S.supI M z'} ∩ closure {z}) ⟨z, fun _ h => h, subset_closure rfl⟩
    ((OpenPart.isOpen_supI_subset z).isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : z ⤳ z' := specializes_iff_mem_closure.2 h2
  refine ⟨z', h3, hs, congrArg AddSubgroup.closure (Set.Subset.antisymm (fun _ h => ?_) h1)⟩
  exact RatModel.Div.of_specializes h hs

theorem exists_functions (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (z' : M.Z) {a : S.Gam}
    (ha : a ∈ S.HH M z') :
    ∃ (W : M.Z.Opens) (l : Q.Λ) (_ : W ≤ Q.W l) (t : Ω) (i : S.J) (f : S.J → Γ(M.Z, W)), z' ∈ W ∧ t ≠ 0 ∧
      (∀ w ∈ W, S.supI M z' ⊆ S.supI M w) ∧ (∀ k, valF M.pt W (f k) = (Q.B l k ⬝ᵥ S.ev a) / t) ∧
      ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K), ⊤ ≤ y ⁻¹ᵁ W → y ≫ M.s = spMap ψ →
        ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y W (f k)) j ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hB.ov.div z'
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z' x₀ hx₀ a ha
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z'))
  set d := (fun j => algebraMap o Ω (S.proj (S.TT M z') 0 j i)) ⬝ᵥ S.ev a with hd
  let V : M.Z.Opens := ⟨(⋂ k, {w | (Q.B l k ⬝ᵥ S.ev a) / S.th x₀ ∈ M.O w}) ∩ {w | S.th x₀ / d ∈ M.O w} ∩
      {w | S.supI M z' ⊆ S.supI M w},
    ((isOpen_iInter_of_finite fun _ => M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)).inter
      (OpenPart.isOpen_supI_subset z')⟩
  have hz : z' ∈ V ⊓ Q.W l := ⟨⟨⟨Set.mem_iInter.2 fun k => h1 _ (by
    rw [Q.basis l z' hl]; exact Submodule.subset_span ⟨k, rfl⟩), h3⟩, fun _ h => h⟩, hl⟩
  have hne : ((V ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty := ⟨z', hz⟩
  choose f hf using fun k => (RatModel.mem_ringOn_iff_exists hne (x := (Q.B l k ⬝ᵥ S.ev a) / S.th x₀)).1
    (RatModel.mem_ringOn.2 fun w hw => Set.mem_iInter.1 hw.1.1.1 k)
  obtain ⟨u, hu⟩ := (RatModel.mem_ringOn_iff_exists hne (x := S.th x₀ / d)).1
    (RatModel.mem_ringOn.2 fun w hw => hw.1.1.2)
  refine ⟨V ⊓ Q.W l, l, inf_le_right, S.th x₀, i, f, hz, hx₀.1, fun w hw => hw.1.2, hf, ?_⟩
  have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K) (hy : ⊤ ≤ y ⁻¹ᵁ (V ⊓ Q.W l)),
      y ≫ M.s = spMap ψ → CrdCalc.valHom y _ hy (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
        ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y _ (f k)) j := by
    intro K _ y ψ hy hψ
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_sum, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_over M.s ψ y hψ _ hy]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ hy]
    rfl
  have hone : u * (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
      ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = 1 := by
    have hp := M.top_le_preimage_pt hne
    refine M.res_injective _ hne ?_
    rw [map_one, map_mul, M.res_apply, hu]
    have e := key Ω M.pt _ hp M.pt_s
    have e2 : (fun k => valR M.pt _ (f k)) = (S.th x₀)⁻¹ • (Q.B l).mulVec (S.ev a) := by
      funext k
      exact (hf k).trans (by rw [div_eq_inv_mul]; rfl)
    have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
    rw [e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e3, Matrix.one_mulVec] at e
    have e4 : ∑ j, algebraMap o Ω (S.proj (S.TT M z') 0 j i) * ((S.th x₀)⁻¹ • S.ev a) j = (S.th x₀)⁻¹ * d := by
      rw [hd, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [M.res_apply, ← valR_of_field, CrdCalc.valR_eq _ _ hp, e, e4]
    have := hx₀.1
    field_simp
  intro K _ y ψ hy hψ
  rw [← key K y ψ hy hψ]
  have := congrArg (CrdCalc.valHom y _ hy) hone
  rw [map_mul, map_one] at this
  exact right_ne_zero_of_mul_eq_one this

def torsSec (Q : Clos ρ M U₀ EE) (a : S.Gam) : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
  pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
    have h : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
    rw [Category.assoc, Category.id_comp]
    exact (congrArg (Q.u₀ ≫ ·) h).trans (Category.comp_id _))

theorem torsSec_over (Q : Clos ρ M U₀ EE) (a : S.Gam) : torsSec Q a ≫ Q.a₀ ≫ Q.P.hom = U₀.ι := by
  rw [Q.cart.w, torsSec, pullback.lift_snd_assoc, Category.id_comp]

theorem agree (Q : Clos ρ M U₀ EE) (a : S.Gam) {W : M.Z.Opens} (h : W.toScheme ⟶ Q.P.left)
    (hh : h ≫ Q.P.hom = W.ι) (e : Sp Ω ⟶ W.toScheme) (he : e ≫ W.ι = M.pt) (e₀ : Sp Ω ⟶ U₀.toScheme)
    (he₀ : e₀ ≫ U₀.ι = M.pt) (hg : e ≫ h = e₀ ≫ torsSec Q a ≫ Q.a₀) {K : Type} [Field K]
    (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
    (h1 : x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι)
    (h2 : x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left) : x ≫ h = x' ≫ Q.a₀ := by
  have lift : ∀ {F : Type} [Field F] (y : Sp F ⟶ W.toScheme) (y₀ : Sp F ⟶ U₀.toScheme), y ≫ W.ι = y₀ ≫ U₀.ι →
      ∃ v : Sp F ⟶ (W ⊓ U₀).toScheme, v ≫ M.Z.homOfLE inf_le_left = y ∧ v ≫ M.Z.homOfLE inf_le_right = y₀ := by
    intro F _ y y₀ hy
    have hr : Set.range (y ≫ W.ι) ⊆ Set.range (W ⊓ U₀).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      exact ⟨(y w).2, hy ▸ (y₀ w).2⟩
    refine ⟨IsOpenImmersion.lift (W ⊓ U₀).ι _ hr, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
    · rw [← cancel_mono U₀.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, hy]
  obtain ⟨v, hv, hv₀⟩ := lift e e₀ (he.trans he₀.symm)
  have hvι : v ≫ (W ⊓ U₀).ι = M.pt := by
    rw [← Scheme.homOfLE_ι M.Z (inf_le_left : W ⊓ U₀ ≤ W), ← Category.assoc, hv, he]
  have : IsDominant (v ≫ (W ⊓ U₀).ι) := hvι ▸ M.isDominant_pt
  have : IsDominant v := IsDominant.of_comp_of_isOpenImmersion v (W ⊓ U₀).ι
  have := Q.proper
  have E : M.Z.homOfLE (inf_le_left : W ⊓ U₀ ≤ W) ≫ h =
      M.Z.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀) ≫ torsSec Q a ≫ Q.a₀ := by
    refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ v ?_
    · simp only [Category.assoc, hh, torsSec_over, Scheme.homOfLE_ι]
    · rw [← Category.assoc, hv, ← Category.assoc, hv₀, hg]
  obtain ⟨y, hy, hy₀⟩ := lift x (x' ≫ pullback.snd _ _) (by rw [h1, Category.assoc])
  have hx' : (x' ≫ pullback.snd _ _) ≫ torsSec Q a = x' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, torsSec, pullback.lift_fst, h2, Category.assoc]
    · rw [Category.assoc, torsSec, pullback.lift_snd, Category.comp_id]
  rw [← hy, Category.assoc, E, ← Category.assoc, hy₀, ← Category.assoc, hx']

theorem crd_generic (Q : Clos ρ M U₀ EE) (a : S.Gam) (l : Q.Λ) {t : Ω} (ht : t ≠ 0)
    (x : Sp Ω ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (hx : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt)
    (hc : Crd Q.O1 Q.st (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a)) :
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x (fun k => (Q.B l k ⬝ᵥ S.ev a) / t) := by
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x
  have h1 := Q.rel l Ω x w hw
  rw [hx] at h1
  obtain ⟨c, hc⟩ := CrdCalc.crd_unique h1 hc
  have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
  have e4 := mul_eq_one_comm.1 e3
  have e5 : S.ev a = (c : Ω) • ((Q.c l).map (valR M.pt (Q.W l))).mulVec w := funext hc
  have e6 : (Q.B l).mulVec (S.ev a) = (c : Ω) • w := by
    rw [e5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec]
  have := CrdCalc.crd_smul ((Units.mk0 t ht)⁻¹ * c) hw
  convert this using 2 with k
  have e7 : Q.B l k ⬝ᵥ S.ev a = c * w k := congrFun e6 k
  rw [e7, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_inv_mul, _root_.mul_assoc]

theorem exists_section : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀ := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q z a ha
  obtain ⟨z', hcl, hs, hH⟩ := exists_closed (S := S) hB.jac z
  obtain ⟨W, l, hle, t, i, f, hz', ht, hsup, hf, hkey⟩ := exists_functions hB Q z' (hH ▸ ha)
  have liftPt : ∀ {X : Scheme.{0}} (y : Sp Ω ⟶ X) (V : X.Opens), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ e : Sp Ω ⟶ V.toScheme, e ≫ V.ι = y := fun y V hV =>
    ⟨IsOpenImmersion.lift V.ι y (by rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hV),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨e, he⟩ := liftPt M.pt W (M.top_le_preimage_pt ⟨z', hz'⟩)
  obtain ⟨e₀, he₀⟩ := liftPt M.pt U₀ (M.top_le_preimage_pt hB.ov.ne)
  have hp : (e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom = M.pt := by
    simp only [Category.assoc, torsSec_over, he₀]
  obtain ⟨e', he'⟩ := liftPt (e₀ ≫ torsSec Q a ≫ Q.a₀) (Q.P.hom ⁻¹ᵁ Q.W l) (by
    change ⊤ ≤ ((e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom) ⁻¹ᵁ Q.W l
    rw [hp]
    exact M.top_le_preimage_pt (Q.ne l))
  have hp' : e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt := by rw [← Category.assoc, he', hp]
  have hc : Crd Q.O1 Q.st (e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a) := by
    rw [he', ← Category.assoc]
    refine Q.crd Ω _ _ ?_
    rw [Category.assoc, torsSec, pullback.lift_fst, ← Category.assoc, Q.u₀_pt e₀ he₀]
    exact (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 Ω S.R.val.toRingHom a
  have hval : ∀ {K : Type} [Field K] (y : Sp K ⟶ W.toScheme), ∃ ψ : o →+* K, (y ≫ W.ι) ≫ M.s = spMap ψ ∧
      ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
        ((Q.c l).map (valR (y ≫ W.ι) (Q.W l))).mulVec (fun k => valR (y ≫ W.ι) W (f k)) j ≠ 0 := fun y =>
    ⟨(Spec.preimage ((y ≫ W.ι) ≫ M.s)).hom, (Spec.map_preimage _).symm,
      hkey _ _ _ (fun w _ => (y w).2) (Spec.map_preimage _).symm⟩
  have hcov : ⨆ j, nonzeroLocus (trivSec (f j)) = ⊤ := by
    refine top_unique fun w _ => ?_
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, -, hψ⟩ := hval y
    have : ∃ k, valR (y ≫ W.ι) W (f k) ≠ 0 := by
      by_contra hn
      push_neg at hn
      simp [hn, Matrix.mulVec, dotProduct] at hψ
    obtain ⟨k, hk⟩ := this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (CrdCalc.top_le_iff y _).1
      ((CrdCalc.crd_isUnit_iff k (crd_trivSec f y)).1 (isUnit_iff_ne_zero.2 hk))⟩
  have : IsDominant (e ≫ W.ι) := he ▸ M.isDominant_pt
  have hdom : IsDominant e := IsDominant.of_comp_of_isOpenImmersion e W.ι
  obtain ⟨g, hg, hge, hgc⟩ := GlobalTheory.T.exists_factor_closedImmersion_dense_points Γ(M.Z, Q.W l) _ W.toScheme
    ((Q.P.hom ∣_ Q.W l) ≫ (Q.aff l).isoSpec.hom) (M.Z.homOfLE hle ≫ (Q.aff l).isoSpec.hom) _ _ S.J (Q.σ l)
    (fun j => trivSec (f j)) (LB.isLB_pull Q.isLB _) (Inh.trivLB_isLB _) (Q.imm l) hcov Ω Unit (fun _ => e)
    (fun _ => e') (by rw [Set.iUnion_const]; exact hdom.denseRange) (fun _ => ⟨by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (Q.W l).ι, Category.assoc, morphismRestrict_ι, hp', Category.assoc, Scheme.homOfLE_ι, he],
      _, crd_trivSec f e, by
      have := crd_generic Q a l ht e' hp' hc
      convert this using 2 with k
      rw [he]
      exact hf k⟩)
  have hg' : g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = W.ι := by
    rw [← Category.assoc, cancel_mono] at hg
    rw [← morphismRestrict_ι, ← Category.assoc, hg, Scheme.homOfLE_ι]
  have hG : Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Set.range Q.G.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, hψ, hne⟩ := hval y
    have h1 := Q.rel l K _ _ (hgc K y _ (crd_trivSec f y))
    rw [Category.assoc y g (_ ≫ _), hg'] at h1
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    have h2 := (OpenPart.le_nonzeroLocus_iff hφ (x := (y ≫ g) ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (ψ := ψ) (by
      rw [← hψ, ← hg']; simp only [Category.assoc]) h1).2 hne
    simp only [Clos.G, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    refine ⟨z', hcl, W, hsup, i, φ, hφ, ?_, (CrdCalc.top_le_iff _ _).1 h2⟩
    change (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (y (IsLocalRing.closedPoint K)) ∈ W
    rw [hg']
    exact (y _).2
  have hfac := IsOpenImmersion.lift_fac Q.G.ι _ hG
  refine ⟨W, IsOpenImmersion.lift Q.G.ι _ hG, hs.mem_open W.isOpen hz', ?_, fun K _ x x' h1 h2 => ?_⟩
  · rw [← Category.assoc, hfac, Category.assoc, hg']
  · rw [hfac]
    refine agree Q a _ (by rw [Category.assoc, hg']) e he e₀ he₀ ?_ x x' h1 h2
    rw [← Category.assoc, hge (), he']

end GlobalTheory.ZH.TorsionSection
end
