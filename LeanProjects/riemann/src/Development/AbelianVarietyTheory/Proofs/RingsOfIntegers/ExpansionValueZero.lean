import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace ExpansionValueZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem cst_comp {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {K : Type} (S : Finset K) (a : K → A) :
    cst q z (∑ i ∈ S, a i) = ∑ i ∈ S, cst q z (a i) := by
  simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem cst_zero {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) : cst q z 0 = 0 := by
  simp only [cst, gs_eq q z ⊤ trivial, map_zero]

theorem exists_coeff {A : Type} [CommRing A] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Sp A ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (e : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ' ε')) (ht : t.IsGen)
    (h : FormEq (fun k => e ≫ φ k) ε φ' ε') :
    ∃ a : A, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp A) (z : Z) (J), Good L z J →
      sval s (r ≫ e) z J = cst r z a * (val t r z J).val := by
  obtain ⟨s', hv⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [h U f, mul_inv_cancel])
    (pullMulSec s e (LB.invGen L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
  have le : (⊤ : (Sp A).Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Sp A ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    (((Sp A).presheaf.map (homOfLE le).op).hom (s'.f PEmpty.elim))
  refine ⟨a, fun Z r z J hJ => ?_⟩
  have e₁ := hv Z r z J hJ
  rw [sval_pullMulSec _ _ _ _ _ _ hJ, val_inv, sval_of s' r z J PEmpty.elim (fun k => k.elim)] at e₁
  have e₂ : cst r z a = sval s (r ≫ e) z J * ((val t r z J)⁻¹).val :=
    (congrArg (gs r z ⊤) ha).trans ((gs_res r z le trivial _).trans e₁)
  rw [e₂, Units.inv_mul_cancel_right]

section Geometry

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  show eSec (thickObj R I e G) ≫ pullback.fst G.hom (thick R I e) = _
  simp [eSec]
  rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]

theorem eSec_pG {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem formEq_zero (D : DegPre R) (k : ℕ) (α : D.X) :
    FormEq (fun i => eSec D.P.A ≫ D.famφB α i) (DegPre.famε k) (fun _ : PUnit => eSec D.P.A)
      (fun _ => (k : ℤ) * 1) := by
  intro U _ f
  have a₀ : eSec D.P.A ≫ D.famφB α 0 = eSec D.P.A := Category.comp_id _
  have a₁ : eSec D.P.A ≫ D.famφB α 1 = eSec D.P.A ≫ D.famφB α 2 := by
    have : η[D.P.A] ≫ ((𝟙 D.P.A) * (toUnit _ ≫ D.c α)) = η[D.P.A] ≫ (toUnit _ ≫ D.c α) := by
      rw [MonObj.comp_mul, Category.comp_id]
      have : η[D.P.A] = (1 : 𝟙_ _ ⟶ D.P.A) := by simp [Hom.one_def]
      rw [this, _root_.one_mul]
    exact congrArg (fun z => z.left) this
  have a₃ : eSec D.P.A ≫ D.famφB α 3 = eSec D.P.A := by
    have : η[D.P.A] ≫ (toUnit D.P.A ≫ η[D.P.A]) = η[D.P.A] := by
      rw [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
    exact congrArg (fun z => z.left) this
  rw [Fin.prod_univ_four, Fintype.prod_unique]
  simp only [a₀, a₁, a₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, DegPre.famε, Matrix.cons_val]
  module

theorem exists_value (D : DegPre R) (k : ℕ) (α : D.X) (g : D.SecB k α) :
    ∃ a : R, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J →
      sval g (r ≫ eSec D.P.A) z J = cst r z a * (val (L := D.P.L) D.rig r z J ^ k).val := by
  obtain ⟨a, ha⟩ := exists_coeff (A := R) D.P.isLB g (eSec D.P.A) (GeneratorPullback.powGen D.P.L _ _ D.rig k)
    (powGen_isGen _ _ _ _ D.rig_gen k) (formEq_zero D k α)
  exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (by rw [val_pow])⟩

end Geometry

section Congruence

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

variable (I G) in
omit [IsDomain R] in

abbrev unitE (e : ℕ) : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left := eSec (thickObj R I e G)

theorem wv_rig (e : ℕ) (z : Sp (R ⧸ I ^ (e + 1))) {J J'} (hJ : Good D.toPre.P.L z J) (hJ' : Good U.LG.L z J') :
    wv U e (unitE I G e) z (J (unitE I G e ≫ pGl U e)) (J' (thick R I e ≫ eSec G)) *
      val (L := U.LG.L) U.LG.rig (thick R I e) z J' = val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J := by
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  rw [hp]
  have m₁ : z ∈ unitE I G e ⁻¹ᵁ
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => J' (thick R I e ≫ eSec G))) :=
    ⟨mem_pull.2 ((congrArg (fun q => q z ∈ D.toPre.P.L.U (J (thick R I e ≫ eSec D.toPre.P.A))) hp).mpr (hJ _)),
      mem_pull.2 ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))⟩
  have m₂ : z ∈ thick R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => J' (thick R I e ≫ eSec G)) :=
    mem_pull.2 (hJ' (thick R I e ≫ eSec G))
  have m₃ : z ∈ thick R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U
      (fun _ => J (thick R I e ≫ eSec D.toPre.P.A)) := mem_pull.2 (hJ (thick R I e ≫ eSec D.toPre.P.A))
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => J (thick R I e ≫ eSec D.toPre.P.A),
    fun _ => J' (thick R I e ≫ eSec G)) (_ ⊓ _ ⊓ _) (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _)
    (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))).symm.trans (W.trans (gm_rp₁ _ z _ _ _ (by exact ⟨⟨m₁, m₂⟩, m₃⟩) _))

theorem value_sub_sum_mem (e k : ℕ) (σ : H0 U.LG.L k) (g : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hE : U.ExpandsAt e k σ g) (x : R)
    (hx : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval σ (r ≫ eSec G) z J = cst r z x * (val (L := U.LG.L) U.LG.rig r z J ^ k).val)
    (a : D.toPre.X → R)
    (ha : ∀ α (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.toPre.P.L z J →
      sval (g α) (r ≫ eSec D.toPre.P.A) z J = cst r z (a α) * (val (L := D.toPre.P.L) D.toPre.rig r z J ^ k).val) :
    ∃ S : Finset D.toPre.X, ∀ T : Finset D.toPre.X, S ⊆ T → x - ∑ α ∈ T, a α ∈ I ^ (e + 1) := by
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ g hE
  have hp : unitE I G e ≫ pGl U e = thick R I e ≫ eSec D.toPre.P.A := eSec_pG I (U.gt e)
  have hf : unitE I G e ≫ fGl I G e = thick R I e ≫ eSec G := eSec_fstG I e G
  have hc : ∀ (z : Sp (R ⧸ I ^ (e + 1))) (c : R),
      cst (thick R I e) z c = cst (𝟙 _) z (Ideal.Quotient.mk (I ^ (e + 1)) c) := fun z c => H1.gs_spec _ z c
  refine ⟨S, fun T hT => ?_⟩
  rw [← Ideal.Quotient.eq]
  refine H1.cst_ext fun z => ?_
  rw [← hc, ← hc, cst_sum]
  choose J hJ using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
  choose J' hJ' using fun ψ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have hJ' : Good U.LG.L z J' := hJ'
  obtain ⟨h₀, h₁⟩ := hS _ (unitE I G e) z J hJ
  have h₂ := h₁ (J' (thick R I e ≫ eSec G))
    ((congrArg (fun q => q z ∈ U.LG.L.U (J' (thick R I e ≫ eSec G))) hf).mpr (hJ' _))
  have hs : sv U k σ (unitE I G e ≫ fGl I G e) z (J' (thick R I e ≫ eSec G)) =
      cst (thick R I e) z x * (val (L := U.LG.L) U.LG.rig (thick R I e) z J' ^ k).val := by
    rw [hf]
    exact (sval_of σ _ z J' (fun _ => J' (thick R I e ≫ eSec G)) (fun _ => by rw [Category.comp_id])).symm.trans
      (hx _ _ z J' hJ')
  have ht : ∀ α, val (tG U e α) (unitE I G e) z J = 1 := fun α => by
    have := (val_pull hJ (tG U e α) (unitE I G e) (𝟙 _)).symm.trans
      ((val_corr hJ ((U.gt e).t_unit α) _).trans (val_one _))
    rwa [Category.id_comp] at this
  have hg : ∀ α, sval (g α) (unitE I G e ≫ pGl U e) z J =
      cst (thick R I e) z (a α) * (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).val := fun α => by
    rw [hp]; exact ha α _ _ z J hJ
  have hw := wv_rig U e z hJ hJ'
  refine (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) z J ^ k).mul_left_inj.1 ?_
  rw [Finset.sum_mul, ← Finset.sum_subset hT (fun α _ hα => (hg α).symm.trans (h₀ α hα))]
  rw [hs, mul_left_comm, ← Units.val_mul, ← mul_pow] at h₂
  refine Eq.trans (by rw [← hw]) (h₂.trans (Finset.sum_congr rfl fun α _ => ?_))
  rw [ht, hg, Units.val_one, _root_.mul_one]

end Congruence

section Value

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F} in
theorem le_val_of_mem_pow {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    (n : ℕ) {c : V} (hc : c ∈ maximalIdeal V ^ n) :
    (((n : ℕ) : ℚ) : WithTop ℚ) ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hc
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hc
  have h : HasVal ϖ (algebraMap V (FractionRing V) (ϖ ^ n)) (n : ℤ) := ⟨1, by simp⟩
  rw [map_mul, map_mul, AddValuation.map_mul, hv _ _ h]
  simpa using le_add_of_nonneg_left (GC.v_alg_nonneg hϖ hv b)

end Value

end ExpansionValueZero

end GlobalTheory
