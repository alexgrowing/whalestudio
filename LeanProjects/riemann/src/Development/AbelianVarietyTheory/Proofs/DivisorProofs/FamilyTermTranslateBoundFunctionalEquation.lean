import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrVal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TranslBound

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing GlobalTheory.FormalValue

section FE

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem exists_fe_val (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) :
    ∃ (eB : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)))
      (c₀ : FractionRing V), HasVal ϖ c₀ (k * Q mu + bOf D.toPre Q mu α) ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
        Good D.toPre.P.L z J → sval (s.s (α + k • mu)) ρ z J = sval (s.s α) (ρ ≫ (DegPre.trF D.toPre F mu).left) z J *
          ((val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val *
            gs ρ z ⊤ (gF D.toPre F (algebraMap (FractionRing V) F c₀))) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  refine ⟨eB, c₀, hc₀, ?_⟩
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2,
      gs_gF_zF, gs_scal_jFK, Category.id_comp, ← hc]
    exact mul_comm _ _)
  intro Z ρ z J hJ
  rw [← hval_u Z ρ z J hJ]
  exact (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hcorr) Z ρ z J hJ

end FE

section Dual

theorem gs_const {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (z : Sp A) (a : R) :
    gs (spMap f) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = toStkA z (f a) := by
  have e := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  exact (gs_eq _ z ⊤ trivial _).trans (congrArg ((Sp A).presheaf.germ ⊤ z trivial).hom e.symm)

theorem redE_surjective (A : Type) [CommRing A] : Function.Surjective (redE A) := by
  intro y
  have h := range_comap_of_surjective _ (TrivSqZeroExt.fstHom A A A).toRingHom TrivSqZeroExt.fst_surjective
  have hy : (show PrimeSpectrum (DualNumber A) from y) ∈
      PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom A A A).toRingHom : Set (DualNumber A)) := fun x hx => by
    have h0 : x.fst = 0 := hx
    have h2 : x * x = 0 := by ext <;> simp [h0]
    exact ((show PrimeSpectrum (DualNumber A) from y).2.mem_or_mem (h2 ▸ Ideal.zero_mem _)).elim id id
  rw [← h] at hy
  exact hy

theorem top_le_of_redE {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp (DualNumber A) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (redE A ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := fun y _ => by
  obtain ⟨w, rfl⟩ := redE_surjective A y
  exact h (Set.mem_univ w)

theorem redE_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    redE B ≫ spMap (dualMap f) = spMap f ≫ redE A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  show (dualMap f x).fst = f x.fst
  simp [dualMap]

theorem dualMap_comp {A B E : Type} [CommRing A] [CommRing B] [CommRing E] (f : A →+* B) (g : B →+* E) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_)
  · show (dualMap g (dualMap f x)).fst = (dualMap (g.comp f) x).fst
    simp [dualMap]
  · show (dualMap g (dualMap f x)).snd = (dualMap (g.comp f) x).snd
    simp [dualMap]

theorem redE_algebraMap (A : Type) [CommRing A] : redE A ≫ spMap (algebraMap A (DualNumber A)) = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {J : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
include hJ

theorem good_red (z : Sp (DualNumber F)) : Good L z (fun ψ : Sp (DualNumber F) ⟶ X => J (redE F ≫ ψ)) :=
  fun ψ => top_le_of_redE ψ _ (hJ _) (Set.mem_univ z)

theorem toStk_sE (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (z : Sp (DualNumber F)) :
    toStkA z (sE s r J) = sval s r z (fun ψ => J (redE F ≫ ψ)) :=
  toStkA_valR_eq_gs r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) z (fun y _ => (good_red hJ y).mem φ r) _

theorem toStk_vE (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (DualNumber F) ⟶ Y) (z : Sp (DualNumber F)) :
    toStkA z (vE t r J) = (val t r z (fun ψ => J (redE F ≫ ψ))).val :=
  toStkA_valR r (LB.wchart L φ fun k => J (redE F ≫ r ≫ φ k)) z (fun y _ => (good_red hJ y).mem φ r) _

theorem toStk_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) (z : Sp F) :
    toStkA z (vF t r J) = (val t r z J).val :=
  toStkA_valR r (LB.wchart L φ fun k => J (r ≫ φ k)) z (fun y _ => Set.mem_iInter.2 fun k => hJ (r ≫ φ k) (Set.mem_univ y)) _

end Dual

section Norm

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [NormedField C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C}

theorem norm_vE (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hI : ν.Integral S) {Y : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε)) (r : Sp (DualNumber C) ⟶ Y)
    (r₀ : Sp (DualNumber S) ⟶ Y) (e : spMap (dualMap S.subtype) ≫ r₀ = r)
    (h : ∀ k, (redE C ≫ r) ≫ φ k ≫ D.P.A.hom = (TF (R := R) C).hom) :
    ‖(vE t r ν.J).fst‖ ≤ 1 ∧ ‖(vE t r ν.J).snd‖ ≤ 1 := by
  subst e
  have e : redE C ≫ spMap (dualMap S.subtype) ≫ r₀ = spMap S.subtype ≫ redE S ≫ r₀ := by
    rw [← Category.assoc, redE_dualMap, Category.assoc]
  rw [e] at h
  have h1 := top_le_of_redE _ _ (IntVal.le_wchart hI φ (redE S ≫ r₀) h)
  have e2 : (fun k => ν.J ((spMap S.subtype ≫ redE S ≫ r₀) ≫ φ k)) =
      fun k => ν.J (redE C ≫ (spMap (dualMap S.subtype) ≫ r₀) ≫ φ k) := funext fun k => by
    rw [← e]; simp only [Category.assoc]
  rw [e2] at h1
  obtain ⟨w, hw⟩ : ∃ w : DualNumber S, vE t (spMap (dualMap S.subtype) ≫ r₀) ν.J = dualMap S.subtype w :=
    ⟨_, valR_spMap (dualMap S.subtype) r₀ _ h1 _⟩
  rw [hw]
  constructor
  · simpa [dualMap] using (hS _).1 w.fst.2
  · simpa [dualMap] using (hS _).1 w.snd.2

end Norm

section Val

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {C : Type} [NormedField C] [Algebra (FractionRing V) C]

theorem norm_hasVal (hC : ∀ r : V, ‖toF V C r‖ ≤ 1) {c : FractionRing V} {n : ℤ} (h : HasVal ϖ c n) :
    ‖algebraMap (FractionRing V) C c‖ = ‖toF V C ϖ‖ ^ n := by
  obtain ⟨u, rfl⟩ := h
  rw [map_mul, norm_mul, map_zpow₀, norm_zpow]
  exact (congrArg _ (IntVal.norm_unit (toF V C) hC u.isUnit)).trans (_root_.mul_one _)

theorem norm_psi_eq {D : DegPre V} {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C}
    (hC : ∀ r : V, ‖toF V C r‖ ≤ 1) (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1) (hI : ν.Integral S) (g : V →+* S)
    (hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom) {Q : D.X → ℤ} (hQ : IsQ D ϖ Q) (χ : N.X) :
    ‖(N.ψ χ : C)‖ = ‖toF V C ϖ‖ ^ Q (ν.eX χ) := by
  have hrig : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := V) C).hom ν.J‖ = 1 :=
    IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w η[D.P.A])).trans (Category.comp_id _)
  obtain ⟨e, c, -, hc, hv⟩ := exists_val_genHasVal (hQ (ν.eX χ))
  have z : Sp C := cpt C
  have E : vF (D.psi (ν.eX χ)) (jFK (R := V) C) ν.J =
      algebraMap (FractionRing V) C c * vF e (jFK (R := V) C ≫ jK V) ν.J := by
    apply (toStkA z).injective
    rw [map_mul, toStk_vF ν.good, toStk_vF ν.good, ← gs_const]
    exact hv _ _ z ν.J fun ψ => ν.good ψ (Set.mem_univ z)
  have he : ‖vF e (jFK (R := V) C ≫ jK V) ν.J‖ = 1 :=
    IntVal.norm_vF hS hI _ _ (spMap g) hg fun _ =>
      (congrArg ((TF (R := V) C).hom ≫ ·) (Over.w (D.c (ν.eX χ)))).trans (Category.comp_id _)
  rw [ν.ψ_eq, norm_mul, hrig, E, norm_mul, he, norm_hasVal hC hc, _root_.mul_one, _root_.mul_one]

end Val

theorem norm_mul_dual {C : Type} [NormedField C] [IsUltrametricDist C] (x y : DualNumber C) {κ : ℝ}
    (h₁ : ‖y.fst‖ ≤ κ) (h₂ : ‖y.snd‖ ≤ κ) :
    ‖(x * y).fst‖ ≤ κ * ‖x.fst‖ ∧ ‖(x * y).snd‖ ≤ κ * max ‖x.fst‖ ‖x.snd‖ := by
  have h0 : 0 ≤ κ := (norm_nonneg _).trans h₁
  constructor
  · rw [TrivSqZeroExt.fst_mul, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)
  · rw [DualNumber.snd_mul]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, mul_comm]
      exact mul_le_mul h₂ (le_max_left _ _) (norm_nonneg _) h0
    · rw [norm_mul, mul_comm]
      exact mul_le_mul h₁ (le_max_right _ _) (norm_nonneg _) h0

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α mu : N.X, ‖(jc ν s gm (α + k • mu)).fst‖ ≤ Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu α)) * ‖(trVal ν s gm α mu).fst‖ ∧ ‖(jc ν s gm (α + k • mu)).snd‖ ≤ Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu α)) * max ‖(trVal ν s gm α mu).fst‖ ‖(trVal ν s gm α mu).snd‖ := by
  intro V _ _ _ D C _ _ _ _ _ hC N ν hν q hq k _ s gm₀ gm _ hp α mu
  obtain ⟨S, hS, hI⟩ := hν
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using exists_QVal hϖ D
  let g : V →+* S := (toF V C).codRestrict S fun x => (hS _).2 (hC.1 x)
  have hg : spMap S.subtype ≫ spMap g = (TF (R := V) C).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  have hg' : spMap (dualMap S.subtype) ≫ spMap (dualMap g) = spMap (dualMap (toF V C)) := dualMap_comp _ _
  obtain ⟨eB, c₀, hc₀, hfe⟩ := exists_fe_val hϖ hQ k (ν.eX mu) (ν.eX α) s
  have hψ : ∀ χ, Real.exp (-q χ) = ‖toF V C ϖ‖ ^ Q (ν.eX χ) := fun χ =>
    (hq.ψ χ).symm.trans (norm_psi_eq hC.1 hS hI g hg hQ χ)
  have ht : ‖toF V C ϖ‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective V (FractionRing V)
      ((algebraMap (FractionRing V) C).injective (by simpa [toF] using h)))
  have hκ : ‖algebraMap (FractionRing V) C c₀‖ = Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu α)) := by
    rw [norm_hasVal hC.1 hc₀, bOf, ← map_add, zpow_add₀ ht, zpow_sub₀ ht, zpow_sub₀ ht, mul_comm (k : ℤ), zpow_mul,
      ← hψ, ← hψ, ← hψ, zpow_natCast, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_add,
      QuadraticMap.polar]
    congr 1; ring
  set c := algebraMap (FractionRing V) C c₀
  set r : Sp (DualNumber C) ⟶ (DegPre.BF D.toPre C).left :=
    (lift (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b).left with hr
  have r₁ : r ≫ (fst (TF (R := V) C) D.toPre.P.A).left = spMap (algebraMap C (DualNumber C)) :=
    congrArg CommaMorphism.left (lift_fst (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b)
  have r₂ : r ≫ (DegPre.prB D.toPre C).left = gm.b.left :=
    congrArg CommaMorphism.left (lift_snd (Over.homMk (spMap (algebraMap C (DualNumber C))) rfl : TE V C ⟶ TF (R := V) C) gm.b)
  have hb : redE C ≫ gm.b.left ≫ D.toPre.P.A.hom = (TF (R := V) C).hom :=
    (congrArg (redE C ≫ ·) (Over.w gm.b)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (TF (R := V) C).hom) (redE_algebraMap C)).trans (Category.id_comp _)))
  have hb₀ : redE C ≫ spMap (dualMap (toF V C)) ≫ (epsR V).hom = (TF (R := V) C).hom := by
    rw [← hb, hp.1, ← Over.w gm₀.b]
    exact congrArg (redE C ≫ ·) (Category.assoc _ _ _).symm
  have n₁ := norm_vE hS hI eB gm.b.left (spMap (dualMap g) ≫ gm₀.b.left)
    (by rw [← Category.assoc, hg']; exact hp.1.symm) (fun i => by
      have hB : ∀ χ j, D.toPre.famφB χ j ≫ D.toPre.P.A.hom = D.toPre.P.A.hom := fun χ j => by
        fin_cases j
        · exact Category.id_comp _
        all_goals exact Over.w _
      refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (fun t => redE C ≫ gm.b.left ≫ t) ?_) hb)
      rcases i with i | i
      · exact hB _ _
      · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hB _ _)).trans (Over.w _)))
  have n₂ := norm_vE hS hI (gm₀.s (ν.eX α + k • ν.eX mu)) (spMap (dualMap (toF V C))) (spMap (dualMap g)) hg'
    (fun i => by
      refine (Category.assoc _ _ _).trans (Eq.trans (congrArg (fun t => redE C ≫ spMap (dualMap (toF V C)) ≫ t) ?_) hb₀)
      fin_cases i <;> exact Over.w _)
  have E : jc ν s gm (α + k • mu) = trVal ν s gm α mu * (TrivSqZeroExt.inl c *
      (vE eB gm.b.left ν.J * vE (gm₀.s (ν.eX α + k • ν.eX mu)) (spMap (dualMap (toF V C))) ν.J)) := by
    have hG := good_red ν.good (cpt (DualNumber C))
    have e₁ := hfe _ r _ _ hG
    have e₂ : gs r (cpt (DualNumber C)) ⊤ (gF D.toPre C c) = toStkA (cpt (DualNumber C)) (TrivSqZeroExt.inl c) :=
      (gs_pull r (fst (TF (R := V) C) D.toPre.P.A).left _ ⊤ trivial _).trans
        ((congrArg (fun t => gs t _ ⊤ _) r₁).trans (gs_const _ _ c))
    have e₃ := (val_corr hG (hp.2 (ν.eX α + k • ν.eX mu)) (𝟙 _)).trans (val_pull hG _ _ _)
    rw [Category.id_comp] at e₃
    rw [r₂, e₂] at e₁
    apply toStkA_injective
    unfold jc trVal
    rw [map_add, map_nsmul, map_mul, map_mul, map_mul, map_mul, toStk_sE ν.good, toStk_sE ν.good, toStk_vE ν.good,
      toStk_vE ν.good, toStk_vE ν.good]
    refine (congrArg₂ (· * ·) e₁ (congrArg Units.val e₃)).trans ?_
    ring
  obtain ⟨m₁, m₂⟩ := norm_mul_dual (vE eB gm.b.left ν.J) _ n₂.1 n₂.2
  rw [_root_.one_mul] at m₁ m₂
  rw [E, ← hκ]
  refine norm_mul_dual _ _ ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (m₁.trans n₁.1)
  · rw [DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (m₂.trans (max_le n₁.1 n₁.2))

end GlobalTheory.MBLow.TranslBound
