import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOfLineBundleFiniteFlatSubgroupScheme
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NondegSpread
open GlobalTheory.CechPic

theorem pairing_add_and_symm : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) ∧
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) := by
  intro S A _ _ hA P hP r₁ r₂ hs ha
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  refine ⟨fun T x x' y => ?_, fun T x y => ?_⟩
  · obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD ha P hP r₁ r₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_iff hP (pull_isLB hP _)).2 hs
    rw [cls_pull hP] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem over_hom_ext_of_local : ∀ (S : Scheme.{0}) (T X : Over S) (a b : T ⟶ X),
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ Out.overResι V ≫ a = Out.overResι V ≫ b) → a = b := by
  intro S T X a b h
  choose V hV e using h
  apply Over.OverMorphism.ext
  exact Scheme.hom_ext_of_forall _ _ fun p => ⟨V p, hV p, congrArg (fun q => q.left) (e p)⟩

theorem hom_ext_of_generic_points : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (H X : Over (Sp O))
    [IsSeparated X.hom] (a b : H ⟶ X), IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ z : T ⟶ H, z ≫ a = z ≫ b) → a = b := by
  intro O K _ _ _ _ _ H X _ a b hfin hflat h
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField O K
  have : IsSchemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) :=
    .of_isPullback (IsPullback.of_hasPullback H.hom (spMap (algebraMap O K))).flip
  let T : Over (Sp O) := Over.mk (pullback.fst H.hom (spMap (algebraMap O K)) ≫ H.hom)
  let z : T ⟶ H := Over.homMk (pullback.fst _ _) rfl
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) ?_
  exact congrArg (fun q => q.left) (h T (pullback.snd _ _) pullback.condition z)

theorem cls_translDiff : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A) (h : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB),
    CechPic.cls _ h = CechPic.pull (fst T A).left (CechPic.pull (lift x x).left (CechPic.cls P hP)) + CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) := by
  intro S A _ P hP hB hS T x h
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have dg : ∀ g : T ⊗ A ⟶ A, CechPic.pull g.left (CechPic.cls _ hD) =
      CechPic.pull (lift g g).left (CechPic.cls P hP) := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have hm : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = (fst T A ≫ x) * snd T A := rfl
  refine (cls_linComb hD (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) ![1, -1] h).trans ?_
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
  rw [hm, dg, dg, hB, hS _ (fst T A ≫ x) (_ * _), hS _ (snd T A) (_ * _), hB, hB, ← pull_comp,
    ← Over.comp_left, comp_lift, MonObj.comp_pow, pow_two, hB, hS _ (snd T A) (fst T A ≫ x)]
  abel

theorem memKL_of_pairing_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A), CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) = 0 →
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x := by
  intro S A _ P hP hB hS T x h0 p
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have e := cls_translDiff S A P hP hB hS T x hM
  rw [h0, add_zero] at e
  obtain ⟨N, hN, hc⟩ := cls_surj (CechPic.pull (lift x x).left (CechPic.cls P hP))
  have e' : cls (N.pull (fst T A).left) (pull_isLB hN _) = cls _ hM := by rw [cls_pull hN, hc, e]
  obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 e'
  exact GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull (fst T A).left _ hN u hu p

theorem exists_local_triv_sq_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∀ (T : Over S) (x : T ⟶ A), MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → ∀ p : T.left,
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ t : (P.pull (lift (snd A (Out.overRes V) ≫ Out.overResι V ≫ x ^ 2) (fst A (Out.overRes V))).left).Gen, t.IsGen := by
  intro S A _ P hP hB hS r₂ T x hx p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have nat : ∀ {Y Z : Over S} (g : Y ⟶ Z) (a b : Z ⟶ A), CechPic.pull g.left (CechPic.pull (lift a b).left (CechPic.cls P hP)) = CechPic.pull (lift (g ≫ a) (g ≫ b)).left (CechPic.cls P hP) :=
    fun g a b => by rw [← pull_comp, ← Over.comp_left, comp_lift]
  have ax : ∀ {Y : Over S} (a : Y ⟶ A), CechPic.pull (lift a (1 : Y ⟶ A)).left (CechPic.cls P hP) = 0 := fun a => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 r₂
    rw [cls_pull hP] at e
    have e' := congrArg (CechPic.pull a.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  let Vo := Out.overRes V
  let u : Vo ⟶ T := Out.overResι V
  let W := (fst T A).left ⁻¹ᵁ V
  let U : Vo ⊗ A ⟶ T ⊗ A := lift (fst Vo A ≫ u) (snd Vo A)
  have k₁ : U ≫ fst T A = fst Vo A ≫ u := lift_fst _ _
  have k₂ : U ≫ snd T A = snd Vo A := lift_snd _ _
  obtain ⟨n, hn⟩ : ∃ n : (Vo ⊗ A).left ⟶ W.toScheme, n ≫ W.ι = U.left :=
    ⟨IsOpenImmersion.lift _ U.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (U ≫ fst T A).left y ∈ V
      rw [k₁]
      show V.ι ((fst Vo A).left y) ∈ V
      have hy := Set.mem_range_self (f := V.ι) ((fst Vo A).left y)
      rwa [Scheme.Opens.range_ι] at hy), IsOpenImmersion.lift_fac _ _ _⟩
  have e0 := (cls_eq_zero_iff (pull_isLB hM _)).2 ⟨c, hc⟩
  rw [cls_pull hM, cls_translDiff S A P hP hB hS T x hM] at e0
  have e1 := congrArg (CechPic.pull n) e0
  rw [map_zero, ← pull_comp, hn, map_add, ← pull_comp, ← Over.comp_left, nat, nat] at e1
  simp only [← Category.assoc, k₁, k₂] at e1
  simp only [Category.assoc] at e1
  have e2 := congrArg (CechPic.pull (lift (𝟙 Vo) (1 : Vo ⟶ A)).left) e1
  rw [map_zero, map_add, nat, nat, lift_fst_assoc, lift_snd, Category.id_comp, ax, add_zero] at e2
  have e3 : CechPic.pull (fst Vo A).left (CechPic.pull (lift (u ≫ x) (u ≫ x)).left (CechPic.cls P hP)) = 0 := by rw [e2, map_zero]
  rw [nat] at e3
  rw [e3, zero_add] at e1
  have e4 := congrArg (CechPic.pull (lift (snd A Vo) (fst A Vo)).left) e1
  rw [map_zero, nat, lift_fst_assoc, lift_snd] at e4
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP]
  exact e4

theorem eq_one_of_generic_nondeg : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left),
    P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H gen T t ht x hx
  obtain ⟨T, ⟨⟨⟩⟩, hT⟩ := T
  change T ⟶ Sp K at t
  change T ⟶ Sp O at hT
  change hT = t ≫ _ at ht
  subst ht
  let T' : Over (Sp K) := Over.mk t
  obtain ⟨x', rfl⟩ := GlobalTheory.SiegelPull.push_surjective h T' x
  rw [← map_one (pushHom h T')]
  congr 1
  apply gen T' x'
  obtain ⟨u, hu⟩ := H
  obtain ⟨c, hc⟩ := hx
  let f := spMap (algebraMap O K)
  let B : Over (Sp O) := Over.mk ((A' ⊗ T').hom ≫ f)
  let a : B ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    show (fst A' T').left ≫ φ ≫ A.hom = (A' ⊗ T').hom ≫ f
    rw [h.1.w, ← Category.assoc, Over.w (fst A' T')])
  let b : B ⟶ Over.mk (t ≫ f) := Over.homMk (snd A' T').left (by
    show (snd A' T').left ≫ t ≫ f = (A' ⊗ T').hom ≫ f
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd A' T')))
  let χ : (A' ⊗ T').left ⟶ (A ⊗ Over.mk (t ≫ f)).left := (lift a b).left
  have c₁ : χ ≫ (fst A (Over.mk (t ≫ f))).left = (fst A' T').left ≫ φ :=
    congrArg (fun q => q.left) (lift_fst a b)
  have c₂ : χ ≫ (snd A (Over.mk (t ≫ f))).left = (snd A' T').left :=
    congrArg (fun q => q.left) (lift_snd a b)
  have sqr : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ =
      χ ≫ (lift (snd A (Over.mk (t ≫ f)) ≫ pushHom h T' x') (fst A (Over.mk (t ≫ f)))).left :=
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := B) (𝟙 _) _ _ χ _ _
      (by rw [Category.id_comp, Over.comp_left, Over.comp_left, ← Category.assoc χ, c₂, Category.assoc]; rfl)
      (by rw [Category.id_comp, c₁]))
  obtain ⟨c₂', h₂⟩ := gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂)
    _ _ χ fun _ => sqr) c hc
  exact exists_down ((isGen_iff u).1 hu) hP hP' c₂' h₂

theorem sq_eq_one_of_memKL_generic : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left)
    (hP : P.IsLB), P'.IsLB → LBIso P' (P.pull φ₂) →
    (∀ (T : Over (Sp O)) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over (Sp O)) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → x ^ 2 = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht x hx
  refine over_hom_ext_of_local _ T A (x ^ 2) 1 fun p => ?_
  obtain ⟨V, hV, hg⟩ := exists_local_triv_sq_of_memKL _ A P hP hB hS r₂ T x hx p
  refine ⟨V, hV, ?_⟩
  rw [MonObj.comp_one]
  exact eq_one_of_generic_nondeg O K A A' φ φ₂ h sq P P' hP hP' H gen (Out.overRes V) (V.ι ≫ t)
    (by simp only [Out.overRes, Over.mk_hom, ht, Category.assoc]) _ hg

theorem nondeg_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ _ _ _ A _ A' _ φ φ₂ hA h sq P P' hP hP' H r₁ r₂ hs ha gen T y hy
  haveI := hA.comm
  haveI := hA.proper
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨hB, hS⟩ := pairing_add_and_symm _ A hA P hP r₁ r₂ hs ha
  obtain ⟨H₀, _, i, -, -, hfin, hflat, hZ⟩ := GlobalTheory.kernel_finiteFlat_subgroup O A hA _ hL ha
  have hi : i ^ 2 = 1 := by
    refine hom_ext_of_generic_points O K H₀ A (i ^ 2) 1 hfin hflat fun T t ht z => ?_
    rw [MonObj.comp_pow, MonObj.comp_one]
    exact sq_eq_one_of_memKL_generic O K A A' φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht (z ≫ i) ((hZ T _).2 ⟨z, rfl⟩)
  obtain ⟨-, hfl, hsu⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow GlobalTheory.abelianSchemeLaws_all.1 O A hA _ hL ha 2
    (by norm_num)
  obtain ⟨T', e, x, he, he', hx⟩ := GlobalTheory.DivisibleHom.exists_lift_point ((𝟙 A) ^ 2) y
  have hx2 : x ^ 2 = e ≫ y := by rw [← hx, MonObj.comp_pow, Category.comp_id]
  have hmem : MemKL A _ x := memKL_of_pairing_sq _ A P hP hB hS T' x (by
    obtain ⟨t, ht⟩ := hy
    have e0 := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e0
    have e1 := congrArg (CechPic.pull (lift (snd T' A) (fst T' A ≫ e)).left) e0
    rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e1
    rw [hx2]
    exact e1)
  obtain ⟨w, hw⟩ := (hZ T' x).1 hmem
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective e
  rw [← hx2, ← hw, ← MonObj.comp_pow, hi, MonObj.comp_one, MonObj.comp_one]

end GlobalTheory.NondegSpread
