import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CartesianLiftThreeCompProjection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

abbrev cPB (χ : D.toPre.X) : DegPre.BF D.toPre F ⟶ D.toPre.P.A := toUnit _ ≫ D.toPre.c χ

lemma aF_prB (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ DegPre.prB D.toPre F = DegPre.prB D.toPre F ≫ oa.onB.act a := by
  unfold aF
  exact lift_snd _ _

lemma aF_cP (oa : D.toPre.OAct O) (a : O) (χ : D.toPre.X) : aF D F oa a ≫ cPB D F χ = cPB D F χ := by
  unfold cPB
  rw [← Category.assoc, toUnit_unique (aF D F oa a ≫ toUnit _) (toUnit _)]

lemma aF_one (oa : D.toPre.OAct O) (a : O) :
    aF D F oa a ≫ (toUnit _ ≫ η[D.toPre.P.A]) = toUnit _ ≫ η[D.toPre.P.A] := by
  rw [← Category.assoc, toUnit_unique (aF D F oa a ≫ toUnit _) (toUnit _)]

lemma fsum_four_left {S' : Scheme.{0}} {T A : Over S'} [GrpObj A] [IsCommMonObj A] (x₀ x₁ x₂ x₃ : T ⟶ A) (e : Fin 4 → ℤ) :
    fsum ![x₀.left, x₁.left, x₂.left, x₃.left] e =
      lf (e 0 • Finsupp.single x₀ 1 + e 1 • Finsupp.single x₁ 1 + e 2 • Finsupp.single x₂ 1 +
        e 3 • Finsupp.single x₃ 1) := by
  simp [fsum, lf, Fin.sum_univ_four, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, Finsupp.smul_single]

def pullSum (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    (DegPre.BF D.toPre F ⟶ D.toPre.P.A) →₀ ℤ :=
  ((((k * N : ℕ) : ℤ) - 1) • Finsupp.single (DegPre.prB D.toPre F) 1 +
      (1 : ℤ) • Finsupp.single (DegPre.prB D.toPre F * cPB D F (star a • χ)) 1 +
      (-1 : ℤ) • Finsupp.single (cPB D F (star a • χ)) 1 + (1 : ℤ) • Finsupp.single 1 1) +
    ((-((k : ℤ) - 1)) • Finsupp.single (DegPre.prB D.toPre F ≫ oa.onB.act a) 1 +
      (-1 : ℤ) • Finsupp.single ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ) 1 +
      (1 : ℤ) • Finsupp.single (cPB D F χ) 1 + (-1 : ℤ) • Finsupp.single 1 1)

lemma fsum_pull (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X) :
    fsum (pullφ D F oa a χ) (pullε k N) = lf (pullSum D F oa a k N χ) := by
  have h1 : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F ≫ oa.onB.act a).left := by
    rw [← Over.comp_left, aF_prB]
  have h2 : (aF D F oa a).left ≫
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ)).left =
      ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left := by
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, aF_prB, aF_cP]
    rfl
  have h3 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ).left = (cPB D F χ).left := by
    rw [← Over.comp_left, aF_cP]
  have h4 : (aF D F oa a).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (aF_one D F oa a)
  have h5 : (padd D.toPre.P.A (DegPre.prB D.toPre F)
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ))).left =
      (DegPre.prB D.toPre F * cPB D F (star a • χ)).left := rfl
  have h6 : (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := rfl
  have h7 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left = (cPB D F (star a • χ)).left := rfl
  simp only [fsum, lf, pullφ, pullε, DegPre.famφ, DegPre.famε, pullSum, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    h1, h2, h3, h4, h5, h6, h7, neg_neg, Finsupp.mapDomain_add, Finsupp.mapDomain_smul,
    Finsupp.mapDomain_single, Finsupp.smul_single_one]
  clear h1 h2 h3 h4 h5 h6 h7
  congr 1
  · simp only [add_assoc]
  · simp only [add_assoc]

lemma mapDomain_zsmul' {α β : Type} (f : α → β) (n : ℤ) (F' : α →₀ ℤ) :
    Finsupp.mapDomain f (n • F') = n • Finsupp.mapDomain f F' := by
  rw [Finsupp.mapDomain_smul]

theorem hasGen_pull (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (k : ℕ) (χ : D.toPre.X) :
    HasGen D.toPre.P.L (lf (pullSum D F oa a k N χ)) := by
  have hA := oa.onB.rosati a
  have hA' := oa.onB.rosati (star a)
  rw [star_star] at hA'
  obtain ⟨uR, huR⟩ := gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act a) (oa.onB.act (star a))) Out.rosatiε hA
  obtain ⟨uR', huR'⟩ :=
    gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act (star a)) (oa.onB.act a)) Out.rosatiε hA'
  have hPM := hasGen_pullMul oa.onB.toRingAct w0 a N hN uΨ huΨ uR huR D.toPre.cub.t D.toPre.cub.isGen
  have h1 := hPM.pull (DegPre.prB D.toPre F).left
  rw [lf_pull] at h1
  have h2 := hasGen_rosati (oa.onB.act (star a)) (oa.onB.act a) uR' huR' (cPB D F χ) (DegPre.prB D.toPre F)
  have h3 : HasGen D.toPre.P.L (lf (Finsupp.single (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A) 1)) := by
    have := HasGen.of_gen (LB.pullGen D.toPre.P.L _ _ D.toPre.rig (toUnit (DegPre.BF D.toPre F)).left)
      (pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _)
    convert this using 1
    simp only [fsum, Fintype.univ_punit, Finset.sum_singleton, lf_single]
    rfl
  have h := (h1.zsmul (-(k : ℤ))).add (h2.add (h3.zsmul ((k : ℤ) * ((N : ℤ) - 1))))
  simp only [← lf_smul, ← lf_add] at h
  convert h using 2
  have hc : cPB D F χ ≫ oa.onB.act (star a) = cPB D F (star a • χ) := by
    simp only [cPB, Category.assoc, oa.c_lin]
  simp only [pullSum, mapDomain_add', mapDomain_sub', mapDomain_zsmul', mapDomain_single', Category.comp_id,
    MonObj.comp_one, lamP, hc]
  rw [mul_comm (cPB D F (star a • χ)), mul_comm (cPB D F χ)]
  push_cast
  module

lemma zF_prB : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := by
  unfold DegPre.zF
  exact lift_snd _ _

lemma zF_prB_mul (x : DegPre.BF D.toPre F ⟶ D.toPre.P.A) :
    DegPre.zF D.toPre F ≫ (DegPre.prB D.toPre F * x) = DegPre.zF D.toPre F ≫ x := by
  show DegPre.zF D.toPre F ≫ (lift (DegPre.prB D.toPre F) x ≫ μ[D.toPre.P.A]) = _
  rw [← Category.assoc, comp_lift, zF_prB]
  exact one_mul _

lemma zF_prB_mul' (oa : D.toPre.OAct O) (a : O) (x : DegPre.BF D.toPre F ⟶ D.toPre.P.A) :
    DegPre.zF D.toPre F ≫ ((DegPre.prB D.toPre F ≫ oa.onB.act a) * x) = DegPre.zF D.toPre F ≫ x := by
  haveI := oa.onB.hom a
  show DegPre.zF D.toPre F ≫ (lift (DegPre.prB D.toPre F ≫ oa.onB.act a) x ≫ μ[D.toPre.P.A]) = _
  rw [← Category.assoc, comp_lift, ← Category.assoc, zF_prB]
  rw [show (1 : TF (R := V) F ⟶ D.toPre.P.A) ≫ oa.onB.act a = 1 from ?_]
  · exact one_mul _
  · show (toUnit _ ≫ η[D.toPre.P.A]) ≫ oa.onB.act a = toUnit _ ≫ η[D.toPre.P.A]
    rw [Category.assoc, IsMonHom.one_hom]

lemma zF_cP (χ : D.toPre.X) : DegPre.zF D.toPre F ≫ cPB D F χ = toUnit _ ≫ D.toPre.c χ := by
  unfold cPB
  rw [← Category.assoc, toUnit_unique (DegPre.zF D.toPre F ≫ toUnit _) (toUnit _)]

lemma zF_fst : DegPre.zF D.toPre F ≫ fst (TF (R := V) F) D.toPre.P.A = 𝟙 _ := by
  unfold DegPre.zF
  exact lift_fst _ _

lemma one_left_TF : (1 : TF (R := V) F ⟶ D.toPre.P.A).left =
    jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A := by
  unfold eSec
  show (toUnit (TF (R := V) F) ≫ η[D.toPre.P.A]).left = _
  rw [Over.comp_left, ← Category.assoc]
  rfl

lemma fsum_pull_zF (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (hN1 : 1 ≤ N) (χ : D.toPre.X) :
    fsum (fun i => (DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) (pullε k N) =
      ((k * (N - 1) : ℕ) : ℤ) • Finsupp.single (1 : TF (R := V) F ⟶ D.toPre.P.A).left 1 := by
  haveI := oa.onB.hom a
  have h1 : (aF D F oa a).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F ≫ oa.onB.act a).left := by
    rw [← Over.comp_left, aF_prB]
  have h2 : (aF D F oa a).left ≫
      (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ)).left =
      ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left := by
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [← Category.assoc, comp_lift, aF_prB, aF_cP]
    rfl
  have h3 : (aF D F oa a).left ≫ (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c χ).left = (cPB D F χ).left := by
    rw [← Over.comp_left, aF_cP]
  have h4 : (aF D F oa a).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (aF_one D F oa a)
  have h5 : (padd D.toPre.P.A (DegPre.prB D.toPre F)
      (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ))).left =
      (DegPre.prB D.toPre F * cPB D F (star a • χ)).left := rfl
  have h6 : (toUnit (DegPre.BF D.toPre F) ≫ η[D.toPre.P.A]).left =
      (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left := rfl
  have h7 : (toUnit (DegPre.BF D.toPre F) ≫ D.toPre.c (star a • χ)).left = (cPB D F (star a • χ)).left := rfl
  have g1 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, zF_prB]
  have g2 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F * cPB D F (star a • χ)).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c (star a • χ)).left := by
    rw [← Over.comp_left, zF_prB_mul, zF_cP]
  have g3 : ∀ y, (DegPre.zF D.toPre F).left ≫ (cPB D F y).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c y).left := by
    intro y
    rw [← Over.comp_left, zF_cP]
  have g4 : (DegPre.zF D.toPre F).left ≫ (1 : DegPre.BF D.toPre F ⟶ D.toPre.P.A).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left]
    congr 1
    show DegPre.zF D.toPre F ≫ (toUnit _ ≫ η[D.toPre.P.A]) = toUnit _ ≫ η[D.toPre.P.A]
    rw [← Category.assoc, toUnit_unique (DegPre.zF D.toPre F ≫ toUnit _) (toUnit _)]
  have g5 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F ≫ oa.onB.act a).left =
      (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, zF_prB]
    congr 1
    show (toUnit _ ≫ η[D.toPre.P.A]) ≫ oa.onB.act a = toUnit _ ≫ η[D.toPre.P.A]
    rw [Category.assoc, IsMonHom.one_hom]
  have g6 : (DegPre.zF D.toPre F).left ≫ ((DegPre.prB D.toPre F ≫ oa.onB.act a) * cPB D F χ).left =
      (toUnit (TF (R := V) F) ≫ D.toPre.c χ).left := by
    rw [← Over.comp_left, zF_prB_mul', zF_cP]
  simp only [fsum, pullφ, pullε, DegPre.famφ, DegPre.famε, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    h1, h2, h3, h4, h5, h6, h7, neg_neg, g1, g2, g3, g4, g5, g6]
  clear h1 h2 h3 h4 h5 h6 h7 g1 g2 g3 g4 g5 g6
  ext y
  classical
  simp only [Finsupp.add_apply, Finsupp.single_apply, Finsupp.smul_apply, smul_eq_mul]
  split_ifs <;> (try push_cast [Nat.cast_sub hN1]) <;> ring

theorem exists_pullGen (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ) (χ : D.toPre.X) :
    ∃ u : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)), u.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) := by
  set n := k * (N - 1)

  set r := LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK n) (jFK (R := V) F)
  have hrig : (D.toPre.rigK).IsGen := pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _
  have hr : r.IsGen := pullGen_isGen_of_isGen _ _ _ (powGen_isGen_of_isGen _ hrig n) _
  set p := (fst (TF (R := V) F) D.toPre.P.A).left
  set z := (DegPre.zF D.toPre F).left
  have hzp : z ≫ p = 𝟙 _ := by
    simp only [z, p]
    rw [← Over.comp_left, zF_fst]
    rfl
  set rT := LB.pullGen D.toPre.P.L _ _ r p
  have hrT : rT.IsGen := pullGen_isGen_of_isGen _ _ r hr p

  obtain ⟨u0, hu0⟩ := (hasGen_pull D F hL oa w0 uΨ huΨ a N hN k χ).gen hL _ _ (fsum_pull D F oa a k N χ)
  set v := LB.mulGen D.toPre.P.L _ _ _ _ u0 (LB.invGen D.toPre.P.L _ _ rT)
  have hv : v.IsGen := mulGen_isGen_of_isGen _ hu0 _ (invGen_isGen_of_isGen _ hrT)

  have hφr : fsum (fun _ : PUnit => jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A)
      (fun _ : PUnit => (n : ℤ) * 1) = (n : ℤ) • Finsupp.single (1 : TF (R := V) F ⟶ D.toPre.P.A).left 1 := by
    rw [one_left_TF]
    simp [fsum, Finsupp.smul_single_one]
  have h0 : fsum (fun i => z ≫ Sum.elim (pullφ D F oa a χ)
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A) i)
      (Sum.elim (pullε k N) (fun _ : PUnit => -((n : ℤ) * 1))) = 0 := by
    rw [fsum_comp, fsum_sumElim, mapDomain_add', ← fsum_comp, fsum_pull_zF D F oa a k N hN1 χ, ← fsum_comp]
    have e : (fun _ : PUnit => z ≫ p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A) =
        fun _ => jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A := by
      funext _
      rw [← Category.assoc, hzp, Category.id_comp]
    rw [e, fsum_neg, hφr, add_neg_cancel]
  obtain ⟨v', hv', hv1⟩ := exists_normalized hL _ _ v hv p z hzp h0
  have hW := mulGen_isGen_of_isGen _ hv' _ hrT
  have hsW : LB.SameSum
      (Sum.elim (Sum.elim (pullφ D F oa a χ)
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A))
        (fun _ : PUnit => p ≫ jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D.toPre.P.A))
      (Sum.elim (Sum.elim (pullε k N) (fun _ : PUnit => -((n : ℤ) * 1))) (fun _ : PUnit => (n : ℤ) * 1))
      (pullφ D F oa a χ) (pullε k N) := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_sumElim, fsum_neg]
    abel
  obtain ⟨u, hu, hcW⟩ := gen_transport hL hsW _ hW
  refine ⟨u, hu, ?_⟩
  have c1 := corr_pullGen (corr_symm hcW) z
  have c2 := corr_pullGen_mulGen v' rT z
  have c4 := corr_trans hL (corr_pullGen_comp r p z)
    (corr_trans hL (corr_pullGen_of_eq r hr _ _ hzp) (corr_pullGen_id r))
  have c3 := corr_mulGen (corr_one_of (fun j hj => hv1 j hj)) c4
  have c5 := corr_mulGen_one r
  exact corr_trans hL c1 (corr_trans hL c2 (corr_trans hL c3 c5))

theorem bf_units_const (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (f : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ) :
    ∃ c : Γ((TF (R := V) F).left, ⊤)ˣ,
      f = Units.map ((fst (TF (R := V) F) D.toPre.P.A).left.appTop).hom.toMonoidHom c := by
  obtain ⟨P', g, hg, -, -, -⟩ := hBC _ _ (TF (R := V) F).hom D.toPre.P
  have hbij := @hGF _ P'.A P'.grp P'.isAb
  let e : P'.A.left ≅ pullback (TF (R := V) F).hom D.toPre.P.A.hom := hg.flip.isoPullback
  have he : e.hom ≫ pullback.fst _ _ = P'.A.hom := hg.flip.isoPullback_hom_fst
  let φ : P'.A.left ⟶ (DegPre.BF D.toPre F).left := e.hom
  have hφinj : Function.Injective φ.appTop.hom := by
    have key : ∀ x, e.inv.appTop.hom (φ.appTop.hom x) = x := by
      intro x
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]
      rfl
    intro x y hxy
    rw [← key x, ← key y, hxy]
  have hcomp : ∀ c : Γ((TF (R := V) F).left, ⊤),
      φ.appTop.hom ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom c) = P'.A.hom.appTop.hom c := by
    intro c
    rw [← he]
    rw [Scheme.Hom.comp_appTop]
    rfl
  obtain ⟨c0, hc0⟩ := hbij.2 (φ.appTop.hom (f : Γ((DegPre.BF D.toPre F).left, ⊤)))
  obtain ⟨c1, hc1⟩ := hbij.2 (φ.appTop.hom ((f⁻¹ : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ) : Γ((DegPre.BF D.toPre F).left, ⊤)))
  have h01 : c0 * c1 = 1 := hbij.1 (by rw [map_mul, hc0, hc1, ← map_mul, Units.mul_inv, map_one, map_one])
  refine ⟨⟨c0, c1, h01, by rw [mul_comm]; exact h01⟩, ?_⟩
  ext
  apply hφinj
  show φ.appTop.hom (f : Γ((DegPre.BF D.toPre F).left, ⊤)) =
    φ.appTop.hom ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom c0)
  rw [hcomp, hc0]

private lemma res_res_lemma {Y : Scheme.{0}} {U W Z : Y.Opens} (h₁ : W ≤ U) (h₂ : Z ≤ W) (x : Γ(Y, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private lemma res_refl_le {Y : Scheme.{0}} {U : Y.Opens} (h : U ≤ U) (x : Γ(Y, U)ˣ) : res h x = x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _]
  simp

lemma res_back {Y : Scheme.{0}} {U W : Y.Opens} (h₁ : U ≤ W) (h₂ : W ≤ U) (x : Γ(Y, U)ˣ) :
    res h₁ (res h₂ x) = x := by
  rw [res_res_lemma, res_refl_le]

lemma units_map_eq_res {Y Z : Scheme.{0}} (g : Z ⟶ Y) (c : Γ(Y, ⊤)ˣ) :
    Units.map (g.appTop).hom.toMonoidHom c = res (le_refl (g ⁻¹ᵁ ⊤)) (pullU g ⊤ c) := by
  rw [res_refl_le]
  rfl

lemma eq_one_of_res_top {Y : Scheme.{0}} (O : Y.Opens) (hO : O = ⊤) (c : Γ(Y, ⊤)ˣ) {h : O ≤ ⊤}
    (e : res h c = 1) : c = 1 := by
  subst hO
  rwa [res_refl_le] at e

lemma shape_ratio {Y : Scheme.{0}} {U₁ U₂ W O O' V₀ : Y.Opens} (p₁ : W ≤ U₁) (p₂ : W ≤ U₂) (a : O ≤ W)
    (x : Γ(Y, U₁)ˣ) (y : Γ(Y, U₂)ˣ) (b : O ≤ V₀) (e : res a (res p₁ x * res p₂ y⁻¹) = res b (1 : Γ(Y, V₀)ˣ))
    (o₁ : O' ≤ U₁) (o₂ : O' ≤ U₂) (hO : O' ≤ O) : res o₁ x = res o₂ y := by
  simp only [map_one, map_mul, map_inv, res_res_lemma] at e
  have e2 := congrArg (fun z => res hO z) (mul_inv_eq_one.mp e)
  simp only [res_res_lemma] at e2
  exact e2

open scoped Classical in

theorem corr_of_zF (hGF : GlobalFnsSt) (hBC : PolBaseChangeSt) (hL : D.toPre.P.L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {φ' : K' → ((DegPre.BF D.toPre F).left ⟶ D.toPre.P.A.left)} {ε' : K' → ℤ}
    (t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ht : t.IsGen)
    (t' : LB.Gen (LB.LinComb D.toPre.P.L φ' ε')) (ht' : t'.IsGen) (hs : LB.SameSum φ ε φ' ε')
    (hval : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L φ ε t (DegPre.zF D.toPre F).left)
      (LB.pullGen D.toPre.P.L φ' ε' t' (DegPre.zF D.toPre F).left)) :
    LB.Gen.Corr D.toPre.P.L φ ε φ' ε' t t' := by
  have hs' : LB.SameSum φ' ε' φ ε := by rw [sameSum_iff_fsum] at hs ⊢; exact hs.symm
  obtain ⟨t'', ht'', c1⟩ := gen_transport hL hs' t' ht'
  set ρ := LB.mulGen D.toPre.P.L _ _ _ _ t (LB.invGen D.toPre.P.L φ ε t'')
  have hρ : ρ.IsGen := mulGen_isGen_of_isGen _ ht _ (invGen_isGen_of_isGen _ ht'')
  have hs0 : LB.SameSum (Sum.elim φ φ) (Sum.elim ε (fun k => -ε k)) (K' := PEmpty) PEmpty.elim PEmpty.elim := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_neg, add_neg_cancel, fsum_empty]
  obtain ⟨te, -, c2⟩ := gen_transport hL hs0 ρ hρ
  let j0 : PEmpty → D.toPre.P.L.ι := PEmpty.elim
  let f : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ := res (le_of_eq (wchart_empty j0).symm) (te.s j0)
  obtain ⟨c, hc⟩ := bf_units_const D F hGF hBC f

  have hz1 : LB.Gen.Corr D.toPre.P.L _ _ (K' := PEmpty) PEmpty.elim PEmpty.elim
      (LB.pullGen D.toPre.P.L _ _ te (DegPre.zF D.toPre F).left) (LB.oneGen D.toPre.P.L) := by
    have a1 := corr_pullGen (corr_symm c2) (DegPre.zF D.toPre F).left
    have a2 := corr_pullGen_mulGen t (LB.invGen D.toPre.P.L φ ε t'') (DegPre.zF D.toPre F).left
    have a3 := corr_mulGen (corr_refl _ (pullGen_isGen_of_isGen _ _ t ht (DegPre.zF D.toPre F).left))
      (corr_pullGen_invGen t'' (DegPre.zF D.toPre F).left)
    have a4 : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L φ ε t (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L φ ε t'' (DegPre.zF D.toPre F).left) :=
      corr_trans hL hval (corr_pullGen c1 _)
    exact corr_trans hL a1 (corr_trans hL a2 (corr_trans hL a3 (corr_ratio_one a4)))
  have hte : te.s j0 = res (fun _ _ => trivial :
      (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).U j0 ≤
      (fst (TF (R := V) F) D.toPre.P.A).left ⁻¹ᵁ ⊤) (pullU (fst (TF (R := V) F) D.toPre.P.A).left ⊤ c) := by
    have e1 : te.s j0 = res (le_of_eq (wchart_empty j0)) f := by
      simp only [f]
      exact (res_back _ _ _).symm
    rw [e1, hc, units_map_eq_res]
    erw [res_res']
    rfl
  have hzp : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, zF_fst]; rfl
  have key : (LB.pullGen D.toPre.P.L _ _ te (DegPre.zF D.toPre F).left).s j0 = res le_top c := by
    show res _ (pullU _ _ (te.s j0)) = _
    rw [hte]
    exact pull_pull_id _ _ hzp _ _ c
  have hc1 : c = 1 := by
    have e := hz1 j0 j0 (fun k => k.elim) (fun k => k.elim) (fun k => k.elim)
    rw [key] at e
    change res _ (res _ c) = res _ (1 : Γ((TF (R := V) F).left, _)ˣ) at e
    rw [map_one] at e
    erw [res_res'] at e
    exact eq_one_of_res_top _ (by ext y; simp [LB.wchart]) c e
  have hf1 : f = 1 := by rw [hc, hc1, map_one]
  have hte1 : te.s j0 = 1 := by
    simp only [f] at hf1
    rw [← res_back (le_of_eq (wchart_empty j0)) (le_of_eq (wchart_empty j0).symm) (te.s j0), hf1, map_one]
    rfl

  have hf1 : f = 1 := by rw [hc, hc1, map_one]
  have htt : LB.Gen.Corr D.toPre.P.L φ ε φ ε t t'' := by
    intro j j₂ hj hj₂ hm
    let J : K ⊕ K → D.toPre.P.L.ι := Sum.elim j j₂
    have hJ : LB.Coh D.toPre.P.L (Sum.elim φ φ) J := by
      rintro (k₁ | k₁) (k₂ | k₂) e
      · exact hj k₁ k₂ e
      · exact hm k₁ k₂ e
      · exact (hm k₂ k₁ e.symm).symm
      · exact hj₂ k₁ k₂ e
    have e := c2 J j0 hJ (fun k => k.elim) (fun _ k' => k'.elim)
    have le : LB.wchart D.toPre.P.L φ j ⊓ LB.wchart D.toPre.P.L φ j₂ ≤ LB.wchart D.toPre.P.L (Sum.elim φ φ) J :=
      fun y hy => Set.mem_iInter.2 fun k => by
        rcases k with k | k
        · exact Set.mem_iInter.1 hy.1 k
        · exact Set.mem_iInter.1 hy.2 k
    rw [hte1] at e
    exact shape_ratio _ _ _ (t.s j) (t''.s j₂) _ e _ _ (le_inf le (fun _ _ => by rw [wchart_empty]; trivial))
  exact corr_trans hL htt (corr_symm c1)

section PullFam

variable (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
  (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
  (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)

def uPull (χ : D.toPre.X) : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N)) :=
  Classical.choose (exists_pullGen D F hL oa w0 uΨ huΨ a N hN hN1 k χ)

lemma uPull_spec (χ : D.toPre.X) :
    (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ).IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ)
        (DegPre.zF D.toPre F).left)
        (LB.pullGen D.toPre.P.L _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rigK (k * (N - 1))) (jFK (R := V) F)) := Classical.choose_spec (exists_pullGen D F hL oa w0 uΨ huΨ a N hN hN1 k χ)

def pullProd (s : Fam D.toPre F k) (χ : D.toPre.X) :=
  mulSec D.toPre.P.L _ _ _ _ (genSec (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ) (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).1)
    (pullSec D.toPre.P.L _ _ (s.s χ) (aF D F oa a).left)

lemma pullProd_sameSum (χ : D.toPre.X) (β : D.toPre.X) (hβ : star a • χ = β) :
    LB.SameSum (Sum.elim (pullφ D F oa a χ) (fun i => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ i))
      (Sum.elim (pullε k N) (DegPre.famε k)) (DegPre.famφ D.toPre F β) (DegPre.famε (k * N)) := by
  subst hβ
  intro ψ
  classical
  have hz : ∀ x : Fin 4, ((if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then -DegPre.famε k x else 0) +
      if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then DegPre.famε k x else 0) = 0 := by
    intro x
    split_ifs <;> simp
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc, ← Finset.sum_add_distrib]
  show (∑ x : Fin 4, if DegPre.famφ D.toPre F (star a • χ) x = ψ then DegPre.famε (k * N) x else 0) +
      ∑ x : Fin 4, ((if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then -DegPre.famε k x else 0) +
        if (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ x = ψ then DegPre.famε k x else 0) =
      ∑ x : Fin 4, if DegPre.famφ D.toPre F (star a • χ) x = ψ then DegPre.famε (k * N) x else 0
  rw [Finset.sum_eq_zero (fun x _ => hz x), add_zero]

open scoped Classical in

def pullSecs (s : Fam D.toPre F k) (β : D.toPre.X) :
    LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F β) (DegPre.famε (k * N))) :=
  if h : ∃ χ, star a • χ = β then
    Classical.choose (sec_transport hL (pullProd_sameSum D F oa a N k h.choose β h.choose_spec)
      (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s h.choose))
  else SecOps.secZero

end PullFam

lemma smul_star_inj {O : Type} [CommRing O] [StarRing O] {X : Type} [AddCommGroup X] [Module O X]
    [Module.Free ℤ X] (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) {χ₁ χ₂ : X}
    (h : star a • χ₁ = star a • χ₂) : χ₁ = χ₂ := by
  have h2 : (a * star a) • χ₁ = (a * star a) • χ₂ := by rw [mul_smul, mul_smul, h]
  rw [hN, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h2
  have h3 : (N : ℤ) • χ₁ = (N : ℤ) • χ₂ := by rw [natCast_zsmul, natCast_zsmul]; exact h2
  exact smul_right_injective X (by omega) h3

private lemma rs_rs_eq_rs_trans {Y : Scheme.{0}} {U W Z : Y.Opens} (h₁ : W ≤ U) (h₂ : Z ≤ W) (x : Γ(Y, U)) :
    rs h₂ (rs h₁ x) = rs (h₂.trans h₁) x := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private lemma rs_mul' {Y : Scheme.{0}} {U W : Y.Opens} (h : W ≤ U) (x y : Γ(Y, U)) :
    rs h (x * y) = rs h x * rs h y := map_mul _ _ _

lemma shape_secRel {Y : Scheme.{0}} {U₁ U₂ U₃ W V₂ O : Y.Opens} (hW : W ≤ U₃) (hWV : W ≤ V₂) (hV : V₂ ≤ U₂)
    (o : O ≤ W ⊓ U₁) (o₁ : O ≤ U₁) (o₂ : O ≤ U₂) (o₃ : O ≤ U₃) (x : Γ(Y, U₁)) (y : Γ(Y, U₂)) (u : Γ(Y, U₃)ˣ)
    (e : rs (inf_le_left : W ⊓ U₁ ≤ W) (rs hW (u : Γ(Y, U₃)) * rs hWV (rs hV y)) =
      rs (inf_le_right : W ⊓ U₁ ≤ U₁) x) :
    rs o₁ x = rs o₂ y * rs o₃ (u : Γ(Y, U₃)) := by
  have e2 := congrArg (fun z => rs o z) e
  simp only [rs_rs_eq_rs_trans, rs_mul'] at e2
  rw [mul_comm]
  exact e2.symm

variable {D F} in

lemma secRel_pullSecs (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k) (χ : D.toPre.X) :
    ∀ (χ₀ : D.toPre.X) (hβ : star a • χ₀ = star a • χ), χ₀ = χ →
      GeneratorPullback.SecRel D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) (DegPre.famε (k * N))
        (Classical.choose (sec_transport hL (pullProd_sameSum D F oa a N k χ₀ (star a • χ) hβ)
          (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s χ₀)))
        (DegPre.famφ D.toPre F χ) (DegPre.famε k) (s.s χ) (aF D F oa a).left
        (pullφ D F oa a χ) (pullε k N) (uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ) := by
  intro χ₀ hβ e
  subst χ₀
  intro j₁ j₂ j₃ hcoh
  have spec := Classical.choose_spec (sec_transport hL (pullProd_sameSum D F oa a N k χ (star a • χ) hβ)
    (pullProd D F hL oa w0 uΨ huΨ a N hN hN1 k s χ))
  have e := spec (Sum.elim j₃ j₂) j₁
    (by
      rintro (k₁ | k₁) (k₂ | k₂) h
      · exact hcoh (Sum.inr (Sum.inr k₁)) (Sum.inr (Sum.inr k₂)) h
      · exact hcoh (Sum.inr (Sum.inr k₁)) (Sum.inr (Sum.inl k₂)) h
      · exact hcoh (Sum.inr (Sum.inl k₁)) (Sum.inr (Sum.inr k₂)) h
      · exact hcoh (Sum.inr (Sum.inl k₁)) (Sum.inr (Sum.inl k₂)) h)
    (fun k₁ k₂ h => hcoh (Sum.inl k₁) (Sum.inl k₂) h)
    (by
      rintro (k | k) k' h
      · exact (hcoh (Sum.inl k') (Sum.inr (Sum.inr k)) h.symm).symm
      · exact (hcoh (Sum.inl k') (Sum.inr (Sum.inl k)) h.symm).symm)
  have ho : LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) j₁ ⊓
      LB.wchart D.toPre.P.L (fun k => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ k) j₂ ⊓
      LB.wchart D.toPre.P.L (pullφ D F oa a χ) j₃ ≤
      LB.wchart D.toPre.P.L (Sum.elim (pullφ D F oa a χ) (fun k => (aF D F oa a).left ≫ DegPre.famφ D.toPre F χ k))
        (Sum.elim j₃ j₂) ⊓ LB.wchart D.toPre.P.L (DegPre.famφ D.toPre F (star a • χ)) j₁ :=
    fun _ hy => ⟨Set.mem_iInter.2 fun k => by
        rcases k with k | k
        · exact Set.mem_iInter.1 hy.2 k
        · exact Set.mem_iInter.1 hy.1.2 k, hy.1.1⟩
  exact shape_secRel _ _ (wchart_comp_le _ _ j₂) ho _ _ _ _ _ _ e

theorem exists_pullAl (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ)
    (s : Fam D.toPre F k)
    (hfe : DegPre.FamFE D.toPre F (k * N) (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s)) :
    ∃ s' : Fam D.toPre F (k * N), PullAl D F oa a k N s s' := by
  refine ⟨⟨pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s, hfe⟩, fun χ => ?_, fun β hβ j => ?_⟩
  · refine ⟨uPull D F hL oa w0 uΨ huΨ a N hN hN1 k χ, (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).1,
      (uPull_spec D F hL oa w0 uΨ huΨ a N hN hN1 k χ).2, ?_⟩
    have hex : ∃ χ₀, star a • χ₀ = star a • χ := ⟨χ, rfl⟩
    show GeneratorPullback.SecRel _ _ _ (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s (star a • χ)) _ _ _ _ _ _ _
    simp only [pullSecs, dif_pos hex]
    exact secRel_pullSecs hL oa w0 uΨ huΨ a N hN hN1 k s χ hex.choose hex.choose_spec
      (smul_star_inj a N hN hN1 hex.choose_spec)
  · have : ¬ ∃ χ, star a • χ = β := fun ⟨χ, h⟩ => hβ χ h.symm
    show (pullSecs D F hL oa w0 uΨ huΨ a N hN hN1 k s β).f j = 0
    simp only [pullSecs, dif_neg this]
    rfl

theorem exists_XB (hL : D.toPre.P.L.IsLB) (oa : D.toPre.OAct O) (w0 : O)
    (uΨ : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4)
      ![(padd D.toPre.P.A (𝟙 _) (oa.onB.act w0)).left, 𝟙 D.toPre.P.A.left, (oa.onB.act w0).left,
        (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen) (a : O) (N : ℕ) (hN : a * star a = (N : O)) (hN1 : 1 ≤ N) (k : ℕ) :
    ∃ X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left]
        ![((k * N : ℕ) : ℤ), -(k : ℤ)]), X.IsGen ∧
      LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
        (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))) := by
  have hA := oa.onB.rosati a
  obtain ⟨uR, huR⟩ := gen_of_local_base hL (Out.rosatiφ D.toPre.P.A (oa.onB.act a) (oa.onB.act (star a))) Out.rosatiε hA
  have hPM := hasGen_pullMul oa.onB.toRingAct w0 a N hN uΨ huΨ uR huR D.toPre.cub.t D.toPre.cub.isGen
  have hRig : HasGen D.toPre.P.L (lf (Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1)) := by
    have := HasGen.of_gen (LB.pullGen D.toPre.P.L _ _ D.toPre.rig (toUnit D.toPre.P.A).left)
      (pullGen_isGen_of_isGen _ _ D.toPre.rig D.toPre.rig_gen _)
    convert this using 1
    simp only [fsum, Fintype.univ_punit, Finset.sum_singleton, lf_single]
    rfl
  have h := (hPM.zsmul (-(k : ℤ))).add (hRig.zsmul ((k : ℤ) * ((N : ℤ) - 1)))
  simp only [← lf_smul, ← lf_add] at h
  have hf : fsum (K := Fin 2) ![𝟙 D.toPre.P.A.left, (oa.onB.act a).left] ![((k * N : ℕ) : ℤ), -(k : ℤ)] =
      lf (-(k : ℤ) • (Finsupp.single (oa.onB.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 D.toPre.P.A) 1 +
        ((N : ℤ) - 1) • Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1) +
        ((k : ℤ) * ((N : ℤ) - 1)) • Finsupp.single (1 : D.toPre.P.A ⟶ D.toPre.P.A) 1) := by
    simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [← Over.id_left, ← lf_single, ← lf_single, ← lf_add]
    congr 1
    rw [← Finsupp.smul_single_one, ← Finsupp.smul_single_one _ (-(k : ℤ))]
    push_cast
    module
  obtain ⟨X0, hX0⟩ := h.gen hL _ _ hf
  have hzp : eSec D.toPre.P.A ≫ (toUnit D.toPre.P.A).left = 𝟙 _ := by
    simp only [eSec, ← Over.comp_left]
    rw [show η[D.toPre.P.A] ≫ toUnit D.toPre.P.A = 𝟙 _ from toUnit_unique _ _]
    rfl
  have hrig : (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (k * (N - 1))).IsGen :=
    powGen_isGen_of_isGen _ D.toPre.rig_gen _
  refine exists_normalized_to hL _ _ X0 hX0 (toUnit D.toPre.P.A).left (eSec D.toPre.P.A) hzp _ _ _ hrig ?_
  have ha : eSec D.toPre.P.A ≫ (oa.onB.act a).left = eSec D.toPre.P.A := by
    haveI := oa.onB.hom a
    simp only [eSec, ← Over.comp_left, IsMonHom.one_hom]
  simp only [fsum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id,
    ha, Fintype.univ_punit, Finset.sum_singleton, ← Finsupp.single_add]
  congr 1
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN1]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.G.DVR
