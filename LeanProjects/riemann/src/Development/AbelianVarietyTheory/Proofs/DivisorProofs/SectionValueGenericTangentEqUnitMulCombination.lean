import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigValD
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegreeFormsDimensionGenericFibreLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.MBLow.TanVal

theorem subsingleton_dual (K : Type) [Field K] : Subsingleton (PrimeSpectrum (DualNumber K)) := by
  have key : ∀ P : PrimeSpectrum (DualNumber K), P.asIdeal = Ideal.span {DualNumber.eps} := by
    intro P
    have hm : (DualNumber.eps : DualNumber K) ∈ P.asIdeal :=
      P.isPrime.mem_of_pow_mem 2 (by rw [pow_two, DualNumber.eps_mul_eps]; exact zero_mem _)
    rcases DualNumber.ideal_trichotomy P.asIdeal with h | h | h
    · rw [h, Ideal.mem_bot] at hm
      have := congrArg TrivSqZeroExt.snd hm
      simp at this
    · exact h
    · exact absurd h P.isPrime.ne_top
  exact ⟨fun P Q ↦ PrimeSpectrum.ext ((key P).trans (key Q).symm)⟩

theorem sp_comp {A B B' : Type} [CommRing A] [CommRing B] [CommRing B'] (a : A →+* B) (b : B' →+* A) :
    spMap a ≫ spMap b = spMap (a.comp b) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem fst_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom A A A).toRingHom :=
  RingHom.ext fun z => by simp [dualMap]

theorem fst_alg (C : Type) [Field C] :
    (TrivSqZeroExt.fstHom C C C).toRingHom.comp (algebraMap C (DualNumber C)) = RingHom.id C :=
  RingHom.ext fun z => by simp

theorem resTop_top {Y : Scheme.{0}} (a : Γ(Y, ⊤)) : resTop ⊤ a = a := by
  simp [resTop]

end GlobalTheory.MBLow.TanVal

noncomputable section
namespace GlobalTheory.MBLow.TanVal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem exists_ptG (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C]
    (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left) :
    ∃ yG : Sp (DualNumber C) ⟶ (UnifPre.GF (G := G) C).left, yG ≫ (U.genF C).left = yA := by
  refine ⟨yA ≫ (lift (fst (TFK (R := R) C) A.A) (snd _ _ ≫ U.gen.inv)).left, ?_⟩
  have h : lift (fst (TFK (R := R) C) A.A) (snd _ _ ≫ U.gen.inv) ≫ U.genF C = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [UnifPre.genF]
    · simp [UnifPre.genF]
  rw [Category.assoc, ← Over.comp_left, h, Over.id_left, Category.comp_id]

theorem genF_snd (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] :
    (U.genF C).left ≫ (snd (TFK (R := R) C) A.A).left =
      (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
  rw [← Over.comp_left, ← Over.comp_left, UnifPre.genF, lift_snd]

theorem genF_fst (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] :
    (U.genF C).left ≫ (fst (TFK (R := R) C) A.A).left =
      (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left := by
  rw [← Over.comp_left, UnifPre.genF, lift_fst]

theorem gs_to_valR {B : Type} [CommRing B] [IsLocalRing B] {X : Scheme.{0}} (x : Sp B ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, V)) :
    (stalkClosedPointIso (CommRingCat.of B)).hom.hom (gs x (IsLocalRing.closedPoint B) V f) = valR x V f :=
  (GlobalTheory.ZH.ThetaData.valR_eq_gs x V (h trivial) f).symm

set_option maxHeartbeats 1000000 in

theorem value_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (C : Type) [Field C] [Algebra (FractionRing R) C] (w₀ : GlobalTheory.UT.W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))), GlobalTheory.UT.NormW U w₀ ρ → ∀ (y : epsR R ⟶ G) (yA : Sp (DualNumber C) ⟶ (TFK (R := R) C ⊗ A.A).left), IsTangent y → VecAt U C y yA → ∀ (k : ℕ) (i₀ : A.L.ι) (jG : U.LG.L.ι), ⊤ ≤ (jFK (R := R) C ≫ eSec A.A) ⁻¹ᵁ A.L.U i₀ → ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → ∃ Θ : (DualNumber C)ˣ, (Θ : DualNumber C).fst * toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) ^ k = valR (jFK (R := R) C) ((A.L.pull (eSec A.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k ∧ ∀ (t : GlobalTheory.UT.SecA A C k) (σ' : U.SecGF C k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) C) A.A).left (U.genF C).left t (UnifPre.gFK (G := G) C) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → C) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) C) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) C) (fun i => scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i)) → valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) = (Θ : DualNumber C) * ∑ i, TrivSqZeroExt.inl (c i) * dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) := by
  intro R _ _ I D A G _ _ U C _ _ w₀ ρ hN y yA hy hV k i₀ jG hi hj
  haveI := subsingleton_dual C
  obtain ⟨yG, e₁⟩ := exists_ptG U C yA
  have e₂ : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left =
      yA ≫ (snd (TFK (R := R) C) A.A).left := by
    rw [← genF_snd, ← Category.assoc, e₁]
  have e₃ : yG ≫ (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left = spMap (algebraMap C (DualNumber C)) := by
    rw [← genF_fst, ← Category.assoc, e₁, hV.1]
  have e₂' : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left =
      yA ≫ (snd (TFK (R := R) C) A.A).left ≫ U.gen.inv.left := by
    rw [← reassoc_of% e₂, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.comp_id]
  have e₄ : yG ≫ UnifPre.gFK (G := G) C = spMap (dualMap (toF R C)) ≫ y.left := by
    rw [UnifPre.gFK, ← Category.assoc, e₂']
    simp only [Category.assoc]
    exact hV.2
  have hfR : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ y.left = eSec G := hy
  have hjj : jFK (R := R) C ≫ jK R = spMap (toF R C) := sp_comp _ _
  have hη : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.snd G.hom (jK R) = 𝟙 _ := Over.w η[(Over.pullback (jK R)).obj G]
  have e₅ : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yG ≫
      (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left = jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G) := by
    apply pullback.hom_ext
    · have l : (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yG ≫
          (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) =
          spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (toF R C)) ≫ y.left := by
        rw [← e₄]; simp only [UnifPre.gFK, Category.assoc]
      rw [l, ← Category.assoc, sp_comp, fst_dualMap, ← sp_comp, Category.assoc, hfR, Category.assoc,
        GlobalTheory.UT.EvalZero.eK_fst, ← Category.assoc, hjj]
    · have l : (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ pullback.snd G.hom (jK R) =
          (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ jFK (R := R) C :=
        (Over.w (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G))).trans
          (Over.w (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G))).symm
      simp only [Category.assoc]
      rw [l, ← Category.assoc yG, e₃, ← Category.assoc, sp_comp, fst_alg, hη]
      simp [spMap]

  have hx₁ : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yA ≫ (snd (TFK (R := R) C) A.A).left =
      jFK (R := R) C ≫ eSec A.A := by
    rw [← e₂, reassoc_of% e₅, GlobalTheory.UT.EvalZero.eK_gen U]
  have m₁ : ⊤ ≤ (yA ≫ (snd (TFK (R := R) C) A.A).left) ⁻¹ᵁ A.L.U i₀ := by
    intro z' _
    obtain rfl : z' = spMap (TrivSqZeroExt.fstHom C C C).toRingHom (IsLocalRing.closedPoint C) :=
      Subsingleton.elim (α := PrimeSpectrum (DualNumber C)) _ _
    have h := hi (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)
    rw [← hx₁] at h
    exact h
  have m₂ : ⊤ ≤ (spMap (dualMap (toF R C)) ≫ y.left) ⁻¹ᵁ U.LG.L.U jG := GlobalTheory.FormalValue.top_le_comp hj _
  have hG₀ : (jFK (R := R) C ≫ jK R) ≫ eSec G =
      (spMap (toF R C) ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ y.left := by
    rw [hjj, Category.assoc, hfR]
  have m₄ : ⊤ ≤ ((jFK (R := R) C ≫ jK R) ≫ eSec G) ⁻¹ᵁ U.LG.L.U jG := by
    rw [hG₀]; exact GlobalTheory.FormalValue.top_le_comp hj _
  have m₅ : ⊤ ≤ (𝟙 (Sp R)) ⁻¹ᵁ ((U.LG.L.pull (eSec G)).U fun _ => jG) := by
    intro z' _
    refine mem_pull.2 ?_
    have h := GlobalTheory.FormalValue.top_le_comp hj (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
      (show z' ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [hfR] at h
    exact h
  obtain ⟨JA, hJA, cJA⟩ := exists_good (Z := Sp (DualNumber C)) A.L A.isLB (IsLocalRing.closedPoint (DualNumber C))
    (fun _ : Unit => yA ≫ (snd (TFK (R := R) C) A.A).left) (fun _ => i₀) (fun _ _ _ => rfl) (fun _ => m₁ trivial)
  obtain ⟨JG, hJG, cJG⟩ := exists_good (Z := Sp (DualNumber C)) U.LG.L U.LG.isLB (IsLocalRing.closedPoint (DualNumber C))
    (fun _ : Unit => spMap (dualMap (toF R C)) ≫ y.left) (fun _ => jG) (fun _ _ _ => rfl) (fun _ => m₂ trivial)
  obtain ⟨JA', hJA', cJA'⟩ := exists_good (Z := Sp C) A.L A.isLB (IsLocalRing.closedPoint C)
    (fun _ : Unit => jFK (R := R) C ≫ eSec A.A) (fun _ => i₀) (fun _ _ _ => rfl) (fun _ => hi trivial)
  obtain ⟨JG', hJG', cJG'⟩ := exists_good (Z := Sp C) U.LG.L U.LG.isLB (IsLocalRing.closedPoint C)
    (fun _ : Unit => (jFK (R := R) C ≫ jK R) ≫ eSec G) (fun _ => jG) (fun _ _ _ => rfl) (fun _ => m₄ trivial)

  have mp : ⊤ ≤ (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) ⁻¹ᵁ
      ((LB.div (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left)).U (fun _ => jG, fun _ => i₀)) := by
    intro z' _
    refine ⟨mem_pull.2 ?_, mem_pull.2 ?_⟩
    · have h := m₂ (show z' ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial)
      rw [← e₄] at h
      exact h
    · have h := m₁ (show z' ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial)
      rw [← e₂] at h
      exact h
  have mp₀ : ⊤ ≤ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) ⁻¹ᵁ
      ((LB.div (U.LG.L.pull (pullback.fst G.hom (jK R))) (A.L.pull U.gen.hom.left)).U (fun _ => jG, fun _ => i₀)) := by
    rw [← e₅]; exact GlobalTheory.FormalValue.top_le_comp mp _
  have hv := GlobalTheory.FormalValue.isUnit_valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ mp
    (w₀.s (fun _ => jG, fun _ => i₀))
  have hvfst : TrivSqZeroExt.fst (valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _
      (w₀.s (fun _ => jG, fun _ => i₀)).val) =
      valR (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) _ (w₀.s (fun _ => jG, fun _ => i₀)).val := by
    have := GlobalTheory.FormalValue.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom
      (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ mp (w₀.s (fun _ => jG, fun _ => i₀)).val
    rw [e₅] at this
    exact this.symm
  have mρ : ⊤ ≤ (jFK (R := R) C) ⁻¹ᵁ LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A) (fun _ => i₀) :=
    fun _ _ => Set.mem_iInter.2 fun _ => hi trivial
  have mr : ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG) :=
    fun _ _ => Set.mem_iInter.2 fun _ => m₄ trivial
  have n₁ := GlobalTheory.UT.EvalZero.normW_ext U C hN (IsLocalRing.closedPoint C) hJA' hJG'
  replace n₁ : (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C)
      (JA' (jFK (R := R) C ≫ eSec A.A)) (JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))).val *
      (gm (jFK (R := R) C) (IsLocalRing.closedPoint C) (LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A)
        (fun _ => JA' (jFK (R := R) C ≫ eSec A.A))) (ρ.s fun _ => JA' (jFK (R := R) C ≫ eSec A.A))).val =
      (gm (jFK (R := R) C ≫ jK R) (IsLocalRing.closedPoint C) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G)
        (fun _ => JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))) (U.LG.rig.s fun _ => JG' ((jFK (R := R) C ≫ jK R) ≫ eSec G))).val := n₁
  rw [cJA' (), cJG' ()] at n₁
  have g₁ := gs_unit (jFK (R := R) C) (IsLocalRing.closedPoint C) (LB.wchart A.L (fun _ : PUnit.{1} => eSec A.A) (fun _ => i₀))
      (mρ (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) (ρ.s fun _ => i₀)
  have g₂ := gs_unit (jFK (R := R) C ≫ jK R) (IsLocalRing.closedPoint C) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG))
      (mr (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) (U.LG.rig.s fun _ => jG)
  replace n₁ := (congrArg (fun q => (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G))
      (IsLocalRing.closedPoint C) i₀ jG).val * q) g₁).trans (n₁.trans g₂.symm)
  have hpw₀ : (GlobalTheory.BoxExpansion.pw w₀ (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C)
      i₀ jG).val = gs (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C) _
        (w₀.s (fun _ => jG, fun _ => i₀)).val := (gs_unit (jFK (R := R) C ≫ eSec ((Over.pullback (jK R)).obj G)) (IsLocalRing.closedPoint C) _
        (mp₀ (show IsLocalRing.closedPoint C ∈ (⊤ : (Sp C).Opens) from trivial)) _).symm
  rw [hpw₀] at n₁
  have n₂ := congrArg (stalkClosedPointIso (CommRingCat.of C)).hom.hom n₁
  rw [map_mul, gs_to_valR _ _ mp₀, gs_to_valR _ _ mρ, gs_to_valR _ _ mr, hjj] at n₂
  have hr : valR (spMap (toF R C)) (LB.wchart U.LG.L (fun _ : PUnit.{1} => eSec G) (fun _ => jG))
      (U.LG.rig.s fun _ => jG).val = toF R C (GlobalTheory.MBLow.TanExp.rigVal U.LG jG) := by
    have := GlobalTheory.FormalValue.valR_spMap (toF R C) (𝟙 (Sp R)) _ m₅ (U.LG.rig.s fun _ => jG).val
    rw [Category.comp_id] at this
    exact this
  rw [hr, ← hvfst] at n₂

  have h1 : ((hv.unit ^ k)⁻¹ : (DualNumber C)ˣ).val *
      (valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _
        (w₀.s (fun _ => jG, fun _ => i₀)).val) ^ k = 1 := by
    have := Units.inv_mul (hv.unit ^ k)
    rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec] at this
  refine ⟨(hv.unit ^ k)⁻¹, ?_, ?_⟩
  · have h2 := congrArg TrivSqZeroExt.fst h1
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_one] at h2
    rw [← n₂, mul_pow, ← _root_.mul_assoc, h2, _root_.one_mul]
    rfl
  intro t σ' hR n c σ hσ
  have cA : JA (yA ≫ (snd (TFK (R := R) C) A.A).left) = i₀ := cJA ()
  have cG : JG (spMap (dualMap (toF R C)) ≫ y.left) = jG := cJG ()
  have a₁ := GlobalTheory.BoxExpansion.isoRel_val hR yG (IsLocalRing.closedPoint (DualNumber C)) hJA hJG
  have e₄' : yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R) =
      spMap (dualMap (toF R C)) ≫ y.left := e₄
  rw [Category.comp_id, e₁, Category.assoc, e₂, cA, Category.assoc, e₄', cG] at a₁
  have a₂ := GlobalTheory.BoxExpansion.secLin_val hσ yG (IsLocalRing.closedPoint (DualNumber C)) hJG
  have st := sval_of t yA (IsLocalRing.closedPoint (DualNumber C)) JA (fun _ => i₀) (fun _ => cA)
  have sσ := fun i => sval_of (σ i) (yG ≫ UnifPre.gFK (G := G) C) (IsLocalRing.closedPoint (DualNumber C)) JG
    (fun _ => jG) (fun _ => by rw [Category.comp_id, e₄]; exact cG)
  have mt : ⊤ ≤ yA ⁻¹ᵁ LB.wchart A.L (fun _ : Fin 1 => (snd (TFK (R := R) C) A.A).left) (fun _ => i₀) :=
    fun _ _ => Set.mem_iInter.2 fun _ => m₁ trivial
  have mσ : ⊤ ≤ y.left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jG) :=
    fun _ _ => Set.mem_iInter.2 fun _ => hj trivial
  have mσ' : ⊤ ≤ (yG ≫ UnifPre.gFK (G := G) C) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jG) := by
    rw [e₄]; exact GlobalTheory.FormalValue.top_le_comp mσ _
  have hpw : (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (GlobalTheory.BoxExpansion.pw w₀ (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left)
        (IsLocalRing.closedPoint (DualNumber C)) i₀ jG).val =
      valR (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left) _ (w₀.s (fun _ => jG, fun _ => i₀)).val := by
    have g := gs_unit (yG ≫ (snd (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left)
      (IsLocalRing.closedPoint (DualNumber C)) _
      (mp (show IsLocalRing.closedPoint (DualNumber C) ∈ (⊤ : (Sp (DualNumber C)).Opens) from trivial))
      (w₀.s (fun _ => jG, fun _ => i₀))
    exact (congrArg (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom g.symm).trans (gs_to_valR _ _ mp _)
  have ht : (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (sval t yA (IsLocalRing.closedPoint (DualNumber C)) JA) =
      valR yA ((LPow A.A A.L (k : ℤ) (TFK (R := R) C)).U fun _ => i₀) (t.f fun _ => i₀) :=
    (congrArg _ st).trans (gs_to_valR _ _ mt _)
  have hσv : ∀ i, (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (sval (σ i) (yG ≫ UnifPre.gFK (G := G) C) (IsLocalRing.closedPoint (DualNumber C)) JG) =
      dualMap (toF R C) (valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) ((σ i).f fun _ => jG)) :=
    fun i => (congrArg _ (sσ i)).trans ((gs_to_valR _ _ mσ' _).trans (by
      rw [e₄]; exact GlobalTheory.FormalValue.valR_spMap _ _ _ mσ _))
  have hc : ∀ i, (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom
      (gs yG (IsLocalRing.closedPoint (DualNumber C)) ⊤
        (scal (fst (TFK (R := R) C) ((Over.pullback (jK R)).obj G)).left (c i))) = TrivSqZeroExt.inl (c i) := fun i => by
    have mtop : ⊤ ≤ yG ⁻¹ᵁ (⊤ : (UnifPre.GF (G := G) C).left.Opens) := fun x _ => show yG x ∈ (⊤ : (UnifPre.GF (G := G) C).left.Opens) from trivial
    rw [gs_to_valR _ _ mtop, ← resTop_top (scal _ (c i)),
      GlobalTheory.ZH.FormCount.valR_scal (algebraMap C (DualNumber C)) yG _ e₃ ⊤ mtop]
    rfl
  have E := congrArg (stalkClosedPointIso (CommRingCat.of (DualNumber C))).hom.hom (a₁.symm.trans a₂)
  rw [map_mul, map_sum, Units.val_pow_eq_pow_val, map_pow, hpw, ht] at E
  simp only [map_mul, hc, hσv] at E
  rw [← E, ← _root_.mul_assoc, h1, _root_.one_mul]

end GlobalTheory.MBLow.TanVal
