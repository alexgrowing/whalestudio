import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AbelianHolomorphicFrameReadingConstOfFormsCancel
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingCorrMulInv
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GeneratorReadingPullbackPeriodRigid

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValSym

section Maps

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Over S}

theorem translPt_eq (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_snd (x : T ⟶ A) : translT A x ≫ snd T A = (fst T A ≫ x) * snd T A := by unfold translT; rw [lift_snd, translPt_eq]

theorem translT_fst (x : T ⟶ A) : translT A x ≫ fst T A = fst T A := by unfold translT; exact lift_fst _ _

theorem negT_snd : negT A T ≫ snd T A = (snd T A)⁻¹ := by unfold negT; rw [lift_snd]; rfl

theorem negT_fst : negT A T ≫ fst T A = fst T A := by unfold negT; exact lift_fst _ _

theorem snd_inv : snd T A ≫ (GrpObj.inv : A ⟶ A) = (snd T A)⁻¹ := rfl

theorem translT_inv_translPt (x : T ⟶ A) : translT A x⁻¹ ≫ translPt A x = snd T A := by rw [translPt_eq, comp_mul, ← Category.assoc, translT_fst, translT_snd, GrpObj.comp_inv, mul_inv_cancel_left]

theorem negT_translPt [IsCommMonObj A] (x : T ⟶ A) :
    negT A T ≫ translPt A x = translT A x⁻¹ ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)) := by
  rw [translPt_eq, comp_mul, ← Category.assoc, negT_fst, negT_snd, ← Category.assoc, translT_snd, ← Hom.inv_def,
    mul_inv_rev, GrpObj.comp_inv, inv_inv]
  exact mul_comm _ _

theorem ptSecT_translT (a x : T ⟶ A) : ptSecT A a ≫ translT A x = ptSecT A (x * a) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, translT_fst]
    unfold ptSecT
    simp
  · rw [Category.assoc, translT_snd, comp_mul, ← Category.assoc]
    unfold ptSecT
    simp

theorem ptSecT_negT (a : T ⟶ A) : ptSecT A a ≫ negT A T = ptSecT A a⁻¹ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, negT_fst]
    unfold ptSecT
    simp
  · rw [Category.assoc, negT_snd, GrpObj.comp_inv]
    unfold ptSecT
    simp

end Maps

section Frame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem e_zero : Φ.e 0 = 1 := by
  have h := Φ.e_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := Φ.e 0) (by rw [_root_.mul_one]; exact h.symm)

theorem e_neg (z : Fin g → ℂ) : Φ.e (-z) = (Φ.e z)⁻¹ := by
  have h := Φ.e_add (-z) z
  rw [neg_add_cancel, GlobalTheory.AnValSym.e_zero Φ] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private theorem isHolFam_comp' {Y Y' : Scheme.{0}} {n : ℕ} {e : (Fin n → ℂ) → (Sp ℂ ⟶ Y)} (he : IsHolFam e)
    (h : Y ⟶ Y') : IsHolFam (fun z => e z ≫ h) := by
  intro U f
  obtain ⟨ho, hd⟩ := he (h ⁻¹ᵁ U) (h.app U f)
  have hv : ∀ z, valAt' (e z ≫ h) U f = valAt' (e z) (h ⁻¹ᵁ U) (h.app U f) := by
    intro z
    unfold valAt'
    by_cases hz : ⊤ ≤ e z ⁻¹ᵁ (h ⁻¹ᵁ U)
    · rw [dif_pos hz, dif_pos (by exact hz)]
      unfold valAt
      rfl
    · rw [dif_neg hz, dif_neg (by exact hz)]
  refine ⟨ho, ?_⟩
  simp only [hv]
  exact hd

theorem hol_ptSecT : IsHolFam (fun z => ((ptSecT A (Φ.e z)).left : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)) := by
  have hA : ∀ z, (Φ.e z).left ≫ A.hom = x0 := fun z => Over.w (Φ.e z)
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolFam_vtfLift A.hom x0 (fun z => (Φ.e z).left) hA Φ.hol
  have h2 := isHolFam_comp' h1 (pullbackSymmetry A.hom x0).hom
  have key : (fun z => ((ptSecT A (Φ.e z)).left : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left)) =
      fun z => ReciprocityTheory.ChartRestriction.G.PullbackSections.vtfLift A.hom x0 (fun z => (Φ.e z).left) hA z ≫ (pullbackSymmetry A.hom x0).hom := by
    funext z
    apply pullback.hom_ext
    · have h := congrArg Over.Hom.left (show ptSecT A (Φ.e z) ≫ fst (Over.mk x0) A = 𝟙 _ by
        unfold ptSecT
        exact lift_fst _ _)
      rw [Over.comp_left] at h
      simp only [Over.mk_hom, Category.assoc, pullbackSymmetry_hom_comp_fst]
      unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.vtfLift
      rw [pullback.lift_snd]
      exact h
    · have h := congrArg Over.Hom.left (show ptSecT A (Φ.e z) ≫ snd (Over.mk x0) A = Φ.e z by
        unfold ptSecT
        exact lift_snd _ _)
      rw [Over.comp_left] at h
      simp only [Over.mk_hom, Category.assoc, pullbackSymmetry_hom_comp_snd]
      unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.vtfLift
      rw [pullback.lift_fst]
      exact h
  rw [key]
  exact h2

theorem genRd_one {Z : Scheme.{0}} (q : Sp ℂ ⟶ Z) :
    Φ.GenRd (K := PEmpty) PEmpty.elim PEmpty.elim (LB.oneGen L.L) q PEmpty.elim 1 := by
  refine ⟨fun k => k.elim, fun j hj => ?_⟩
  simp only [Finset.univ_eq_empty, Finset.prod_empty, _root_.mul_one]
  unfold LB.oneGen
  exact ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one q _ hj

theorem neg_const [IsCommMonObj A] (k : ℤ) (nu : LB.Gen (negLB A L.L k (Over.mk x0))) (hnu : nu.IsGen) :
    ∃ v : ℂ, v ≠ 0 ∧ ∀ z, Φ.GenRd (K := Fin 2)
      ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] nu
      (ptSecT A (Φ.e z)).left ![z, -z] v := by
  have hq : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A).left = (Φ.e z).left := fun z => by
    rw [← Over.comp_left]
    unfold ptSecT
    rw [lift_snd]
  have hq' : ∀ z, (ptSecT A (Φ.e z)).left ≫ (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left = (Φ.e (-z)).left :=
    fun z => by
      rw [← Over.comp_left, ← Category.assoc]
      unfold ptSecT
      rw [lift_snd, ← Hom.inv_def, e_neg Φ z]
  have hmap : ∀ (z : Fin g → ℂ) (i : Fin 2), (ptSecT A (Φ.e z)).left ≫
      (![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) i =
      (Φ.e ((![LinearMap.id, -LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) i z)).left := by
    intro z i
    fin_cases i
    · simpa using hq z
    · simpa using hq' z
  have hper : ∀ gm ∈ Φ.lat, (∀ z, (ptSecT A (Φ.e (z + gm))).left = (ptSecT A (Φ.e z)).left) ∧
      ∀ i, (![LinearMap.id, -LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) i gm ∈ Φ.lat := by
    intro gm hgm
    refine ⟨fun z => ?_, fun i => ?_⟩
    · rw [Φ.e_add, (Φ.e_ker gm).2 hgm, _root_.mul_one]
    · fin_cases i
      · simpa using hgm
      · simpa using Φ.lat.neg_mem hgm
  have hherm : ∀ z w, ∑ i, ((![k, -k] : Fin 2 → ℤ) i : ℂ) *
      hermForm Φ.Hm ((![LinearMap.id, -LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) i z)
        ((![LinearMap.id, -LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) i w) = 0 := by
    intro z w
    simp [Fin.sum_univ_two, hermForm, Matrix.mulVec_neg]
  obtain ⟨⟨v, hv, hR⟩, -⟩ := GlobalTheory.AnVal.genRd_const S A L x0 g Φ _ (Fin 2)
    ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] nu hnu g
    (fun z => (ptSecT A (Φ.e z)).left) ![LinearMap.id, -LinearMap.id] Φ.lat (hol_ptSecT Φ) hmap Φ.span hper hherm
  refine ⟨v, hv, fun z => ?_⟩
  have e2 : (fun i => (![LinearMap.id, -LinearMap.id] : Fin 2 → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) i z) = ![z, -z] := by
    funext i
    fin_cases i <;> simp
  have h2 := hR z
  rwa [e2] at h2

end Frame

theorem sq_const_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ), Φ.ThConst k U x c → (∃ nu : LB.Gen (negLB A L.L k (Over.mk x0)), nu.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (symGen A L.L k U nu) (LB.oneGen L.L)) → c ^ 2 = 1 := by
  intro S A _ _ L x0 g Φ k U x c hT hc
  obtain ⟨nu, hnu, hcorr⟩ := hc
  unfold symGen at hcorr
  obtain ⟨hpt, hU⟩ := hT
  obtain ⟨v, hv, hnuR⟩ := neg_const Φ k nu hnu
  have e0 : Φ.e 0 = 1 := e_zero Φ
  have hx' : Φ.e (-x) = U.pt⁻¹ := by rw [e_neg, hpt]
  have hp1 : (ptSecT A (Φ.e 0)).left ≫ (translT A U.pt⁻¹).left = (ptSecT A (Φ.e (-x))).left := by
    rw [← Over.comp_left, ptSecT_translT, e0, _root_.mul_one, hx']
  have hp3 : (ptSecT A (Φ.e 0)).left ≫ (negT A (Over.mk x0)).left = (ptSecT A (Φ.e 0)).left := by
    rw [← Over.comp_left, ptSecT_negT, e0, inv_one]
  have R1 := (GlobalTheory.AnVal.AnFr.genRd_pullGen_iff Φ ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ
    (translT A U.pt⁻¹).left (ptSecT A (Φ.e 0)).left ![-x, x + -x] (c * fock Φ.Hm k x (fun _ => 1) (-x))).2
    (by rw [hp1]; exact hU (-x))
  have R2 := hnuR 0
  have R3 := (GlobalTheory.AnVal.AnFr.genRd_pullGen_iff Φ ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ
    (negT A (Over.mk x0)).left (ptSecT A (Φ.e 0)).left ![0, x + 0] (c * fock Φ.Hm k x (fun _ => 1) 0)).2
    (by rw [hp3]; exact hU 0)
  have R4a := (GlobalTheory.AnVal.AnFr.genRd_pullGen_iff Φ
    ![(snd (Over.mk x0) A).left, (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left] ![k, -k] nu
    (translT A U.pt⁻¹).left (ptSecT A (Φ.e 0)).left ![-x, -(-x)] v).2
    (by rw [hp1]; exact hnuR (-x))
  have G := GlobalTheory.AnValGenCorr.genRd_corr_mul_inv S A L x0 g Φ
  have R4 := (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ R4a R4a).2.2.2
  have M1 := (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 R2).2.2.1
  have M2 := (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ R3 R4).2.2.1
  have MT := (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 M2).2.2.1
  have O := genRd_one Φ (ptSecT A (Φ.e 0)).left
  obtain ⟨J, hJc, hJ⟩ := (G _ _ _ _ _ _ _ _ _ _ _ _ _ _ MT O).1 hcorr
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.prod_empty, Sum.elim_inl,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one] at hJ
  have m2 : (translT A U.pt⁻¹).left ≫ (translPt A U.pt).left = (snd (Over.mk x0) A).left := by
    rw [← Over.comp_left, translT_inv_translPt]
  have m5 : (negT A (Over.mk x0)).left ≫ (snd (Over.mk x0) A).left = (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, negT_snd, snd_inv]
  have m6 : (negT A (Over.mk x0)).left ≫ (translPt A U.pt).left =
      (translT A U.pt⁻¹).left ≫ (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, negT_translPt, Over.comp_left]
  simp only [m2, m5, m6, add_neg_cancel, neg_zero, add_zero, neg_neg] at hJ
  have pt1 : (ptSecT A (Φ.e 0)).left ≫ ((translT A U.pt⁻¹).left ≫ (snd (Over.mk x0) A).left) = (Φ.e (-x)).left := by
    rw [← Category.assoc, hp1, ← Over.comp_left]
    unfold ptSecT
    rw [lift_snd]
  have pt2 : (ptSecT A (Φ.e 0)).left ≫ (snd (Over.mk x0) A).left = (Φ.e 0).left := by
    rw [← Over.comp_left]
    unfold ptSecT
    rw [lift_snd]
  have pt3 : (ptSecT A (Φ.e 0)).left ≫ (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left = (Φ.e 0).left := by
    rw [← Over.comp_left, ← Category.assoc]
    unfold ptSecT
    rw [lift_snd, ← Hom.inv_def, e0, inv_one]
  have pt4 : (ptSecT A (Φ.e 0)).left ≫ ((translT A U.pt⁻¹).left ≫ (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left) =
      (Φ.e x).left := by
    rw [← Category.assoc, hp1, ← Over.comp_left, ← Category.assoc]
    unfold ptSecT
    rw [lift_snd, ← Hom.inv_def, ← e_neg Φ, neg_neg]
  have hF : ∀ ψ p, (ptSecT A (Φ.e 0)).left ≫ ψ = (Φ.e p).left → Φ.fr (J ψ) p ^ k ≠ 0 :=
    fun ψ p h => zpow_ne_zero _ (Φ.fr_ne _ _ (by rw [← h]; exact hJc ψ))
  have n1 := hF _ (-x) pt1
  have n2 := hF _ 0 pt2
  have n3 := hF _ 0 pt3
  have n4 := hF _ x pt4
  simp only [zpow_neg] at hJ
  generalize Φ.fr (J ((translT A U.pt⁻¹).left ≫ (snd (Over.mk x0) A).left)) (-x) ^ k = a1 at hJ n1
  generalize Φ.fr (J (snd (Over.mk x0) A).left) 0 ^ k = a2 at hJ n2
  generalize Φ.fr (J (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left) 0 ^ k = a3 at hJ n3
  generalize Φ.fr (J ((translT A U.pt⁻¹).left ≫ (snd (Over.mk x0) A ≫ (GrpObj.inv : A ⟶ A)).left)) x ^ k = a4 at hJ n4
  have hf : fock Φ.Hm k x (fun _ => 1) (-x) * fock Φ.Hm k x (fun _ => 1) 0 = 1 := by
    simp only [fock, _root_.mul_one]
    rw [← Complex.exp_add]
    have hH1 : hermForm Φ.Hm (-x) x = -hermForm Φ.Hm x x := by simp [hermForm]
    have hH0 : hermForm Φ.Hm 0 x = 0 := by simp [hermForm]
    rw [hH1, hH0, ← Complex.exp_zero]
    congr 1
    ring
  have hP : a1 * a2⁻¹ * (a2 * a3⁻¹) * (a3 * a4⁻¹ * (a1⁻¹ * a4)) = 1 := by
    rw [show a1 * a2⁻¹ * (a2 * a3⁻¹) * (a3 * a4⁻¹ * (a1⁻¹ * a4)) =
      (a1 * a1⁻¹) * (a2 * a2⁻¹) * (a3 * a3⁻¹) * (a4 * a4⁻¹) by ring]
    rw [mul_inv_cancel₀ n1, mul_inv_cancel₀ n2, mul_inv_cancel₀ n3, mul_inv_cancel₀ n4]
    norm_num
  rw [hP, _root_.mul_one] at hJ
  rw [show c * fock Φ.Hm k x (fun _ => 1) (-x) * v * (c * fock Φ.Hm k x (fun _ => 1) 0 * v⁻¹) =
    c ^ 2 * (fock Φ.Hm k x (fun _ => 1) (-x) * fock Φ.Hm k x (fun _ => 1) 0) * (v * v⁻¹) by ring,
    mul_inv_cancel₀ hv, hf, _root_.mul_one, _root_.mul_one] at hJ
  exact hJ

end GlobalTheory.AnValSym
