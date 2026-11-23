import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDivStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundlesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndSurjectiveOfFormIs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousPolynomialVolumePullbackCombinaStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVarietyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.VolPoly

theorem eval_eq_of_eventually {r r' : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (Ψ' : MvPolynomial (Fin (r' + 1)) ℚ)
    (a : Fin (r + 1) → ℤ) (a' : Fin (r' + 1) → ℤ)
    (h : ∀ᶠ t : ℕ in Filter.atTop,
      MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ =
        MvPolynomial.eval (fun i => (((a' + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ') :
    MvPolynomial.eval (fun i => (a i : ℚ)) Ψ = MvPolynomial.eval (fun i => (a' i : ℚ)) Ψ' := by
  have key : ∀ {r : ℕ} (Ψ : MvPolynomial (Fin (r + 1)) ℚ) (a : Fin (r + 1) → ℤ), ∃ p : Polynomial ℚ,
      ∀ t : ℕ, p.eval (t : ℚ) =
        MvPolynomial.eval (fun i => (((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i : ℤ) : ℚ)) Ψ := by
    intro r Ψ a
    refine ⟨MvPolynomial.aeval (fun i => Polynomial.C (a i : ℚ) + if i = 0 then Polynomial.X else 0) Ψ, fun t => ?_⟩
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    by_cases hi : i = 0 <;> simp [hi, Pi.single_apply]
  obtain ⟨p, hp⟩ := key Ψ a
  obtain ⟨p', hp'⟩ := key Ψ' a'
  have e : p = p' := by
    obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 h
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite t₀).image (f := fun t : ℕ => (t : ℚ)) Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    show p.eval (t : ℚ) = p'.eval (t : ℚ)
    rw [hp, hp', ht₀ t ht]
  have h0 := (hp 0).symm.trans (e ▸ hp' 0)
  simpa using h0

theorem sum_monomial_add_single {r : ℕ} (a : Fin (r + 1) → ℤ) (t : ℕ) :
    ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) ((a + Pi.single (M := fun _ => ℤ) 0 (t : ℤ) : Fin (_ + 1) → ℤ) i) =
      ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (a i) + (t : Polynomial ℤ) := by
  simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  congr 1
  rw [Fin.sum_univ_succ]
  simp

theorem exists_poly_extension (g : ℕ) (A : Polynomial ℤ → Prop) (V : Polynomial ℤ → ℚ → Prop)
    (hV : ∀ F x y, V F x → V F y → x = y)
    (hΨ : ∀ r : ℕ, ∃ Ψ : MvPolynomial (Fin r) ℚ, Ψ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      A (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) →
        V (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) (MvPolynomial.eval (fun i => (a i : ℚ)) Ψ))
    (hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, A (F + t)) :
    ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ,
      D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧
      ∀ F, A F → V F (D F) := by
  choose Ψ hh hΨ using hΨ
  have hF : ∀ F : Polynomial ℤ,
      ∑ i : Fin (F.natDegree + 1), Polynomial.monomial (i : ℕ) (F.coeff i) = F := fun F => by
    rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i))]
    exact (F.as_sum_range).symm
  refine ⟨fun F => MvPolynomial.eval (fun i : Fin (F.natDegree + 1) => (F.coeff i : ℚ)) (Ψ _), fun r => ?_,
    fun F h => ?_⟩
  · refine ⟨MvPolynomial.aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0) (Ψ (r + 1)), ?_,
      fun a => ?_⟩
    · have := (hh (r + 1)).aeval (n := 1) (Fin.snoc (α := fun _ => MvPolynomial (Fin r) ℚ) MvPolynomial.X 0)
        (fun i => by
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using MvPolynomial.isHomogeneous_zero _ _ _
          · simpa using MvPolynomial.isHomogeneous_X _ _)
      simpa using this
    · set F := ∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i) with hFa
      have e : ∑ i : Fin (r + 1), Polynomial.monomial (i : ℕ) (Fin.snoc (α := fun _ => ℤ) a 0 i) = F := by
        rw [Fin.sum_univ_castSucc]
        simp [hFa]
      have e₂ := eval_eq_of_eventually (Ψ (F.natDegree + 1)) (Ψ (r + 1)) (fun i => F.coeff i)
        (Fin.snoc (α := fun _ => ℤ) a 0) ((hA F).mono fun t ht => by
          have h₁ := hΨ _ ((fun i : Fin (F.natDegree + 1) => F.coeff i) + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          have h₂ := hΨ _ (Fin.snoc (α := fun _ => ℤ) a 0 + Pi.single (M := fun _ => ℤ) 0 (t : ℤ))
          rw [sum_monomial_add_single, hF] at h₁
          rw [sum_monomial_add_single, e] at h₂
          exact hV _ _ _ (h₁ ht) (h₂ ht))
      refine e₂.trans ?_
      rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
      congr 2
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  · have := hΨ _ (fun i : Fin (F.natDegree + 1) => F.coeff i)
    rw [hF] at this
    exact this h

theorem relAmple_of_cls_eq {K : Type} [Field K] (P : Out.PolAV (Sp K)) {M N : LB P.A.left} (hM : M.IsLB) (hN : N.IsLB)
    (e : CechPic.cls M hM = CechPic.cls N hN) (h : Out.RelAmple P.A M) : Out.RelAmple P.A N := by
  haveI : IsProper P.A.hom := P.isAb.proper
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hM] at h
  rw [relAmple_iff_isAmpleLB_of_isAffine P.A hN]
  exact h.of_lbIso hN ((CechPic.cls_eq_iff hN hM).1 e.symm)

theorem exists_vol_poly : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A), M.IsLB → FormIs P M s → ∀ (ev : Polynomial ℤ → (P.A ⟶ P.A)), ev 1 = 𝟙 P.A → (∀ F G, ev (F + G) = ev F * ev G) → (∀ F, ev (Polynomial.X * F) = ev F ≫ s) → ∃ D : Polynomial ℤ → ℚ, (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) ∧ (∀ F, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) → Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev (F)] P.L) P.g ((D F : ℚ) : ℝ)) ∧ ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) ∧ IsFinite (ev (F + t)).left := by
  intro h₁ h₂ K _ _ P M s hM hs ev e₁ eadd eX
  obtain ⟨-, emul, hform, -, hdiv, hone, -⟩ := (GlobalTheory.T.polarisationForm_intPolynomial_bundles h₁ h₂ K P M s hM hs).2 ev e₁ eadd eX
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => LB.isLB_linComb P.isLB _ _
  let b : Polynomial ℤ →+ CechPic.Pic P.A.left := AddMonoidHom.mk' (fun F => CechPic.cls _ (hB F)) fun F G => by
    have := (CechPic.cls_eq_iff (LB.isLB_div (hB _) (hB _)) (hB _)).2 (hdiv F G)
    rw [CechPic.cls_div (hB _) (hB _)] at this
    exact (sub_eq_iff_eq_add'.1 this)
  have hb : ∀ F, b F = CechPic.cls _ (hB F) := fun _ => rfl
  have hp : ∀ n, (lbPow P.L n).IsLB := fun n => LB.isLB_linComb P.isLB _ _
  have b₁ : b 1 = 2 • CechPic.cls _ P.isLB :=
    ((CechPic.cls_eq_iff (hB 1) (hp 2)).2 hone).trans (CechPic.cls_lbPow P.isLB 2 _)
  have hA : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (F + t)] P.L) := fun F => by
    have h := GlobalTheory.T.eventually_section_and_relAmple_pow_div K P P.L _ P.isLB (hB (-F)) P.ample
    have ht : Filter.Tendsto (fun t : ℕ => t * 2) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun t => by show t ≤ t * 2; omega) Filter.tendsto_id
    refine (ht.eventually h).mono fun t h => relAmple_of_cls_eq P (LB.isLB_div (hp _) (hB _)) (hB _) ?_ h.2
    rw [CechPic.cls_div (hp _) (hB _), CechPic.cls_lbPow P.isLB, ← hb, ← hb, map_neg, map_add, ← nsmul_one t,
      map_nsmul, b₁, mul_smul, sub_neg_eq_add, add_comm]
  obtain ⟨D, hD, hD'⟩ := exists_poly_extension P.g (fun F => Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L))
    (fun F x => Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g (x : ℝ))
    (fun F x y hx hy => by exact_mod_cast (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ hx hy)
    (fun r => by
      let φ : Fin r × ULift.{0} (Finset (Fin 2)) → (P.A.left ⟶ P.A.left) := fun p =>
        (psum P.A ![𝟙 P.A, ev (Polynomial.monomial (p.1 : ℕ) 1)] p.2.down).left
      obtain ⟨Φ, hΦ, hv⟩ := GlobalTheory.T.exists_homogeneousPolynomial_volume_pullback_combinations h₁ h₂ K P _ φ
      refine ⟨MvPolynomial.aeval (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
        MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1) Φ, ?_, fun a ha => ?_⟩
      · simpa using hΦ.aeval (n := 1) (fun p : Fin r × ULift.{0} (Finset (Fin 2)) =>
          MvPolynomial.C ((-1 : ℚ) ^ (2 - p.2.down.card)) * MvPolynomial.X p.1)
          fun p => (MvPolynomial.isHomogeneous_X ℚ p.1).C_mul _
      · let ε : Fin r × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => a p.1 * (-1) ^ (2 - p.2.down.card)
        have hC : (LB.LinComb P.L φ ε).IsLB := LB.isLB_linComb P.isLB _ _
        have e : CechPic.cls _ (hB (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i))) = CechPic.cls _ hC := by
          rw [← hb, map_sum, CechPic.cls_linComb P.isLB, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun i _ => ?_
          have : Polynomial.monomial (i : ℕ) (a i) = a i • Polynomial.monomial (i : ℕ) (1 : ℤ) := by
            rw [Polynomial.smul_monomial, smul_eq_mul, _root_.mul_one]
          rw [this, map_zsmul, hb]
          refine (congrArg (a i • ·) (CechPic.cls_linComb P.isLB _ _ _)).trans ?_
          simp only [Finset.smul_sum, ε, φ, mul_smul]
        have := (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hC).2.2.1 _ _ (hB _) ((CechPic.cls_eq_iff _ _).1 e.symm)
          (hv ε (relAmple_of_cls_eq P (hB _) hC e ha))
        convert this using 2
        rw [← MvPolynomial.aeval_eq_eval, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply]
        congr 2
        funext p
        simp [ε, mul_comm])
    hA
  refine ⟨D, hD, hD', fun F => (hA F).mono fun t ht => ⟨ht, ?_⟩⟩
  have hf := (GlobalTheory.FormFinite.isFinite_and_surjective_of_formIs h₁ h₂ K P _ _ (hB _) ht (hform _)).1
  rw [mul_comm, emul, Over.comp_left] at hf
  haveI : IsProper P.A.hom := P.isAb.proper
  haveI : IsSeparated ((ev 2).left ≫ P.A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (ev 2).left := IsSeparated.of_comp _ P.A.hom
  exact IsFinite.of_comp _ (ev 2).left

end GlobalTheory.VolPoly

end
