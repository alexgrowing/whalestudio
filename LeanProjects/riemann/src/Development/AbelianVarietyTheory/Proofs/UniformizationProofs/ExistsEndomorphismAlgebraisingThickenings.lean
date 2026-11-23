import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosedStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomogeneousFormSectionsEqZeroOfThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMorphismToProjectiveOfRankOneSectionsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThickeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleGeneratingSectionsAllThickeningsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EndAlg

variable {X X' : Scheme.{0}} {κ : Type}

theorem eval₂_scale {σ R A : Type} [CommRing R] [CommRing A] (φ : R →+* A) (c : A) (x : σ → A)
    {P : MvPolynomial σ R} {e : ℕ} (hP : P.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => x j * c) P = MvPolynomial.eval₂ φ x P * c ^ e := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := hP (MvPolynomial.mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, _root_.mul_one, Finsupp.sum] at hd'
  rw [← hd']
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, _root_.mul_assoc]

theorem gs_eval {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) (φ : X' ⟶ X) (z : X') (U : X.Opens)
    (h : φ z ∈ U) (x : κ → Γ(X, U)) (P : MvPolynomial κ R) :
    gs φ z U (MvPolynomial.eval₂Hom (cst f U) x P) =
      MvPolynomial.eval₂ ((X'.presheaf.germ ⊤ z trivial).hom.comp (cst (φ ≫ f) ⊤)) (fun j => gs φ z U (x j)) P := by
  rw [gs_eq φ z U h, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext r
    simp only [RingHom.comp_apply]
    rw [← gs_eq φ z U h]
    simp only [GlobalTheory.AbLaw.cst, rs, RingHom.comp_apply]
    rw [gs_res φ z le_top h, gs_eq φ z ⊤ trivial]
    have hid : X'.presheaf.map (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [show (homOfLE (le_top : (⊤ : X'.Opens) ≤ ⊤)) = 𝟙 _ from Subsingleton.elim _ _]
      exact X'.presheaf.map_id _
    rw [hid]
    simp only [CommRingCat.hom_id, RingHom.id_apply]
    rfl
  · funext j
    simp only [Function.comp_apply]
    exact (gs_eq φ z U h _).symm

theorem isUnit_gs_iff (r : X' ⟶ X) (z : X') (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h a]
  refine (X'.mem_basicOpen (U := r ⁻¹ᵁ U) ((r.app U).hom a) z h).symm.trans ?_
  rw [← Scheme.Hom.preimage_basicOpen]
  rfl

theorem exists_pull {M : LB X} (s : LB.Sec M) (π : X' ⟶ X) :
    ∃ t : LB.Sec (M.pull π), ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good M z J →
      sval t r z J = gs (r ≫ π) z _ (s.f (J (r ≫ π))) := by
  have hle : ∀ j : PUnit → M.ι, LB.wchart M (fun _ : PUnit => π) j ≤ π ⁻¹ᵁ M.U (j ⟨⟩) :=
    fun _ _ hy => Set.mem_iInter.1 hy ⟨⟩
  refine ⟨⟨fun j => (X'.presheaf.map (homOfLE (hle j)).op).hom ((π.app (M.U (j ⟨⟩))).hom (s.f (j ⟨⟩))),
    fun i j => ?_⟩, ?_⟩
  · refine ReciprocityTheory.ChartRestriction.G.DVR.app_compat_generic π (hle i) (hle j) (s.f _) (s.f _) _ (s.compat _ _) _ ?_
    show (∏ k : PUnit, _) = _
    rw [Fintype.prod_unique, zpow_one]
  · intro Z r z J hJ
    have hm := hJ.mem (fun _ : PUnit => π) r
    have hz : (r ≫ π) z ∈ M.U (J (r ≫ π)) := hJ (r ≫ π)
    show gs r z _ ((X'.presheaf.map (homOfLE (hle _)).op).hom ((π.app _).hom (s.f _))) = _
    rw [gs_res r z (hle _) hm, gs_pull r π z _ hz]

theorem exists_prod {H : LB X} (hH : H.IsLB) (p g : X' ⟶ X) (t : ℤ) (s : LB.Sec H)
    (u : LB.Sec (LB.LinComb H (K := Fin 2) ![p, g] ![t, -1])) :
    ∃ w : LB.Sec (LB.LinComb H (K := PUnit) (fun _ => p) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ g) z _ (s.f (J (r ≫ g))) * sval u r z J := by
  obtain ⟨t0, ht0⟩ := exists_pull s g
  have hF : FormEq (Sum.elim (fun _ : PUnit => g) ![p, g]) (Sum.elim (fun _ : PUnit => (1 : ℤ)) ![t, -1])
      (fun _ : PUnit => p) (fun _ => t) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨w, hw⟩ := exists_sec hH hF (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.mulSec t0 u)
  refine ⟨w, fun Z r z J hJ => ?_⟩
  rw [hw Z r z J hJ, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_mulSec t0 u r z hJ, ht0 Z r z J hJ]

private theorem gs_sec_chart_transition {X Z : Scheme.{0}} {H : LB X} (s : LB.Sec H) (ψ : Z ⟶ X) (z : Z) (k k' : H.ι)
    (hk : ψ z ∈ H.U k) (hk' : ψ z ∈ H.U k') :
    gs ψ z (H.U k) (s.f k) = gs ψ z (H.U k ⊓ H.U k') (H.g k k' : Γ(X, H.U k ⊓ H.U k')) * gs ψ z (H.U k') (s.f k') := by
  have hkk : ψ z ∈ H.U k ⊓ H.U k' := TopologicalSpace.Opens.mem_inf.2 ⟨hk, hk'⟩
  rw [← gs_res ψ z (inf_le_left : H.U k ⊓ H.U k' ≤ H.U k) hkk, s.compat k k', gs_mul ψ z _ hkk,
    gs_res ψ z inf_le_right hkk]

theorem exists_end_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, f e ≫ Y.hom = pullback.fst Y.hom (thick R I e) ≫ Y.hom) → (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ g : Y ⟶ Y, ∀ e, pullback.fst Y.hom (thick R I e) ≫ g.left = f e := by
  intro R _ _ _ I hI Y hsm hpr f hf hfc
  obtain ⟨H, hH, n, s, hva⟩ := id hpr
  obtain ⟨t, m, u, hcov, hu⟩ := GlobalTheory.T.exists_compatible_generatingSections_all_thickenings R I Y H n s hsm hH hva f hfc
  have hw0 : ∀ e (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ w : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => pullback.fst Y.hom (thick R I e)) (fun _ => t)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval w r z J = gs (r ≫ f e) z _ ((s i).f (J (r ≫ f e))) * sval (u e j) r z J :=
    fun e i j => exists_prod hH (pullback.fst Y.hom (thick R I e)) (f e) t (s i) (u e j)
  choose w hw using hw0
  have hS0 : ∀ (i : Fin (n + 1)) (j : Fin (m + 1)), ∃ S : LB.Sec (LB.LinComb H (K := PUnit)
      (fun _ => 𝟙 Y.left) (fun _ => t)),
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good H z J →
        sval S (r ≫ pullback.fst Y.hom (thick R I e)) z J = sval (w e i j) r z J := by
    intro i j
    refine GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hsm hpr Y.left H PUnit (fun _ => 𝟙 Y.left) (fun _ => t)
      (fun e _ => pullback.fst Y.hom (thick R I e)) hH (fun e k => Category.comp_id _) (fun e => w e i j) ?_
    intro e z J hJ
    rw [hw (e + 1) i j _ _ z J hJ, hw e i j _ _ z J hJ, hfc e, Category.id_comp, hu e j z J hJ]
  choose S hS using hS0
  have hN : (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).IsLB := LB.isLB_linComb hH _ _
  have key : ∀ e (z : (thickObj R I e Y).left) (k' : PUnit → H.ι),
      pullback.fst Y.hom (thick R I e) z ∈ H.U (k' ⟨⟩) →
      ∃ J, Good H z J ∧ f e z ∈ H.U (J (f e)) ∧ ∀ i j,
        gs (pullback.fst Y.hom (thick R I e)) z
            ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k') ((S i j).f k') =
          gs (f e) z (H.U (J (f e))) ((s i).f (J (f e))) * sval (u e j) (𝟙 _) z J := by
    intro e z k' hz
    obtain ⟨J, hJ, hJk⟩ := exists_good H hH z (fun _ : PUnit => 𝟙 _ ≫ pullback.fst Y.hom (thick R I e))
      (fun _ => k' ⟨⟩) (fun _ _ _ => rfl) (fun _ => by simpa using hz)
    refine ⟨J, hJ, hJ (f e), fun i j => ?_⟩
    have h1 := (hS i j e _ (𝟙 _) z J hJ).trans (hw e i j _ (𝟙 _) z J hJ)
    rw [sval_of (S i j) _ z J k' (fun k => by cases k; simpa using hJk ⟨⟩)] at h1
    rw [Category.id_comp, Category.id_comp] at h1
    exact h1
  have hcov' : (⨆ i, ⨆ j, nonzeroLocus (S i j)) = ⊤ := by
    have hjac : I ≤ (⊥ : Ideal R).jacobson := by have := hI; exact IsAdicComplete.le_jacobson_bot (I := I)
    have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy R Y.left Y.hom hpr
    refine GlobalTheory.T.open_eq_top_of_contains_special_part_universallyClosed R I hjac Y _ fun z => ?_
    have hz1 : z ∈ ⨆ j, nonzeroLocus (u 0 j) := by rw [hcov]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hz1
    unfold nonzeroLocus at hj
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hj
    have hz2 : f 0 z ∈ ⨆ i, nonzeroLocus (s i) := by rw [hva.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz2
    unfold nonzeroLocus at hi
    obtain ⟨kk0, hkk0⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have hkU : z ∈ LB.wchart H ![pullback.fst Y.hom (thick R I 0), f 0] k := Scheme.basicOpen_le _ _ hk
    have hq : pullback.fst Y.hom (thick R I 0) z ∈ H.U (k 0) := Set.mem_iInter.1 hkU 0
    obtain ⟨J, hJ, hJe, hv⟩ := key 0 z (fun _ => k 0) hq
    have hqN : pullback.fst Y.hom (thick R I 0) z ∈
        (LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U (fun _ => k 0) :=
      Set.mem_iInter.2 fun _ => hq
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩⟩
    unfold nonzeroLocus
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k 0, ?_⟩
    rw [← isUnit_gs_iff _ _ _ hqN, hv i j]
    refine IsUnit.mul ?_ ?_
    · have hm0 : f 0 z ∈ H.U kk0 := Scheme.basicOpen_le _ _ hkk0
      have hu0 := (isUnit_gs_iff (f 0) z (H.U kk0) hm0 ((s i).f kk0)).2 hkk0
      rw [gs_sec_chart_transition (s i) (f 0) z kk0 (J (f 0)) hm0 hJe] at hu0
      exact isUnit_of_mul_isUnit_right hu0
    · have hm := hJ.mem ![pullback.fst Y.hom (thick R I 0), f 0] (𝟙 _)
      rw [sval_of (u 0 j) (𝟙 _) z J _ (fun _ => rfl), sec_trans (u 0 j) (𝟙 _) z hm hkU]
      exact (Units.isUnit _).mul ((isUnit_gs_iff _ _ _ hkU _).2 hk)
  have hrel : ∀ i i' j j' k, (S i j).f k * (S i' j').f k = (S i j').f k * (S i' j).f k := by
    intro i i' j j' k
    have hF : (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2 * MvPolynomial.X 3 :
        MvPolynomial (Fin 4) R).IsHomogeneous 2 :=
      ((MvPolynomial.isHomogeneous_X R 0).mul (MvPolynomial.isHomogeneous_X R 1)).sub
        ((MvPolynomial.isHomogeneous_X R 2).mul (MvPolynomial.isHomogeneous_X R 3))
    have h := GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin 4) ![S i j, S i' j', S i j', S i' j] 2 _ hN hF ?_ k
    · simpa [sub_eq_zero] using h
    · intro e z k hz
      obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
      rw [gs_eval Y.hom _ z _ hz]
      simp [hv]
      ring
  have hhom : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d →
      (∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom (H.U k)) (fun i => (s i).f k) F = 0) →
      ∀ j k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst Y.hom ((LB.LinComb H (K := PUnit) (fun _ => 𝟙 Y.left) (fun _ => t)).U k))
        (fun i => (S i j).f k) F = 0 := by
    intro d F hF h0 j
    refine GlobalTheory.T.homogeneousForm_sections_eq_zero_of_thickenings R I hI Y hsm hpr _ (Fin (n + 1)) (fun i => S i j) d F hN hF ?_
    intro e z k hz
    obtain ⟨J, hJ, hJe, hv⟩ := key e z k (Set.mem_iInter.1 hz ⟨⟩)
    rw [gs_eval Y.hom _ z _ hz]
    simp only [hv]
    have h2 := gs_eval Y.hom (f e) z (H.U (J (f e))) hJe (fun i => (s i).f (J (f e))) F
    rw [h0, hf e] at h2
    have hz0 : gs (f e) z (H.U (J (f e))) 0 = 0 := by rw [gs_eq _ _ _ hJe, map_zero, map_zero]
    rw [eval₂_scale _ (sval (u e j) (𝟙 _) z J) (fun i => gs (f e) z (H.U (J (f e))) ((s i).f (J (f e)))) hF,
      ← h2, hz0, zero_mul]
  obtain ⟨φ, hφ, huniq⟩ := GlobalTheory.T.exists_morphism_to_projective_of_rank_one_sections R Y.left Y.hom H n s hH hva Y.left Y.hom _ m S hN hcov' hrel hhom
  refine ⟨Over.homMk φ hφ, fun e => ?_⟩
  refine huniq _ (pullback.fst Y.hom (thick R I e)) (f e) (hf e) ?_
  intro z k k' i i' j hzk hzk'
  obtain ⟨J, hJ, hJe, hv⟩ := key e z k' (Set.mem_iInter.1 hzk' ⟨⟩)
  rw [hv, hv, gs_sec_chart_transition (s i) (f e) z k (J (f e)) hzk hJe, gs_sec_chart_transition (s i') (f e) z k (J (f e)) hzk hJe]
  ring

end GlobalTheory.EndAlg
