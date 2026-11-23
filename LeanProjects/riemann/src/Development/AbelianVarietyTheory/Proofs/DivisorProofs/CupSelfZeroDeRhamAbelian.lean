import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullbackAxesCohomologyProjectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToStructureH1SurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamHypercohomologyCupAnticommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCupOneFormsZeroImpCoordinatesZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupSumClosedGlobalOneFormsEqZeroIffSumWedgeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamH1RankPrimitiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

section Helpers

variable {R : Type} [CommRing R]

theorem cup_self_eq_zero_of_wedgeO' {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F)
    (x : CatCoh.H1 F) : cup F x x = 0 := by
  obtain ⟨e, he⟩ := hW
  rw [← he]
  have : exteriorPower.ιMulti R 2 ![x, x] = 0 :=
    AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)
  rw [this, map_zero]

theorem fn_cupZZ_self_exact {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R} (hW : WedgeO F) (c : cechDeRhamTotalCocyclesOne F) :
    ∃ f, d1 F f = (cupZZ F c c).1.1 := by
  have h := cup_self_eq_zero_of_wedgeO' hW (H1.mk F (cechDeRhamTotalCocyclesOne.fn F c))
  rw [cup_mk, H2.mk_eq_zero] at h
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf⟩

variable {Y A : Over (Sp R)}

theorem pH2_cupHH_over (f : Y ⟶ A) (a b : HH1 A.hom) :
    deRhamH2Pullback f (cupHH A.hom a b) = cupHH Y.hom (deRhamH1Pullback f a) (deRhamH1Pullback f b) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.1 a b

theorem toHO1_pH1_over (f : Y ⟶ A) (a : HH1 A.hom) : toHO1 Y.hom (deRhamH1Pullback f a) = pO1 f (toHO1 A.hom a) :=
  ((pull_comp_cup_id).2.1 R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f)).2.2 a

theorem pH1_clAll_over (f : Y ⟶ A) (hc : Closed1 (OAff A.hom) = ⊤) (hc' : Closed1 (OAff Y.hom) = ⊤)
    (w : GlobForm A.hom) : deRhamH1Pullback f (clAll (OAff A.hom) hc w) = clAll (OAff Y.hom) hc' (pF f w) :=
  GlobalTheory.T.pull_closed_form_class R R _ _ A.hom Y.hom (RingHom.id R) f.left (ovw f) hc hc' w

end Helpers

section Wsum

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem wsum_finAppend {n n' : ℕ} (u v : Fin n → Glob1 F) (u' v' : Fin n' → Glob1 F) :
    wsum F (Fin.append u u') (Fin.append v v') = wsum F u v + wsum F u' v' := by
  funext T
  simp only [wsum, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.add_apply]

theorem wsum_neg_first {n : ℕ} (u v : Fin n → Glob1 F) : wsum F (fun k ↦ -u k) v = -wsum F u v := by
  funext T
  simp only [wsum, Submodule.coe_neg, Pi.neg_apply, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]

theorem wsum_eq_add_of_cupSum_eq (hc : Closed1 F = ⊤) (hsur : Function.Surjective (toO F)) {m : ℕ}
    (u₁ v₁ u₂ v₂ u₃ v₃ : Fin m → Glob1 F)
    (h : ∑ k, cupHyp F (clAll F hc (u₁ k)) (clAll F hc (v₁ k)) =
      ∑ k, cupHyp F (clAll F hc (u₂ k)) (clAll F hc (v₂ k)) + ∑ k, cupHyp F (clAll F hc (u₃ k)) (clAll F hc (v₃ k))) :
    wsum F u₁ v₁ = wsum F u₂ v₂ + wsum F u₃ v₃ := by
  have h2 : ∑ k, cupHyp F (clAll F hc (Fin.append (Fin.append u₁ (fun k ↦ -u₂ k)) (fun k ↦ -u₃ k) k))
      (clAll F hc (Fin.append (Fin.append v₁ v₂) v₃ k)) = 0 := by
    rw [Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, map_neg, LinearMap.neg_apply, Finset.sum_neg_distrib]
    rw [h]
    abel
  have h3 := (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R C F hc hsur _ _ _).1 h2
  rw [wsum_finAppend, wsum_finAppend, wsum_neg_first, wsum_neg_first] at h3
  rw [← sub_eq_zero, ← h3]
  abel

end Wsum

theorem cupHH_self_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ a : HH1 A.hom, cupHH A.hom a a = 0 := by
  intro R _ A _ g hA hs a
  have hb := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hb2 := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hc := GlobalTheory.T.abelianScheme_globalOneForms_closed R A g hA hs
  have hc2 := GlobalTheory.T.abelianScheme_globalOneForms_closed R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hsur := GlobalTheory.T.de_rham_to_structure_h1_surjective R A g hA hs
  have hsur2 := GlobalTheory.T.de_rham_to_structure_h1_surjective R (A ⊗ A) (g + g) hb.2.2.1 hb.2.2.2
  have hW := (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hs).2.1
  have hP : ∀ x : HH1 A.hom, deRhamH1Pullback μ[A] x = deRhamH1Pullback (fst A A) x + deRhamH1Pullback (snd A A) x := (GlobalTheory.T.de_rham_h1_rank_primitive R A g hA hs).2
  have hPF : ∀ x : GlobForm A.hom, pF μ[A] x = pF (fst A A) x + pF (snd A A) x := GlobalTheory.T.abelianScheme_globalOneForms_primitive R A g hA hs
  have hax := GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A
  have anti := GlobalTheory.T.cechDeRhamHypercohomologyCup_anticomm R _ (OAff (A ⊗ A).hom)

  have hprim : deRhamH2Pullback μ[A] (cupHH A.hom a a) =
      deRhamH2Pullback (fst A A) (cupHH A.hom a a) + deRhamH2Pullback (snd A A) (cupHH A.hom a a) := by
    rw [pH2_cupHH_over, pH2_cupHH_over, pH2_cupHH_over, hP a]
    have h := anti (deRhamH1Pullback (fst A A) a) (deRhamH1Pullback (snd A A) a)
    simp only [map_add, LinearMap.add_apply]
    linear_combination (norm := module) h

  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective _ a
  obtain ⟨n, a', w, hz⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R _ (OAff A.hom) hb.1 hb.2.1 hc hsur (cupZZ _ c c) (fn_cupZZ_self_exact hW c)
  rw [← cupHyp_mk] at hz
  change cupHH A.hom _ _ = _ at hz
  set z := cupHH A.hom (Hyp1.mk _ c) (Hyp1.mk _ c)
  clear_value z

  have hcross : ∑ k, (cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (fst A A) (a' k)) (clAll _ hc2 (pF (snd A A) (w k))) +
      cupHyp (OAff (A ⊗ A).hom) (deRhamH1Pullback (snd A A) (a' k)) (clAll _ hc2 (pF (fst A A) (w k)))) = 0 := by
    have h := hprim
    rw [hz] at h
    simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2, hP, hPF, map_add, LinearMap.add_apply,
      Finset.sum_add_distrib] at h
    rw [Finset.sum_add_distrib]
    linear_combination (norm := module) h

  have hk : ∀ l : Glob1 (OAff A.hom) →ₗ[R] R, ∑ k, l (w k) • toO (OAff A.hom) (a' k) = 0 := by
    intro l
    have h2 : ∑ k, cupHH (A ⊗ A).hom
        (Fin.append (fun k ↦ deRhamH1Pullback (fst A A) (a' k)) (fun k ↦ deRhamH1Pullback (snd A A) (a' k)) k)
        (clAll _ hc2 (Fin.append (fun k ↦ pF (snd A A) (w k)) (fun k ↦ pF (fst A A) (w k)) k)) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [← Finset.sum_add_distrib]
      exact hcross
    have h3 := GlobalTheory.T.sum_cup_oneForms_zero_imp_coordinates_zero R _ _ hb2.1 hb2.2.1 hc2 hsur2 (n + n) _ _ h2
      (l ∘ₗ pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
    rw [Fin.sum_univ_add] at h3
    simp only [Fin.append_left, Fin.append_right, LinearMap.comp_apply, (hax.2.1 _).2.2.2.1,
      (hax.2.1 _).2.2.2.2.1, map_zero, zero_smul, Finset.sum_const_zero, add_zero] at h3
    have h4 := congrArg (pO1 (lift (𝟙 A) (toUnit A ≫ η[A]))) h3
    simp only [map_sum, map_smul, map_zero] at h4
    simpa only [toHO1_pH1_over, (hax.1 _).1] using h4

  obtain ⟨m, ⟨Φ⟩⟩ := hb.1
  obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R _ (OAff A.hom) hb.2.1 m Φ
  have hu : ∀ i, ∃ u : Glob1 (OAff A.hom), clAll _ hc u = ∑ k, L i (w k) • a' k := by
    intro i
    have hm : ∑ k, L i (w k) • a' k ∈ Fil1 (OAff A.hom) := by
      rw [Fil1, LinearMap.mem_ker, map_sum]
      simpa only [map_smul] using hk (L i)
    rw [Fil1_eq_range] at hm
    obtain ⟨ω, hω⟩ := hm
    refine ⟨ω.1, ?_⟩
    rw [← hω]
    rfl
  choose u hu using hu
  have hz2 : z = ∑ i, cupHyp (OAff A.hom) (clAll _ hc (u i)) (clAll _ hc (Φ.w i)) := by
    rw [hz]
    simp only [hu]
    conv_lhs => enter [2, k]; rw [hL (w k)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Finset.sum_comm

  have hwp : wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (Φ.w k)) =
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (Φ.w k)) +
      wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (Φ.w k)) := by
    have h := hprim
    rw [hz2] at h
    simp only [map_sum, pH2_cupHH_over, pH1_clAll_over _ hc hc2] at h
    exact wsum_eq_add_of_cupSum_eq _ hc2 hsur2 _ _ _ _ _ _ h
  have hw0 := GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme R A g hA hs m u Φ.w hwp
  rw [hz2]
  exact (GlobalTheory.T.cupSum_closedGlobalOneForms_eq_zero_iff_sumWedge R _ _ hc hsur m u Φ.w).2 hw0

end GlobalTheory.AbCoh
