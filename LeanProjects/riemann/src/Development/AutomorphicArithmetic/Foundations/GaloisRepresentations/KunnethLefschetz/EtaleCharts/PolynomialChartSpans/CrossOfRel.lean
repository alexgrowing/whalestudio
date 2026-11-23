import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsHomogeneousGeneratorsIdealSheafClosedImmer
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsBlowupAffineChartCoverOfSpanEq
import Development.AutomorphicArithmetic.WhittakerHecke.CechCocycleLineBundle
import Development.AutomorphicArithmetic.WhittakerHecke.SectionsGeneratedOverAffineProductCover
import Development.AutomorphicArithmetic.WhittakerHecke.IsUnitChartCoordAndHomogeneousChartTransition
import Development.AutomorphicArithmetic.WhittakerHecke.RestrictMemNonZeroDivisorsOfIsAffineOpen

noncomputable section

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor FunctorialResolution.Blowup
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

namespace UpperTheory.Gal.KunnethLefschetz.G

private lemma cross_of_rel {A : Type*} [CommRing A] {T T' b Cl Ck Dl Dk : A} (hT : T ∈ nonZeroDivisors A)
    (hT' : T' ∈ nonZeroDivisors A) (hb : IsUnit b) {n : ℕ}
    (hl : T * Cl * b ^ n = T' * Dl) (hk : T * Ck * b ^ n = T' * Dk) :
    Cl * Dk = Ck * Dl := by
  have h0 : (Cl * Dk - Ck * Dl) * (T * T' * b ^ n) = 0 := by
    linear_combination (T' * Dk) * hl - (T' * Dl) * hk
  have hu : T * T' * b ^ n ∈ nonZeroDivisors A :=
    mul_mem (mul_mem hT hT') (hb.pow n).mem_nonZeroDivisors
  exact sub_eq_zero.1 ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).1 h0)

theorem blEmb : BlowUpEmbedding := by
  intro R _ _ Z W p hp I π hπ
  obtain ⟨N, i, hi, rfl⟩ := hp
  obtain ⟨n, M, F, hF, hgen⟩ := UpperTheory.exists_homogeneous_generators_idealSheaf_closedImmersion i I
  have hU : ∀ a : Fin (N + 1), IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a)) :=
    fun a => (isAffineOpen_stdOpen a).preimage i
  let U : Fin (N + 1) → Z.affineOpens := fun a => ⟨_, hU a⟩
  let g : ∀ a, Fin (M + 1) → Γ(Z, (U a).1) := fun a m => i.appLE _ _ le_rfl (chartHom a (F m))
  choose V le c hVa hVc hc1 hc2 hc3 hc4 hc5 using
    fun a => UpperTheory.exists_blowup_affine_chart_cover_of_span_eq I π hπ (U a) (g a) (hgen a (hU a))
  have hle : ∀ a m, V a m ≤ (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) := le
  have key : ∀ a m (O : W.Opens) (hO : O ≤ V a m) l,
      W.presheaf.map (homOfLE hO).op (π.appLE _ _ (le a m) (g a l)) =
        (π ≫ i).appLE _ O (hO.trans (hle a m)) (chartHom a (F l)) := by
    intro a m O hO l
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    simp only [g]
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have hcross : ∀ (x y : Fin (N + 1) × Fin (M + 1)) (l k : Fin (M + 1)),
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 l) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 k) =
      W.presheaf.map (homOfLE (inf_le_left : V x.1 x.2 ⊓ V y.1 y.2 ≤ V x.1 x.2)).op (c x.1 x.2 k) *
        W.presheaf.map (homOfLE (inf_le_right : V x.1 x.2 ⊓ V y.1 y.2 ≤ V y.1 y.2)).op (c y.1 y.2 l) := by
    rintro ⟨a, m⟩ ⟨b, m'⟩ l k
    dsimp only
    have h1 : V a m ⊓ V b m' ≤ V a m := inf_le_left
    have h2 : V a m ⊓ V b m' ≤ V b m' := inf_le_right
    obtain ⟨hu, hrel⟩ := UpperTheory.isUnit_chart_coord_and_homogeneous_chart_transition (π ≫ i) (V a m ⊓ V b m') a b (h1.trans (hle a m)) (h2.trans (hle b m'))
    have e1 : ∀ l, (π ≫ i).appLE _ _ (h1.trans (hle a m)) (chartHom a (F l)) =
        W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) := fun l => by
      rw [← key a m _ h1 l, hc1, map_mul]
    have e2 : ∀ l, (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (F l)) =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← key b m' _ h2 l, hc1, map_mul]
    have r : ∀ l, W.presheaf.map (homOfLE h1).op (π.appLE _ _ (le a m) (g a m)) *
          W.presheaf.map (homOfLE h1).op (c a m l) *
          (π ≫ i).appLE _ _ (h2.trans (hle b m')) (chartHom b (X a : MvPolynomial (Fin (N + 1)) R)) ^ n =
        W.presheaf.map (homOfLE h2).op (π.appLE _ _ (le b m') (g b m')) *
          W.presheaf.map (homOfLE h2).op (c b m' l) := fun l => by
      rw [← e1, ← e2]; exact hrel n (F l) (hF l)
    exact cross_of_rel (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa a m) h1 _ (hc3 a m))
      (UpperTheory.restrict_mem_nonZeroDivisors_of_isAffineOpen (hVa b m') h2 _ (hc3 b m')) hu (r l) (r k)
  have hcov : iSup (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) = ⊤ := by
    rw [iSup_prod]
    simp_rw [hVc]
    change ⨆ a, (π ≫ i) ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  obtain ⟨f, hfs, hf⟩ := UpperTheory.cech_cocycle_line_bundle (π ≫ i ≫ PSpace.str R N) M
    (fun x : Fin (N + 1) × Fin (M + 1) => V x.1 x.2) hcov (fun x => x.2) (fun x => c x.1 x.2)
    (fun x => hc2 x.1 x.2) hcross
  choose hD hcoord using hf
  have hpf : ∀ a m m', W.basicOpen (c a m' m) = V a m' ⊓ f ⁻¹ᵁ (Proj.basicOpen (grading R M) (X m') ⊓
      Proj.basicOpen (grading R M) (X m)) := by
    intro a m m'
    rw [← hcoord (a, m') m, Scheme.basicOpen_appLE, basicOpen_chartHom_X]
  have eV : ∀ a m, V a m = π ⁻¹ᵁ (U a).1 ⊓ f ⁻¹ᵁ Proj.basicOpen (grading R M) (X m) := by
    intro a m
    refine _root_.le_antisymm (le_inf (le a m) (hD (a, m))) ?_
    rintro w ⟨hw1, hw2⟩
    have hw : w ∈ iSup (V a) := by rw [hVc]; exact hw1
    obtain ⟨m', hm'⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
    have hb : w ∈ W.basicOpen (c a m' m) := by
      rw [hpf]
      exact ⟨hm', hD (a, m') hm', hw2⟩
    rw [← hc5] at hb
    exact hb.2
  have cU : iSup (fun a => (U a).1) = ⊤ := by
    change ⨆ a, i ⁻¹ᵁ Proj.basicOpen (grading R N) (X a) = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X]
    rfl
  refine ⟨M, f, hfs.symm, UpperTheory.sections_generated_over_affine_product_cover (i ≫ PSpace.str R N) (PSpace.str R M) π f hfs.symm
    (fun a => (U a).1) (fun m => Proj.basicOpen (grading R M) (X m)) (fun a => hU a)
    (fun m => isAffineOpen_stdOpen m) cU iSup_basicOpen_X V hVa eV ?_⟩
  intro a m s
  obtain ⟨P, rfl⟩ := hc4 a m s
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [coe_eval₂Hom, eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | mul_X p l hp =>
    rw [map_mul, coe_eval₂Hom, eval₂_X]
    exact mul_mem hp (Subring.subset_closure (Or.inr ⟨chartHom m (X l), hcoord (a, m) l⟩))

end UpperTheory.Gal.KunnethLefschetz.G
