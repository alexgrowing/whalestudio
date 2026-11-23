import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineChartOfLeftInverseMatrix

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.GrCl

section CellsInP

open MvPolynomial
open GlobalTheory.ProjSpace (grading spMap_pt pt_str_assoc pt_baseChange pt_eq_pt_iff span_range_comp_eq_top exists_mem_chart
  pt_preimage_basicOpen isPullback_baseChange baseChange mem_spOpen)
open GlobalTheory.SplitCells (lin lin_hom)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ} {ρ : R →+* S} {J : Type} {ξ : J → Fin (N + 1) → S}
  {ℓ : J → Fin (N + 1) → R}

theorem eval₂_lin' (a : Fin (N + 1) → R) (w : Fin (N + 1) → S) : eval₂ ρ w (lin a) = ∑ q, ρ (a q) * w q := by
  simp [lin, eval₂_sum]

theorem cell_immersion (hc : Cells ρ ξ ℓ) (j : J) (hv) :
    IsImmersion (pt ρ (ξ j) hv) ∧ ∃ T : Set (PSpace R N), IsClosed T ∧
      Set.range (pt ρ (ξ j) hv) = T ∩ (Proj.basicOpen (grading R N) (lin (ℓ j)) : Set (PSpace R N)) := by
  have h1 : eval₂Hom ρ (ξ j) (lin (ℓ j)) = 1 := by rw [coe_eval₂Hom, eval₂_lin', hc.one]
  have hu : IsUnit (eval₂Hom ρ (ξ j) (lin (ℓ j))) := h1 ▸ isUnit_one
  have hm : lin (ℓ j) ∈ grading R N 1 := lin_hom _
  have e : pt ρ (ξ j) hv = _ := ProjPoint.ofHom_eq_awayι _ _ _ one_pos hm hu
  have hs : Function.Surjective (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu) := by
    intro p
    obtain ⟨F, rfl⟩ := hc.gen j p
    change _ ∈ (ProjPoint.awayLift (grading R N) (eval₂Hom ρ (ξ j)) _ hu).range
    induction F using MvPolynomial.induction_on with
    | C a =>
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 0 (C a) (isHomogeneous_C _ a)
      rw [pow_zero, mul_one] at this
      exact ⟨_, this⟩
    | add F G hF hG => rw [map_add]; exact add_mem hF hG
    | mul_X F k hF =>
      rw [map_mul]
      refine mul_mem hF ?_
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 1 (X k) (isHomogeneous_X R k)
      rw [h1, one_pow, mul_one] at this
      exact ⟨_, this⟩
  have hcl : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))) :=
    IsClosedImmersion.spec_of_surjective _ hs
  refine ⟨by rw [e]; infer_instance, ?_⟩
  obtain ⟨T, hT, hT'⟩ := (Proj.awayι (grading R N) _ hm one_pos).isOpenEmbedding.isInducing.isClosed_iff.1
    (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))).isClosedEmbedding.isClosed_range
  refine ⟨T, hT, ?_⟩
  have hr : Set.range (Proj.awayι (grading R N) _ hm one_pos) = Proj.basicOpen (grading R N) (lin (ℓ j)) :=
    congrArg (fun U : (PSpace R N).Opens => (U : Set (PSpace R N))) (Proj.opensRange_awayι _ _ hm one_pos)
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hT', Set.image_preimage_eq_inter_range, hr]

theorem cell_overlap (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) {j j' : J} {x : PSpace R N}
    (hx : x ∈ Set.range (pt ρ (ξ j') (hv j'))) (h : x ∈ Proj.basicOpen (grading R N) (lin (ℓ j))) :
    x ∈ Set.range (pt ρ (ξ j) (hv j)) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : y.asIdeal.IsPrime := y.isPrime
  let K : Type := y.asIdeal.ResidueField
  let ψ' : S →+* K := algebraMap S K
  have h2 : eval₂ ρ (ξ j') (lin (ℓ j)) ∉ y.asIdeal := by
    rw [← mem_spOpen, ← pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos (lin_hom _)]
    exact h
  have h3 : ∑ q, ψ' (ρ (ℓ j q)) * ψ' (ξ j' q) ≠ 0 := by
    intro h0
    apply h2
    rw [eval₂_lin', ← Ideal.algebraMap_residueField_eq_zero, map_sum]
    simpa only [map_mul] using h0
  obtain ⟨ψ, u, hb, hu⟩ := hc.ovl K j j' ψ' h3
  let z : Sp K := IsLocalRing.closedPoint K
  have hz : spMap ψ' z = y := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap ψ' (IsLocalRing.maximalIdeal K) = y.asIdeal
    rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot]
    exact Ideal.ker_algebraMap_residueField _
  have e : spMap ψ ≫ pt ρ (ξ j) (hv j) = spMap ψ' ≫ pt ρ (ξ j') (hv j') := by
    rw [spMap_pt, spMap_pt, hb]
    exact (pt_eq_pt_iff _ _ _).2 ⟨u, hu⟩
  refine ⟨spMap ψ z, ?_⟩
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, hz]

theorem isClosed_iUnion_cell (hc : Cells ρ ξ ℓ) (hv : ∀ j, Ideal.span (Set.range (ξ j)) = ⊤) :
    IsClosed (⋃ j, Set.range (pt ρ (ξ j) (hv j))) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases h : ∃ j, y ∈ Proj.basicOpen (grading R N) (lin (ℓ j))
  · obtain ⟨j, hj⟩ := h
    obtain ⟨T, hT, e⟩ := (cell_immersion hc j (hv j)).2
    have hyT : y ∉ T := fun h' => hy (Set.mem_iUnion.2 ⟨j, e ▸ ⟨h', hj⟩⟩)
    refine Filter.mem_of_superset
      ((hT.isOpen_compl.inter (Proj.basicOpen (grading R N) (lin (ℓ j))).isOpen).mem_nhds ⟨hyT, hj⟩) ?_
    rintro z ⟨h1, h2⟩ hz
    obtain ⟨j', hz⟩ := Set.mem_iUnion.1 hz
    have := cell_overlap hc hv hz h2
    rw [e] at this
    exact h1 this.1
  · push_neg at h
    obtain ⟨q, hq⟩ := exists_mem_chart R N y
    obtain ⟨T, _, jj, a, ha⟩ := hc.lin q
    let F : MvPolynomial (Fin (N + 1)) R := X q - ∑ t, C (a t) * lin (ℓ (jj t))
    have hF : F.IsHomogeneous 1 := by
      refine (isHomogeneous_X R q).sub (IsHomogeneous.sum _ _ _ fun t _ => ?_)
      simpa using (isHomogeneous_C _ (a t)).mul (lin_hom (ℓ (jj t)))
    have hyF : y ∈ Proj.basicOpen (grading R N) F := by
      intro hmem
      refine hq ?_
      have h4 : ∑ t, C (a t) * lin (ℓ (jj t)) ∈ y.asHomogeneousIdeal :=
        sum_mem fun t _ => Ideal.mul_mem_left _ _ (not_not.1 (h (jj t)))
      have := add_mem hmem h4
      simpa [F] using this
    refine Filter.mem_of_superset ((Proj.basicOpen (grading R N) F).isOpen.mem_nhds hyF) ?_
    intro z hz hz'
    obtain ⟨j', w, rfl⟩ := Set.mem_iUnion.1 hz'
    have h5 : w ∈ pt ρ (ξ j') (hv j') ⁻¹ᵁ Proj.basicOpen (grading R N) F := hz
    rw [pt_preimage_basicOpen ρ (ξ j') (hv j') one_pos hF, mem_spOpen] at h5
    refine h5 ?_
    have h6 : eval₂ ρ (ξ j') F = 0 := by
      simp only [F, eval₂_sub, eval₂_X, eval₂_sum, eval₂_mul, eval₂_C, eval₂_lin']
      rw [ha j']
      simp
    rw [h6]
    exact zero_mem _

theorem cells_immersed : ∀ (O : Type) [CommRing O] (Z P : Scheme.{0}) (s : Z ⟶ Sp O) (N : ℕ) (p₁ : P ⟶ Z) (p₂ : P ⟶ PSpace O N), IsPullback p₁ p₂ s (PSpace.str O N) → ∀ (R S : Type) [CommRing R] [CommRing S] (χ : Sp R ⟶ Z) (g : O →+* R) (ρ : R →+* S) (J : Type) (ξ : J → Fin (N + 1) → S) (ℓ : J → Fin (N + 1) → R) (i : J → (Sp S ⟶ P)), IsOpenImmersion χ → χ ≫ s = spMap g → Cells ρ ξ ℓ → (∀ j, i j ≫ p₁ = spMap ρ ≫ χ) → (∀ j, ∃ hv, i j ≫ p₂ = pt (ρ.comp g) (ξ j) hv) → (∀ j, IsImmersion (i j)) ∧ (∀ j, ∃ U : P.Opens, Set.range (i j) = (⋃ j', Set.range (i j')) ∩ (U : Set P)) ∧ ∃ T : Set P, IsClosed T ∧ ⋃ j, Set.range (i j) = T ∩ p₁ ⁻¹' Set.range χ := by
  intro O _ Z P s N p₁ p₂ hP R S _ _ χ g ρ J ξ ℓ i hχ hg hc hi₁ hi₂
  have hb := isPullback_baseChange N g
  rw [← hg] at hb
  let e : PSpace R N ⟶ P := hP.flip.lift (baseChange N g) (PSpace.str R N ≫ χ) (by rw [hb.w, Category.assoc])
  have he : IsPullback e (PSpace.str R N) p₁ χ := hb.of_right' hP.flip
  have he₂ : e ≫ p₂ = baseChange N g := hP.flip.lift_fst _ _ _
  have heo : IsOpenImmersion e := MorphismProperty.of_isPullback he.flip hχ
  have hr : Set.range e = p₁ ⁻¹' Set.range χ := by
    rw [← Scheme.Pullback.range_fst, ← he.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact he.isoPullback.hom.surjective.range_comp _
  choose hv hi₂ using hi₂
  have hj : ∀ j, i j = pt ρ (ξ j) (hv j) ≫ e := fun j =>
    hP.hom_ext (by rw [hi₁, Category.assoc, he.w, pt_str_assoc]) (by rw [hi₂, Category.assoc, he₂, pt_baseChange])
  have hm : ∀ j, Set.range (i j) = e '' Set.range (pt ρ (ξ j) (hv j)) := fun j => by
    rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hinj := e.isOpenEmbedding.injective
  refine ⟨fun j => ?_, fun j => ⟨e ''ᵁ Proj.basicOpen (grading R N) (lin (ℓ j)), Set.ext fun x => ?_⟩,
    (e '' (⋃ j, Set.range (pt ρ (ξ j) (hv j)))ᶜ)ᶜ,
    (e.isOpenEmbedding.isOpenMap _ (isClosed_iUnion_cell hc hv).isOpen_compl).isClosed_compl,
    Set.ext fun x => ?_⟩
  · have := (cell_immersion hc j (hv j)).1
    rw [hj]
    infer_instance
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨T, -, eT⟩ := (cell_immersion hc j (hv j)).2
      have hy₂ := hy
      rw [eT] at hy₂
      exact ⟨⟨j, y, hy, rfl⟩, y, hy₂.2, rfl⟩
    · rintro ⟨⟨j', y, hy, rfl⟩, y', hy', e'⟩
      obtain rfl := hinj e'
      exact ⟨y', cell_overlap hc hv hy hy', rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm, ← hr]
    constructor
    · rintro ⟨j, y, hy, rfl⟩
      refine ⟨?_, y, rfl⟩
      rintro ⟨y', hy', e'⟩
      obtain rfl := hinj e'
      exact hy' (Set.mem_iUnion.2 ⟨j, hy⟩)
    · rintro ⟨hx, y, rfl⟩
      by_contra hn
      refine hx ⟨y, fun hy => hn ?_, rfl⟩
      obtain ⟨j, hy⟩ := Set.mem_iUnion.1 hy
      exact ⟨j, y, hy, rfl⟩

end CellsInP

end GlobalTheory.GrCl
