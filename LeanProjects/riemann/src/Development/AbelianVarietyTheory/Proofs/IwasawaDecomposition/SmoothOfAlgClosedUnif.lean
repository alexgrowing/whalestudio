import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TriIff
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphismStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineSpaceCoveredSmoothOfRelativeDimensionAddStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCoveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlockStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLineStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueProjectiveBundleFlagRefinementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleCompStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLieEigenpartsFrameFamilyOverVarietyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TautologicalFamilyRefinementCompatibleLieAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlagStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrameStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenFrameBasePointLiftsUniqueFlagSpaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceDimensionEqSumChooseStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := GlobalTheory.T.projective_bundle_points_of_rational_model F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, GlobalTheory.T.geometricallyIntegral_of_affCover F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, GlobalTheory.T.isFlagRefinementBundle_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := GlobalTheory.T.exists_graded_line_divisors_full_flag E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

theorem nonempty_flagTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z) → Nonempty (FlagTor Z e U) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U hσ hU hne hF hsm hS
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp E H Dw l Xo c σ N U hσ hU hne hF
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c O β Z F e hF hsm
  have key := fun i : U.Comp =>
    haveI := (hB (q i)).1
    exists_flagCpt Z e hS (B (q i)) (j (q i)) (hB (q i)).2.2.1
  choose C f hπ hdim hl using key
  have lift : ∀ (K : Type) [Field K] (x : Sp K ⟶ gen Z) (i : Comp Xo c),
      x (IsLocalRing.closedPoint K) ∈ Set.range (j i) → ∃ x' : Sp K ⟶ (B i).X, x' ≫ j i = x := fun K _ x i h => by
    have := (hB i).1
    refine ⟨IsOpenImmersion.lift (j i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨w, rfl⟩
    rwa [show w = IsLocalRing.closedPoint K from Subsingleton.elim (α := PrimeSpectrum K) _ _]
  refine ⟨⟨C, fun k => ?_, fun K _ _ χ x hx g => ?_, fun i x s => ?_⟩⟩
  · rw [hdim, (hB _).2.1, GlobalTheory.T.flag_space_dimension_eq_sum_choose E H Dw, hU.1]
  · obtain ⟨i₀, hi, hi'⟩ := hcov (x (IsLocalRing.closedPoint K))
    obtain ⟨i, rfl⟩ := q.surjective i₀
    obtain ⟨x', hx'⟩ := lift K x _ hi
    obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hl i K χ x x' hx' hx g
    refine ⟨⟨i, p⟩, ⟨by rw [hπ, ← Category.assoc, hp1, hx'], hp2⟩, ?_⟩
    rintro ⟨i', p'⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    rw [hπ, ← Category.assoc] at h1
    obtain rfl : i' = i := q.injective (hi' _ ⟨(p' ≫ f i') (IsLocalRing.closedPoint K), by
      rw [← h1]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩)
    have := (hB (q i')).1
    rw [hp3 p' ⟨(cancel_mono (j (q i'))).1 (h1.trans hx'.symm), h2⟩]
  · let x₀ : Sp ℂ ⟶ gen Z := (GlobalTheory.AllWt.ptF (S := CAt σ) (U.un i x) ≫ Z.jQ :)
    have hx₀ : x₀ ≫ genStr Z = spMap σ :=
      (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _))
    obtain ⟨x', hx'⟩ := lift ℂ x₀ (q i) ((hB _).2.2.2 _ (hq i x _))
    obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z _ _ x₀ hx₀
    obtain ⟨p, ⟨hp1, -⟩, -⟩ := hl i _ _ x₀ x' hx' hx₀ g
    have : p ≫ (C i).π = x₀ := by rw [hπ, ← Category.assoc, hp1, hx']
    exact ⟨p s, (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun t : Sp ℂ ⟶ gen Z => t s) this)⟩

end GlobalTheory.FlagBundle
