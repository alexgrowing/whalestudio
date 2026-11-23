import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartRestrEqGerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameEqUnitSmulDForm
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanLogDerGermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryComponentStalkRegularBoundaryIdealProdPaStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open IsLocalRing

theorem isUnit_det_of_span_eq_top (k A : Type) [CommRing k] [CommRing A] [Algebra k A] {N : ℕ} (g : Fin N → A)
    (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (hδ : Submodule.span A (Set.range δ) = ⊤) :
    IsUnit (Matrix.of fun i j => δ j (g i)).det := by
  classical
  have h : ∀ i, ∃ a : Fin N → A, ∑ j, a j • δ j = KaehlerDifferential.linearMapEquivDerivation k A (bΩ.coord i) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun A).1 (hδ ▸ Submodule.mem_top)
  choose a ha using h
  have hm : (Matrix.of fun i j => δ j (g i)) * (Matrix.of fun j i => a i j) = 1 := by
    ext l i
    have h1 := congrArg (fun d : Derivation k A A => d (g l)) (ha i)
    simp only [KaehlerDifferential.linearMapEquivDerivation_apply_apply, ← hg] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h2 : (∑ j, a i j • δ j) (g l) = ∑ j, a i j * δ j (g l) := by
      have := map_sum (Derivation.coeFnAddMonoidHom (R := k) (A := A) (M := A)) (fun j => a i j • δ j) Finset.univ
      have h3 := congrFun this (g l)
      rw [Finset.sum_apply] at h3
      exact h3
    rw [h2] at h1
    simp only [Matrix.of_apply, mul_comm (δ _ _)]
    rw [h1]
    simp [Finsupp.single_apply]
  exact Matrix.isUnit_det_of_right_inverse hm

theorem det_mem_maximalIdeal (k A : Type) [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A] {N : ℕ}
    (g : Fin N → A) (bΩ : Module.Basis (Fin N) A Ω[A⁄k]) (hg : ∀ i, bΩ i = KaehlerDifferential.D k A (g i))
    (δ : Fin N → Derivation k A A) (t : A) (ht : t ∈ maximalIdeal A)
    (hd : KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]))
    (hδ : ∀ j, δ j t ∈ Ideal.span {t}) : (Matrix.of fun i j => δ j (g i)).det ∈ maximalIdeal A := by
  classical
  set c : Fin N → A := fun i => bΩ.repr (KaehlerDifferential.D k A t) i with hc
  have hsum : KaehlerDifferential.D k A t = ∑ i, c i • bΩ i := (bΩ.sum_repr _).symm
  have hne : (fun i => residue A (c i)) ≠ 0 := by
    intro h0
    apply hd
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact (residue_eq_zero_iff _).1 (congrFun h0 i)
  rw [← residue_eq_zero_iff, RingHom.map_det]
  refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne, ?_⟩
  funext j
  have h1 : δ j t = ∑ i, c i * δ j (g i) := by
    rw [← (δ j).liftKaehlerDifferential_comp_D t, hsum, map_sum]
    simp [hg]
  have h2 : residue A (δ j t) = 0 :=
    (residue_eq_zero_iff _).2 ((Ideal.span_singleton_le_iff_mem _).2 ht (hδ j))
  rw [h1, map_sum] at h2
  simpa [Matrix.vecMul, dotProduct] using h2

theorem derivation_mem_span_of_prod {k A : Type} [CommRing k] [CommRing A] [IsRegularLocalRing A] [Algebra k A] {n : ℕ}
    (f : Fin n → A) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp A n f) (J : Finset (Fin n)) {j : Fin n} (hj : j ∈ J)
    (δ : Derivation k A A) (hδ : δ (∏ i ∈ J, f i) ∈ Ideal.span {∏ i ∈ J, f i}) : δ (f j) ∈ Ideal.span {f j} := by
  classical
  have hD : IsDomain A := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := ReciprocityTheory.AnForm.R.prime_of_regular_params f hf.1 hf.2
  rw [Ideal.mem_span_singleton] at hδ ⊢
  rw [← Finset.mul_prod_erase J f hj, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hδ
  have h1 : f j ∣ (∏ i ∈ J.erase j, f i) * δ (f j) :=
    (dvd_add_right (dvd_mul_right _ _)).1 ((dvd_mul_right _ _).trans hδ)
  refine ((hp j).dvd_or_dvd h1).resolve_left fun h2 => ?_
  obtain ⟨i, hi, h3⟩ := (hp j).exists_mem_finset_dvd h2
  exact (ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).2 j i (Finset.ne_of_mem_erase hi).symm
    ((hp j).associated_of_dvd (hp i) h3)

theorem D_notMem_smul_top {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (ResidueField A)] {t : A} (ht : t ∈ maximalIdeal A) (ht2 : t ∉ maximalIdeal A ^ 2) :
    KaehlerDifferential.D k A t ∉ (maximalIdeal A) • (⊤ : Submodule A Ω[A⁄k]) := by
  intro hm
  have h := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := k) (fun _ : Unit => t) (fun _ => ht)
    (linearIndependent_unique_iff.2 (by
      intro h0
      exact ht2 ((Ideal.toCotangent_eq_zero _ _).1 h0)))
  refine h.ne_zero () ?_
  generalize KaehlerDifferential.D k A t = w at hm
  refine Submodule.smul_induction_on hm (fun r hr w _ => ?_) (fun x y hx hy => ?_)
  · rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff _).2 hr, TensorProduct.zero_tmul]
  · rw [TensorProduct.tmul_add, hx, hy, add_zero]

theorem derivation_mem_map {k R A : Type} [CommRing k] [CommRing R] [CommRing A] [Algebra k A] (φ : R →+* A)
    (I : Ideal R) (d : R → R) (hd : ∀ r ∈ I, d r ∈ I) (δ : Derivation k A A) (hδ : ∀ r, δ (φ r) = φ (d r))
    {a : A} (ha : a ∈ I.map φ) : δ a ∈ I.map φ := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hδ]
    exact Ideal.mem_map_of_mem _ (hd r hr)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x hx0 hx =>
    rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hx0)

theorem exists_boundary_param : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∀ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx ((b j).1 r)) → x ∉ (j₀ TF.Y Z).opensRange → ∃ t ∈ IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x), KaehlerDifferential.D c.F ((X₀ TF.Y Z).presheaf.stalk x) t ∉ (IsLocalRing.maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x)) • (⊤ : Submodule ((X₀ TF.Y Z).presheaf.stalk x) Ω[(X₀ TF.Y Z).presheaf.stalk x⁄c.F]) ∧ ∀ j, δ j t ∈ Ideal.span {t} := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hx b δ hδ hn
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  obtain ⟨hreg, n, f, J, hf, ⟨j, hj⟩, hI⟩ := GlobalTheory.T.boundary_componentStalk_regular_boundaryIdeal_prod_params E H Dw l Xo c TF Z x U hx hn
  have hm : f j ∈ maximalIdeal ((X₀ TF.Y Z).presheaf.stalk x) := hf.1 ▸ Ideal.subset_span ⟨j, rfl⟩
  refine ⟨f j, hm, ?_, fun i => ?_⟩
  · obtain ⟨V, hV, hxV, -⟩ := Opens.isBasis_iff_nbhd.1 (X₀ TF.Y Z).isBasis_affineOpens (show x ∈ (⊤ : (X₀ TF.Y Z).Opens) from trivial)
    haveI := GlobalTheory.AdaptedFrame.formallySmooth_residueField (s₀ TF.Y Z) (n := Dw.dim) hV x hxV (by
      ext t
      change ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) ⊤ t) =
        ((X₀ TF.Y Z).presheaf.germ V x hxV).hom (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX (s₀ TF.Y Z) V t)
      rw [← GlobalTheory.TopForm.resG_comp_algX (s₀ TF.Y Z) (le_top : V ≤ ⊤), RingHom.comp_apply, germ_resG])
    exact D_notMem_smul_top hm ((ReciprocityTheory.AnForm.R.regular_params_spec f hf.1 hf.2).1 j)
  · refine derivation_mem_span_of_prod f hf J hj (δ i) ?_
    rw [← hI]
    refine derivation_mem_map _ _ (b i).1 (b i).2.2 (δ i) (hδ i) ?_
    rw [hI]
    exact Ideal.subset_span rfl

theorem local_topPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → (barComp TF.Y Z).ι x ∈ U.1 → ∀ (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), spMap ρ ≫ LogKS.chart U = GlobalTheory.LogKSDiv.genPt TF Z ≫ (barComp TF.Y Z).ι → ∀ (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ ((b j).1 r)) → ∀ (U' : (X₀ TF.Y Z).Opens) (ω : TopForm.FormsOn (s₀ TF.Y Z) Dw.dim U'), TopForm.IsFrame ω → ∀ hx : x ∈ U', RegAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ∧ (UnitAt x (GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω)) ↔ x ∈ (j₀ TF.Y Z).opensRange) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U hU hxU ρ hρ b D hD U' ω hω hx
  have h1 := chartRestr_eq_germ E H Dw l Xo c TF Z x U hU hxU ρ hρ
  obtain ⟨δ, hδK, hδR⟩ := GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension E H Dw l Xo c TF Z x U hU hxU ρ h1 (fun j => (b j).1) D hD
  obtain ⟨g, bΩ, u, hg, hu, hform⟩ := frame_eq_unit_smul_dForm E H Dw l Xo c TF Z x U' ω hω hx
  letI := (stalkAlg TF Z x).toAlgebra
  have key : topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D (formOf U' (gen_mem hx) ω) =
      algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField
        (u * (Matrix.of fun i j => δ j (g i)).det) := by
    rw [hform, LinearMap.map_smul, topPair_dForm, smul_eq_mul, map_mul, RingHom.map_det]
    congr 2
    ext i j
    exact hδK j (g i)
  refine ⟨⟨_, key.symm⟩, fun hU' => ?_, fun hr => ?_⟩
  · by_contra hn
    obtain ⟨t, htm, htd, htδ⟩ := exists_boundary_param E H Dw l Xo c TF Z x U hxU b δ hδR hn
    have hz := det_mem_maximalIdeal c.F _ g bΩ hg δ t htm htd htδ
    refine (zeroAt_iff.1 ⟨_, Ideal.mul_mem_left _ u hz, key.symm⟩).2 hU'
  · have hs := GlobalTheory.T.span_logDer_germs' E H Dw l Xo c TF Z x U hU hxU b δ hδR hr
    exact ⟨_, hu.mul (isUnit_det_of_span_eq_top c.F _ g bΩ hg δ hs), key.symm⟩

end GlobalTheory.LogKSDiv
