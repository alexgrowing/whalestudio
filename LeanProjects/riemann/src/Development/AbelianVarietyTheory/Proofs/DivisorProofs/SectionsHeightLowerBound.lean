import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsSumPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterShiftLeOfBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightInverseCoordinateNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryConjugateMatrixFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormCoordinateSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartGenericPointFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartSurjectiveFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMetricUnitaryGaugeStatement

open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.SelfInterImage

theorem isSelfInter_pull_fs (hF : GlobalTheory.Published.FubiniStudyChowHeight) (hC : GlobalTheory.Published.CycleHeights) {K : Type} [Field K]
    [NumberField K] {m D δ : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} (hX : IsArithVar p D)
    (π : X ⟶ PSpace (𝓞 K) m) (hπ : π ≫ PSpace.str (𝓞 K) m = p) (hdeg : π.residueDegree (genericPoint X) = 1)
    (A : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (hc : ∀ σ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ,
      A ((starRingEnd ℂ).comp σ) = (A σ).map (starRingEnd ℂ) * U)
    (f : MvPolynomial (Fin (D + 1) × Fin (m + 1)) K)
    (hf : IsChowFormInt (((π (genericPoint X) : ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) (𝓞 K))).asHomogeneousIdeal.toIdeal).map
      (MvPolynomial.map (algebraMap (𝓞 K) K))) D δ f) :
    ((HermLB.fs (PSpace.str (𝓞 K) m) (ProjSpace.O1_isLB (𝓞 K) m) (ProjSpace.coord (𝓞 K) m)
      (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) A hA hc).pull π hπ).IsSelfInter
      ((Module.finrank ℚ K : ℝ) * formHeight δ (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
        (fun σ => A (σ.comp (algebraMap (𝓞 K) K))) f) := by
  have hP : IsArithVar (PSpace.str (𝓞 K) m) m := GlobalTheory.TrueGeo.Base.isArithVar_pspace m
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (π (genericPoint X))
  have hr : Set.range i = closure {π (genericPoint X)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    exact Set.eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i π)
  obtain ⟨g, rfl⟩ : ∃ g : X ⟶ Z, g ≫ i = π := ⟨inv (Limits.pullback.snd i π) ≫ Limits.pullback.fst i π, by
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint X) = genericPoint Z := i.isClosedEmbedding.injective hi.symm
  have hdg : g.residueDegree (genericPoint X) = 1 := by
    rwa [GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.Published.residueDegree_of_isClosedImmersion i, one_mul] at hdeg
  have hch : CharZero Γ(Z, ⊤) := have := hX.charZero; g.appTop.hom.charZero
  have hZn := hP.isNoetherian_sub i
  have hpp : IsProper p := by
    obtain ⟨N, j, _, hj⟩ := hX.isProjOver
    have := isProper_str (𝓞 K) N
    exact hj ▸ inferInstance
  have hst := isProper_str (𝓞 K) m
  have hgp : IsProper g := by
    have : IsProper (g ≫ i ≫ PSpace.str (𝓞 K) m) := by rw [← Category.assoc, hπ]; exact hpp
    exact IsProper.of_comp g (i ≫ PSpace.str (𝓞 K) m)
  have hgs : Function.Surjective g := by
    rw [← Set.range_eq_univ, ← g.isClosedMap.isClosed_range.closure_eq]
    exact Set.eq_univ_of_univ_subset ((genericPoint_spec Z).def.ge.trans
      (closure_mono (Set.singleton_subset_iff.2 ⟨_, hg⟩)))
  have hdZ : topologicalKrullDim Z = (D + 1 : ℕ) :=
    le_antisymm ((GlobalTheory.PosBaseChange.dim_le_of_isClosedMap g.isClosedMap hgs).trans hX.dim_eq.le)
      (hX.dim_eq.ge.trans (GlobalTheory.ProperCover.dim_le_of_residueDegree_pos g hg (hdg ▸ one_pos)))
  have hZ : IsArithVar (i ≫ PSpace.str (𝓞 K) m) D := hP.of_isClosedImmersion i hch hdZ
  obtain ⟨h, hh, -⟩ := hC.existsUnique hP (HermLB.fs (PSpace.str (𝓞 K) m) (ProjSpace.O1_isLB (𝓞 K) m)
    (ProjSpace.coord (𝓞 K) m) (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) A hA hc)
  have h₁ := hC.heightProjection (𝓞 K) _ X _ p m D hP hX (g ≫ i) hπ
    ((topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr).trans hdZ)
    (by rw [hdeg]; exact one_ne_zero) _ h hh
  have h₂ := (hh.isSelfInter_restrict hP i rfl).unique hZ (hF K m D δ Z i hZ A hA hc f (hi ▸ hf))
  rwa [hdeg, Nat.cast_one, one_mul, ← hi, h₂] at h₁

theorem formHeight_linSubst_eq {K : Type} [Field K] [NumberField K] {B N n δ : ℕ} (hN : 0 < N) (hNn : N ≤ n)
    {g : Matrix (Fin N) (Fin n) K} {A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ}
    {A' : (K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ} (hA : ∀ σ, (A σ).det ≠ 0)
    (h : ∀ σ : K →+* ℂ, g.map σ * A' σ =
      A σ * Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0)
    {f : MvPolynomial (Fin B × Fin N) K} (hf : f ≠ 0) (hm : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f) :
    formHeight δ (1 : Matrix (Fin n) (Fin n) K) A' (linSubst g f) = formHeight δ g A f := by
  rw [formHeight, formHeight, HeightUnique.linSubst_one]
  congr 2
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h0 : linSubst (A σ) (MvPolynomial.map σ f) ≠ 0 := fun e => by
    have e' := congrArg (linSubst (A σ)⁻¹) e
    rw [HeightUnique.linSubst_linSubst, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hA σ)),
      HeightUnique.linSubst_one, linSubst, map_zero] at e'
    exact hf (MvPolynomial.map_injective σ σ.injective (e'.trans (map_zero _).symm))
  have hm' : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) (MvPolynomial.map σ f) := fun s hs =>
    hm s (MvPolynomial.support_map_subset σ f hs)
  rw [GlobalTheory.ImageHeightUnique.map_linSubst, HeightUnique.linSubst_linSubst, h σ, ← HeightUnique.linSubst_linSubst,
    GlobalTheory.SphereMeanDrop.blockSphereMean_incl B N n δ _ hN hNn h0 (HeightUnique.linSubst_homog _ hm')]
  ring

theorem sum_normSq_eq {N n : ℕ} (hNn : N ≤ n) {g : Matrix (Fin N) (Fin n) ℂ} {A : Matrix (Fin N) (Fin N) ℂ}
    {A' : Matrix (Fin n) (Fin n) ℂ}
    (h : g * A' = A * Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0)
    {v : Fin n → ℂ} {β : Fin N → ℂ} (hv : ∀ k, v k = ∑ j, g j k * β j) :
    ∑ a, ‖∑ k, A' k a * v k‖ ^ 2 = ∑ a, ‖∑ j, A j a * β j‖ ^ 2 := by
  have e (a : Fin n) : ∑ k, A' k a * v k = ∑ j, (g * A') j a * β j := by
    simp only [hv, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [e, h]
  symm
  refine Fintype.sum_of_injective (Fin.castLE hNn) (Fin.castLE_injective hNn) _ _ (fun a ha => ?_) fun a => ?_
  · have : ∀ j : Fin N, (j : ℕ) ≠ a := fun j hj => ha ⟨j, Fin.ext hj⟩
    simp [Matrix.mul_apply, this]
  · simp [Matrix.mul_apply, Fin.val_inj]

variable {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω]

theorem semilinear_gen {W : Submodule (𝓞 K) V} {N n : ℕ} {b : Module.Basis (Fin N) K V} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} {gw : Fin n → W} (σ : K →+* ℂ) (ℓ : W → ℂ)
    (hg : ∀ k, (gw k : V) = ∑ j, g j k • b j) (hc : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hℓ : ∀ (m : ℕ) (β : Fin m → 𝓞 K) (u : Fin m → W) (x : W), (x : V) = ∑ k, β k • (u k : V) →
      ℓ x = ∑ k, σ (β k : K) * ℓ (u k)) (k : Fin n) :
    ℓ (gw k) = ∑ j, σ (g j k) * ∑ l, σ (c l j) * ℓ (gw l) := by
  set e : Fin n → K := fun l => ∑ j, g j k * c l j with he
  have hexp : (gw k : V) = ∑ l, e l • (gw l : V) := by
    rw [hg k]
    simp_rw [hc, he, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image e)
  choose β hβ using fun l => hd _ (Finset.mem_image_of_mem e (Finset.mem_univ l))
  have hβ' : ∀ l, ((β l : 𝓞 K) : K) = ((d : 𝓞 K) : K) * e l := fun l => by
    rw [← Algebra.smul_def, ← hβ l]
  have hx1 : (((d : 𝓞 K) • gw k : W) : V) = ∑ l, β l • (gw l : V) := by
    rw [Submodule.coe_smul, ← algebraMap_smul K, hexp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← algebraMap_smul K (β l), smul_smul]
    congr 1
    exact (hβ' l).symm
  have hx2 : (((d : 𝓞 K) • gw k : W) : V) = ∑ _i : Fin 1, (d : 𝓞 K) • (gw k : V) := by
    simp
  have e1 := hℓ n β gw _ hx1
  have e2 := hℓ 1 (fun _ => (d : 𝓞 K)) (fun _ => gw k) _ hx2
  simp only [Finset.univ_unique, Finset.sum_singleton] at e2
  have hd0 : σ ((d : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero, ne_eq, RingOfIntegers.coe_eq_zero_iff]
    exact nonZeroDivisors.coe_ne_zero d
  apply mul_left_cancel₀ hd0
  rw [← e2, e1]
  simp only [hβ', map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [he, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem adjoin_ratios_eq_top {ev : V →ₗ[K] Ω} (hR : GlobalTheory.DegVal.GenRatios ev) {n : ℕ} {u : Fin n → V}
    (hu : Submodule.span K (Set.range u) = ⊤) {i : Fin n} (hi : ev (u i) ≠ 0) :
    IntermediateField.adjoin K (Set.range fun j => ev (u j) / ev (u i)) = ⊤ := by
  have key (v : V) : ev v / ev (u i) ∈ IntermediateField.adjoin K (Set.range fun j => ev (u j) / ev (u i)) := by
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hu.ge (Submodule.mem_top (x := v)))
    rw [map_sum, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [map_smul, smul_div_assoc]
    exact IntermediateField.smul_mem _ (IntermediateField.subset_adjoin _ _ (Set.mem_range_self j))
  refine top_le_iff.1 (hR.2.ge.trans (IntermediateField.adjoin_le_iff.2 ?_))
  rintro _ ⟨v, w, rfl⟩
  rw [← div_div_div_cancel_right₀ hi]
  exact div_mem (key v) (key w)

theorem selfInter_eq (hFS : GlobalTheory.Published.FubiniStudyChowHeight) (hC : GlobalTheory.Published.CycleHeights)
    {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V} {ev : V →ₗ[K] Ω} {D : ℕ} {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp (𝓞 K)} {L : HermLB p} {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} {t a : ℝ}
    (hR : GlobalTheory.DegVal.GenRatios ev) (hD : 0 < imageDeg ev D) (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s)
    (ha : (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a) :
    a = (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, hg, hc, hφ⟩ := hM.fs_shift hR.1 t
  have hspan : Submodule.span K (Set.range fun k => (gw k : V)) = ⊤ := by
    refine top_le_iff.1 (b.span_eq.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨j, rfl⟩
    rw [hc j]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨i₀, hi₀⟩ : ∃ k, ev (gw k) ≠ 0 := by
    by_contra! h
    exact hR.1 (LinearMap.ext_on_range hspan fun k => h k)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i₀.pos; omega⟩
  have hgc : g * c = 1 := by
    ext j l
    have e := congrArg (fun v => b.repr v j) (hc l)
    simp only [hg, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at e
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [eq_comm (a := j), e, mul_comm]
  obtain ⟨hNn, M, P, hMP, hPM, hgM⟩ := GlobalTheory.T.right_inverse_coordinate_normal_form K N (m + 1) g c hgc
  obtain ⟨A', hA', hU', hgA⟩ := GlobalTheory.T.unitary_conjugate_matrix_family K N (m + 1) g M A hNn
    (Matrix.isUnit_det_of_right_inverse hMP).ne_zero hgM hF.herm
    (GlobalTheory.ConjUnitary.conj_frame_unitary K N A hF.conj hF.herm)

  obtain ⟨N₀, b₀, f₀, hf₀⟩ := (imageDeg_pos_iff ev D).1 hD
  have hf := isChowFormInt_basis ev b₀ b hf₀
  set f := linSubst (b₀.toMatrix b) f₀
  set δ := imageDeg ev D
  have hN : 0 < N := by
    obtain ⟨z, hz, -⟩ := hf.exists_point
    obtain ⟨j, -⟩ := Function.ne_iff.1 hz
    exact j.pos
  have hgJ : g = (Matrix.of fun (j : Fin N) (k : Fin (m + 1)) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) * P := by
    rw [← hgM, Matrix.mul_assoc, hMP, Matrix.mul_one]
  have hf' : IsChowFormInt (coneIdeal K fun k => ev (gw k)) D δ (linSubst g f) := by
    have h₁ := GlobalTheory.T.chow_form_coordinate_substitution K N (m + 1) D δ _ _ f hNn (fun q => mem_coneIdeal_coord _ (fun j => ev (b j)) q) hf
    have h₂ := isChowFormInt_linSubst hPM hMP (fun q => mem_coneIdeal_coord P _ q) h₁
    rw [HeightUnique.linSubst_linSubst, ← hgJ] at h₂
    convert h₂ using 3 with k
    have e : ev (gw k) = ∑ j, algebraMap K Ω (g j k) * ev (b j) := by
      simp only [hg, map_sum, map_smul, Algebra.smul_def]
    rw [e]
    conv_lhs => rw [hgJ]
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hδ : (0 : ℝ) < ((D : ℝ) + 1) * δ := mul_pos (by positivity) (Nat.cast_pos.2 hD)
  have hht : ((D : ℝ) + 1) * δ * (imageHeight Nm W ev D + t) = formHeight δ g A f := by
    obtain ⟨N₁, n₁, b₁, g₁, A₁, -, -, hF₁, -⟩ := hM.fs
    rw [← imageHeight_exp_smul (exists_isImageHeight_iff.2 ⟨⟨_, _, _, _, _, hF₁⟩, hD⟩) t,
      GlobalTheory.ImageHeightUnique.imageHeight_eq K V Ω _ W ev D (formHeight δ g A f / (((D : ℝ) + 1) * δ))
        ⟨N, m + 1, b, g, A, δ, f, hF, hf, mul_div_cancel₀ _ hδ.ne'⟩, mul_div_cancel₀ _ hδ.ne']

  let L' := L.shift (fun _ => t) (fun _ => rfl)
  let sk : Fin (m + 1) → L'.B.Sec := fun k => s (gw k)
  have hsk : ⨆ k, nonzeroLocus (sk k) = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨w, hw⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.bpf.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨j, hj⟩ := exists_chart L.isLB x
    have hwm : (w : V) ∈ Submodule.span (𝓞 K) (Set.range fun k => (gw k : V)) := by
      rw [show (fun k => (gw k : V)) = fun k => ∑ j, g j k • b j from funext hg, hF.span]
      exact w.2
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hwm
    have h1 := (X.mem_basicOpen _ x hj).1 ((mem_nonzeroLocus_iff _ j hj).1 hw)
    rw [GlobalTheory.ImageModel.sec_linear K V Ω Nm W ev D X p L ψ s hM hR.1 _ β gw w hβ.symm j, map_sum] at h1
    obtain ⟨k, -, hk⟩ := IsLocalRing.exists_of_isUnit_sum h1
    rw [map_mul] at hk
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (mem_nonzeroLocus_iff (s (gw k)) j hj).2
      ((X.mem_basicOpen _ x hj).2 (isUnit_of_mul_isUnit_right hk))⟩
  let A₀ : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun τ => A' (TrueGeo.OfLattice.extEmb τ)
  have hA₀ : ∀ τ, (A₀ τ).det ≠ 0 := fun τ => hA' _
  have hU₀ : ∀ τ : 𝓞 K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin (m + 1)) ℂ,
      A₀ ((starRingEnd ℂ).comp τ) = (A₀ τ).map (starRingEnd ℂ) * U := fun τ => by
    have he : TrueGeo.OfLattice.extEmb ((starRingEnd ℂ).comp τ) =
        (starRingEnd ℂ).comp (TrueGeo.OfLattice.extEmb τ) :=
      TrueGeo.OfLattice.extEmb_eq (by rw [RingHom.comp_assoc, TrueGeo.OfLattice.extEmb_comp])
    simp only [A₀, he]
    exact hU' _
  have hiso := GlobalTheory.T.hermitian_metric_unitary_gauge (𝓞 K) X p L' m sk hsk A₀ hA₀ hU₀ fun τ i y hy => by
    obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = τ := ⟨_, TrueGeo.OfLattice.extEmb_comp τ⟩
    have he : TrueGeo.OfLattice.extEmb (σ.comp (algebraMap (𝓞 K) K)) = σ := TrueGeo.OfLattice.extEmb_eq rfl
    refine (hφ σ i y hy).trans (congrArg Real.log ?_)
    simp only [A₀, he]
    refine Eq.trans ?_ (sum_normSq_eq hNn (hgA σ) (β := fun j => ∑ l, σ (c l j) * valR y.1 (L.B.U i) ((s (gw l)).f i))
      (semilinear_gen σ (fun w => valR y.1 (L.B.U i) ((s w).f i)) hg hc
        fun m β u x hx => GlobalTheory.ImageModel.valR_section_sum K V Ω Nm W ev D X p L ψ s hM hR.1 _ i y hy m β u x hx)).symm
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

  let π := ProjSpace.toProj p sk hsk
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hsk.ge (TopologicalSpace.Opens.mem_top (genericPoint X)))
  obtain ⟨n, hn⟩ := exists_chart L.isLB (genericPoint X)
  have hne : fnOf _ hn ((s (gw i)).f n) ≠ 0 := fnOf_sec_ne_zero (L := L.B) hi hn
  have hyi : ev (gw i) ≠ 0 := fun h0 => by
    have e := hM.ratio (gw i₀) (gw i) n hn
    rw [h0, map_zero, zero_mul] at e
    exact mul_ne_zero ((map_ne_zero ψ).2 hi₀) hne e
  have hη : genericPoint X ∈ nonzeroLocus (sk i) ⊓ L.B.U n := ⟨hi, hn⟩
  have hU : nonzeroLocus (sk i) ⊓ L.B.U n ≤ π ⁻¹ᵁ ProjSpace.chart (𝓞 K) m i :=
    inf_le_left.trans (ProjSpace.toProj_preimage_chart p sk hsk i).ge
  have hrat (j) : fnOf _ hη (ProjSpace.pullRatio π _ i hU j) = ψ (ev (gw j) / ev (gw i)) := by
    have e := congrArg (fnOf _ hη) (ProjSpace.sec_eq_pullRatio_toProj_mul p sk hsk i j n hU inf_le_right)
    have r (k) : fnOf _ hη (resG X (inf_le_right : nonzeroLocus (sk i) ⊓ L.B.U n ≤ L.B.U n) ((s (gw k)).f n)) =
        fnOf _ hn ((s (gw k)).f n) := fnOf_resG _ hη _
    replace e : fnOf _ hn ((s (gw j)).f n) = fnOf _ hη (ProjSpace.pullRatio π _ i hU j) * fnOf _ hn ((s (gw i)).f n) :=
      (r j).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg (_ * ·) (r i))))
    have e' := hM.ratio (gw i) (gw j) n hn
    rw [map_div₀, eq_div_iff ((map_ne_zero ψ).2 hyi)]
    refine mul_right_cancel₀ hne ?_
    rw [← e', e]
    ring
  have hI := GlobalTheory.T.projective_chart_generic_point_function K Ω m (fun k => ev (gw k)) X p π ψ i _ hη hU (ProjSpace.toProj_str p sk hsk) hM.base hyi hrat
  have hdeg := GlobalTheory.T.projective_chart_surjective_function K Ω m _ X p π ψ i _ hη hU (ProjSpace.toProj_str p sk hsk) hM.bij.2 hM.base
    (adjoin_ratios_eq_top hR hspan hyi) hrat
  have h₁ := hiso.isSelfInter hM.arith (isSelfInter_pull_fs hFS hC hM.arith π (ProjSpace.toProj_str p sk hsk) hdeg
    A₀ hA₀ hU₀ _ (hI ▸ hf'))
  have hA : (fun σ : K →+* ℂ => A₀ (σ.comp (algebraMap (𝓞 K) K))) = A' := funext fun σ =>
    congrArg A' (TrueGeo.OfLattice.extEmb_eq rfl)
  rw [ha.unique hM.arith h₁, hA, formHeight_linSubst_eq hN hNn hF.herm hgA hf.ne_zero hf.homog, ← hht]
  ring

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem selfInter_le_of_chow : GlobalTheory.Published.FubiniStudyChowHeight → Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun hF hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hD hM ha =>
    (selfInter_eq hF hP.q11 hR hD hM ha).le

open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O in

theorem selfInter_le : GlobalTheory.CovTop.HypothesesX → Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec) (t a : ℝ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → (L.shift (fun _ => t) (fun _ => rfl)).IsSelfInter a → a ≤ (Module.finrank ℚ K : ℝ) * ((D : ℝ) + 1) * ((imageDeg ev D : ℝ) * (imageHeight Nm W ev D + t)) :=
  fun hX => selfInter_le_of_chow hX.fsch

end GlobalTheory.SelfInterImage
