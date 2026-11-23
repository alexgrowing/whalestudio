import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryOneParameterRealPlaceComponent

noncomputable section

namespace GlobalTheory.CompanionTheory.StdK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x) := fun x => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    exact ⟨m, hm, hi⟩
  choose m hm hi using h
  let b := Module.finBasis F E
  let u : Fin (Module.finrank F E) → Fˣ := fun i => Units.mk0 (m (b i) : F) (by exact_mod_cast hm _)
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  have e : u i • b i = m (b i) • b i := by
    change ((m (b i) : F)) • b i = _
    exact Int.cast_smul_eq_zsmul F _ _
  rw [e]
  exact hi _

theorem isOpen_intAd : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
  have h : IsOpen {f : FiniteAdeleRing (𝓞 F) F | ∀ v, f v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage continuous_snd

theorem evFin_finOne (v : HeightOneSpectrum (𝓞 F)) : evFin F v (finOne F) = 1 := rfl

theorem evI_finOne_mul (a : AF F) : evI F (finOne F * a) = 0 := by
  have e : (finOne F * a).1 = 0 := by
    change (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  unfold evI
  rw [e, map_zero]

variable (F E) in

def finInt : AddSubgroup (AE F E) :=
  (intHat F E).comap (DistribMulAction.toAddMonoidHom (AE F E) (finOne F))

theorem mem_finInt {z : AE F E} : z ∈ finInt F E ↔ finOne F • z ∈ intHat F E := Iff.rfl

theorem smul_incl_mem_finInt {a : AF F} (ha : ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (E := E) (AF F) (o : E) ∈ finInt F E := by
  rw [mem_finInt, smul_smul]
  refine AddSubgroup.subset_closure ⟨finOne F * a, evI_finOne_mul a, fun v => ?_, o, rfl⟩
  rw [map_mul, evFin_finOne, one_mul]
  exact ha v

theorem isOpen_finInt : IsOpen (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨b, hb⟩ := exists_intBasis (F := F) (E := E)
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hS : IsOpen {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} := by
    have e0 : {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun z => e z i) ⁻¹' {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    exact isOpen_iInter_of_finite fun i => (isOpen_intAd (F := F)).preimage ((continuous_apply i).comp he)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · intro i v
    simp
  · intro z hz
    have e1 : z = ∑ i, e z i • (Algebra.TensorProduct.basis (AF F) b i) :=
      ((Algebra.TensorProduct.basis (AF F) b).sum_equivFun z).symm
    rw [e1]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact smul_incl_mem_finInt (hz i) ⟨b i, hb i⟩

theorem isClosed_finInt : IsClosed (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact AddSubgroup.isClosed_of_isOpen _ isOpen_finInt

theorem compFin_finOne_smul (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, map_mul, evFin_finOne]

theorem absFin_le_one_of_mem {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, o, rfl⟩ := hz
    have e : compFin F E v (a • inclR (F := F) (E := E) (AF F) (o : E)) = evFin F v a ⊗ₜ[F] (o : E) := by
      simp [compFin, inclR, TensorProduct.smul_tmul']
    rw [e]
    refine (absFin_tmul_le F v _ o).trans ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (ha v)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | neg x _ hx =>
    rw [map_neg, absFin_neg]
    exact hx

theorem opNorm_le_one {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (h : M * Mᴴ = 1) : opNorm M ≤ 1 := by
  have e : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M * star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h, map_one]
  have h2 := CStarRing.norm_self_mul_star (x := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  rw [e] at h2
  have h3 : ‖(1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h4 := norm_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  nlinarith

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem heightGL_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (B : Base F E) (hcm : IsCMExt F E σ)
    (g : GL ι (AE F E)) (hu : ∀ w, (g.1.map (piInf (B.emb w))) * (g.1.map (piInf (B.emb w)))ᴴ = 1)
    (hf : ∀ i j, g.1 i j ∈ finInt F E) (hf' : ∀ i j, (g⁻¹).1 i j ∈ finInt F E) : heightGL F g = 1 := by
  rw [heightGL_eq_one_iff]
  refine ⟨fun w => htOf_eq_one.2 ⟨?_, ?_⟩, fun v => htOf_eq_one.2 ⟨?_, ?_⟩⟩
  · rw [normInf_eq_opNorm hcm (B.emb w)]
    exact opNorm_le_one (hu w)
  · rw [normInf_eq_opNorm hcm (B.emb w), ← map_inv]
    change opNorm ((g⁻¹).1.map (piInf (B.emb w))) ≤ 1
    have hM : g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 := mul_eq_one_comm.1 (hu w)
    have h2 : (g⁻¹).1.map (piInf (B.emb w)) = (g.1.map (piInf (B.emb w)))ᴴ := by
      calc _ = (g.1.map (piInf (B.emb w)))ᴴ * g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) := by
            rw [h1, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, hM, Matrix.mul_one]
    rw [h2]
    exact opNorm_le_one (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
  · refine (normFin_le_iff F v).2 fun i j => ?_
    change absFin F v (compFin F E v (g.1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf i j) v
  · refine (normFin_le_iff F v).2 fun i j => ?_
    rw [← map_inv]
    change absFin F v (compFin F E v ((g⁻¹).1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf' i j) v

theorem isCompact_of_isStdK (B : Base F E) (hcm : IsCMExt F E σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  let bA : GL (Fin n ⊕ Fin n) (AE F E) := Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) b
  let m : G2 σ Y → GL (Fin n ⊕ Fin n) (AE F E) := fun x => bA⁻¹ * x.1 * bA
  have hm : ∀ x, (m x).1 = inFrame b x := fun x => rfl
  have hv : Continuous fun x : G2 σ Y => (x.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hfr : Continuous fun x : G2 σ Y => inFrame b x := (continuous_const.matrix_mul hv).matrix_mul continuous_const
  have hfi : Continuous fun x : G2 σ Y => inFrame b x⁻¹ := hfr.comp continuous_inv
  have hcl : IsClosed (K : Set (G2 σ Y)) := by
    have e1 : (K : Set (G2 σ Y)) = (⋂ w, {k : G2 σ Y | (inFrame b k).map (piInf (B.emb w)) *
          ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k i j) ⁻¹' (finInt F E : Set (AE F E))) ∩
          ⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k⁻¹ i j) ⁻¹' (finInt F E : Set (AE F E))) := by
      ext k
      simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_finInt]
    rw [e1]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_))
    · have h := hfr.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (B.emb w))
      exact h.matrix_mul h.matrix_conjTranspose
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfr)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfi)
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hUG : IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) := by
    have hg : Continuous fun g : GL (Fin n ⊕ Fin n) (AE F E) => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hg.matrix_transpose.matrix_mul continuous_const).matrix_mul (hg.matrix_map hσ)) continuous_const
  have hC := hUG.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_heightGL_le (E := E) (n := Fin n ⊕ Fin n) F (heightGL F bA * heightGL F bA⁻¹))
  refine hC.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨hu, hf⟩ := (hK k).1 hk
  have hinv : (m k)⁻¹ = m k⁻¹ := by
    change (bA⁻¹ * k.1 * bA)⁻¹ = bA⁻¹ * (k.1)⁻¹ * bA
    group
  have h1 : heightGL F (m k) = 1 := heightGL_eq_one B hcm (m k) hu
    (fun i j => mem_finInt.2 (hf k (by simp) i j))
    (fun i j => by
      rw [hinv]
      exact mem_finInt.2 (hf k⁻¹ (by simp) i j))
  have e2 : k.1 = bA * m k * bA⁻¹ := by
    change k.1 = bA * (bA⁻¹ * k.1 * bA) * bA⁻¹
    group
  change heightGL F k.1 ≤ _
  rw [e2]
  refine (heightGL_mul_le F _ _).trans ?_
  rw [(heightGL_mul_of_eq_one F h1 bA).1]

theorem isCompact_K : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK

end GlobalTheory.CompanionTheory.StdK

end
