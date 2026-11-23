import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.SWLit.WittStd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := ((IsAlgClosed.lift : E →ₐ[ℚ] ℂ) : E →+* ℂ)
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_isWittBasis (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {n : ℕ} (l : E) (J : Matrix (Fin n) (Fin n) E)
    (hl : l ≠ 0) (hJ : J.det ≠ 0) : ∃ T : GL (Fin (n + n)) E, IsWittBasis σ J l T := by
  set Z : Matrix (Fin n) (Fin n) E := ((l / 2) • J⁻¹).map σ with hZ
  have hZσ : Z.map σ = (l / 2) • J⁻¹ := by
    ext i j
    simp [hZ, sigma_sigma h]
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hrel : (2 : E) • (J * Z.map σ) = l • (1 : Matrix (Fin n) (Fin n) E) := by
    rw [hZσ, Matrix.mul_smul, Matrix.mul_nonsing_inv J hJu, smul_smul]
    congr 1
    field_simp
  have hZdet : Z.det ≠ 0 := by
    intro h0
    have := (σ : E →+* E).map_det ((l / 2) • J⁻¹)
    rw [show (σ : E →+* E).mapMatrix ((l / 2) • J⁻¹) = Z from rfl, h0, map_eq_zero] at this
    simp [Matrix.det_smul, Matrix.det_nonsing_inv, hl, hJ] at this
  have hM : (blk 1 Z 1 (-Z)).det ≠ 0 := by
    rw [blk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_one₁₁, Matrix.one_mul,
      show -Z - Z = (-2 : E) • Z by rw [neg_smul, two_smul]; abel, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hZdet
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, Z, hrel, rfl⟩

theorem incM_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

theorem incM_one {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

variable (σ : E →ₐ[F] E) {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E)

theorem incM_inv_mul : incM F (T⁻¹).1 * incM F T.1 = 1 := by
  rw [← incM_mul, Units.inv_mul, incM_one]

theorem incM_mul_inv : incM F T.1 * incM F (T⁻¹).1 = 1 := by
  rw [← incM_mul, Units.mul_inv, incM_one]

theorem inBasis_mul (g h : UA σ J₂) : inBasis σ T (g * h) = inBasis σ T g * inBasis σ T h := by
  simp only [inBasis]
  rw [show mat (g * h) = mat g * mat h from rfl]
  calc incM F (T⁻¹).1 * (mat g * mat h) * incM F T.1
      = incM F (T⁻¹).1 * mat g * (incM F T.1 * incM F (T⁻¹).1) * mat h * incM F T.1 := by
        rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inBasis_one : inBasis σ T (1 : UA σ J₂) = 1 := by
  simp only [inBasis]
  rw [show mat (1 : UA σ J₂) = 1 from rfl, Matrix.mul_one, incM_inv_mul]

theorem entry_mul_mem (v : HeightOneSpectrum (𝓞 F)) {A B : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)}
    (hA : ∀ i j, compFin F E v (A i j) ∈ intLoc F E v) (hB : ∀ i j, compFin F E v (B i j) ∈ intLoc F E v) (i j) :
    compFin F E v ((A * B) i j) ∈ intLoc F E v := by
  rw [Matrix.mul_apply, map_sum]
  exact Subring.sum_mem _ fun k _ => by rw [map_mul]; exact Subring.mul_mem _ (hA i k) (hB k j)

def stdK : Subgroup (UA σ J₂) where
  carrier := {g | (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧
      compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ}
  one_mem' := by
    refine ⟨fun v i j => ?_, fun w τ => ?_⟩
    · rw [inv_one, inBasis_one, Matrix.one_apply]
      split_ifs <;> simp [one_mem, zero_mem]
    · rw [inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
      exact one_mem _
  mul_mem' := by
    intro g h hg hh
    refine ⟨fun v i j => ⟨?_, ?_⟩, fun w τ => ?_⟩
    · rw [inBasis_mul]
      exact entry_mul_mem v (fun i j => (hg.1 v i j).1) (fun i j => (hh.1 v i j).1) i j
    · rw [mul_inv_rev, inBasis_mul]
      exact entry_mul_mem v (fun i j => (hh.1 v i j).2) (fun i j => (hg.1 v i j).2) i j
    · rw [inBasis_mul, Matrix.map_mul]
      exact mul_mem (hg.2 w τ) (hh.2 w τ)
  inv_mem' := by
    intro g hg
    refine ⟨fun v i j => ⟨(hg.1 v i j).2, by rw [inv_inv]; exact (hg.1 v i j).1⟩, fun w τ => ?_⟩
    have hU := hg.2 w τ
    set U := (inBasis σ T g).map (piInf τ)
    set V := (inBasis σ T g⁻¹).map (piInf τ)
    have hVU : V * U = 1 := by
      simp only [V, U]
      rw [← Matrix.map_mul, ← inBasis_mul, inv_mul_cancel, inBasis_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hV : V = star U := by
      calc V = V * (U * star U) := by rw [Matrix.mem_unitaryGroup_iff.1 hU, Matrix.mul_one]
        _ = (V * U) * star U := by rw [Matrix.mul_assoc]
        _ = star U := by rw [hVU, Matrix.one_mul]
    show V ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ
    rw [hV, Matrix.mem_unitaryGroup_iff, star_star]
    exact Matrix.mem_unitaryGroup_iff'.1 hU

theorem mem_stdK_iff (g : UA σ J₂) : g ∈ stdK σ T ↔
    (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧ compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ :=
  Iff.rfl

theorem isStdK_stdK : IsStdK σ T (stdK σ T : Subgroup (UA σ J₂)) := fun g => mem_stdK_iff σ T g

omit [NumberField F] [NumberField E] in

theorem opNorm_le_one {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    opNorm U ≤ 1 := by
  have h1 : opNorm (star U * U) ≤ 1 := by
    rw [Matrix.mem_unitaryGroup_iff'.1 hU]; exact opNorm_one_le
  unfold opNorm at h1 ⊢
  rw [map_mul, map_star, CStarRing.nnnorm_star_mul_self, ← sq] at h1
  exact (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 h1

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ : AE F E → ℂ) := by
  let L : AE F E →+ ℂ := (piInf τ).toAddMonoidHom
  refine IsModuleTopology.continuous_of_distribMulActionHomₑ (R := AF F)
    (σ := (piInf τ).toMonoidHom.comp (algebraMap (AF F) (AE F E)).toMonoidHom) ?_
    { L with map_smul' := fun r x => by simp [L, Algebra.smul_def] }
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst) |>.congr fun a => by
      change _ = infEmb τ (_ ⊗ₜ[F] (1 : E))
      rw [infEmb_tmul, map_one, mul_one]; rfl

omit [NumberField F] [NumberField E] in
theorem bc_val {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (f : A →+* B)
    (x : GL m A) : ((Formalism.UG.bc f x : GL m B) : Matrix m m B) = (x : Matrix m m A).map f := rfl

theorem piInf_eq {w : InfinitePlace F} (τ : EmbOver E w) : ⇑(piInf τ) = ⇑(infEmb τ) ∘ ⇑(compInf F E w) := rfl

def basGL : GL (Fin (n + n)) (AE F E) := Formalism.UG.bc (inclR (F := F) (AF F)) T

def conjB (g : UA σ J₂) : GL (Fin (n + n)) (AE F E) := (basGL T)⁻¹ * g.1 * basGL T

theorem conjB_val (g : UA σ J₂) :
    ((conjB σ T g : GL (Fin (n + n)) (AE F E)) : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = inBasis σ T g := by
  rw [conjB, Units.val_mul, Units.val_mul, basGL, ← map_inv, bc_val, bc_val]
  rfl

theorem conjB_inv (g : UA σ J₂) : (conjB σ T g)⁻¹ = conjB σ T g⁻¹ := by
  simp only [conjB, Subgroup.coe_inv, mul_inv_rev, inv_inv, mul_assoc]

theorem height_conjB_le {g : UA σ J₂} (hg : g ∈ stdK σ T) : heightGL F (conjB σ T g) ≤ 1 := by
  have hg' : g⁻¹ ∈ stdK σ T := inv_mem hg
  refine le_of_eq ((heightGL_eq_one_iff F).2 ⟨fun w => ?_, fun v => ?_⟩)
  · have e1 : ((Formalism.UG.bc (compInf F E w)) (conjB σ T g))⁻¹ = Formalism.UG.bc (compInf F E w) (conjB σ T g⁻¹) := by
      rw [← map_inv, conjB_inv]
    refine htOf_eq_one.2 ⟨(normInf_le_iff F w).2 fun τ => ?_, (normInf_le_iff F w).2 fun τ => ?_⟩
    · rw [bc_val, Matrix.map_map, conjB_val, ← piInf_eq]
      exact opNorm_le_one (hg.2 w τ)
    · rw [e1, bc_val, Matrix.map_map, conjB_val, ← piInf_eq]
      exact opNorm_le_one (hg'.2 w τ)
  · have e1 : ((Formalism.UG.bc (compFin F E v)) (conjB σ T g))⁻¹ = Formalism.UG.bc (compFin F E v) (conjB σ T g⁻¹) := by
      rw [← map_inv, conjB_inv]
    refine htOf_eq_one.2 ⟨(normFin_le_iff F v).2 fun i j => ?_, (normFin_le_iff F v).2 fun i j => ?_⟩
    · rw [bc_val, Matrix.map_apply, conjB_val]
      exact absFin_le_one_of_mem_intLoc (hg.1 v i j).1
    · rw [e1, bc_val, Matrix.map_apply, conjB_val]
      exact absFin_le_one_of_mem_intLoc (hg'.1 v i j).1

theorem isCompact_stdK (h : IsCMExt F E σ) : IsCompact ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  have hcl : IsClosed (UG (cA σ) (incM F J₂) : Set (GL (Fin (n + n)) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin (n + n)) (AE F E) => (g : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) :=
      Units.continuous_val
    have hc : Continuous (cA σ : AE F E → AE F E) :=
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (F := F) (E := E) (AF F) σ).congr fun z => (GlobalTheory.IwLine.cA_eq_sigR σ z).symm
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hc))
      continuous_const
  have hemb : Topology.IsClosedEmbedding (conjB σ T (J₂ := J₂)) :=
    ((Homeomorph.mulLeft (basGL T)⁻¹).trans (Homeomorph.mulRight (basGL T))).isClosedEmbedding.comp
      hcl.isClosedEmbedding_subtypeVal
  have hcont : Continuous fun g : UA σ J₂ => inBasis σ T g :=
    (Units.continuous_val.comp hemb.continuous).congr (conjB_val σ T)
  have hcont' : Continuous fun g : UA σ J₂ => inBasis σ T g⁻¹ := hcont.comp continuous_inv
  have hOc : ∀ v : HeightOneSpectrum (𝓞 F), IsClosed (intLoc F E v : Set (Fv F v ⊗[F] E)) := fun v => by
    haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) := IsModuleTopology.topologicalAddGroup (Fv F v) _
    exact AddSubgroup.isClosed_of_isOpen (intLoc F E v).toAddSubgroup (GlobalTheory.ThK.isCompact_isOpen_intLoc v).2
  have hKc : IsClosed ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) := by
    have e0 : ((stdK σ T : Subgroup (UA σ J₂)) : Set (UA σ J₂)) =
        (⋂ v, ⋂ i, ⋂ j, ((fun g : UA σ J₂ => compFin F E v (inBasis σ T g i j)) ⁻¹' (intLoc F E v : Set _) ∩
          (fun g : UA σ J₂ => compFin F E v (inBasis σ T g⁻¹ i j)) ⁻¹' (intLoc F E v : Set _))) ∩
        ⋂ w, ⋂ τ : EmbOver E w, (fun g : UA σ J₂ => (inBasis σ T g).map (piInf τ)) ⁻¹'
          (Matrix.unitaryGroup (Fin (n + n)) ℂ : Set (Matrix (Fin (n + n)) (Fin (n + n)) ℂ)) := by
      ext g
      simp only [SetLike.mem_coe, mem_stdK_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    refine IsClosed.inter (isClosed_iInter fun v => isClosed_iInter fun i => isClosed_iInter fun j =>
      IsClosed.inter ?_ ?_) (isClosed_iInter fun w => isClosed_iInter fun τ => ?_)
    · exact (hOc v).preimage ((GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v).comp
        ((continuous_apply j).comp ((continuous_apply i).comp hcont)))
    · exact (hOc v).preimage ((GlobalTheory.ThK.LemF.QuotInv.continuous_compFinV v).comp
        ((continuous_apply j).comp ((continuous_apply i).comp hcont')))
    · exact isClosed_unitary.preimage (hcont.matrix_map (continuous_piInf τ))
  exact (hemb.isCompact_preimage (isCompact_heightGL_le F 1)).of_isClosed_subset hKc
    fun g hg => height_conjB_le σ T hg

theorem exists_wittBasis_stdK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (l : E) (J : Matrix (Fin n) (Fin n) E)
    (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E), l ≠ 0 → J.det ≠ 0 → J₂ = dblGram finSumFinEquiv J →
    ∃ (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)), IsWittBasis σ J l T ∧ IsStdK σ T K ∧
      IsCompact (K : Set (UA σ J₂)) := by
  intro F E _ _ _ _ _ σ h n l J J₂ hl hJ _
  obtain ⟨T, hT⟩ := exists_isWittBasis σ h l J hl hJ
  exact ⟨T, stdK σ T, hT, isStdK_stdK σ T, isCompact_stdK σ T h⟩

end GlobalTheory.SWLit.WittStd

end
