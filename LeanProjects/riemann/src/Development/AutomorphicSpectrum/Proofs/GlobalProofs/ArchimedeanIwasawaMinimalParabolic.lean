import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstAlongCocompactUniqueStages
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

section Flag

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}

end Flag

private theorem col_mem_lemma {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} (X : Matrix (Fin n) (Fin r) E) {k : Fin r}
    {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ⊤) (i : Fin r) (hi : i ≤ k) :
    (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ GlobalTheory.StdPar.colSpan F X {i' | i' ≤ k} := by
  obtain ⟨B, -, hB⟩ := hg
  have hi' : i.val < k.val + 1 := Nat.lt_succ_of_le hi
  have key : (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i =
      ∑ p : Fin (k.val + 1), B.1 p ⟨i.val, hi'⟩ • (adMat F X)ᵀ (Fin.castLE k.2 p) := by
    ext a
    have h := congrFun (congrFun hB a) ⟨i.val, hi'⟩
    simp only [Matrix.mul_apply] at h
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact h.trans (Finset.sum_congr rfl fun p _ => mul_comm _ _)
  rw [key]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨Fin.castLE k.2 p, Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp p.2), rfl⟩)

private theorem mapsTo_lemma_2 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    {T : Finset (Fin r)} {g : GAd σ J} (hg : g ∈ GlobalTheory.StdPar.levi σ J X Y T) {I : Set (Fin r)}
    (hI : ∀ i ∈ I, ∃ k ∈ T, i ≤ k ∧ ∀ i' ≤ k, i' ∈ I) :
    ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, (matHom _ σ J g).1 *ᵥ y ∈ GlobalTheory.StdPar.colSpan F X I := by
  intro y hy
  have hle : GlobalTheory.StdPar.colSpan F X I ≤
      (GlobalTheory.StdPar.colSpan F X I).comap (Matrix.mulVecLin (matHom _ σ J g).1) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨k, hk, hik, hsub⟩ := hI i hi
    have hfs : g ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k) ⊤ :=
      (Subgroup.mem_inf.mp ((Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hg) k)) hk)).1
    exact (Submodule.span_mono (Set.image_mono fun i' hi' => hsub i' hi')) (col_mem_lemma X hfs i hik)
  exact hle hy

private theorem mem_colPerp_lemma_3 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
    {I : Set (Fin r)} {y : Fin n → AF F ⊗[F] E} :
    y ∈ GlobalTheory.StdPar.colPerp σ J X I ↔
      ∀ i ∈ I, (adMat F (Formalism.UG.cT (σ : E →+* E) X * J) *ᵥ y) i = 0 := by
  simp only [GlobalTheory.StdPar.colPerp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply,
    LinearMap.proj_apply, Matrix.mulVecLin_apply]

private theorem span_sub_lemma_4 {R : Type} [CommRing R] {n : ℕ} (M₁ M₂ : Matrix (Fin n) (Fin n) R)
    (A : Submodule R (Fin n → R)) {s : Set (Fin n → R)} (h : ∀ z ∈ s, M₁ *ᵥ z - M₂ *ᵥ z ∈ A) :
    ∀ z ∈ Submodule.span R s, M₁ *ᵥ z - M₂ *ᵥ z ∈ A := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
    convert add_mem hx hy using 1
    abel
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_sub]
    exact A.smul_mem c hx

private theorem span_form_lemma_5 {R : Type} [CommRing R] {n : ℕ} (τ : R →+* R) (w : Fin n → R)
    {s : Set (Fin n → R)} (h : ∀ z ∈ s, ∑ a, τ (z a) * w a = 0) :
    ∀ z ∈ Submodule.span R s, ∑ a, τ (z a) * w a = 0 := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    rw [← Finset.mul_sum, hx, mul_zero]

private theorem perp_lemma_6 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X : Matrix (Fin n) (Fin r) E}
    {I : Set (Fin r)} {g : GAd σ J}
    (hg : ∀ i ∈ I, (matHom _ σ J g).1 *ᵥ (adMat F X)ᵀ i ∈ GlobalTheory.StdPar.colSpan F X I) :
    ∀ y ∈ GlobalTheory.StdPar.colPerp σ J X I, (matHom _ σ J g⁻¹).1 *ᵥ y ∈ GlobalTheory.StdPar.colPerp σ J X I := by
  intro y hy
  rw [mem_colPerp_lemma_3] at hy ⊢
  have hP : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) =
      Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J := by
    simp only [GlobalTheory.SiegelSet.adMat]
    rw [Matrix.map_mul]
    congr 1
  have hU : Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have hGG : (matHom _ σ J g).1 * (matHom _ σ J g⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hJ : JR (AF F) J * (matHom _ σ J g⁻¹).1 = Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J := by
    calc JR (AF F) J * (matHom _ σ J g⁻¹).1
        = (Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1) *
            (matHom _ σ J g⁻¹).1 := by rw [hU]
      _ = Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J := by
          rw [Matrix.mul_assoc, hGG, Matrix.mul_one]
  have hC : Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 =
      Formalism.UG.cT (sigR (AF F) σ) ((matHom _ σ J g).1 * adMat F X) := by
    simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hPG : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * (matHom _ σ J g⁻¹).1 =
      Formalism.UG.cT (sigR (AF F) σ) ((matHom _ σ J g).1 * adMat F X) * JR (AF F) J := by
    calc adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * (matHom _ σ J g⁻¹).1
        = (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * JR (AF F) J) * (matHom _ σ J g⁻¹).1 :=
          congrArg (fun M => M * (matHom _ σ J g⁻¹).1) hP
      _ = Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * (JR (AF F) J * (matHom _ σ J g⁻¹).1) :=
          Matrix.mul_assoc _ _ _
      _ = Formalism.UG.cT (sigR (AF F) σ) (adMat F X) *
            (Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J) :=
          congrArg (fun M => Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * M) hJ
      _ = (Formalism.UG.cT (sigR (AF F) σ) (adMat F X) * Formalism.UG.cT (sigR (AF F) σ) (matHom _ σ J g).1) *
            JR (AF F) J := (Matrix.mul_assoc _ _ _).symm
      _ = Formalism.UG.cT (sigR (AF F) σ) ((matHom _ σ J g).1 * adMat F X) * JR (AF F) J :=
          congrArg (fun M => M * JR (AF F) J) hC
  have hspan := span_form_lemma_5 (sigR (AF F) σ) (JR (AF F) J *ᵥ y) (s := (fun i => (adMat F X)ᵀ i) '' I) (by
    rintro _ ⟨i', hi', rfl⟩
    have h := hy i' hi'
    rw [hP] at h
    exact (congrFun (Matrix.mulVec_mulVec y (Formalism.UG.cT (sigR (AF F) σ) (adMat F X)) (JR (AF F) J)) i').trans h)
  intro i hi
  have h3 := hspan _ (hg i hi)
  rw [Matrix.mulVec_mulVec, hPG]
  exact (congrFun (Matrix.mulVec_mulVec y
    (Formalism.UG.cT (sigR (AF F) σ) ((matHom _ σ J g).1 * adMat F X)) (JR (AF F) J)) i).symm.trans h3

private theorem conj_trivOn_lemma_7 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    {A B : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)} {g u : GAd σ J}
    (hA : ∀ y, y ∈ A ↔ (matHom _ σ J g).1 *ᵥ y ∈ A) (hu : ∀ y, y ∈ A ↔ (matHom _ σ J u).1 *ᵥ y ∈ A)
    (hB : ∀ y ∈ B, (matHom _ σ J u).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ y) - (matHom _ σ J g⁻¹).1 *ᵥ y ∈ A) :
    g * u * g⁻¹ ∈ GlobalTheory.StdPar.trivOn σ J A B := by
  have e1 : ∀ y, (matHom _ σ J (g * u * g⁻¹)).1 *ᵥ y =
      (matHom _ σ J g).1 *ᵥ ((matHom _ σ J u).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ y)) := by
    intro y
    simp only [map_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e2 : ∀ y, (matHom _ σ J g).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · rw [e1, ← hA, ← hu, hA ((matHom _ σ J g⁻¹).1 *ᵥ y), e2]
  · rw [e1]
    have h : (matHom _ σ J g).1 *ᵥ ((matHom _ σ J u).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ y)) - y =
        (matHom _ σ J g).1 *ᵥ ((matHom _ σ J u).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ y) -
          (matHom _ σ J g⁻¹).1 *ᵥ y) := by
      rw [Matrix.mulVec_sub, e2]
    rw [h]
    exact (hA _).mp (hB y hy)

private theorem conj_mem_unip_lemma_8 {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (hxx : Formalism.UG.cT (σ : E →+* E) X * J * X = 0) {T : Finset (Fin r)} {g u : GAd σ J}
    (hg : g ∈ GlobalTheory.StdPar.levi σ J X Y T) (hu : u ∈ GlobalTheory.StdPar.unip σ J X T) :
    g * u * g⁻¹ ∈ GlobalTheory.StdPar.unip σ J X T := by
  classical
  have hgi : g⁻¹ ∈ GlobalTheory.StdPar.levi σ J X Y T := inv_mem hg
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  have hu1' := Subgroup.mem_iInf.mp hu1
  have e2' : ∀ y, (matHom _ σ J g⁻¹).1 *ᵥ ((matHom _ σ J g).1 *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]
  have hiff : ∀ I : Set (Fin r), (∀ i ∈ I, ∃ k ∈ T, i ≤ k ∧ ∀ i' ≤ k, i' ∈ I) →
      ∀ y, y ∈ GlobalTheory.StdPar.colSpan F X I ↔ (matHom _ σ J g).1 *ᵥ y ∈ GlobalTheory.StdPar.colSpan F X I := by
    intro I hI y
    refine ⟨mapsTo_lemma_2 hg hI y, fun h => ?_⟩
    have := mapsTo_lemma_2 hgi hI _ h
    rwa [e2'] at this
  have hIW : ∀ i ∈ {i : Fin r | ∃ k ∈ T, i ≤ k}, ∃ k ∈ T, i ≤ k ∧ ∀ i' ≤ k, i' ∈ {i : Fin r | ∃ k ∈ T, i ≤ k} :=
    fun i hi => by
      obtain ⟨k, hk, hik⟩ := hi
      exact ⟨k, hk, hik, fun i' hi' => ⟨k, hk, hi'⟩⟩
  have hIj : ∀ j : Fin r, ∀ i ∈ {i : Fin r | ∃ k ∈ T, i ≤ k ∧ k < j},
      ∃ k ∈ T, i ≤ k ∧ ∀ i' ≤ k, i' ∈ {i : Fin r | ∃ k ∈ T, i ≤ k ∧ k < j} :=
    fun j i hi => by
      obtain ⟨k, hk, hik, hkj⟩ := hi
      exact ⟨k, hk, hik, fun i' hi' => ⟨k, hk, hi', hkj⟩⟩
  have hperp : ∀ y ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ T, i ≤ k},
      (matHom _ σ J g⁻¹).1 *ᵥ y ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ T, i ≤ k} :=
    perp_lemma_6 fun i hi => mapsTo_lemma_2 hg hIW _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hxj : ∀ j : Fin r, (adMat F X)ᵀ j ∈ GlobalTheory.StdPar.colPerp σ J X {i | ∃ k ∈ T, i ≤ k} := by
    intro j
    rw [mem_colPerp_lemma_3]
    intro i _
    have h0 : adMat F (Formalism.UG.cT (σ : E →+* E) X * J) * adMat F X = 0 := by
      simp only [GlobalTheory.SiegelSet.adMat]
      rw [← Matrix.map_mul, hxx]
      simp
    exact congrFun (congrFun h0 i) j
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_iInf.mpr fun j => ?_, ?_⟩
  · refine conj_trivOn_lemma_7 (hiff _ (hIj j)) (hu1' j).1 ?_
    have hcol : (matHom _ σ J u).1 *ᵥ ((matHom _ σ J g⁻¹).1 *ᵥ (adMat F X)ᵀ j) -
        (matHom _ σ J g⁻¹).1 *ᵥ (adMat F X)ᵀ j ∈ GlobalTheory.StdPar.colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j} := by
      by_cases hex : ∃ k ∈ T, j ≤ k
      · obtain ⟨k₀, hk₀T, hjk₀⟩ := hex
        have hmS : k₀ ∈ T.filter fun k => j ≤ k := Finset.mem_filter.mpr ⟨hk₀T, hjk₀⟩
        obtain ⟨k', hk'S, hmin'⟩ : ∃ k' ∈ T.filter (fun k => j ≤ k),
            ∀ k ∈ T.filter (fun k => j ≤ k), k' ≤ k :=
          ⟨_, Finset.min'_mem _ ⟨k₀, hmS⟩, fun k hk => Finset.min'_le _ k hk⟩
        have hk'T : k' ∈ T := (Finset.mem_filter.mp hk'S).1
        have hjk' : j ≤ k' := (Finset.mem_filter.mp hk'S).2
        have hfs : g⁻¹ ∈ GlobalTheory.StdPar.frameStab σ J (GlobalTheory.StdPar.initCols X k') ⊤ :=
          (Subgroup.mem_inf.mp ((Subgroup.mem_iInf.mp ((Subgroup.mem_iInf.mp hgi) k')) hk'T)).1
        have hz := col_mem_lemma X hfs j hjk'
        have hs := span_sub_lemma_4 (matHom _ σ J u).1 1
          (GlobalTheory.StdPar.colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j})
          (s := (fun i => (adMat F X)ᵀ i) '' {i' | i' ≤ k'}) (by
            rintro _ ⟨i, hi, rfl⟩
            rw [Matrix.one_mulVec]
            have h1 := (hu1' i).2 _ (Submodule.subset_span ⟨i, Set.mem_singleton i, rfl⟩)
            refine (Submodule.span_mono (Set.image_mono ?_)) h1
            rintro i' ⟨k, hk, hi'k, hki⟩
            refine ⟨k, hk, hi'k, ?_⟩
            by_contra hkj
            have hjk : j ≤ k := not_lt.mp hkj
            have hle := hmin' k (Finset.mem_filter.mpr ⟨hk, hjk⟩)
            exact absurd (lt_of_lt_of_le hki hi) (not_lt.mpr hle)) _ hz
        rwa [Matrix.one_mulVec] at hs
      · have hIeq : {i : Fin r | ∃ k ∈ T, i ≤ k ∧ k < j} = {i : Fin r | ∃ k ∈ T, i ≤ k} :=
          Set.ext fun i => ⟨fun h => by
              obtain ⟨k, hk, h1, _⟩ := h
              exact ⟨k, hk, h1⟩,
            fun h => by
              obtain ⟨k, hk, h1⟩ := h
              exact ⟨k, hk, h1, not_le.mp fun h' => hex ⟨k, hk, h'⟩⟩⟩
        rw [hIeq]
        exact hu2.2 _ (hperp _ (hxj j))
    intro y hy
    have hs := span_sub_lemma_4 ((matHom _ σ J u).1 * (matHom _ σ J g⁻¹).1) (matHom _ σ J g⁻¹).1
      (GlobalTheory.StdPar.colSpan F X {i | ∃ k ∈ T, i ≤ k ∧ k < j})
      (s := (fun i => (adMat F X)ᵀ i) '' {j}) (by
        rintro _ ⟨i, hi, rfl⟩
        rw [Set.mem_singleton_iff.mp hi, ← Matrix.mulVec_mulVec]
        exact hcol) y hy
    rwa [← Matrix.mulVec_mulVec] at hs
  · exact conj_trivOn_lemma_7 (hiff _ hIW) hu2.1 fun y hy => hu2.2 _ (hperp y hy)

theorem conj_mem_unip_of_mem_levi : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)),
    ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, ∀ n ∈ unip D.sp.cm.sig V.gram X T,
      g * n * g⁻¹ ∈ unip D.sp.cm.sig V.gram X T := by
  intro D V m X Y hW T g hg u hu
  exact conj_mem_unip_lemma_8 hW.xx hg hu

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
