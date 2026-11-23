import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.ExistsFiniteUnitaryClassesOfDualEqSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicHermitianFormGaloisMemOfMemCompletion

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
open GlobalTheory.AdLat

namespace GlobalTheory.Mem.ClassFinite

section Unitary

theorem hform_eq {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = (σ ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J g : Matrix (Fin n) (Fin n) A)
    (x y : Fin n → A) :
    Formalism.UG.hform σ J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ g * J * g) x y := by
  have h : σ ∘ (g *ᵥ x) = (g.map σ) *ᵥ (σ ∘ x) := by
    funext i; exact RingHom.map_mulVec σ g x i
  rw [hform_eq, hform_eq, h, Formalism.UG.cT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (σ ∘ x) (g.map σ)ᵀ, Matrix.vecMul_transpose]

theorem hform_single {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform σ J (Pi.single i 1) (Pi.single j 1) = J i j := by
  simp [Formalism.UG.hform, Pi.single_apply]

theorem mem_unitary_iff {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (g : GL (Fin n) A) :
    g ∈ Formalism.UG.UJ σ J ↔ ∀ x y, Formalism.UG.hform σ J ((g : Matrix (Fin n) (Fin n) A) *ᵥ x)
      ((g : Matrix (Fin n) (Fin n) A) *ᵥ y) = Formalism.UG.hform σ J x y := by
  change Formalism.UG.cT σ (g : Matrix (Fin n) (Fin n) A) * J * (g : Matrix (Fin n) (Fin n) A) = J ↔ _
  constructor
  · intro h x y; rw [hform_mulVec, h]
  · intro h; ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hform_single, hform_single] at this

theorem baseChange_mem {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) E)
    (hg : g ∈ Formalism.UG.UJ (σ : E →+* E) J) : Formalism.UG.bc (inclR (F := F) R) g ∈ HR R σ J := by
  have hc : Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) =
      (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j; simp [Formalism.UG.cT, sigR, inclR]
  have hg' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J := hg
  change Formalism.UG.cT (sigR R σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R)) * J.map (inclR (F := F) R) *
      (g : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) = J.map (inclR (F := F) R)
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem exists_compact_of_entries {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (C : Set (R ⊗[F] E)) (hC : IsCompact C) :
    ∃ K : Set (HA R σ J), IsCompact K ∧ ∀ h : HA R σ J, (∀ i j, (HA.mat R σ J h).1 i j ∈ C) → h ∈ K := by
  have : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  have : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hc : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  let S : Set (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  let f : Matrix (Fin M) (Fin M) (R ⊗[F] E) → (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun A => MulOpposite.op (JR (F := F) R J⁻¹ * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J))
  have hf : Continuous f := MulOpposite.continuous_op.comp (continuous_const.matrix_mul
    ((continuous_id.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const))
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image hf)), fun h hh => ?_⟩
  have hm : (HA.mat R σ J h).1 ∈ S := fun i _ j _ => hh i j
  refine ⟨hm, (HA.mat R σ J h).1, hm, ?_⟩
  have hu : Formalism.UG.cT (sigR R σ) (HA.mat R σ J h).1 * JR (F := F) R J * (HA.mat R σ J h).1 = JR (F := F) R J := h.2
  have h1 : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  change MulOpposite.op _ = MulOpposite.op ((HA.mat R σ J h)⁻¹).1
  congr 1
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc, hu, h1]

end Unitary

section Lattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def intLat (E : Type) [Field E] (n : ℕ) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

def intSet (E : Type) [Field E] : Set E := {x | IsIntegral ℤ x}

omit [NumberField E] in
theorem mem_intLat (v : Fin n → E) : v ∈ intLat E n ↔ ∀ i, IsIntegral ℤ (v i) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [NumberField E] in
theorem single_mem_intLat (i : Fin n) {x : E} (hx : IsIntegral ℤ x) :
    (Pi.single i x : Fin n → E) ∈ intLat E n := by
  rw [mem_intLat]
  intro j
  by_cases h : j = i
  · subst h; simpa using hx
  · simpa [h] using isIntegral_zero

omit [NumberField E] in
theorem intLat_fg : (intLat E n).FG := Submodule.fg_pi fun _ => by
  rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

omit [NumberField E] in
theorem span_intLat : Submodule.span E (intLat E n : Set (Fin n → E)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact single_mem_intLat i isIntegral_one

theorem one_tmul_mem_iff (x : E) :
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x ∈ hat1 F (intSet E) ↔ IsIntegral ℤ x := by
  have h : ∀ x : E, x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ IsIntegral ℤ x := fun x => by
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have e : intSet E = ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := Set.ext fun x => (h x).symm
  rw [e, one_tmul_mem_adelicCompletion_fractionalIdeal_iff, h]

omit [NumberField E] in
theorem mul_mem_int {x y : RA F E} (hx : x ∈ hat1 F (intSet E)) (hy : y ∈ hat1 F (intSet E)) :
    x * y ∈ hat1 F (intSet E) :=
  mul_mem_adelicCompletionOfElementSet_of_mul_mem F (fun _ ha _ hb => IsIntegral.mul ha hb) hx hy

omit [NumberField E] in

theorem mem_hat_intLat (z : Fin n → RA F E) :
    z ∈ hat F (intLat E n : Set (Fin n → E)) ↔ ∀ i, z i ∈ hat1 F (intSet E) := by
  constructor
  · intro hz i
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact tmul_mem_adelicCompletion_of_integral F ha ((mem_intLat x).1 hx i)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro hz
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := hz i
    generalize z i = t at hi
    induction hi using AddSubgroup.closure_induction with
    | mem t ht =>
      obtain ⟨a, ha, x, hx, rfl⟩ := ht
      refine AddSubgroup.subset_closure ⟨a, ha, _, single_mem_intLat i hx, ?_⟩
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Pi.single_add]; exact add_mem hx hy
    | neg x _ hx => rw [Pi.single_neg]; exact neg_mem hx

theorem exists_int_bound (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (hG : G.det ≠ 0) :
    ∃ N : ℤ, N ≠ 0 ∧
      (∀ z ∈ hat F (intLat E n : Set (Fin n → E)), ∀ w ∈ hat F (intLat E n : Set (Fin n → E)),
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)) * hermA c G z w ∈ hat1 F (intSet E)) ∧
      ∀ z : Fin n → RA F E, (∀ w ∈ hat F (intLat E n : Set (Fin n → E)), hermA c G z w ∈ hat1 F (intSet E)) →
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) : RA F E) • z ∈ hat F (intLat E n : Set (Fin n → E)) := by
  obtain ⟨N, hN, hNi⟩ := HermClass.exists_int_mul_isIntegral E
    ((Set.finite_range fun p : Fin n × Fin n => G p.1 p.2).union
      (Set.finite_range fun p : Fin n × Fin n => G⁻¹ p.1 p.2))
  refine ⟨N, hN, fun z hz w hw => ?_, fun z hz => ?_⟩
  · rw [mem_hat_intLat] at hz hw
    simp only [hermA, Finset.mul_sum]
    refine sum_mem fun a _ => sum_mem fun b _ => ?_
    have h1 := mul_mem_int (mul_mem_int (hz a) ((one_tmul_mem_iff (F := F) _).2 (hNi _ (Or.inl ⟨(a, b), rfl⟩))))
      (galoisAut_mem_adelicCompletionOfElementSet F c (I := intSet E) (J := intSet E)
        (fun x hx => IsIntegral.map (c : E →+* E).toIntAlgHom hx) (hw b))
    have e : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * G a b) =
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] G a b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [e] at h1
    convert h1 using 1
    ring
  · have h1 : ∀ b, (z ᵥ* G.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F))) b ∈ hat1 F (intSet E) := fun b => by
      have := hz _ (Translate.fv_mem_hat (F := F) (single_mem_intLat b isIntegral_one))
      convert this using 1
      simp only [hermA, Matrix.vecMul, dotProduct, Matrix.map_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_eq_single b]
      · simp [fv, inclR, ← Algebra.TensorProduct.one_def]
      · intro b' _ hb; simp [fv, hb]
      · simp
    have h2 : (z ᵥ* G.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F))) ᵥ*
        G⁻¹.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) = z := by
      rw [Matrix.vecMul_vecMul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hG),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
    rw [← h2, mem_hat_intLat]
    intro i
    generalize z ᵥ* G.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) = u at h1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum]
    refine sum_mem fun b _ => ?_
    have h3 := mul_mem_int (h1 b) ((one_tmul_mem_iff (F := F) _).2 (hNi _ (Or.inr ⟨(b, i), rfl⟩)))
    have e : (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E) * G⁻¹ b i) =
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)) * inclR (F := F) (FiniteAdeleRing (𝓞 F) F) (G⁻¹ b i) := by
      simp [inclR]
    rw [e] at h3
    convert h3 using 1
    ring

end Lattice

section Classes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem hermA_transpose (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → RA F E) :
    hermA c Jᵀ x y = Formalism.UG.hform (sigR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E))
      (JR (FiniteAdeleRing (𝓞 F) F) J) y x := by
  unfold hermA Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, mul_comm (x j), ← mul_assoc]
  rfl

omit [NumberField E] in
theorem map_mulVec_fv (γ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    γ.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) *ᵥ fv F x = fv F (γ *ᵥ x) := by
  funext i
  simp [fv, inclR, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem exists_finite_translates [IsCMField E] (c : E ≃ₐ[F] E) (hc : ∀ x, c x = IsCMField.complexConj E x)
    (G : Matrix (Fin n) (Fin n) E) (hG : ∀ a b, c (G a b) = G b a) (hdet : G.det ≠ 0) {α : Type}
    (g : α → GL (Fin n) (RA F E))
    (hg : ∀ a x y, hermA c G ((g a).1 *ᵥ x) ((g a).1 *ᵥ y) = hermA c G x y) :
    ∃ S : Set α, S.Finite ∧ ∀ a, ∃ s ∈ S, ∃ γ : GL (Fin n) E,
      (∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm G (γ.1 *ᵥ x) (γ.1 *ᵥ y) = ReciprocityTheory.ChartRestriction.G.FD.herm G x y) ∧
      ∀ z ∈ hat F (intLat E n : Set (Fin n → E)),
        ((g s)⁻¹ * (Formalism.UG.bc (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * g a)).1 *ᵥ z ∈
          hat F (intLat E n : Set (Fin n → E)) := by
  obtain ⟨N, hN, hN1, hN2⟩ := exists_int_bound c G hdet
  choose Λ hΛ hfg hsp hhat using fun a =>
    exists_lattice_latOf F E n (intLat E n) (g a) intLat_fg span_intLat
  have hh : ∀ x y, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ReciprocityTheory.ChartRestriction.G.FD.herm G x y := fun x y => by
    rw [hermA_fv_fv]
    simp only [hc]
    rfl
  have hmem : ∀ a x, x ∈ Λ a ↔ ∃ z ∈ hat F (intLat E n : Set (Fin n → E)), (g a).1 *ᵥ z = fv F x :=
    fun a x => by rw [← SetLike.mem_coe, hΛ]; rfl
  have hup : ∀ a, ∀ z ∈ hat F (intLat E n : Set (Fin n → E)), (g a).1 *ᵥ z ∈ hat F (Λ a : Set (Fin n → E)) :=
    fun a z hz => by rw [← SetLike.mem_coe, hhat]; exact ⟨z, hz, rfl⟩
  obtain ⟨S, hS, H⟩ := GlobalTheory.exists_finite_unitary_classes G (fun a b => (hc _).symm.trans (hG a b)) hdet hN
    (𝔪 := ⊤) top_ne_bot Λ (fun _ => (Empty.elim : Empty → _)) (fun a => ⟨hfg a, hsp a⟩)
    (fun a x hx y hy => by
      obtain ⟨z, hz, ez⟩ := (hmem a x).1 hx
      obtain ⟨w, hw, ew⟩ := (hmem a y).1 hy
      have := hN1 z hz w hw
      rwa [← hg a, ez, ew, hh, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_tmul_mem_iff] at this)
    (fun a x hx => by
      have hz : (g a).1 *ᵥ (((g a)⁻¹).1 *ᵥ fv F x) = fv F x := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      refine (hmem a _).2 ⟨_, hN2 (((g a)⁻¹).1 *ᵥ fv F x) fun w hw => ?_, ?_⟩
      · rw [← hg a, hz]
        refine adelicHermitianFormGalois_mem_of_mem_completion c G (fun y hy => ?_) (hup a w hw)
        rw [hh, one_tmul_mem_iff]
        exact hx y hy
      · rw [Matrix.mulVec_smul, hz, Translate.fv_smul])
    (fun _ i => i.elim)
  refine ⟨S, hS, fun a => ?_⟩
  obtain ⟨s, hs, γ, h1, h2, -⟩ := H a
  refine ⟨s, hs, γ, h1, fun z hz => ?_⟩
  have h3 : γ.1.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) *ᵥ ((g a).1 *ᵥ z) ∈
      hat F (Λ s : Set (Fin n → E)) := by
    refine Translate.mulVec_mem_hat (fun x hx => ?_) (hup a z hz)
    rw [SetLike.mem_coe, Translate.mem_pre, map_mulVec_fv]
    exact Translate.fv_mem_hat ((h2 x).1 hx)
  rw [← SetLike.mem_coe, hhat] at h3
  obtain ⟨w, hw, e⟩ := h3
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change ((g s)⁻¹).1 *ᵥ (γ.1.map (inclR (F := F) (FiniteAdeleRing (𝓞 F) F)) *ᵥ ((g a).1 *ᵥ z)) ∈ _
  rw [← e, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  exact hw

theorem exists_finite_cosets {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (K : Subgroup H) (hK : IsOpen (K : Set H)) (C : Set H) (hC : IsCompact C) :
    ∃ T : Finset H, ∀ x ∈ C, ∃ t ∈ T, t⁻¹ * x ∈ K := by
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover (fun t : H => (fun x => t⁻¹ * x) ⁻¹' (K : Set H))
    (fun t => hK.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨t, ht, h⟩ := Set.mem_iUnion₂.1 (hT hx)
  exact ⟨t, ht, h⟩

end Classes

theorem exists_finset_classes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ K : Subgroup (HA (Af F) σ J), IsOpen (K : Set (HA (Af F) σ J)) → ∃ S : Finset (HA (Af F) σ J), ∀ g : HA (Af F) σ J, ∃ γ : HFinIn (Af F) σ J, ∃ s ∈ S, ∃ k ∈ K, g = γ • (s * k) := by
  classical
  intro F E _ _ _ _ _ σ hσ M J hJ K hK
  obtain ⟨h1, h2, h3, h4⟩ := hσ
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : Algebra.IsQuadraticExtension F E := ⟨h3⟩
  have : IsCMField E := IsCMField.ofCMExtension F E
  have hc : ∀ x, σ x = IsCMField.complexConj E x := fun x => by
    let φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    apply φ.injective
    rw [h4, IsCMField.complexEmbedding_complexConj]
    rfl
  obtain ⟨c, rfl⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ), rfl⟩
  have : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
    IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) _
  have : IsTopologicalGroup (HA (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E) J) :=
    inferInstanceAs (IsTopologicalGroup (HR (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E) J))
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨C, hC, hCe⟩ := StabGroup.exists_compact_entries F E (intLat E M) intLat_fg span_intLat
  obtain ⟨C', hC', hCe'⟩ := exists_compact_of_entries (FiniteAdeleRing (𝓞 F) F)
    (c : E →ₐ[F] E) J hJ.2 C hC
  obtain ⟨T, hT⟩ := exists_finite_cosets K hK C' hC'
  obtain ⟨S, hS, H⟩ := exists_finite_translates c hc Jᵀ (fun a b => hJ.1 a b)
    (by rw [Matrix.det_transpose]; exact hJ.2) (HA.mat (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E) J)
    (fun a x y => by
      rw [hermA_transpose, hermA_transpose]
      exact (mem_unitary_iff _ _ _).1 a.2 y x)
  refine ⟨Finset.image₂ (· * ·) hS.toFinset T, fun g => ?_⟩
  obtain ⟨s, hs, γ, hγ, hz⟩ := H g
  have hh : ∀ x y, ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y = Formalism.UG.hform ((c : E →ₐ[F] E) : E →+* E) J y x :=
    fun x y => by
      unfold ReciprocityTheory.ChartRestriction.G.FD.herm Formalism.UG.hform
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm, mul_comm (x j), ← mul_assoc, ReciprocityTheory.ChartRestriction.G.FD.cc, ← hc]
      rfl
  have hγU : γ ∈ Formalism.UG.UJ ((c : E →ₐ[F] E) : E →+* E) J :=
    (mem_unitary_iff _ _ _).2 fun x y => by rw [← hh, ← hh, hγ]
  let γ' : HA (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E) J :=
    ⟨_, baseChange_mem (FiniteAdeleRing (𝓞 F) F) _ J γ hγU⟩
  let γ'' : HFinIn (FiniteAdeleRing (𝓞 F) F) (c : E →ₐ[F] E) J := ⟨γ', γ, hγU, rfl⟩
  obtain ⟨t, ht, hk⟩ := hT (s⁻¹ * (γ' * g)) (hCe' _ (hCe _ hz))
  refine ⟨γ''⁻¹, s * t, Finset.mem_image₂_of_mem (hS.mem_toFinset.2 hs) ht, _, hk, ?_⟩
  change g = γ'⁻¹ * (s * t * (t⁻¹ * (s⁻¹ * (γ' * g))))
  group

end GlobalTheory.Mem.ClassFinite
