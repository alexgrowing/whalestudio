import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm

open NumberField IsDedekindDomain Topology Filter Set MeasureTheory
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

abbrev PPos (n : ℕ) (S : Finset ℕ) : Type :=
  {p : Fin n × Fin n // ∃ s ∈ S, (p.1 : ℕ) < s ∧ s ≤ (p.2 : ℕ)}

section Ring

variable {n : ℕ} {S : Finset ℕ} {R : Type*} [CommRing R]

def parEntry (X : PPos n S → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if h : ∃ s ∈ S, (i : ℕ) < s ∧ s ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0

theorem parEntry_apply (X : PPos n S → R) (i j : Fin n) :
    parEntry X i j = if h : ∃ s ∈ S, (i : ℕ) < s ∧ s ≤ (j : ℕ) then X ⟨(i, j), h⟩ else 0 := rfl

theorem parEntry_apply_of_le (X : PPos n S → R) {i j : Fin n} (hij : j ≤ i) :
    parEntry X i j = 0 := by
  rw [parEntry_apply, dif_neg]
  rintro ⟨s, -, h1, h2⟩
  have : (j : ℕ) ≤ i := hij
  omega

def parMatrix (X : PPos n S → R) : Matrix (Fin n) (Fin n) R := 1 + parEntry X

theorem parMatrix_isUpperTriangular (X : PPos n S → R) : (parMatrix X).IsUpperTriangular := by
  intro i j hji
  have hji' : j < i := hji
  simp only [parMatrix, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji').symm, zero_add]
  exact parEntry_apply_of_le X (le_of_lt hji')

theorem det_parMatrix (X : PPos n S → R) : (parMatrix X).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (parMatrix_isUpperTriangular X)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [parMatrix, parEntry_apply_of_le X (le_refl i)]

def parGL (X : PPos n S → R) : GL (Fin n) R :=
  Matrix.nonsingInvUnit (parMatrix X) (by rw [det_parMatrix]; exact isUnit_one)

@[simp] theorem coe_parGL (X : PPos n S → R) :
    ((parGL X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = parMatrix X := rfl

theorem coe_parGL_inv (X : PPos n S → R) :
    (((parGL X)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = (parMatrix X).adjugate := by
  change (parMatrix X)⁻¹ = _
  rw [Matrix.inv_def, det_parMatrix, Ring.inverse_one, one_smul]

end Ring

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} {S : Finset ℕ}

theorem diagonal_parGL (ξ : PPos n S → K) :
    AdelicGLn.diagonal K n (parGL ξ) = parGL (fun p => algebraMap K 𝔸[K] (ξ p)) := by
  ext i j
  simp only [AdelicGLn.diagonal_apply, coe_parGL, parMatrix, Matrix.add_apply, parEntry_apply,
    Matrix.one_apply]
  split_ifs <;> simp

theorem continuous_parMatrix :
    Continuous (parMatrix : (PPos n S → 𝔸[K]) → Matrix (Fin n) (Fin n) 𝔸[K]) := by
  refine continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [parEntry_apply]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

theorem continuous_parGL :
    Continuous (parGL : (PPos n S → 𝔸[K]) → AdelicGLn.AdelicGL K n) := by
  refine Units.continuous_iff.2 ⟨continuous_parMatrix, ?_⟩
  have : (fun X : PPos n S → 𝔸[K] => (((parGL X)⁻¹ : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) 𝔸[K])) = fun X => (parMatrix X).adjugate :=
    funext fun X => coe_parGL_inv X
  rw [this]
  exact continuous_parMatrix.matrix_adjugate

variable (K n S) in

abbrev parMeasure : Measure (PPos n S → 𝔸[K]) := Measure.pi fun _ => GroundTheory.Global.adeleMeasure K

variable (K n S) in

def parFundamentalDomain : Set (PPos n S → 𝔸[K]) :=
  Set.univ.pi fun _ => GroundTheory.Global.fundamentalSet K

variable (S) in

def constantTermPar (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  ∫ X in parFundamentalDomain K n S, φ (parGL X * g) ∂parMeasure K n S

section Box

variable (K) in

abbrev boxMeasure : Measure 𝔸[K] :=
  (GroundTheory.Global.adeleMeasure K).restrict (GroundTheory.Global.fundamentalSet K)

variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

theorem setIntegral_box_eq (F : (ι → 𝔸[K]) → ℂ) :
    ∫ X in Set.univ.pi (fun _ : ι => GroundTheory.Global.fundamentalSet K), F X
        ∂(Measure.pi fun _ => GroundTheory.Global.adeleMeasure K) =
      ∫ X, F X ∂(Measure.pi fun _ : ι => boxMeasure K) := by
  rw [Measure.restrict_pi_pi]

theorem integrable_box {F : (ι → 𝔸[K]) → ℂ} (hF : Continuous F) :
    Integrable F (Measure.pi fun _ : ι => boxMeasure K) := by
  set C : Set (ι → 𝔸[K]) := Set.univ.pi fun _ =>
    closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ
      (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod
      (GroundTheory.Global.isCompact_integralFiniteAdeles K)
  have hDC : (Set.univ.pi fun _ : ι => GroundTheory.Global.fundamentalSet K) ⊆ C := by
    intro X hX p _
    exact ⟨subset_closure (hX p (mem_univ p)).1, (hX p (mem_univ p)).2⟩
  have h1 : IntegrableOn F (Set.univ.pi fun _ : ι => GroundTheory.Global.fundamentalSet K)
      (Measure.pi fun _ => GroundTheory.Global.adeleMeasure K) :=
    (hF.continuousOn.integrableOn_compact hC).mono_set hDC
  rw [IntegrableOn, Measure.restrict_pi_pi] at h1
  exact h1

theorem integral_box_reindex (e : ι ≃ ι') (F : (ι' → 𝔸[K]) → ℂ) :
    ∫ Y, F Y ∂(Measure.pi fun _ : ι' => boxMeasure K) =
      ∫ X, F (fun i' => X (e.symm i')) ∂(Measure.pi fun _ : ι => boxMeasure K) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => boxMeasure K) e
  rw [← hmp.integral_comp' F]
  congr 1
  funext X
  congr 1
  funext i'
  obtain ⟨i, rfl⟩ := e.surjective i'
  rw [Equiv.symm_apply_apply]
  exact Equiv.piCongrLeft_apply_apply (fun _ => 𝔸[K]) e X i

end Box

theorem constantTermPar_eq_integral (φ : AdelicGLn.AdelicGL K n → ℂ)
    (g : AdelicGLn.AdelicGL K n) :
    constantTermPar S φ g =
      ∫ X, φ (parGL X * g) ∂(Measure.pi fun _ : PPos n S => boxMeasure K) :=
  setIntegral_box_eq _

theorem constantTerm_eq_integral (r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ)
    (g : AdelicGLn.AdelicGL K n) :
    constantTerm r φ g =
      ∫ X, φ (unipGL X * g) ∂(Measure.pi fun _ : UPos n r => boxMeasure K) :=
  setIntegral_box_eq _

def pposSingletonEquiv (n r : ℕ) : UPos n r ≃ PPos n {r} where
  toFun p := ⟨p.1, r, Finset.mem_singleton_self r, p.2⟩
  invFun q := ⟨q.1, by
    obtain ⟨s, hs, h⟩ := q.2
    rw [Finset.mem_singleton] at hs
    exact hs ▸ h⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem parGL_singleton {R : Type*} [CommRing R] {r : ℕ} (X : UPos n r → R) :
    parGL (fun q => X ((pposSingletonEquiv n r).symm q)) = unipGL X := by
  apply Units.ext
  ext i j
  simp only [coe_parGL, coe_unipGL, parMatrix, unipMatrix, Matrix.add_apply, parEntry_apply,
    blockEntry_apply]
  congr 1
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · have h' : ∃ s ∈ ({r} : Finset ℕ), (i : ℕ) < s ∧ s ≤ (j : ℕ) :=
      ⟨r, Finset.mem_singleton_self r, h⟩
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ ∃ s ∈ ({r} : Finset ℕ), (i : ℕ) < s ∧ s ≤ (j : ℕ) := by
      rintro ⟨s, hs, hh⟩
      rw [Finset.mem_singleton] at hs
      exact h (hs ▸ hh)
    rw [dif_neg h', dif_neg h]

theorem constantTermPar_singleton (r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ)
    (g : AdelicGLn.AdelicGL K n) : constantTermPar {r} φ g = constantTerm r φ g := by
  rw [constantTermPar_eq_integral, constantTerm_eq_integral,
    integral_box_reindex (pposSingletonEquiv n r)]
  simp only [parGL_singleton]

section Split

variable {R : Type*} [CommRing R] {r : ℕ}

def IsTop (r : ℕ) (q : PPos n S) : Prop := (q.1.1 : ℕ) < r ∧ r ≤ (q.1.2 : ℕ)

instance (r : ℕ) : DecidablePred (IsTop (n := n) (S := S) r) := fun q => by
  unfold IsTop; infer_instance

def topEquiv (hr : r ∈ S) : {q : PPos n S // IsTop r q} ≃ UPos n r where
  toFun q := ⟨q.1.1, q.2⟩
  invFun p := ⟨⟨p.1, r, hr, p.2⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def joinPos (a : {q : PPos n S // IsTop r q} → R) (b : {q : PPos n S // ¬ IsTop r q} → R) :
    PPos n S → R :=
  fun q => if h : IsTop r q then a ⟨q, h⟩ else b ⟨q, h⟩

theorem blockEntry_mul_parEntry (hmax : ∀ s ∈ S, ∀ i j : Fin n, (i : ℕ) < s → s ≤ (j : ℕ) → s ≤ r)
    (A : UPos n r → R) (X : PPos n S → R) : blockEntry A * parEntry X = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [blockEntry_apply, parEntry_apply]
  split_ifs with h1 h2
  · obtain ⟨s, hs, h3, h4⟩ := h2
    have := hmax s hs k j h3 h4
    omega
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

theorem parGL_eq_unipGL_mul (hr : r ∈ S)
    (hmax : ∀ s ∈ S, ∀ i j : Fin n, (i : ℕ) < s → s ≤ (j : ℕ) → s ≤ r)
    (a : {q : PPos n S // IsTop r q} → R) (b : {q : PPos n S // ¬ IsTop r q} → R) :
    parGL (joinPos a b) = unipGL (fun p => a ((topEquiv hr).symm p)) * parGL (joinPos 0 b) := by
  apply Units.ext
  simp only [Units.val_mul, coe_parGL, coe_unipGL]
  rw [unipMatrix, parMatrix, parMatrix, add_mul, one_mul, mul_add, mul_one,
    blockEntry_mul_parEntry hmax, add_zero]
  ext i j
  simp only [Matrix.add_apply, parEntry_apply, blockEntry_apply, joinPos]
  rw [add_assoc]
  congr 1
  by_cases hP : ∃ s ∈ S, (i : ℕ) < s ∧ s ≤ (j : ℕ)
  · rw [dif_pos hP, dif_pos hP]
    by_cases hT : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · have hT' : IsTop r (⟨(i, j), hP⟩ : PPos n S) := hT
      rw [dif_pos hT, dif_pos hT', dif_pos hT', Pi.zero_apply, zero_add]
      rfl
    · have hT' : ¬ IsTop r (⟨(i, j), hP⟩ : PPos n S) := hT
      rw [dif_neg hT, dif_neg hT', dif_neg hT', add_zero]
  · rw [dif_neg hP, dif_neg hP, zero_add, dif_neg]
    rintro hT
    exact hP ⟨r, hr, hT⟩

end Split

theorem exists_max_break (hS : ∃ s ∈ S, 0 < s ∧ s < n) :
    ∃ r ∈ S, 0 < r ∧ r < n ∧
      ∀ s ∈ S, ∀ i j : Fin n, (i : ℕ) < s → s ≤ (j : ℕ) → s ≤ r := by
  classical
  set T := S.filter fun s => 0 < s ∧ s < n
  have hT : T.Nonempty := by
    obtain ⟨s, hs, h⟩ := hS
    exact ⟨s, Finset.mem_filter.2 ⟨hs, h⟩⟩
  have hr := Finset.mem_filter.1 (T.max'_mem hT)
  refine ⟨T.max' hT, hr.1, hr.2.1, hr.2.2, fun s hs i j h1 h2 => ?_⟩
  refine T.le_max' s (Finset.mem_filter.2 ⟨hs, ?_, ?_⟩)
  · omega
  · have := j.2
    omega

theorem IsCuspidal.constantTermPar_eq_zero {φ : AdelicGLn.AdelicGL K n → ℂ} (hφc : Continuous φ)
    (hφ : IsCuspidal φ) {S : Finset ℕ} (hS : ∃ s ∈ S, 0 < s ∧ s < n)
    (g : AdelicGLn.AdelicGL K n) : constantTermPar S φ g = 0 := by
  classical
  obtain ⟨r, hr, hr0, hrn, hmax⟩ := exists_max_break hS
  obtain ⟨e, he⟩ : ∃ e, e = MeasurableEquiv.piEquivPiSubtypeProd (fun _ : PPos n S => 𝔸[K]) (IsTop r) :=
    ⟨_, rfl⟩
  have hmp : MeasurePreserving e (Measure.pi fun _ : PPos n S => boxMeasure K)
      ((Measure.pi fun i : {q : PPos n S // IsTop r q} => boxMeasure K).prod
        (Measure.pi fun i : {q : PPos n S // ¬ IsTop r q} => boxMeasure K)) :=
    he ▸ measurePreserving_piEquivPiSubtypeProd (fun _ : PPos n S => boxMeasure K) (IsTop r)
  have hsymm : ∀ a b, e.symm (a, b) = joinPos a b := by
    intro a b
    subst he
    funext q
    simp [MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, joinPos]
  set F : (PPos n S → 𝔸[K]) → ℂ := fun X => φ (parGL X * g)
  have hF : Continuous F := hφc.comp (continuous_parGL.mul continuous_const)
  have hFi := integrable_box (ι := PPos n S) hF
  have hFe : Integrable (F ∘ e.symm)
      ((Measure.pi fun i : {q : PPos n S // IsTop r q} => boxMeasure K).prod
        (Measure.pi fun i : {q : PPos n S // ¬ IsTop r q} => boxMeasure K)) :=
    ((hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hFi
  rw [constantTermPar_eq_integral]
  have e1 : ∫ X, φ (parGL X * g) ∂(Measure.pi fun _ : PPos n S => boxMeasure K) =
      ∫ z, (F ∘ e.symm) z ∂((Measure.pi fun i : {q : PPos n S // IsTop r q} => boxMeasure K).prod
        (Measure.pi fun i : {q : PPos n S // ¬ IsTop r q} => boxMeasure K)) := by
    rw [← hmp.integral_comp' (F ∘ e.symm)]
    simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply, F]
  rw [e1, integral_prod_symm _ hFe]
  have h0 : ∀ b, ∫ a, (F ∘ e.symm) (a, b)
      ∂(Measure.pi fun i : {q : PPos n S // IsTop r q} => boxMeasure K) = 0 := by
    intro b
    have e2 : ∀ a, (F ∘ e.symm) (a, b) =
        φ (unipGL (fun p => a ((topEquiv hr).symm p)) * (parGL (joinPos 0 b) * g)) := by
      intro a
      simp only [Function.comp_apply, F, hsymm]
      rw [← mul_assoc, ← parGL_eq_unipGL_mul hr hmax a b]
    simp_rw [e2]
    rw [← integral_box_reindex (topEquiv hr)
      (fun A => φ (unipGL A * (parGL (joinPos 0 b) * g))), ← constantTerm_eq_integral]
    exact hφ r hr0 hrn _
  simp_rw [h0]
  exact integral_zero _ _

theorem isCuspidal_iff_constantTermPar {φ : AdelicGLn.AdelicGL K n → ℂ} (hφ : Continuous φ) :
    IsCuspidal φ ↔
      ∀ S : Finset ℕ, (∃ s ∈ S, 0 < s ∧ s < n) → ∀ g, constantTermPar S φ g = 0 := by
  refine ⟨fun h S hS g => h.constantTermPar_eq_zero hφ hS g, fun h r hr hrn g => ?_⟩
  rw [← constantTermPar_singleton]
  exact h {r} ⟨r, Finset.mem_singleton_self r, hr, hrn⟩ g

theorem mem_cuspForms_iff_constantTermPar {φ : AdelicGLn.AdelicGL K n → ℂ} :
    φ ∈ cuspForms K n ↔ IsAutomorphicForm φ ∧
      ∀ S : Finset ℕ, (∃ s ∈ S, 0 < s ∧ s < n) → ∀ g, constantTermPar S φ g = 0 := by
  rw [mem_cuspForms]
  exact ⟨fun h => ⟨h.1, (isCuspidal_iff_constantTermPar h.1.continuous).1 h.2⟩,
    fun h => ⟨h.1, (isCuspidal_iff_constantTermPar h.1.continuous).2 h.2⟩⟩

end AutomorphicForm

end

end GroundTheory.Automorphic
