import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

noncomputable section

namespace GlobalTheory.ThK.PlaneCo.Std

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul {m k l : Type} [Fintype k] (A : Matrix m k E) (C : Matrix k l E) :
    incM F (A * C) = incM F A * incM F C := by
  simp [incM, Matrix.map_mul]

theorem incM_transpose {m k : Type} (A : Matrix m k E) : incM F Aᵀ = (incM F A)ᵀ := by
  simp [incM, Matrix.transpose_map]

theorem coefLin_incM {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) E) :
    coefLin (F := F) H H' (incM F u) = incM F (planeCoef H * u * (planeCoef H')ᵀ) := by
  show incM F (planeCoef H) * incM F u * (incM F (planeCoef H'))ᵀ = _
  rw [incM_mul, incM_mul, incM_transpose]

def ratS {n d n₁ d₁ : ℕ} (H : Plane E n n₁) (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) E)
    (k : Kc F E d₁ n₁) : F :=
  (bE F E).repr ((planeCoef H * u * (planeCoef H')ᵀ) (posS k.1).1 (posS k.1).2) k.2

theorem planeT_incM_fst (σ : E →ₐ[F] E) {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁)
    (H' : Plane E d d₁) (u : Matrix (Fin n) (Fin d) E) (k : Kc F E d₁ n₁) :
    (planeT σ X W H H' (incM F u)).1.1 k = algebraMap F (AF F) (ratS H H' u k) := by
  show (bA F E).repr (sI H H' (incM F u) k.1) k.2 = _
  simp only [sI, coefLin_incM]
  show (bA F E).repr ((1 : AF F) ⊗ₜ[F] _) k.2 = _
  simp [bA, Algebra.TensorProduct.basis_repr_tmul, ratS]

theorem planeMat_mulVec {n n₁ : ℕ} (H : Plane E n n₁) (u : Fin n₁ → E) (s t : E) :
    planeMat H *ᵥ Sum.elim u ![s, t] = H.ι *ᵥ u + s • H.x + t • H.y := by
  funext i
  simp [planeMat, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mul_comm]
  ring

theorem planeCoef_mul_planeMat (σ : E →ₐ[F] E) (B : Base F E) {n n₁ i₀ i₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n)
    (Y₁ : Spc F E n₁) [Submodule.IsLattice E Y.L] (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) :
    planeCoef H * planeMat H = 1 := by
  have h : n₁ + 2 = n := hH.rank.symm
  set e : Fin n₁ ⊕ Fin 2 ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  set M' := (planeMat H).submatrix id e.symm with hM'
  have hP : planeCoef H = (M'⁻¹).submatrix e id := by
    simp only [planeCoef, dif_pos h]; rfl
  have hM : planeMat H = M'.submatrix id e := by
    rw [hM', Matrix.submatrix_submatrix]; simp
  have hsurj : Function.Surjective M'.mulVec := by
    have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.range (Matrix.mulVecLin M') := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
      refine ⟨Sum.elim u ![s, t] ∘ e.symm, ?_⟩
      have hc : M' *ᵥ (Sum.elim u ![s, t] ∘ e.symm) = planeMat H *ᵥ Sum.elim u ![s, t] := by
        funext i
        simp only [hM', Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id, Function.comp]
        exact Equiv.sum_comp e.symm (fun k => planeMat H i k * Sum.elim u ![s, t] k)
      rw [Matrix.mulVecLin_apply, hc, planeMat_mulVec]
      abel
    rw [Submodule.IsLattice.span_eq_top, top_le_iff] at hle
    intro w
    obtain ⟨p, hp⟩ : w ∈ LinearMap.range (Matrix.mulVecLin M') := by rw [hle]; trivial
    exact ⟨p, hp⟩
  have hu : IsUnit M'.det := (Matrix.isUnit_iff_isUnit_det M').1 (Matrix.mulVec_surjective_iff_isUnit.1 hsurj)
  rw [hP, hM, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul _ hu]
  simp

theorem posS_injective {d₁ n₁ : ℕ} : Function.Injective (posS : Ic d₁ n₁ → _) := by
  rintro (j | a) (j' | a') h <;> simp_all [posS]

theorem exists_ratS_single (σ : E →ₐ[F] E) (B : Base F E) {n d n₁ d₁ i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d)
    (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁) [Submodule.IsLattice E X.L]
    [Submodule.IsLattice E W.L] (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (k₀ : Kc F E d₁ n₁) : ∃ u : Matrix (Fin n) (Fin d) E, ∀ k, ratS H H' u k = if k = k₀ then 1 else 0 := by
  classical
  set C : Matrix (Fin n₁ ⊕ Fin 2) (Fin d₁ ⊕ Fin 2) E :=
    Matrix.of fun a b => if (a, b) = posS k₀.1 then bE F E k₀.2 else 0 with hC
  refine ⟨planeMat H * C * (planeMat H')ᵀ, fun k => ?_⟩
  have h1 := planeCoef_mul_planeMat σ B H X X₁ hH
  have h2 := planeCoef_mul_planeMat σ B H' W W₁ hH'
  have hk : planeCoef H * (planeMat H * C * (planeMat H')ᵀ) * (planeCoef H')ᵀ = C := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, h2,
      Matrix.transpose_one, Matrix.mul_one]
  unfold ratS
  rw [hk, hC]
  simp only [Matrix.of_apply, Prod.mk.eta]
  by_cases e : k = k₀
  · subst e; simp
  · rw [if_neg e]
    by_cases e1 : posS k.1 = posS k₀.1
    · have e1' := posS_injective e1
      have e2 : k.2 ≠ k₀.2 := fun h => e (Prod.ext e1' h)
      rw [if_pos e1, Module.Basis.repr_self, Finsupp.single_apply, if_neg (Ne.symm e2)]
    · rw [if_neg e1]; simp

def adAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v x)

theorem evFin_adAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : evFin F v (adAt v x) = x := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (singleFin v x) = x
  exact evalV_singleFin_self v x

theorem at_adAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : At (evFin F v) (adAt v x) := by
  intro u hu
  refine Prod.ext ?_ ?_
  · show u.1 * 0 = 0; rw [mul_zero]
  · apply GlobalTheory.AdelicU.af_ext
    intro w
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (u.2 * singleFin v x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w 0
    rw [map_mul, map_zero]
    by_cases hw : w = v
    · subst hw
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w u.2 = 0 := hu
      rw [this, zero_mul]
    · rw [evalV_singleFin_ne hw, mul_zero]

theorem incM_smul {m k : Type} (c : F) (u : Matrix m k E) :
    incM F (c • u) = algebraMap F (AF F) c • incM F u := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, algebraMap_smul]
  show (1 : AF F) ⊗ₜ[F] (c • u i j) = c • ((1 : AF F) ⊗ₜ[F] u i j)
  rw [TensorProduct.tmul_smul]

theorem exists_zsmul_mem_lat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L] (x : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [Submodule.IsLattice.span_eq_top (A := E) (M := L)]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hy _
    · rw [mul_smul]; exact zsmul_mem hz _
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    have hal : IsAlgebraic ℤ a :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨k, hk, hi⟩ := hal.exists_integral_multiple
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have h := L.smul_mem (⟨k • a, hi⟩ : 𝓞 E) hy
    convert h using 1
    funext j
    change ((k * m) • (a * y j)) = (k • a) * (m • y j)
    simp only [zsmul_eq_mul, Int.cast_mul]
    ring

theorem incM_sum {m k ι : Type} (s : Finset ι) (f : ι → Matrix m k E) :
    incM F (∑ i ∈ s, f i) = ∑ i ∈ s, incM F (f i) := by
  ext a b
  simp [incM, Matrix.sum_apply, map_sum]

theorem eventually_smul_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) [Submodule.IsLattice E X.L]
    [Submodule.IsLattice E W.L] (u : Matrix (Fin n) (Fin d) E) :
    ∀ᶠ v in cofinite, ∀ a : AF F, At (evFin F v) a → evFin F v a ∈ v.adicCompletionIntegers F →
      a • incM F u ∈ latAtV X W v := by
  classical
  choose m hm hmL using fun j : Fin d => exists_zsmul_mem_lat X.L (fun i => u i j)
  choose m' hm' hmL' using fun j : Fin d => exists_zsmul_mem_lat W.L (Pi.single j (1 : E))
  have hu : u = ∑ j, (((m j * m' j : ℤ) : F)⁻¹) •
      Matrix.vecMulVec (m j • fun i => u i j) (m' j • (Pi.single j (1 : E) : Fin d → E)) := by
    ext i j'
    rw [Matrix.sum_apply, Finset.sum_eq_single j']
    · have h1 : ((m j' : ℤ) : E) ≠ 0 := Int.cast_ne_zero.2 (hm j')
      have h2 : ((m' j' : ℤ) : E) ≠ 0 := Int.cast_ne_zero.2 (hm' j')
      rw [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same]
      simp only [Algebra.smul_def, map_inv₀, map_intCast, zsmul_eq_mul, Int.cast_mul, map_mul, mul_one]
      field_simp
      simp [algebraMap_int_eq]
    · intro j _ hj
      simp [Matrix.vecMulVec_apply, Pi.single_apply, Ne.symm hj]
    · simp
  filter_upwards [eventually_all.2 fun j => GlobalTheory.VacIndic.eventually_int (((m j * m' j : ℤ) : F)⁻¹)] with v hv a ha hai
  rw [hu, incM_sum, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [incM_smul, smul_smul]
  exact AddSubgroup.subset_closure ⟨_, GlobalTheory.VacIndic.at_mul_right ha,
    by rw [map_mul, GlobalTheory.VacIndic.evFin_algebraMap]; exact mul_mem hai (hv j), _, hmL j, _, hmL' j, rfl⟩

theorem vacS_eventually_std : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ᶠ v in cofinite, vacS σ X W H H' v = Set.indicator {y | ∀ k, y k ∈ v.adicCompletionIntegers F} 1 := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' _hB hX hW hH hH'
  classical
  haveI := hX.lat
  haveI := hW.lat
  obtain ⟨G, hG⟩ := GlobalTheory.VacIndic.exists_gen X.L W.L hX.lat hW.lat
  choose M hM using exists_ratS_single σ B X W X₁ W₁ H H' hH hH'
  have e1 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k,
      algebraMap F (Fv F v) (ratS H H' g k) ∈ v.adicCompletionIntegers F :=
    (eventually_all_finset G).2 fun g _ => eventually_all.2 fun k => GlobalTheory.VacIndic.eventually_int _
  have e2 := eventually_all.2 fun k₀ => eventually_smul_mem_latAtV X W (M k₀)
  filter_upwards [e1, e2] with v h1 h2
  have hsub : ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, At (evFin F v) a ∧
      evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ g ∈ G, z = a • incM F g},
      ∀ k, evFin F v ((planeT σ X W H H' γ).1.1 k) ∈ v.adicCompletionIntegers F := by
    intro γ hγ
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
      intro k
      rw [map_smul]
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, planeT_incM_fst, map_mul,
        GlobalTheory.VacIndic.evFin_algebraMap]
      exact mul_mem hai (h1 g hg k)
    | zero => intro k; simp only [map_zero, Prod.fst_zero, Pi.zero_apply]; exact zero_mem _
    | add z z' _ _ h h' =>
      intro k; simp only [map_add, Prod.fst_add, Pi.add_apply]; exact add_mem (h k) (h' k)
    | neg z _ h => intro k; simp only [map_neg, Prod.fst_neg, Pi.neg_apply]; exact neg_mem (h k)
  have hset : latS σ X W H H' v = {y | ∀ k, y k ∈ v.adicCompletionIntegers F} := by
    ext y
    constructor
    · rintro ⟨γ, hγ, hy⟩ k
      rw [hy k]
      exact hsub γ (GlobalTheory.VacIndic.latAtV_le X W G hG v hγ) k
    · intro hy
      refine ⟨∑ k₀, adAt v (y k₀) • incM F (M k₀),
        sum_mem fun k₀ _ => h2 k₀ _ (at_adAt v _) (by rw [evFin_adAt]; exact hy k₀), fun k => ?_⟩
      simp only [map_sum, map_smul, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        planeT_incM_fst, hM, map_mul, evFin_adAt, GlobalTheory.VacIndic.evFin_algebraMap]
      rw [Finset.sum_eq_single k]
      · simp
      · intro k₀ _ hk; simp [Ne.symm hk]
      · simp
  unfold vacS
  rw [hset]

end GlobalTheory.ThK.PlaneCo.Std
