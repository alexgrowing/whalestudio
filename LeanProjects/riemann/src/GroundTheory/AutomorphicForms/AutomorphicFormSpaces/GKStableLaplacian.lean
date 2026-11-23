import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure
import GroundTheory.AutomorphicForms.GKModules.Casimir
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt

open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

theorem exists_monic_aeval_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (V : Submodule ℂ M) [FiniteDimensional ℂ V] (hV : ∀ w ∈ V, T w ∈ V)
    {v : M} (hv : v ∈ V) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval T P v = 0 := by
  by_cases hv0 : v = 0
  · refine ⟨Polynomial.X, Polynomial.monic_X, by simp, ?_⟩
    simp [hv0]
  have hmemk : ∀ k : ℕ, (T ^ k) v ∈ V := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hV _ ih
  set m := Module.finrank ℂ V
  let u : Fin (m + 1) → M := fun i => (T ^ (i : ℕ)) v
  have hspan : Submodule.span ℂ (range u) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemk i
  have hnot : ¬ LinearIndependent ℂ u := fun hli => by
    have h1 := finrank_span_eq_card hli
    have h2 := Submodule.finrank_mono hspan
    rw [h1, Fintype.card_fin] at h2
    omega
  obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℂ,
      Q = ∑ j : Fin (m + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) := ⟨_, rfl⟩
  have hQv : Polynomial.aeval T Q v = 0 := by
    have e1 : Polynomial.aeval T Q v = ∑ j : Fin (m + 1), c j • (T ^ (j : ℕ)) v := by
      rw [hQdef, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Module.End.mul_apply,
        Module.algebraMap_end_apply]
    rw [e1]
    exact hc
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply hi
    have := congrArg (fun P => P.coeff (i : ℕ)) h0
    simp only [hQdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      have : (i : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e).symm
      simp [this]
    · simp
  refine ⟨Q * Polynomial.C Q.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hQ0, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hQ0))]
    by_contra hdeg
    push Not at hdeg
    have hQc := Polynomial.eq_C_of_natDegree_le_zero hdeg
    have hc0 : Q.coeff 0 ≠ 0 := by
      intro hc0; apply hQ0; rw [hQc, hc0, map_zero]
    rw [hQc, Polynomial.aeval_C, Module.algebraMap_end_apply] at hQv
    exact hv0 ((smul_eq_zero.1 hQv).resolve_left hc0)
  · rw [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      hQv, smul_zero]

theorem map_aeval_apply_of_intertwine {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (f : M →ₗ[ℂ] N) {A : Module.End ℂ M} {B : Module.End ℂ N}
    (hAB : ∀ m, f (A m) = B (f m)) (P : Polynomial ℂ) (m : M) :
    f (Polynomial.aeval A P m) = Polynomial.aeval B P (f m) :=
  by apply _root_.UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open Reduction

theorem sliceL_uAction (g : AdelicGLn.AdelicGL K n) (u : UEnv K n) (φ : archSmooth K n) :
    sliceL g (uAction u φ) = (isExpLieAlgebra K n).rightUAction (F := ℂ) u (sliceL g φ) :=
  Subtype.ext (archSlice_uAction u φ g)

variable (K n) in

def laplacianU {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) :
    UEnv K n :=
  ∑ i, UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)

theorem rightUAction_laplacianU {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) :
    (isExpLieAlgebra K n).rightUAction (F := ℂ) (laplacianU K n b) =
      (isExpLieAlgebra K n).laplacian (F := ℂ) b := by
  simp only [laplacianU, IsExpLieAlgebra.laplacian, map_sum, map_mul,
    IsExpLieAlgebra.rightUAction_ι]

theorem laplacianU_eq_casimir_add {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : ι → ℝ) :
    laplacianU K n b = casimir b ε + ∑ i, (1 - ε i) •
      (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i)) := by
  simp only [laplacianU, casimir, ← Finset.sum_add_distrib, ← add_smul, add_sub_cancel, one_smul]

variable (φ : archSmooth K n)

def archKSpan : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ (range fun k : archCompact K n => rtInf (k : archGroup K n) φ)

theorem rtInf_one (ψ : archSmooth K n) : rtInf (1 : archGroup K n) ψ = ψ := by
  ext g
  simp [GroundTheory.Automorphic.rightTranslate]

theorem self_mem_archKSpan : φ ∈ archKSpan φ := by
  have h := Submodule.subset_span (R := ℂ)
    (s := range fun k : archCompact K n => rtInf (k : archGroup K n) φ) ⟨1, rfl⟩
  simp only [OneMemClass.coe_one, rtInf_one] at h
  exact h

theorem rtInf_rtInf (a b : archGroup K n) (ψ : archSmooth K n) :
    rtInf a (rtInf b ψ) = rtInf (a * b) ψ := by
  ext g
  simp [GroundTheory.Automorphic.rightTranslate, mul_assoc]

theorem rtInf_mem_archKSpan (k : archCompact K n) {ψ : archSmooth K n} (hψ : ψ ∈ archKSpan φ) :
    rtInf (k : archGroup K n) ψ ∈ archKSpan φ := by
  refine Submodule.span_induction (p := fun ψ _ => rtInf (k : archGroup K n) ψ ∈ archKSpan φ)
    ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k', rfl⟩
    dsimp only
    rw [rtInf_rtInf]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem finiteDimensional_archKSpan (hK : IsKFinite (φ : AdelicGLn.AdelicGL K n → ℂ)) :
    FiniteDimensional ℂ (archKSpan φ) := by
  set Wf := Submodule.span ℂ (range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
    rightTranslate (k : AdelicGLn.AdelicGL K n) (φ : AdelicGLn.AdelicGL K n → ℂ))
  have : FiniteDimensional ℂ Wf := hK
  have hW : ∀ w : archKSpan φ, ((w : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf := by
    rintro ⟨w, hw⟩
    refine Submodule.span_induction
      (p := fun w _ => ((w : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨⟨infEmb K n k, k.2⟩, rfl⟩
    · exact Wf.zero_mem
    · intro x y _ _ hx hy
      exact Wf.add_mem hx hy
    · intro c x _ hx
      exact Wf.smul_mem c hx
  refine FiniteDimensional.of_injective
    (((archSmooth K n).subtype ∘ₗ (archKSpan φ).subtype).codRestrict Wf hW) ?_
  intro x y hxy
  have := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext this)

theorem isZFinite_of_mem_archKSpan (hZ : IsZFinite φ) {ψ : archSmooth K n}
    (hψ : ψ ∈ archKSpan φ) : IsZFinite ψ := by
  refine Submodule.span_induction (p := fun ψ _ => IsZFinite ψ) ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩
    exact hZ.map_rtInf _
  · exact isZFinite_zero
  · intro x y _ _ hx hy; exact hx.add hy
  · intro c x _ hx; exact hx.smul c

theorem uAction_ι_mem_archKSpan (hK : IsKFinite (φ : AdelicGLn.AdelicGL K n → ℂ))
    (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n)
    {ψ : archSmooth K n} (hψ : ψ ∈ archKSpan φ) :
    uAction (UniversalEnvelopingAlgebra.ι ℝ X) ψ ∈ archKSpan φ := by
  have : FiniteDimensional ℂ (archKSpan φ) := finiteDimensional_archKSpan φ hK
  set Wf := (archKSpan φ).map (archSmooth K n).subtype
  have hc : ∀ t : ℝ, ((rtInf ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) ψ :
      archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) ∈ Wf := fun t =>
    ⟨_, rtInf_mem_archKSpan φ ⟨_, hX t⟩ hψ, rfl⟩
  have hd : ∀ x : AdelicGLn.AdelicGL K n, HasDerivAt
      (fun t : ℝ => ((rtInf ((isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) ψ :
        archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) x)
      (((uAction (UniversalEnvelopingAlgebra.ι ℝ X) ψ : archSmooth K n) :
        AdelicGLn.AdelicGL K n → ℂ) x) 0 := by
    intro x
    have h := (isExpLieAlgebra K n).hasDerivAt_rightDeriv ((mem_archSmooth.1 ψ.2) x)
      ((isExpLieAlgebra K n).ofLie X) 1
    simp only [one_mul, archSlice_apply] at h
    rw [uAction_ι_apply]
    exact h
  have : FiniteDimensional ℂ Wf := inferInstance
  obtain ⟨w, hw, e⟩ := mem_of_hasDerivAt Wf hc hd
  rwa [show w = uAction (UniversalEnvelopingAlgebra.ι ℝ X) ψ from Subtype.ext e] at hw

def zkArchSpan : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {v | ∃ z ∈ (isExpLieAlgebra K n).centerU, ∃ ψ ∈ archKSpan φ, v = uAction z ψ}

theorem uAction_mem_zkArchSpan {z : UEnv K n} (hz : z ∈ (isExpLieAlgebra K n).centerU)
    {ψ : archSmooth K n} (hψ : ψ ∈ archKSpan φ) : uAction z ψ ∈ zkArchSpan φ :=
  Submodule.subset_span ⟨z, hz, ψ, hψ, rfl⟩

theorem self_mem_zkArchSpan : φ ∈ zkArchSpan φ := by
  have := uAction_mem_zkArchSpan φ (z := 1) (Subalgebra.one_mem _) (self_mem_archKSpan φ)
  rwa [map_one, Module.End.one_apply] at this

theorem finiteDimensional_zkArchSpan (hK : IsKFinite (φ : AdelicGLn.AdelicGL K n → ℂ))
    (hZ : IsZFinite φ) : FiniteDimensional ℂ (zkArchSpan φ) := by
  have : FiniteDimensional ℂ (archKSpan φ) := finiteDimensional_archKSpan φ hK
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional (archKSpan φ)).2 this
  set S : s → Submodule ℂ (archSmooth K n) := fun x =>
    Submodule.span ℂ ((fun z => uAction z (x : archSmooth K n)) ''
      ((isExpLieAlgebra K n).centerU : Set (UEnv K n)))
  have : ∀ x, FiniteDimensional ℂ (S x) := fun x =>
    isZFinite_of_mem_archKSpan φ hZ (hs ▸ Submodule.subset_span x.2)
  suffices hle : zkArchSpan φ ≤ ⨆ x, S x from Submodule.finiteDimensional_of_le hle
  refine Submodule.span_le.2 ?_
  rintro _ ⟨z, hz, ψ, hψ, rfl⟩
  rw [← hs] at hψ
  change uAction z ψ ∈ ⨆ x, S x
  refine Submodule.span_induction (p := fun ψ _ => uAction z ψ ∈ ⨆ x, S x) ?_ ?_ ?_ ?_ hψ
  · intro x hx
    exact Submodule.mem_iSup_of_mem ⟨x, hx⟩ (Submodule.subset_span ⟨z, hz, rfl⟩)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem exists_aeval_laplacian_sliceL_eq_zero_of_isSmoothKZ {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsSmoothKZ φ) {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : (isExpLieAlgebra K n).lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ ∀ g,
      Polynomial.aeval ((isExpLieAlgebra K n).laplacian (F := ℂ) b) P
        (sliceL g ⟨φ, hφ.isSmooth.1⟩) = 0 := by
  set φ' : archSmooth K n := ⟨φ, hφ.isSmooth.1⟩
  have hKf : IsKFinite ((φ' : archSmooth K n) : AdelicGLn.AdelicGL K n → ℂ) := hφ.isKFinite
  have hZ : IsZFinite φ' := hφ.isZFinite
  have := finiteDimensional_zkArchSpan φ' hKf hZ
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU :=
    casimir_mem_center hε2 horth hsymm hinv

  have hsum : ∀ ψ ∈ archKSpan φ', (∑ i, (1 - ε i) •
      uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) ψ)) ∈ archKSpan φ' := by
    intro ψ hψ
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with e | e
    · rw [e, sub_self, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_of_tower_mem _ _
        (uAction_ι_mem_archKSpan φ' hKf _ (hK i e) (uAction_ι_mem_archKSpan φ' hKf _ (hK i e) hψ))

  have hgen : ∀ z ∈ (isExpLieAlgebra K n).centerU, ∀ ψ ∈ archKSpan φ',
      uAction (laplacianU K n b) (uAction z ψ) ∈ zkArchSpan φ' := by
    intro z hz ψ hψ
    have hc : laplacianU K n b * z = z * laplacianU K n b :=
      Subalgebra.mem_center_iff.1 hz (laplacianU K n b)
    have e : uAction (laplacianU K n b) (uAction z ψ) = uAction (z * casimir b ε) ψ +
        uAction z (∑ i, (1 - ε i) • uAction (UniversalEnvelopingAlgebra.ι ℝ (b i))
          (uAction (UniversalEnvelopingAlgebra.ι ℝ (b i)) ψ)) := by
      rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply,
        laplacianU_eq_casimir_add b ε, map_add, LinearMap.add_apply, map_add, map_mul,
        Module.End.mul_apply, map_sum, LinearMap.sum_apply]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_mul, LinearMap.smul_apply, Module.End.mul_apply]
    rw [e]
    exact Submodule.add_mem _ (uAction_mem_zkArchSpan φ' (Subalgebra.mul_mem _ hz hΩ) hψ)
      (uAction_mem_zkArchSpan φ' hz (hsum ψ hψ))
  have hV : ∀ w ∈ zkArchSpan φ', uAction (laplacianU K n b) w ∈ zkArchSpan φ' := by
    intro w hw
    refine Submodule.span_induction
      (p := fun w _ => uAction (laplacianU K n b) w ∈ zkArchSpan φ') ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, ψ, hψ, rfl⟩
      exact hgen z hz ψ hψ
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  obtain ⟨P, hPm, hPd, hP⟩ := exists_monic_aeval_apply_eq_zero (uAction (laplacianU K n b))
    (zkArchSpan φ') hV (self_mem_zkArchSpan φ')
  refine ⟨P, hPm, hPd, fun g => ?_⟩
  have := map_aeval_apply_of_intertwine (sliceL g) (A := uAction (laplacianU K n b))
    (B := (isExpLieAlgebra K n).laplacian (F := ℂ) b)
    (fun m => by rw [sliceL_uAction, rightUAction_laplacianU]) P φ'
  rw [hP, map_zero] at this
  exact this.symm

theorem IsSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : IsSmoothKZ φ) {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (ε : Fin d → ℝ) (B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : (isExpLieAlgebra K n).lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ ∀ g,
      Polynomial.aeval ((isExpLieAlgebra K n).laplacian (F := ℂ) b) P
        (sliceL g ⟨φ, hφ.isSmooth.1⟩) = 0 :=
  exists_aeval_laplacian_sliceL_eq_zero_of_isSmoothKZ hφ b ε B hε horth hsymm hinv hK

end AutomorphicForm

end

end GroundTheory.Automorphic
