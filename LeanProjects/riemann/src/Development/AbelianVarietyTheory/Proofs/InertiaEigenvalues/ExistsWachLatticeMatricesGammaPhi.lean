import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

noncomputable section

namespace GlobalTheory.HWL.Mat

section Abstract

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : Submodule A M} {r : ℕ}

theorem coeff_ext (nb : Module.Basis (Fin r) A ↥N) {a b : Fin r → A}
    (h : ∑ i, a i • (nb i : M) = ∑ i, b i • (nb i : M)) (i : Fin r) : a i = b i := by
  have hli : LinearIndependent A (fun i => (nb i : M)) :=
    nb.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  exact Fintype.linearIndependent_iffₛ.1 hli a b h i

theorem eq_sum (nb : Module.Basis (Fin r) A ↥N) {x : M} (hx : x ∈ N) :
    x = ∑ i, nb.repr ⟨x, hx⟩ i • (nb i : M) := by
  have h := congrArg N.subtype (nb.sum_repr ⟨x, hx⟩)
  rw [map_sum] at h
  simpa using h.symm

theorem semi_sum {f : M →+ M} {σ : A → A} (hf : ∀ a x, f (a • x) = σ a • f x) (a : Fin r → A)
    (x : Fin r → M) : f (∑ i, a i • x i) = ∑ i, σ (a i) • f (x i) := by
  rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hf _ _

theorem sum_sum (P C : Matrix (Fin r) (Fin r) A) (e : Fin r → M) (j : Fin r) :
    ∑ k, C k j • ∑ i, P i k • e i = ∑ i, (P * C) i j • e i := by
  simp only [Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem common_exp (S : Submodule A M) (Q : A) (x : Fin r → M) (h : ∀ j, ∃ k : ℕ, Q ^ k • x j ∈ S) :
    ∃ m : ℕ, ∀ j, Q ^ m • x j ∈ S := by
  choose k hk using h
  refine ⟨∑ j, k j, fun j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [hc, add_comm, pow_add, mul_smul]
  exact S.smul_mem _ (hk j)

theorem exists_matrices {Γ : Type} [Mul Γ] (nb : Module.Basis (Fin r) A ↥N) (Q π : A)
    (φ : M →+ M) (σ : A → A) (hφ : ∀ a x, φ (a • x) = σ a • φ x)
    (γ : Γ → M →+ M) (τ : Γ → A →+* A) (hγ : ∀ g a x, γ g (a • x) = τ g a • γ g x)
    (hmul : ∀ g h x, γ (g * h) x = γ g (γ h x)) (hcomm : ∀ g x, φ (γ g x) = γ g (φ x))
    (hNφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hNinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set M)))
    (hNΓ : ∀ g, ∀ x ∈ N, γ g x ∈ N) (hNπ : ∀ g, ∀ x ∈ N, ∃ y ∈ N, γ g x - x = π • y) :
    ∃ (m m' : ℕ) (Gm : Γ → Matrix (Fin r) (Fin r) A) (Pm Pm' : Matrix (Fin r) (Fin r) A),
      (∀ g h, Gm (g * h) = Gm g * (Gm h).map (τ g)) ∧
      (∀ g i j, ∃ c, Gm g i j = (if i = j then 1 else 0) + π * c) ∧
      Pm * Pm' = (Q ^ m') • (1 : Matrix (Fin r) (Fin r) A) ∧
      (∀ g, (τ g Q ^ m) • (Pm * (Gm g).map σ) = (Q ^ m) • (Gm g * Pm.map (τ g))) ∧
      (∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M)) ∧
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) := by
  classical
  obtain ⟨m, hm⟩ := common_exp N Q (fun j => φ (nb j : M)) fun j => hNφ _ (nb j).2
  obtain ⟨k, hk⟩ := common_exp _ Q (fun j => (nb j : M)) fun j => hNinv _ (nb j).2
  have hspan : Submodule.span A (φ '' (N : Set M)) ≤
      Submodule.span A (Set.range fun i => φ (nb i : M)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [eq_sum nb hx, semi_sum hφ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun A).1 (hspan (hk j))
  obtain ⟨Gm, hG⟩ : ∃ Gm : Γ → Matrix (Fin r) (Fin r) A,
      ∀ g j, γ g (nb j : M) = ∑ i, Gm g i j • (nb i : M) :=
    ⟨fun g i j => nb.repr ⟨_, hNΓ g _ (nb j).2⟩ i, fun g j => eq_sum nb _⟩
  obtain ⟨Pm, hP⟩ : ∃ Pm : Matrix (Fin r) (Fin r) A,
      ∀ j, Q ^ m • φ (nb j : M) = ∑ i, Pm i j • (nb i : M) :=
    ⟨fun i j => nb.repr ⟨_, hm j⟩ i, fun j => eq_sum nb _⟩
  have hone : ∀ (a : A) (j : Fin r),
      ∑ i, (a * if i = j then 1 else 0) • (nb i : M) = a • (nb j : M) := by
    intro a j
    rw [Finset.sum_eq_single j] <;> simp +contextual
  refine ⟨m, m + k, Gm, Pm, Matrix.of fun i j => c j i, ?_, ?_, ?_, ?_, hG, hP⟩
  · intro g h
    ext i j
    refine coeff_ext nb (a := fun i => Gm (g * h) i j)
      (b := fun i => (Gm g * (Gm h).map (τ g)) i j) ?_ i
    rw [← hG, hmul, hG h, semi_sum (hγ g), ← sum_sum]
    simp only [hG, Matrix.map_apply]
  · intro g i j
    obtain ⟨y, hy, e⟩ := hNπ g _ (nb j).2
    refine ⟨nb.repr ⟨y, hy⟩ i, ?_⟩
    refine coeff_ext nb (a := fun i => Gm g i j)
      (b := fun i => (if i = j then 1 else 0) + π * nb.repr ⟨y, hy⟩ i) ?_ i
    have h1 := hone 1 j
    simp only [one_mul, one_smul] at h1
    simp only [add_smul, Finset.sum_add_distrib, mul_smul]
    rw [← hG, h1, ← Finset.smul_sum, ← eq_sum nb hy, ← e]
    abel
  · ext i j
    refine coeff_ext nb (a := fun i => (Pm * Matrix.of fun i j => c j i) i j)
      (b := fun i => ((Q ^ (m + k)) • (1 : Matrix (Fin r) (Fin r) A)) i j) ?_ i
    rw [← sum_sum]
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, hone, ← hP, Matrix.of_apply]
    rw [pow_add, mul_smul, ← hc j, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _
  · intro g
    ext i j
    refine coeff_ext nb (a := fun i => ((τ g Q ^ m) • (Pm * (Gm g).map σ)) i j)
      (b := fun i => ((Q ^ m) • (Gm g * Pm.map (τ g))) i j) ?_ i
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← sum_sum, ← sum_sum]
    have h1 : ∑ k, (Gm g).map σ k j • ∑ i, Pm i k • (nb i : M) = Q ^ m • γ g (φ (nb j : M)) := by
      rw [← hcomm, hG, semi_sum hφ, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← hP, smul_comm, Matrix.map_apply]
    have h2 : ∑ k, Pm.map (τ g) k j • ∑ i, Gm g i k • (nb i : M) =
        τ g Q ^ m • γ g (φ (nb j : M)) := by
      rw [← map_pow, ← hγ, hP, semi_sum (hγ g)]
      exact Finset.sum_congr rfl fun l _ => by rw [← hG, Matrix.map_apply]
    rw [h1, h2, smul_comm]

end Abstract

theorem wach_matrices : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ} {Γ : WGam PD LL O v n s} {R : WSer Γ} {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai] {RW : Type} [CommRing RW] [Algebra O RW] {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai} {I : WIo R (O ⊗[Zl] Ai) RW inclR φR gR πA} {E : WEt I} {zl : PowerSeries Zl →+* LetA O n} (Mo : WN E zl) (T : LocLat G Qp LL O) (r : ℕ) (nb : Module.Basis (Fin r) (LetA O n) ↥(Mo.N T)), ∃ (m m' : ℕ) (Gm : Γ.Gam → Matrix (Fin r) (Fin r) (LetA O n)) (Pm Pm' : Matrix (Fin r) (Fin r) (LetA O n)), (∀ g h, Gm (g * h) = Gm g * (Gm h).map (letγ (R.γ₀ g))) ∧ (∀ g i j k, PowerSeries.constantCoeff (Gm g i j k) = if i = j then 1 else 0) ∧ Pm * Pm' = (R.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (LetA O n)) ∧ (∀ g, (letγ (R.γ₀ g) R.Q ^ m) • (Pm * (Gm g).map (letφ R.φ₀)) = (R.Q ^ m) • (Gm g * Pm.map (letγ (R.γ₀ g)))) ∧ (∀ g j, E.γD T g (nb j : E.DD T) = ∑ i, Gm g i j • (nb i : E.DD T)) ∧ ∀ j, R.Q ^ m • E.φD T (nb j : E.DD T) = ∑ i, Pm i j • (nb i : E.DD T) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n s Γ R Zl Ai _ _ _ _
    RW _ _ inclR φR gR πA I E zl Mo T r nb
  have hφ : ∀ (a : LetA O n) (x : E.DD T), E.φD T (a • x) = letφ R.φ₀ a • E.φD T x := by
    intro a x
    rw [← algebraMap_smul R.EE a x, E.φD_smul, R.φE_ext, algebraMap_smul]
  have hγ : ∀ g (a : LetA O n) (x : E.DD T),
      E.γD T g (a • x) = letγ (R.γ₀ g) a • E.γD T g x := by
    intro g a x
    rw [← algebraMap_smul R.EE a x, E.γD_smul, R.γE_ext, algebraMap_smul]
  obtain ⟨m, m', Gm, Pm, Pm', h1, h2, h3, h4, h5, h6⟩ :=
    exists_matrices nb R.Q letπ (E.φD T).toAddMonoidHom (letφ R.φ₀) hφ
      (fun g => (E.γD T g).toAddMonoidHom) (fun g => (letγ (n := n) (R.γ₀ g)).toRingHom) hγ
      (E.γD_mul T) (E.φγ_comm T) (Mo.N_φ T) (Mo.N_φinv T) (Mo.N_Γ T) (Mo.N_π T)
  refine ⟨m, m', Gm, Pm, Pm', h1, ?_, h3, h4, h5, h6⟩
  intro g i j k
  obtain ⟨c, hc⟩ := h2 g i j
  rw [hc]
  split_ifs <;> simp [letπ]

end GlobalTheory.HWL.Mat
