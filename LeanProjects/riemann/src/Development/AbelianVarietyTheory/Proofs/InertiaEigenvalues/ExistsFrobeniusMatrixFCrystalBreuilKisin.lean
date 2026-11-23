import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.FrobMat

theorem isFrac_add {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) (c : ℕ) :
    IsFrac d y (d ^ c • m) (k + c) := by
  unfold IsFrac at *
  rw [h, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_smul, pow_add, mul_comm]

theorem isFrac_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k a : ℕ} (h : IsFrac d y m k) (hka : k ≤ a) :
    IsFrac d y (d ^ (a - k) • m) a := by
  have := isFrac_add h (a - k)
  rwa [Nat.add_sub_cancel' hka] at this

theorem isFrac_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A}
    {y : LocalizedModule (Submonoid.powers d) M} {m : M} {k : ℕ} (h : IsFrac d y m k) :
    d ^ k • y = LocalizedModule.mk m 1 := by
  unfold IsFrac at h
  rw [h, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, OneMemClass.coe_one]

theorem exists_common_den {R : Type} [CommRing R] (x : R) {ι : Type} [Finite ι]
    (f : ι → Localization.Away x) : ∃ (n : ℕ) (g : ι → R), ∀ i, algebraMap R _ (g i) = x ^ n • f i := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers x) f
  choose g hg using hn
  exact ⟨n, g, hg⟩

theorem span_eq_top_of_semiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {ι : Type} [Fintype ι]
    (e : Module.Basis ι A M) : Submodule.span B (Set.range fun i => u (e i)) = ⊤ := by
  let S := Submodule.span B (Set.range fun i => u (e i))
  have hu : ∀ x, u x ∈ S := by
    intro x
    rw [← e.sum_repr x, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [u.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨w, -, huniq⟩ := h (N ⧸ S) 0
  have h1 : S.mkQ = w := huniq _ fun x => by
    simp only [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]; exact hu x
  have h2 : (0 : N →ₗ[B] N ⧸ S) = w := huniq _ fun x => by simp
  rw [eq_top_iff]
  intro y _
  have := LinearMap.congr_fun (h1.trans h2.symm) y
  simpa using this

end GlobalTheory.BSP.FrobMat

namespace GlobalTheory.BSP.FrobMat

theorem frob_matrix_general {R Mo : Type} [CommRing R] [IsDomain R] [AddCommGroup Mo] [Module R Mo]
    (φ : R →+* R) (x : R) (hx : x ≠ 0)
    (u : Mo →ₛₗ[(algebraMap R (Localization.Away x)).comp φ] LocalizedModule (Submonoid.powers x) Mo)
    (hu : SemiBC u) {d : ℕ} (e : Module.Basis (Fin d) R Mo) :
    ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) R), A * A' = x ^ b • (1 : Matrix (Fin d) (Fin d) R) ∧
      ∀ j, IsFrac x (u (e j)) (∑ i, A i j • e i) a := by
  haveI : Module.Free R Mo := Module.Free.of_basis e
  have h1 : ∀ j, ∃ m k, IsFrac x (u (e j)) m k := fun j => exists_isFrac _ _
  choose m k hmk using h1
  let a := ∑ j, k j
  have hk : ∀ j, k j ≤ a := fun j => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let m' : Fin d → Mo := fun j => x ^ (a - k j) • m j
  have hm' : ∀ j, IsFrac x (u (e j)) (m' j) a := fun j => isFrac_le (hmk j) (hk j)
  let A : Matrix (Fin d) (Fin d) R := fun i j => e.repr (m' j) i
  have hA : ∀ j, ∑ i, A i j • e i = m' j := fun j => e.sum_repr (m' j)
  have hsp := span_eq_top_of_semiBC hu e
  have h2 : ∀ k' : Fin d, ∃ c : Fin d → Localization.Away x,
      ∑ j, c j • u (e j) = LocalizedModule.mk (e k') 1 := fun k' =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (Submodule.eq_top_iff'.1 hsp _)
  choose c hc using h2
  obtain ⟨n, A', hA'⟩ := exists_common_den x (fun p : Fin d × Fin d => c p.2 p.1)
  let A'' : Matrix (Fin d) (Fin d) R := fun j k' => A' (j, k')
  refine ⟨a, a + n, A, A'', ?_, fun j => (hA j).symm ▸ hm' j⟩
  have key : ∀ k', LocalizedModule.mk (x ^ (a + n) • e k') (1 : Submonoid.powers x) =
      LocalizedModule.mk (∑ j, A' (j, k') • m' j) 1 := by
    intro k'
    have hr : LocalizedModule.mk (∑ j, A' (j, k') • m' j) (1 : Submonoid.powers x) =
        ∑ j, A' (j, k') • LocalizedModule.mk (m' j) (1 : Submonoid.powers x) := by
      rw [← LocalizedModule.mkLinearMap_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, LocalizedModule.mkLinearMap_apply]
    rw [hr, ← LocalizedModule.smul'_mk, ← hc k', pow_add, mul_smul, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_assoc (x ^ n) (c k' j), ← hA' (j, k'), algebraMap_smul, smul_comm,
      isFrac_smul (hm' j)]
  have key2 : ∀ k', x ^ (a + n) • e k' = ∑ j, A' (j, k') • m' j := by
    intro k'
    obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 (key k')
    simp only [Submonoid.smul_def, one_smul] at hr
    exact smul_right_injective _ (pow_ne_zero r hx) hr
  ext i k'
  have h3 := congrArg (fun y => e.repr y i) (key2 k')
  simp only [map_smul, e.repr_self, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, smul_eq_mul] at h3
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [eq_comm] at h3
  simp only [eq_comm (a := k') (b := i)] at h3
  rw [← h3]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.BSP.FrobMat

theorem GlobalTheory.BSP.frob_matrix_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), ∃ (a b : ℕ) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) bk.S) ∧ ∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a := by
  intro l _ K bk d M e
  haveI : IsDomain bk.prism.A := inferInstanceAs (IsDomain bk.S)
  exact GlobalTheory.BSP.FrobMat.frob_matrix_general (R := bk.prism.A) bk.prism.D.φ (bk.toP bk.E) bk.E_ne_zero
    (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩)
    (M.Φ_bc bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩) e
