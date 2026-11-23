import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
namespace FunctorialResolution.EmbeddedResolution

namespace EtaleCoordinates

variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]

theorem coord_smul_partialDeriv_mem_tangentDerivations (h : ι) :
    coord k ι S h • partialDeriv k ι S h ∈
      tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) :=
  smul_mem_tangentDerivations k (Ideal.span ({coord k ι S h} : Set S))
    (Ideal.mem_span_singleton_self (coord k ι S h)) (partialDeriv k ι S h)

theorem partialDeriv_mem_tangentDerivations_of_ne {i h : ι} (hih : i ≠ h) :
    partialDeriv k ι S i ∈ tangentDerivations k (Ideal.span ({coord k ι S h} : Set S)) := by
  rw [mem_tangentDerivations_span_singleton, partialDeriv_coord_of_ne k ι S i h hih]
  exact Submodule.zero_mem _

theorem coord_mul_partialDeriv_mem_logDerivIdeal (h : ι) (J : Ideal S) {g : S} (hg : g ∈ J) :
    coord k ι S h * partialDeriv k ι S h g ∈
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J := by
  have hmem := derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (coord k ι S h • partialDeriv k ι S h)
    (coord_smul_partialDeriv_mem_tangentDerivations k ι S h) hg
  simpa [smul_eq_mul] using hmem

theorem partialDeriv_mem_logDerivIdeal_of_ne {i h : ι} (hih : i ≠ h) (J : Ideal S) {g : S}
    (hg : g ∈ J) :
    partialDeriv k ι S i g ∈ logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J :=
  derivation_apply_mem_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) J
    (partialDeriv k ι S i) (partialDeriv_mem_tangentDerivations_of_ne k ι S hih) hg

def partialDerivIdeal (h : ι) (J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x}

private theorem partialDerivIdeal_def (h : ι) (J : Ideal S) :
    partialDerivIdeal k ι S h J =
      J ⊔ Ideal.span {x : S | ∃ g ∈ J, partialDeriv k ι S h g = x} := rfl

theorem le_partialDerivIdeal (h : ι) (J : Ideal S) : J ≤ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact le_sup_left

theorem partialDeriv_mem_partialDerivIdeal (h : ι) (J : Ideal S) {g : S} (hg : g ∈ J) :
    partialDeriv k ι S h g ∈ partialDerivIdeal k ι S h J := by
  rw [partialDerivIdeal_def]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩)

theorem partialDerivIdeal_le_iff (h : ι) (J K : Ideal S) :
    partialDerivIdeal k ι S h J ≤ K ↔ J ≤ K ∧ ∀ g ∈ J, partialDeriv k ι S h g ∈ K := by
  rw [partialDerivIdeal_def, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g hg => h2 ⟨g, hg, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    exact h2 g hg

theorem partialDerivIdeal_le (h : ι) {J K : Ideal S} (hJK : J ≤ K)
    (hD : ∀ g ∈ J, partialDeriv k ι S h g ∈ K) : partialDerivIdeal k ι S h J ≤ K :=
  (partialDerivIdeal_le_iff k ι S h J K).mpr ⟨hJK, hD⟩

theorem partialDerivIdeal_mono (h : ι) : Monotone (partialDerivIdeal k ι S h) := by
  intro I J hIJ
  rw [partialDerivIdeal_le_iff]
  refine ⟨hIJ.trans (le_partialDerivIdeal k ι S h J), fun g hg => ?_⟩
  exact partialDeriv_mem_partialDerivIdeal k ι S h J (hIJ hg)

def partialDerivIdealIterate (h : ι) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | l + 1, J => partialDerivIdeal k ι S h (partialDerivIdealIterate h l J)

theorem partialDerivIdealIterate_zero (h : ι) (J : Ideal S) :
    partialDerivIdealIterate k ι S h 0 J = J := rfl

theorem partialDerivIdealIterate_succ (h : ι) (l : ℕ) (J : Ideal S) :
    partialDerivIdealIterate k ι S h (l + 1) J =
      partialDerivIdeal k ι S h (partialDerivIdealIterate k ι S h l J) := rfl

theorem partialDerivIdealIterate_one (h : ι) (J : Ideal S) :
    partialDerivIdealIterate k ι S h 1 J = partialDerivIdeal k ι S h J := rfl

private def evalDerivationAddHom (g : S) : Derivation k S S →+ S where
  toFun D := D g
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S] in
private theorem derivation_sum_apply (s : Finset ι) (f : ι → Derivation k S S) (g : S) :
    (∑ i ∈ s, f i) g = ∑ i ∈ s, f i g :=
  map_sum (evalDerivationAddHom k S g) f s

theorem derivation_apply_eq_sum_partialDeriv [Fintype ι] (D : Derivation k S S) (g : S) :
    D g = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g := by
  have h1 : D g = (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g :=
    congrArg (fun E : Derivation k S S => E g) (eq_sum_smul_partialDeriv k ι S D)
  have h2 : (∑ i, D (coord k ι S i) • partialDeriv k ι S i : Derivation k S S) g
      = ∑ i, D (coord k ι S i) * partialDeriv k ι S i g :=
    derivation_sum_apply k ι S Finset.univ (fun i => D (coord k ι S i) • partialDeriv k ι S i) g
  exact h1.trans h2

private theorem derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal [Fintype ι] (h : ι) (I : Ideal S) :
    derivIdeal k I ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ⊔ partialDerivIdeal k ι S h I := by
  rw [derivIdeal_le_iff]
  refine ⟨(le_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I).trans le_sup_left, ?_⟩
  intro D g hg
  rw [derivation_apply_eq_sum_partialDeriv k ι S D g]
  refine Ideal.sum_mem _ ?_
  intro i _
  by_cases hi : i = h
  · rw [hi]
    exact Submodule.mem_sup_right
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg))
  · exact Submodule.mem_sup_left
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hg))

private def idealInfComapPartialDeriv (h : ι) (K : Ideal S) : Ideal S where
  carrier := {g : S | g ∈ K ∧ partialDeriv k ι S h g ∈ K}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨Submodule.add_mem K ha1 hb1, ?_⟩
    rw [map_add]
    exact Submodule.add_mem K ha2 hb2
  zero_mem' := by
    refine ⟨Submodule.zero_mem K, ?_⟩
    rw [map_zero]
    exact Submodule.zero_mem K
  smul_mem' := by
    intro c x hx
    obtain ⟨hx1, hx2⟩ := hx
    refine ⟨Ideal.mul_mem_left K c hx1, ?_⟩
    have hl : partialDeriv k ι S h (c * x)
        = c * partialDeriv k ι S h x + x * partialDeriv k ι S h c := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    show partialDeriv k ι S h (c * x) ∈ K
    rw [hl]
    exact Submodule.add_mem K (Ideal.mul_mem_left K c hx2) (Ideal.mul_mem_right _ K hx1)

private theorem mem_idealInfComapPartialDeriv_iff (h : ι) (K : Ideal S) (g : S) :
    g ∈ idealInfComapPartialDeriv k ι S h K ↔ g ∈ K ∧ partialDeriv k ι S h g ∈ K := Iff.rfl

private theorem partialDerivIdeal_logDerivIdeal_le [Fintype ι] [DecidableEq ι] (h : ι) (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I) ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) (partialDerivIdeal k ι S h I) := by
  have key : logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ≤
      idealInfComapPartialDeriv k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S))
          (partialDerivIdeal k ι S h I)) := by
    rw [logDerivIdeal_le_iff]
    constructor
    · intro g hg
      rw [mem_idealInfComapPartialDeriv_iff]
      refine ⟨?_, ?_⟩
      · exact le_logDerivIdeal k _ _ (le_partialDerivIdeal k ι S h I hg)
      · exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg)
    · intro D hD y hy
      rw [mem_idealInfComapPartialDeriv_iff]
      have hDmem : D (coord k ι S h) ∈ Ideal.span ({coord k ι S h} : Set S) :=
        (mem_tangentDerivations_span_singleton k (coord k ι S h) D).mp hD
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hDmem
      refine ⟨?_, ?_⟩
      · exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
          (derivation_apply_mem_logDerivIdeal k _ I D hD hy)
      · rw [derivation_apply_eq_sum_partialDeriv k ι S D y]
        rw [map_sum]
        refine Ideal.sum_mem _ ?_
        intro i _
        rw [Derivation.leibniz]
        refine Submodule.add_mem _ ?_ ?_
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul, ← hc, mul_assoc]
            refine Ideal.mul_mem_left _ _ ?_
            exact coord_mul_partialDeriv_mem_logDerivIdeal k ι S h
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul, partialDeriv_comm k ι S h i y]
            refine Ideal.mul_mem_left _ _ ?_
            exact partialDeriv_mem_logDerivIdeal_of_ne k ι S hi
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
              (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hy)
  refine partialDerivIdeal_le k ι S h ?_ ?_
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).1
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).2

private theorem partialDerivIdeal_logDerivIdealIterate_le [Fintype ι] [DecidableEq ι] (h : ι) (m : ℕ)
    (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m I) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m
        (partialDerivIdeal k ι S h I) := by
  induction m with
  | zero => exact le_of_eq (by simp only [logDerivIdealIterate_zero])
  | succ m ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact (partialDerivIdeal_logDerivIdeal_le k ι S h _).trans (logDerivIdeal_mono k _ ih)

theorem derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate [Fintype ι] [DecidableEq ι]
    (h : ι) (n : ℕ) (J : Ideal S) :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by
  induction n with
  | zero =>
      rw [derivIdealIterate_zero]
      exact le_iSup₂ (f := fun m (_ : m ≤ 0) =>
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (0 - m)
          (partialDerivIdealIterate k ι S h m J)) 0 le_rfl
  | succ n ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun l => ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun hl => ?_
      refine le_trans (derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal k ι S h _) ?_
      refine sup_le ?_ ?_
      · rw [← logDerivIdealIterate_succ, show n - l + 1 = n + 1 - l from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) l (by omega)
      · refine le_trans (partialDerivIdeal_logDerivIdealIterate_le k ι S h (n - l) _) ?_
        rw [← partialDerivIdealIterate_succ, show n - l = n + 1 - (l + 1) from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) (l + 1) (by omega)

end EtaleCoordinates

end FunctorialResolution.EmbeddedResolution
