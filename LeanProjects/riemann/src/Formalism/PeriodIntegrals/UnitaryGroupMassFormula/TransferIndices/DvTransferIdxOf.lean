import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

def IntEl {K : Type} [Field K] [NumberField K] {G : Type} (z : MonoidAlgebra K G) : Prop :=
  ∀ g, z.coeff g ∈ Set.range (algebraMap (𝓞 K) K)

def BlockIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (n : ℕ) (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V)
    (Γ : Matrix (Fin n) (Fin n) (𝓞 K)), Γ.det ≠ 0 →
    (∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = algebraMap (𝓞 K) K (Γ j i) • x) →
    (∀ i, ∀ x ∈ X, Φ i x ∈ Y) → (∀ j, ∀ y ∈ Y, Ψ j y ∈ X) →
    (∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N.FG → Submodule.span K (M : Set V) = ⊤ →
      Submodule.span K (N : Set V) = ⊤ →
      (∀ i, ∀ x ∈ M, x ∈ X → Φ i x ∈ M) → (∀ j, ∀ y ∈ M, y ∈ Y → Ψ j y ∈ M) →
      (∀ i, ∀ x ∈ N, x ∈ X → Φ i x ∈ N) → (∀ j, ∀ y ∈ N, y ∈ Y → Ψ j y ∈ N) →
      Formalism.HN.rkK (M ⊓ Y.restrictScalars (𝓞 K)) = n * Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        |(idxAt w (M ⊓ Y.restrictScalars (𝓞 K)) (N ⊓ Y.restrictScalars (𝓞 K)) : ℝ) -
            (n : ℝ) * (idxAt w (M ⊓ X.restrictScalars (𝓞 K)) (N ⊓ X.restrictScalars (𝓞 K)) : ℝ)| ≤
          (Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) : ℝ) * (vAdd w (algebraMap (𝓞 K) K Γ.det) : ℝ)

def SumIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (S : Type) [Fintype S] [DecidableEq S] (π : S → V →ₗ[K] V) (m : ℕ), 0 < m →
    (∀ s t, π s ∘ₗ π t = if s = t then π s else 0) →
    ∀ M N : Submodule (𝓞 K) V, M.FG → N.FG → Submodule.span K (M : Set V) = ⊤ →
      Submodule.span K (N : Set V) = ⊤ →
      (∀ s, ∀ x ∈ M, x ∈ LinearMap.range (∑ t, π t) → ((m : ℕ) : 𝓞 K) • π s x ∈ M) →
      (∀ s, ∀ x ∈ N, x ∈ LinearMap.range (∑ t, π t) → ((m : ℕ) : 𝓞 K) • π s x ∈ N) →
      Formalism.HN.rkK (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) =
                ∑ s, Formalism.HN.rkK (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        |(idxAt w (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K))
              (N ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) : ℝ) -
            ∑ s, (idxAt w (M ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K))
              (N ⊓ (LinearMap.range (π s)).restrictScalars (𝓞 K)) : ℝ)| ≤
          (Formalism.HN.rkK (M ⊓ (LinearMap.range (∑ t, π t)).restrictScalars (𝓞 K)) : ℝ) *
            (vAdd w ((m : ℕ) : K) : ℝ)

def GrpData : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G),
    M1 T P0 →
    (∀ s t, eS T s * eS T t = if s = t then eS T s else 0) ∧
    (∀ s (z : MonoidAlgebra K G), eS T s * z = z * eS T s) ∧
    eps P * eps P = eps P ∧
    (∀ s, IntEl (((Fintype.card G : ℕ) : K) • eS T s)) ∧
    ∀ s, ∃ (a b : Fin (nS T P s) → MonoidAlgebra K G) (Γ : Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)),
      Γ.det ≠ 0 ∧
      (∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K Γ.det)‖ ≤ ((Fintype.card G : ℕ) : ℝ) ^ (4 * nS T P s)) ∧
      (∀ i, IntEl (a i)) ∧ (∀ j, IntEl (b j)) ∧
      (∀ i j, b j * a i * (eps P0 * eS T s) = algebraMap (𝓞 K) K (Γ j i) • (eps P0 * eS T s)) ∧
      (∀ i, a i * (eps P0 * eS T s) = eps P * eS T s * a i * (eps P0 * eS T s)) ∧
      (∀ j, b j * (eps P * eS T s) = eps P0 * eS T s * b j * (eps P * eS T s)) ∧
      ∃ b' : Fin (nS T P s) → MonoidAlgebra K G,
        (∀ i, b' i * (eps P * eS T s) = eps P0 * eS T s * b' i * (eps P * eS T s)) ∧
        ∑ i, a i * b' i * (eps P * eS T s) = eps P * eS T s

def VNonneg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K),
    0 ≤ vAdd w (algebraMap (𝓞 K) K x)

def VFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K), x ≠ 0 →
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => vAdd w (algebraMap (𝓞 K) K x)).Finite

def VSumLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ), x ≠ 0 → 0 < B →
    (∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) →
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), lw K w * (vAdd w (algebraMap (𝓞 K) K x) : ℝ) ≤ Real.log B

section Lat

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem intEl_mem (ρ : Representation K G V) (L : Submodule (𝓞 K) V) (hL : ∀ g, ∀ x ∈ L, ρ g x ∈ L)
    (z : MonoidAlgebra K G) (hz : IntEl z) : ∀ x ∈ L, ρ.asAlgebraHom z x ∈ L := by
  intro x hx
  rw [← MonoidAlgebra.sum_single z]
  rw [Finsupp.sum, map_sum, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun g _ => ?_
  obtain ⟨o, ho⟩ := hz g
  rw [Representation.asAlgebraHom_single, LinearMap.smul_apply, ← ho, algebraMap_smul]
  exact L.smul_mem o (hL g x hx)

end Lat

theorem dvTransferIdx_of (hB : BlockIdx) (hS : SumIdx) (hG : GrpData) (hV0 : VNonneg) (hVF : VFin)
    (hVS : VSumLe) : PI.Dv.Conclusion4b 1 := by
  intro K _ _ _ _ G _ _ T P0 P hM1
  obtain ⟨hO, hZ, hE, hIe, hD⟩ := hG K G T P0 P hM1
  choose a b Γ hdet hnorm ha hb hba haX hbY hsurj using hD
  refine ⟨Γ, hdet, ?_⟩
  intro A ρ B hA hBL
  obtain ⟨hAG, hAL, -⟩ := hA
  obtain ⟨hBG, hBL', -⟩ := hBL
  have hAfg : A.L.FG := hAG.2.1
  have hAsp : Submodule.span K (A.L : Set A.V) = ⊤ := hAG.2.2
  have hBfg : B.FG := hBG.2.1
  have hBsp : Submodule.span K (B : Set A.V) = ⊤ := hBG.2.2

  have hblk : ∀ s, _ := fun s => hB K A.V (nS T P s)
    (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s)))
    (fun i => ρ.asAlgebraHom (a s i)) (fun j => ρ.asAlgebraHom (b s j)) (Γ s) (hdet s)
    (by
      rintro i j x ⟨y, rfl⟩
      have := congrArg (fun z => ρ.asAlgebraHom z y) (hba s i j)
      simpa only [map_mul, Module.End.mul_apply, map_smul, LinearMap.smul_apply] using this)
    (by
      rintro i x ⟨y, rfl⟩
      refine ⟨ρ.asAlgebraHom (a s i * (eps P0 * eS T s)) y, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← haX s i, map_mul, Module.End.mul_apply])
    (by
      rintro j x ⟨y, rfl⟩
      refine ⟨ρ.asAlgebraHom (b s j * (eps P * eS T s)) y, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← hbY s j, map_mul, Module.End.mul_apply])
    (by
      rintro y ⟨y', rfl⟩
      obtain ⟨b', hb'1, hb'2⟩ := hsurj s
      refine ⟨fun i => ρ.asAlgebraHom (b' i * (eps P * eS T s)) y', fun i => ?_, ?_⟩
      · refine ⟨ρ.asAlgebraHom (b' i * (eps P * eS T s)) y', ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← hb'1 i]
      · conv_lhs => rw [← hb'2]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_assoc, map_mul, Module.End.mul_apply])
    A.L B hAfg hBfg hAsp hBsp
    (fun i x hx _ => intEl_mem ρ A.L hAL (a s i) (ha s i) x hx)
    (fun j x hx _ => intEl_mem ρ A.L hAL (b s j) (hb s j) x hx)
    (fun i x hx _ => intEl_mem ρ B hBL' (a s i) (ha s i) x hx)
    (fun j x hx _ => intEl_mem ρ B hBL' (b s j) (hb s j) x hx)

  have hπ : ∑ t, ρ.asAlgebraHom (eps P * eS T t) = ρ.asAlgebraHom (eps P * eG T) := by
    rw [eG, Finset.mul_sum, map_sum]
  have hcomm : ∀ s, eps P * eS T s = eS T s * eps P := fun s => (hZ s (eps P)).symm
  have hsum := hS K A.V T.S (fun s => ρ.asAlgebraHom (eps P * eS T s)) (Fintype.card G) Fintype.card_pos
    (by
      intro s t
      rw [← Module.End.mul_eq_comp, ← map_mul]
      have : eps P * eS T s * (eps P * eS T t) = eps P * (eS T s * eS T t) := by
        rw [mul_assoc, ← mul_assoc (eS T s), ← hcomm s, mul_assoc, ← mul_assoc, hE]
      rw [this, hO s t]
      split_ifs <;> simp)
    A.L B hAfg hBfg hAsp hBsp
    (by
      intro s x hx hxr
      rw [hπ] at hxr
      obtain ⟨y, rfl⟩ := hxr
      have h1 : ρ.asAlgebraHom (eps P * eS T s) (ρ.asAlgebraHom (eps P * eG T) y) =
          ρ.asAlgebraHom (eS T s) (ρ.asAlgebraHom (eps P * eG T) y) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hcomm s, mul_assoc,
          ← mul_assoc (eps P) (eps P), hE]
      rw [h1]
      have h2 := intEl_mem ρ A.L hAL _ (hIe s) _ hx
      rw [map_smul, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul] at h2
      rw [Nat.cast_smul_eq_nsmul]
      exact h2)
    (by
      intro s x hx hxr
      rw [hπ] at hxr
      obtain ⟨y, rfl⟩ := hxr
      have h1 : ρ.asAlgebraHom (eps P * eS T s) (ρ.asAlgebraHom (eps P * eG T) y) =
          ρ.asAlgebraHom (eS T s) (ρ.asAlgebraHom (eps P * eG T) y) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hcomm s, mul_assoc,
          ← mul_assoc (eps P) (eps P), hE]
      rw [h1]
      have h2 := intEl_mem ρ B hBL' _ (hIe s) _ hx
      rw [map_smul, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul] at h2
      rw [Nat.cast_smul_eq_nsmul]
      exact h2)
  simp only [hπ] at hsum
  obtain ⟨hrkY, hsumw⟩ := hsum
  have hcardK : algebraMap (𝓞 K) K ((Fintype.card G : ℕ) : 𝓞 K) = ((Fintype.card G : ℕ) : K) := map_natCast _ _
  have hvG : ∀ w : HeightOneSpectrum (𝓞 K), 0 ≤ vAdd w ((Fintype.card G : ℕ) : K) := fun w => by
    have := hV0 K w ((Fintype.card G : ℕ) : 𝓞 K); rwa [hcardK] at this
  have hrk : rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ := by
    show Formalism.HN.rkK (A.L ⊓ _) = _
    rw [hrkY, rkT]
    exact Finset.sum_congr rfl fun s _ => (hblk s).1
  have hdel : ∀ w, delRk T P0 P A ρ Γ w =
      ∑ s, (rS T P0 A ρ s : ℝ) * (vAdd w (algebraMap (𝓞 K) K (Γ s).det) : ℝ) +
        (rkT T P0 P A ρ : ℝ) * (vAdd w ((Fintype.card G : ℕ) : K) : ℝ) := by
    intro w
    simp only [delRk, rkT, vCard, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hn : nS T P s = 0
    · haveI : IsEmpty (Fin (nS T P s)) := by rw [hn]; infer_instance
      have h0 : vAdd w (algebraMap (𝓞 K) K (Γ s).det) = 0 := by simp [Matrix.det_isEmpty, vAdd]
      rw [h0, hn]; simp
    · have : (nS T P s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      push_cast; field_simp
  have hdelnn : ∀ w, 0 ≤ delRk T P0 P A ρ Γ w := by
    intro w; rw [hdel]
    refine add_nonneg (Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) ?_)
      (mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hvG w))
    exact_mod_cast hV0 K w _
  refine ⟨fun w => ⟨hdelnn w, ?_⟩, ?_⟩
  · rw [one_mul, hdel]
    have e1 := hsumw w
    have e2 := fun s => (hblk s).2 w
    simp only [cut, cutE]
    rw [show (Formalism.HN.rkK (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))).restrictScalars (𝓞 K)) : ℝ) =
        (rkT T P0 P A ρ : ℝ) from by exact_mod_cast hrk] at e1
    have : ∀ s, |(idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K)) : ℝ) -
        (nS T P s : ℝ) * (idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))).restrictScalars (𝓞 K)) : ℝ)| ≤
        (rS T P0 A ρ s : ℝ) * (vAdd w (algebraMap (𝓞 K) K (Γ s).det) : ℝ) := e2
    calc _ = |((idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eG T))).restrictScalars (𝓞 K)) : ℝ) -
          ∑ s, (idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K)) : ℝ)) +
          ∑ s, ((idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P * eS T s))).restrictScalars (𝓞 K)) : ℝ) -
          (nS T P s : ℝ) * (idxAt w (A.L ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))).restrictScalars (𝓞 K))
          (B ⊓ (LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))).restrictScalars (𝓞 K)) : ℝ))| := by
          rw [Finset.sum_sub_distrib]; ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add e1 ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => this s))
      _ = _ := add_comm _ _
  ·
    classical
    have hc0 : ((Fintype.card G : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    set F : Finset (HeightOneSpectrum (𝓞 K)) := (hVF K _ hc0).toFinset ∪
      Finset.univ.biUnion (fun s => (hVF K _ (hdet s)).toFinset) with hF
    have hsG : (Function.support fun w => lw K w * (vAdd w ((Fintype.card G : ℕ) : K) : ℝ)) ⊆ F := by
      intro w hw
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hw
      simp only [hF, Finset.coe_union, Set.mem_union, Set.Finite.coe_toFinset, Function.mem_support, hcardK]
      exact Or.inl hw.2
    have hss : ∀ s, (Function.support fun w => lw K w * (vAdd w (algebraMap (𝓞 K) K (Γ s).det) : ℝ)) ⊆ F := by
      intro s w hw
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hw
      simp only [hF, Finset.coe_union, Set.mem_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ,
        Set.iUnion_true, Set.mem_iUnion, Set.Finite.coe_toFinset, Function.mem_support]
      exact Or.inr ⟨s, hw.2⟩
    have hout : ∀ w, w ∉ F → delRk T P0 P A ρ Γ w = 0 := by
      intro w hw
      simp only [hF, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
        Function.mem_support, ne_eq, not_or, not_exists, not_not] at hw
      rw [hdel, ← hcardK, hw.1]
      simp [hw.2]
    have hsd : (Function.support fun w => lw K w * delRk T P0 P A ρ Γ w) ⊆ F := by
      intro w hw
      by_contra hwF
      exact hw (by simp only [hout w hwF, mul_zero])
    rw [finsum_eq_sum_of_support_subset _ hsd]
    have hcpos : (0 : ℝ) < ((Fintype.card G : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hla : 0 ≤ laG G := Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
    have hG1 : ∑ᶠ w, lw K w * (vAdd w ((Fintype.card G : ℕ) : K) : ℝ) ≤ laG G := by
      have := hVS K ((Fintype.card G : ℕ) : 𝓞 K) ((Fintype.card G : ℕ) : ℝ) hc0 hcpos
        (fun σ => by rw [hcardK, map_natCast, Complex.norm_natCast])
      rw [hcardK] at this
      exact this
    have hS1 : ∀ s, ∑ w ∈ F, lw K w * (vAdd w (algebraMap (𝓞 K) K (Γ s).det) : ℝ) ≤
        4 * (nS T P s : ℝ) * laG G := by
      intro s
      rw [← finsum_eq_sum_of_support_subset _ (hss s)]
      refine (hVS K _ _ (hdet s) (pow_pos hcpos _) (hnorm s)).trans (le_of_eq ?_)
      rw [Real.log_pow, laG]; push_cast; ring
    have hG2 : ∑ w ∈ F, lw K w * (vAdd w ((Fintype.card G : ℕ) : K) : ℝ) ≤ laG G := by
      rw [← finsum_eq_sum_of_support_subset _ hsG]; exact hG1
    have hrkT : (rkT T P0 P A ρ : ℝ) = ∑ s, (nS T P s : ℝ) * (rS T P0 A ρ s : ℝ) := by
      rw [rkT]; push_cast; rfl
    calc ∑ w ∈ F, lw K w * delRk T P0 P A ρ Γ w
        = ∑ s, (rS T P0 A ρ s : ℝ) * ∑ w ∈ F, lw K w * (vAdd w (algebraMap (𝓞 K) K (Γ s).det) : ℝ) +
          (rkT T P0 P A ρ : ℝ) * ∑ w ∈ F, lw K w * (vAdd w ((Fintype.card G : ℕ) : K) : ℝ) := by
          simp only [hdel, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun w _ => by ring
          · exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ ∑ s, (rS T P0 A ρ s : ℝ) * (4 * (nS T P s : ℝ) * laG G) + (rkT T P0 P A ρ : ℝ) * laG G :=
          add_le_add (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hS1 s) (Nat.cast_nonneg _))
            (mul_le_mul_of_nonneg_left hG2 (Nat.cast_nonneg _))
      _ = 5 * laG G * (rkT T P0 P A ρ : ℝ) := by
          rw [hrkT, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ ≤ 8 * laG G * (rkT T P0 P A ρ : ℝ) := by
          have : 0 ≤ (rkT T P0 P A ρ : ℝ) := Nat.cast_nonneg _
          nlinarith

end PI.Dv.TIW
