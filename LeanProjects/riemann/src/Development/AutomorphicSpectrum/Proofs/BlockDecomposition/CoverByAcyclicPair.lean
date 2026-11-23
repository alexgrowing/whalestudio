import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairStructureOnLine
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.GeneralizedVermaModulePolynomial
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CreAnnApply
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MemFiltOfWords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SgMulSelf

open Finset
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.RealMult.CovR

open GlobalTheory.CompanionTheory.RealMult
open Formalism.REAL (GlRel)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.DSICKoszul (homotopy_ring filt mem_filt_succ euler_filt)

variable {n : ℕ}

theorem key_lt (p : Pos n) : CompanionTheory.D.LK.key p < n * n := by
  unfold CompanionTheory.D.LK.key
  have h1 := p.1.1.2
  have h2 := p.1.2.2
  calc (p.1.1 : ℕ) * n + p.1.2 < ((p.1.1 : ℕ) + 1) * n := by rw [add_mul, one_mul]; omega
    _ ≤ n * n := Nat.mul_le_mul_right _ h1

theorem keyR_inj {i j : Ix n} (h : keyR i = keyR j) : i = j := by
  obtain ⟨s, p⟩ := i
  obtain ⟨t, q⟩ := j
  have hp := key_lt p
  have hq := key_lt q
  unfold keyR at h
  cases s <;> cases t <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add] at h
  · rw [CompanionTheory.D.LK.Car.key_inj h]
  · omega
  · omega
  · rw [CompanionTheory.D.LK.Car.key_inj (Nat.add_left_cancel h)]

def twR (i j : Ix n) : ℂ := if keyR j < keyR i then -1 else 1

theorem twR_self (i : Ix n) : twR i i = 1 := by simp [twR]

theorem twR_mul_self (i j : Ix n) : twR i j * twR i j = 1 := by
  unfold twR; split_ifs <;> simp

theorem twR_swap {i j : Ix n} (h : i ≠ j) : twR j i = -twR i j := by
  have hk : keyR i ≠ keyR j := fun e => h (keyR_inj e)
  unfold twR
  rcases lt_or_gt_of_ne hk with h1 | h1
  · simp [h1, h1.not_gt]
  · simp [h1, h1.not_gt]

theorem sgR_mul_self (i : Ix n) (A : Finset (Ix n)) : sgR i A * sgR i A = 1 := by
  unfold sgR
  rw [← mul_pow]; simp

theorem sgR_insert (i : Ix n) {j : Ix n} {A : Finset (Ix n)} (h : j ∉ A) :
    sgR i (insert j A) = twR i j * sgR i A := by
  unfold sgR twR
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sgR_erase (i : Ix n) {j : Ix n} {A : Finset (Ix n)} (h : j ∈ A) :
    sgR i (A.erase j) = twR i j * sgR i A := by
  have h1 := sgR_insert i (Finset.notMem_erase j A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, twR_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annR_apply (i : Ix n) (x : Cr n V) (A : Finset (Ix n)) :
    annR i x A = if i ∈ A then 0 else sgR i A • x (insert i A) := rfl

theorem creR_apply (i : Ix n) (x : Cr n V) (A : Finset (Ix n)) :
    creR i x A = if i ∈ A then sgR i A • x (A.erase i) else 0 := rfl

theorem liftR_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cr n V) (A : Finset (Ix n)) :
    liftR n T x A = T (x A) := rfl

theorem annR_creR (i j : Ix n) :
    (annR i * creR j + creR j * annR i : Module.End ℂ (Cr n V)) = if i = j then 1 else 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annR_apply, creR_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ A
    · simp [hi, sgR_erase i hi, twR_self, smul_smul, sgR_mul_self, Finset.insert_erase hi]
    · simp [hi, sgR_insert i hi, twR_self, smul_smul, sgR_mul_self, Finset.erase_insert hi]
  have hji : j ≠ i := fun e => hij e.symm
  rw [if_neg hij, LinearMap.zero_apply, Pi.zero_apply]
  by_cases hi : i ∈ A
  · simp [hi, hij]
  by_cases hj : j ∈ A
  swap
  · simp [hj, hji]
  simp only [hi, hj, Finset.mem_insert, Finset.mem_erase, or_true, and_false, if_true, if_false]
  rw [sgR_insert j hi, sgR_erase i hj, twR_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul,
    ← add_smul]
  have : sgR i A * (-twR i j * sgR j A) + sgR j A * (twR i j * sgR i A) = 0 := by ring
  rw [this, zero_smul]

theorem creR_annR_apply (i : Ix n) (x : Cr n V) (A : Finset (Ix n)) :
    creR i (annR i x) A = if i ∈ A then x A else 0 := by
  by_cases h : i ∈ A
  · simp [creR_apply, annR_apply, h, sgR_erase i h, twR_self, smul_smul, sgR_mul_self, insert_erase h]
  · simp [creR_apply, h]

theorem annR_mem {Q : Submodule ℂ V} {x : Cr n V} (h : ∀ A, x A ∈ Q) (i : Ix n) (A : Finset (Ix n)) :
    annR i x A ∈ Q := by
  rw [annR_apply]; split_ifs
  · exact Q.zero_mem
  · exact Q.smul_mem _ (h _)

theorem creR_mem {Q : Submodule ℂ V} {x : Cr n V} (h : ∀ A, x A ∈ Q) (i : Ix n) (A : Finset (Ix n)) :
    creR i x A ∈ Q := by
  rw [creR_apply]; split_ifs
  · exact Q.smul_mem _ (h _)
  · exact Q.zero_mem

theorem annR_ne {i : Ix n} {x : Cr n V} {A : Finset (Ix n)} (h : annR i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annR_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · exact ⟨hi, fun h0 => h (by simp [hi, h0])⟩

theorem creR_ne {i : Ix n} {x : Cr n V} {A : Finset (Ix n)} (h : creR i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [creR_apply] at h
  by_cases hi : i ∈ A
  · exact ⟨hi, fun h0 => h (by simp [hi, h0])⟩
  · simp [hi] at h

theorem annR_liftR (i : Ix n) (T : Module.End ℂ V) :
    Commute (annR i : Module.End ℂ (Cr n V)) (liftR n T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [annR_apply, liftR_apply, h]

theorem creR_liftR (i : Ix n) (T : Module.End ℂ V) :
    Commute (creR i : Module.End ℂ (Cr n V)) (liftR n T) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  by_cases h : i ∈ A <;> simp [creR_apply, liftR_apply, h]

theorem bdR_apply (E1 E2 : Fin n → Fin n → Module.End ℂ V) (x : Cr n V) (A : Finset (Ix n)) :
    bdR E1 E2 x A = (∑ i : Ix n, rl E1 E2 i (annR i x A)) +
      (1 / 2 : ℂ) • ∑ i : Ix n, ∑ j : Ix n, ∑ k : Ix n, cst i j k • creR k (annR j (annR i x)) A := by
  simp only [bdR, LinearMap.add_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, Module.End.mul_apply]
  rfl

theorem degR_bdR (E1 E2 : Fin n → Fin n → Module.End ℂ V) {j : ℕ} {y : Cr n V} (hy : DegR (j + 1) y) :
    DegR j (bdR E1 E2 y) := by
  intro A hA
  by_contra hc
  apply hA
  rw [bdR_apply, Finset.sum_eq_zero, Finset.sum_eq_zero, smul_zero, add_zero]
  · refine fun i _ => Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases h : creR k (annR j' (annR i y)) A = 0
    · rw [h, smul_zero]
    · exfalso
      obtain ⟨h1, h2⟩ := creR_ne h
      obtain ⟨h3, h4⟩ := annR_ne h2
      obtain ⟨h5, h6⟩ := annR_ne h4
      have e1 := hy _ h6
      rw [card_insert_of_notMem h5, card_insert_of_notMem h3] at e1
      have e2 := card_erase_add_one h1
      omega
  · intro i _
    by_cases h : annR i y A = 0
    · rw [h, map_zero]
    · exfalso
      obtain ⟨h1, h2⟩ := annR_ne h
      have e1 := hy _ h2
      rw [card_insert_of_notMem h1] at e1
      omega

structure FiltR (R a d : Ix n → Module.End ℂ V) (Fil : ℕ → Submodule ℂ V) : Prop where
  a_comm : ∀ i j, Commute (a i) (a j)
  d_comm : ∀ i j, Commute (d i) (d j)
  da : ∀ i j, d i * a j - a j * d i = if i = j then 1 else 0
  mono : Monotone Fil
  exh : ∀ z, ∃ k, z ∈ Fil k
  a_mem : ∀ i k, ∀ z ∈ Fil k, a i z ∈ Fil (k + 1)
  r_mem : ∀ i k, ∀ z ∈ Fil k, R i z - a i z ∈ Fil k
  d_mem : ∀ i k, ∀ z ∈ Fil (k + 1), d i z ∈ Fil k
  d_zero : ∀ i, ∀ z ∈ Fil 0, d i z = 0

theorem acycR {Z : Type} [AddCommGroup Z] [Module ℂ Z] (E1 E2 : Fin n → Fin n → Module.End ℂ Z)
    (a d : Ix n → Module.End ℂ Z) (Fil : ℕ → Submodule ℂ Z) (hS : bdR E1 E2 * bdR E1 E2 = 0)
    (hF : FiltR (rl E1 E2) a d Fil) (j : ℕ) (x : Cr n Z) (hx : DegR (j + 1) x) (hcyc : bdR E1 E2 x = 0) :
    ∃ t : Cr n Z, DegR (j + 2) t ∧ bdR E1 E2 t = x := by
  let H : Module.End ℂ (Cr n Z) := ∑ i : Ix n, (liftR n (d i) : Module.End ℂ (Cr n Z)) * creR i
  let Da : Module.End ℂ (Cr n Z) := ∑ i : Ix n, (liftR n (a i) : Module.End ℂ (Cr n Z)) * annR i
  let N : Module.End ℂ Z := ∑ i : Ix n, a i * d i
  let G : ℕ → Submodule ℂ Z := fun k => Nat.casesOn k ⊥ Fil
  have hdG : ∀ i k, ∀ z ∈ G (k + 1), d i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => exact hF.d_zero i z hz
    | succ k => exact hF.d_mem i k z hz
  have hNG : ∀ k, ∀ z ∈ G k, N z ∈ G k := fun k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k =>
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun i _ => ?_
      cases k with
      | zero => rw [Module.End.mul_apply, hF.d_zero _ z hz, map_zero]; exact Submodule.zero_mem _
      | succ k => exact hF.a_mem _ k _ (hF.d_mem _ k z hz)
  have hrG : ∀ i k, ∀ z ∈ G k, rl E1 E2 i z - a i z ∈ G k := fun i k z hz => by
    cases k with
    | zero => obtain rfl : z = 0 := hz; simp
    | succ k => exact hF.r_mem i k z hz
  have hGf : ∀ k, G k ≤ filt d k := fun k => by
    induction k with
    | zero => exact bot_le
    | succ k ih => exact fun z hz => (mem_filt_succ _ _ _).2 fun i => ih (hdG _ k z hz)
  have hGm : ∀ k, G k ≤ G (k + 1) := fun k => by
    cases k with
    | zero => exact bot_le
    | succ k => exact hF.mono (Nat.le_succ k)
  have hH : ∀ (y : Cr n Z) A, H y A = ∑ i : Ix n, d i (creR i y A) := fun y A => by
    simp only [H, LinearMap.sum_apply, Finset.sum_apply]; rfl
  have hHG : ∀ k (y : Cr n Z), (∀ A, y A ∈ G (k + 1)) → ∀ A, H y A ∈ G k := fun k y hy A => by
    rw [hH]; exact Submodule.sum_mem _ fun i _ => hdG _ k _ (creR_mem hy _ _)
  have hρ : ∀ k (y : Cr n Z), (∀ A, y A ∈ G k) → ∀ A, (bdR E1 E2 y - Da y) A ∈ G k := fun k y hy A => by
    have e : Da y A = ∑ i : Ix n, a i (annR i y A) := by
      simp only [Da, LinearMap.sum_apply, Finset.sum_apply]; rfl
    rw [Pi.sub_apply, bdR_apply, e, add_sub_right_comm, ← Finset.sum_sub_distrib]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => ?_) (Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun k _ => ?_))
    · exact hrG i _ _ (annR_mem hy _ _)
    · exact Submodule.smul_mem _ _ (creR_mem (annR_mem (annR_mem hy _) _) _ _)
  have hom : Da * H + H * Da =
      ∑ i : Ix n, (liftR n (a i) : Module.End ℂ (Cr n Z)) * liftR n (d i) + ∑ i : Ix n, creR i * annR i := by
    refine homotopy_ring (fun i : Ix n => (liftR n (a i) : Module.End ℂ (Cr n Z))) (fun i => liftR n (d i))
      (fun i => annR i) (fun i => creR i) (fun i j => annR_liftR _ _)
      (fun i j => creR_liftR _ _) (fun i j => ?_) (fun i j => annR_creR i j)
    refine LinearMap.ext fun y => funext fun A => ?_
    have e := congrArg (fun T : Module.End ℂ Z => T (y A)) (hF.da i j)
    by_cases h : i = j
    · simpa [h, liftR_apply] using e
    · simpa [h, liftR_apply] using e
  have hHs : ∀ (m : ℕ) (y : Cr n Z), DegR m y → DegR (m + 1) (H y) := fun m y hy A hA => by
    rw [hH] at hA
    obtain ⟨i, -, hi⟩ := exists_ne_zero_of_sum_ne_zero hA
    obtain ⟨h1, h2⟩ := creR_ne (fun h => hi (by rw [h, map_zero]) : creR i y A ≠ 0)
    have e1 := hy _ h2
    have e2 := card_erase_add_one h1
    omega
  have hΔ : ∀ y : Cr n Z, DegR (j + 1) y → bdR E1 E2 y = 0 → ∀ A, bdR E1 E2 (H y) A =
      N (y A) + ((j + 1 : ℕ) : ℂ) • y A + ((bdR E1 E2 (H y) - Da (H y)) A + H (bdR E1 E2 y - Da y) A) := by
    intro y hy hc A
    have e := congrArg (fun T : Module.End ℂ (Cr n Z) => T y A) hom
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.sum_apply, Finset.sum_apply,
      creR_annR_apply, liftR_apply] at e
    have e2 : (∑ i : Ix n, if i ∈ A then y A else 0) = ((j + 1 : ℕ) : ℂ) • y A := by
      by_cases h : y A = 0
      · simp [h]
      · rw [← hy A h, ← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
        congr 2
        ext i; simp
    have e3 : N (y A) = ∑ i : Ix n, a i (d i (y A)) := by simp only [N, LinearMap.sum_apply]; rfl
    rw [e3, ← e2, ← e, hc, zero_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
    abel
  have main : ∀ k (y : Cr n Z), (∀ A, y A ∈ G k) → DegR (j + 1) y → bdR E1 E2 y = 0 →
      ∃ t : Cr n Z, DegR (j + 2) t ∧ bdR E1 E2 t = y := by
    intro k
    induction k with
    | zero => exact fun y hy _ _ => ⟨0, fun _ h => absurd rfl h, by rw [map_zero]; exact (funext hy).symm⟩
    | succ k ihk =>
      have inner : ∀ m (y : Cr n Z), (∀ A, y A ∈ G (k + 1)) → (∀ A, y A ∈ filt d m ⊔ G k) →
          DegR (j + 1) y → bdR E1 E2 y = 0 → ∃ t : Cr n Z, DegR (j + 2) t ∧ bdR E1 E2 t = y := by
        intro m
        induction m with
        | zero => exact fun y _ hy => ihk y fun A => by simpa [filt] using hy A
        | succ m ih =>
          intro y hy1 hy2 hs hc
          have hne : ((m : ℂ) + (j + 1 : ℕ)) ≠ 0 := by exact_mod_cast (by omega : m + (j + 1) ≠ 0)
          have hL : ∀ A, (bdR E1 E2 (H y) - Da (H y)) A + H (bdR E1 E2 y - Da y) A ∈ G k := fun A =>
            Submodule.add_mem _ (hρ k _ (hHG k y hy1) A) (hHG k _ (hρ (k + 1) y hy1) A)
          have hw : ∀ A, (bdR E1 E2 (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y) A =
              (N (y A) - (m : ℂ) • y A) + ((bdR E1 E2 (H y) - Da (H y)) A + H (bdR E1 E2 y - Da y) A) := fun A => by
            rw [Pi.sub_apply, hΔ y hs hc A, Pi.smul_apply, add_smul]
            abel
          obtain ⟨t, ht, hbt⟩ := ih (bdR E1 E2 (H y) - ((m : ℂ) + (j + 1 : ℕ)) • y)
            (fun A => by
              rw [hw]
              exact Submodule.add_mem _ (Submodule.sub_mem _ (hNG (k + 1) _ (hy1 A)) (Submodule.smul_mem _ _ (hy1 A)))
                (hGm k (hL A)))
            (fun A => by
              rw [hw]
              obtain ⟨u, hu, g, hg, e⟩ := Submodule.mem_sup.1 (hy2 A)
              refine Submodule.add_mem _ ?_ (Submodule.mem_sup_right (hL A))
              rw [← e, map_add, smul_add, add_sub_add_comm]
              exact Submodule.add_mem_sup (euler_filt a d hF.d_comm hF.da m u hu)
                (Submodule.sub_mem _ (hNG _ _ hg) (Submodule.smul_mem _ _ hg)))
            (fun A hA => by
              by_cases h : y A = 0
              · exact degR_bdR E1 E2 (hHs (j + 1) y hs) A fun h' => hA (by simp [h, h'])
              · exact hs A h)
            (by
              rw [map_sub, map_smul, hc, smul_zero, sub_zero]
              exact LinearMap.congr_fun hS _)
          refine ⟨((m : ℂ) + (j + 1 : ℕ))⁻¹ • (H y - t), fun A hA => ?_, ?_⟩
          · by_cases h : t A = 0
            · exact hHs (j + 1) y hs A fun h' => hA (by simp [h, h'])
            · exact ht A h
          · rw [map_smul, map_sub, hbt, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hne, one_smul]
      exact fun y hy => inner (k + 1) y hy fun A => Submodule.mem_sup_left (hGf _ (hy A))
  choose f hf using hF.exh
  exact main ((univ.sup fun A => f (x A)) + 1) x
    (fun A => hF.mono (Finset.le_sup (f := fun A => f (x A)) (mem_univ A)) (hf _)) hx hcyc

section Tens

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def FW (Fil : ℕ → Submodule ℂ Z) (k : ℕ) : Submodule ℂ (Z ⊗[ℂ] Z) :=
  Submodule.span ℂ {t | ∃ k₁ k₂ z w, z ∈ Fil k₁ ∧ w ∈ Fil k₂ ∧ k₁ + k₂ ≤ k ∧ t = z ⊗ₜ[ℂ] w}

theorem tmul_mem_FW (Fil : ℕ → Submodule ℂ Z) {k k₁ k₂ : ℕ} {z w : Z} (hz : z ∈ Fil k₁) (hw : w ∈ Fil k₂)
    (h : k₁ + k₂ ≤ k) : z ⊗ₜ[ℂ] w ∈ FW Fil k :=
  Submodule.subset_span ⟨k₁, k₂, z, w, hz, hw, h, rfl⟩

theorem FW_map (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ (Z ⊗[ℂ] Z)) (k : ℕ) (Q : Submodule ℂ (Z ⊗[ℂ] Z))
    (h : ∀ k₁ k₂ z w, z ∈ Fil k₁ → w ∈ Fil k₂ → k₁ + k₂ ≤ k → T (z ⊗ₜ[ℂ] w) ∈ Q) : ∀ t ∈ FW Fil k, T t ∈ Q := by
  refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
  rintro _ ⟨k₁, k₂, z, w, hz, hw, hk, rfl⟩
  exact h k₁ k₂ z w hz hw hk

theorem FW_mono (Fil : ℕ → Submodule ℂ Z) : Monotone (FW Fil) := fun k l hkl =>
  Submodule.span_mono (by
    rintro _ ⟨k₁, k₂, z, w, hz, hw, hk, rfl⟩
    exact ⟨k₁, k₂, z, w, hz, hw, hk.trans hkl, rfl⟩)

theorem FW_exh (Fil : ℕ → Submodule ℂ Z) (hm : Monotone Fil) (he : ∀ z, ∃ k, z ∈ Fil k) (t : Z ⊗[ℂ] Z) :
    ∃ k, t ∈ FW Fil k := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul z w =>
    obtain ⟨k, hk⟩ := he z
    obtain ⟨l, hl⟩ := he w
    exact ⟨k + l, tmul_mem_FW Fil hk hl le_rfl⟩
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    exact ⟨max k l, Submodule.add_mem _ (FW_mono Fil (le_max_left _ _) hk) (FW_mono Fil (le_max_right _ _) hl)⟩

theorem rT_mem (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (s : ℕ) (h : ∀ l, ∀ z ∈ Fil l, T z ∈ Fil (l + s))
    (k : ℕ) : ∀ t ∈ FW Fil k, (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil (k + s) :=
  FW_map Fil _ k _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.rTensor_tmul]
    exact tmul_mem_FW Fil (h _ _ hz) hw (by omega)

theorem lT_mem (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (s : ℕ) (h : ∀ l, ∀ z ∈ Fil l, T z ∈ Fil (l + s))
    (k : ℕ) : ∀ t ∈ FW Fil k, (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil (k + s) :=
  FW_map Fil _ k _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.lTensor_tmul]
    exact tmul_mem_FW Fil hz (h _ _ hw) (by omega)

theorem rT_low (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h : ∀ l, ∀ z ∈ Fil (l + 1), T z ∈ Fil l)
    (h0 : ∀ z ∈ Fil 0, T z = 0) (k : ℕ) :
    ∀ t ∈ FW Fil (k + 1), (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil k :=
  FW_map Fil _ _ _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.rTensor_tmul]
    cases k₁ with
    | zero => rw [h0 z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | succ k₁ => exact tmul_mem_FW Fil (h _ _ hz) hw (by omega)

theorem lT_low (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h : ∀ l, ∀ z ∈ Fil (l + 1), T z ∈ Fil l)
    (h0 : ∀ z ∈ Fil 0, T z = 0) (k : ℕ) :
    ∀ t ∈ FW Fil (k + 1), (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t ∈ FW Fil k :=
  FW_map Fil _ _ _ fun k₁ k₂ z w hz hw hk => by
    rw [LinearMap.lTensor_tmul]
    cases k₂ with
    | zero => rw [h0 w hw, TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | succ k₂ => exact tmul_mem_FW Fil hz (h _ _ hw) (by omega)

theorem rT_zero (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h0 : ∀ z ∈ Fil 0, T z = 0) :
    ∀ t ∈ FW Fil 0, (T.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t = 0 := fun t ht => by
  have := FW_map Fil (T.rTensor Z) 0 ⊥ (fun k₁ k₂ z w hz hw hk => by
    obtain rfl : k₁ = 0 := by omega
    rw [LinearMap.rTensor_tmul, h0 z hz, TensorProduct.zero_tmul]; exact Submodule.zero_mem _) t ht
  simpa using this

theorem lT_zero (Fil : ℕ → Submodule ℂ Z) (T : Module.End ℂ Z) (h0 : ∀ z ∈ Fil 0, T z = 0) :
    ∀ t ∈ FW Fil 0, (T.lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) t = 0 := fun t ht => by
  have := FW_map Fil (T.lTensor Z) 0 ⊥ (fun k₁ k₂ z w hz hw hk => by
    obtain rfl : k₂ = 0 := by omega
    rw [LinearMap.lTensor_tmul, h0 w hw, TensorProduct.tmul_zero]; exact Submodule.zero_mem _) t ht
  simpa using this

theorem rT_lT_comm (S T : Module.End ℂ Z) :
    Commute (S.rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) (T.lTensor Z) := by
  show _ * _ = _ * _
  apply TensorProduct.ext'
  intro z w
  simp

theorem rT_mul (S T : Module.End ℂ Z) :
    ((S * T).rTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) = S.rTensor Z * T.rTensor Z := by
  apply TensorProduct.ext'
  intro z w
  simp

theorem lT_mul (S T : Module.End ℂ Z) :
    ((S * T).lTensor Z : Module.End ℂ (Z ⊗[ℂ] Z)) = S.lTensor Z * T.lTensor Z := by
  apply TensorProduct.ext'
  intro z w
  simp

end Tens

theorem freeR (n : ℕ) : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (P1 P2 : Fin n → Fin n → Module.End ℂ W)
    (χ : W →ₗ[ℂ] ℂ) (w₀ : W) (a d : Ix n → Module.End ℂ W) (Fil : ℕ → Submodule ℂ W),
    Pair2 P1 P2 ∧ χ w₀ = 1 ∧ (∀ c e w, χ (P1 c e w) = 0) ∧ (∀ c e w, χ (P2 c e w) = 0) ∧
      FiltR (rl P1 P2) a d Fil := by
  obtain ⟨Z, _, _, M, χ, z₀, a, d, Fil, hM, h1, h0, hF⟩ := CompanionTheory.D.LK.free_all n n
  let R : Module.End ℂ Z → Module.End ℂ (Z ⊗[ℂ] Z) := fun T => T.rTensor Z
  let L : Module.End ℂ Z → Module.End ℂ (Z ⊗[ℂ] Z) := fun T => T.lTensor Z
  have hRL : ∀ S T, R S * L T = L T * R S := fun S T => (rT_lT_comm S T).eq
  have hR1 : R 1 = 1 := LinearMap.rTensor_id _ _
  have hL1 : L 1 = 1 := LinearMap.lTensor_id _ _
  have hR0 : R 0 = 0 := LinearMap.rTensor_zero _
  have hL0 : L 0 = 0 := LinearMap.lTensor_zero _
  have hRm : ∀ S T, R (S * T) = R S * R T := rT_mul
  have hLm : ∀ S T, L (S * T) = L S * L T := lT_mul
  have hRs : ∀ S T, R (S - T) = R S - R T := fun S T => LinearMap.rTensor_sub _ _
  have hLs : ∀ S T, L (S - T) = L S - L T := fun S T => LinearMap.lTensor_sub _ _
  let χ' : Z ⊗[ℂ] Z →ₗ[ℂ] ℂ := LinearMap.mul' ℂ ℂ ∘ₗ TensorProduct.map χ χ
  have hχ : ∀ z w, χ' (z ⊗ₜ w) = χ z * χ w := fun z w => by simp [χ']
  let aR : Ix n → Module.End ℂ (Z ⊗[ℂ] Z) := fun i => if i.1 then R (a i.2) + L (a i.2) else L (a i.2)
  let dR : Ix n → Module.End ℂ (Z ⊗[ℂ] Z) := fun i => if i.1 then R (d i.2) else L (d i.2) - R (d i.2)
  have hda : ∀ p q : Pos n, d p * a q = a q * d p + if p = q then 1 else 0 := fun p q => by
    rw [← hF.da p q p.1.1.2]; abel
  have hr : ∀ p q : Pos n, R (d p) * R (a q) = R (a q) * R (d p) + if p = q then 1 else 0 := fun p q => by
    have := congrArg R (hda p q)
    by_cases h : p = q
    · simpa [h, hRm, ← hR1, R, LinearMap.rTensor_add] using this
    · simpa [h, hRm, hR0, R, LinearMap.rTensor_add] using this
  have hl : ∀ p q : Pos n, L (d p) * L (a q) = L (a q) * L (d p) + if p = q then 1 else 0 := fun p q => by
    have := congrArg L (hda p q)
    by_cases h : p = q
    · simpa [h, hLm, ← hL1, L, LinearMap.lTensor_add] using this
    · simpa [h, hLm, hL0, L, LinearMap.lTensor_add] using this
  have hcomR : ∀ {S T : Module.End ℂ Z}, Commute S T → Commute (R S) (R T) := fun h => by
    show _ * _ = _ * _
    rw [← hRm, ← hRm, h.eq]
  have hcomL : ∀ {S T : Module.End ℂ Z}, Commute S T → Commute (L S) (L T) := fun h => by
    show _ * _ = _ * _
    rw [← hLm, ← hLm, h.eq]
  have hRLc : ∀ S T, Commute (R S) (L T) := fun S T => rT_lT_comm S T
  refine ⟨Z ⊗[ℂ] Z, inferInstance, inferInstance, fun c e => R (M c e), fun c e => L (M c e), χ', z₀ ⊗ₜ z₀, aR, dR,
    FW Fil, ⟨?_, ?_, ?_⟩, by simp [hχ, h1], ?_, ?_, ⟨?_, ?_, ?_, FW_mono Fil, FW_exh Fil hF.mono hF.exh, ?_, ?_, ?_, ?_⟩⟩
  · intro a' b c e
    have := congrArg R (hM a' b c e)
    rw [hRs, hRm, hRm, hRs] at this
    rw [this]
    split_ifs <;> simp [hR0]
  · intro a' b c e
    have := congrArg L (hM a' b c e)
    rw [hLs, hLm, hLm, hLs] at this
    rw [this]
    split_ifs <;> simp [hL0]
  · exact fun a' b c e => hRL _ _
  · intro c e t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z w => simp [R, hχ, h0]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  · intro c e t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul z w => simp [L, hχ, h0]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hF.a_comm p q
    cases s <;> cases t <;> simp only [aR, Bool.false_eq_true, if_false, if_true]
    · exact hcomL c1
    · exact (hRLc _ _).symm.add_right (hcomL c1) |>.symm.symm
    · exact (hRLc _ _).add_left (hcomL c1)
    · exact ((hcomR c1).add_right (hRLc _ _)).add_left ((hRLc _ _).symm.add_right (hcomL c1))
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hF.d_comm p q
    cases s <;> cases t <;> simp only [dR, Bool.false_eq_true, if_false, if_true]
    · exact ((hcomL c1).sub_right (hRLc _ _).symm).sub_left ((hRLc _ _).sub_right (hcomR c1))
    · exact (hRLc _ _).symm.sub_left (hcomR c1)
    · exact (hRLc _ _).sub_right (hcomR c1)
    · exact hcomR c1
  · rintro ⟨s, p⟩ ⟨t, q⟩
    have c1 := hRL (d p) (a q)
    have c2 := hRL (a q) (d p)
    have r1 := hr p q
    have l1 := hl p q
    cases s <;> cases t <;> simp only [aR, dR, Bool.false_eq_true, if_false, if_true, sub_mul, mul_sub, add_mul, mul_add,
      r1, l1, c1, ← c2, Prod.mk.injEq, reduceCtorEq, false_and, true_and, and_true] <;> by_cases h : p = q <;> simp [h] <;> abel
  · rintro ⟨s, p⟩ k t ht
    cases s
    · exact lT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht
    · exact Submodule.add_mem _ (rT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht)
        (lT_mem Fil (a p) 1 (fun l z hz => hF.a_mem p l z hz) k t ht)
  · rintro ⟨s, p⟩ k t ht
    have h3 : ∀ l, ∀ z ∈ Fil l, (M p.1.1 p.1.2 - a p) z ∈ Fil (l + 0) := fun l z hz => hF.r_mem p l z hz
    cases s
    · have := lT_mem Fil _ 0 h3 k t ht
      simpa [rl, aR, L, LinearMap.lTensor_sub] using this
    · have e1 := rT_mem Fil _ 0 h3 k t ht
      have e2 := lT_mem Fil _ 0 h3 k t ht
      have e3 := Submodule.add_mem _ e1 e2
      show (R (M p.1.1 p.1.2) + L (M p.1.1 p.1.2)) t - (R (a p) + L (a p)) t ∈ FW Fil k
      have e4 : (R (M p.1.1 p.1.2) + L (M p.1.1 p.1.2)) t - (R (a p) + L (a p)) t =
          R (M p.1.1 p.1.2 - a p) t + L (M p.1.1 p.1.2 - a p) t := by
        rw [hRs, hLs]
        simp only [LinearMap.add_apply, LinearMap.sub_apply]
        abel
      rw [e4]
      exact e3
  · rintro ⟨s, p⟩ k t ht
    have e1 := rT_low Fil (d p) (fun l z hz => ?_) (hF.d_zero p) k t ht
    have e2 := lT_low Fil (d p) (fun l z hz => ?_) (hF.d_zero p) k t ht
    · cases s
      · exact Submodule.sub_mem _ e2 e1
      · exact e1
    · exact hF.d_mem p l z hz
    · exact hF.d_mem p l z hz
  · rintro ⟨s, p⟩ t ht
    have e1 := rT_zero Fil (d p) (hF.d_zero p) t ht
    have e2 := lT_zero Fil (d p) (hF.d_zero p) t ht
    cases s
    · simp only [dR, Bool.false_eq_true, if_false, LinearMap.sub_apply]
      rw [show R (d p) t = 0 from e1, show L (d p) t = 0 from e2, sub_zero]
    · simpa [dR, R] using e1

theorem coverR_of (hS : BdSqR) : CoverR := by
  intro n V _ _ E1 E2 hE
  obtain ⟨W, _, _, P1, P2, χ, w₀, a, d, Fil, hP, h1, h01, h02, hF⟩ := freeR n
  let F1 : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) := fun c e => (E1 c e).rTensor W + (P1 c e).lTensor V
  let F2 : Fin n → Fin n → Module.End ℂ (V ⊗[ℂ] W) := fun c e => (E2 c e).rTensor W + (P2 c e).lTensor V
  have hPair : Pair2 F1 F2 := by
    refine ⟨fun a' b c e => CompanionTheory.D.LK.kRel_tens (ε := CompanionTheory.D.LK.allT n) (fun a b c d _ _ => hE.gl1 a b c d) hP.gl1
        a' b c e rfl rfl, fun a' b c e => CompanionTheory.D.LK.kRel_tens (ε := CompanionTheory.D.LK.allT n)
        (fun a b c d _ _ => hE.gl2 a b c d) hP.gl2 a' b c e rfl rfl, fun a' b c e => ?_⟩
    apply TensorProduct.ext'
    intro v w
    have e1 := LinearMap.congr_fun (hE.comm a' b c e) v
    have e2 := LinearMap.congr_fun (hP.comm a' b c e) w
    simp only [Module.End.mul_apply] at e1 e2
    simp only [F1, F2, Module.End.mul_apply, LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      map_add, e1, e2, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  let S : ℕ → Set (V ⊗[ℂ] W) := fun k => {t | ∃ v z, z ∈ Fil k ∧ t = v ⊗ₜ z}
  have hin : ∀ {k : ℕ} (v : V) {z : W}, z ∈ Fil k → v ⊗ₜ[ℂ] z ∈ Submodule.span ℂ (S k) :=
    fun v _ hz => Submodule.subset_span ⟨_, _, hz, rfl⟩
  have hmap : ∀ (T : Module.End ℂ (V ⊗[ℂ] W)) (k : ℕ) (Q : Submodule ℂ (V ⊗[ℂ] W)),
      (∀ v z, z ∈ Fil k → T (v ⊗ₜ z) ∈ Q) → ∀ t ∈ Submodule.span ℂ (S k), T t ∈ Q := by
    intro T k Q h
    refine fun t ht => (Submodule.span_le (p := Q.comap T)).2 ?_ ht
    rintro _ ⟨v, z, hz, rfl⟩
    exact h v z hz
  have hm : Monotone fun k => Submodule.span ℂ (S k) := fun k l hkl =>
    Submodule.span_mono (by rintro _ ⟨v, z, hz, rfl⟩; exact ⟨v, z, hF.mono hkl hz, rfl⟩)
  have hFY : FiltR (rl F1 F2) (fun i => (a i).lTensor V) (fun i => (d i).lTensor V)
      (fun k => Submodule.span ℂ (S k)) := by
    refine ⟨?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j => (hF.a_comm i j).map (Module.End.lTensorAlgHom ℂ W V)
    · exact fun i j => (hF.d_comm i j).map (Module.End.lTensorAlgHom ℂ W V)
    · intro i j
      have := congrArg (Module.End.lTensorAlgHom ℂ W V) (hF.da i j)
      rw [map_sub, map_mul, map_mul, apply_ite (Module.End.lTensorAlgHom ℂ W V), map_one, map_zero] at this
      exact this
    · intro t
      induction t using TensorProduct.induction_on with
      | zero => exact ⟨0, Submodule.zero_mem _⟩
      | tmul v z =>
        obtain ⟨k, hk⟩ := hF.exh z
        exact ⟨_, hin v hk⟩
      | add p q hp hq =>
        obtain ⟨k, hk⟩ := hp
        obtain ⟨l, hl⟩ := hq
        exact ⟨max k l, Submodule.add_mem _ (hm (le_max_left _ _) hk) (hm (le_max_right _ _) hl)⟩
    · exact fun i k => hmap _ k _ fun v z hz => hin v (hF.a_mem i _ z hz)
    · intro i k
      refine hmap (rl F1 F2 i - (a i).lTensor V) k _ fun v z hz => ?_
      have e : (rl F1 F2 i - (a i).lTensor V : Module.End ℂ (V ⊗[ℂ] W)) (v ⊗ₜ z) =
          rl E1 E2 i v ⊗ₜ z + v ⊗ₜ (rl P1 P2 i z - a i z) := by
        obtain ⟨s, p⟩ := i
        cases s <;> simp only [rl, F1, F2, Bool.false_eq_true, if_false, if_true, LinearMap.sub_apply,
          LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.tmul_sub,
          TensorProduct.add_tmul, TensorProduct.tmul_add] <;> abel
      rw [e]
      exact Submodule.add_mem _ (hin _ hz) (hin _ (hF.r_mem i _ z hz))
    · exact fun i k => hmap _ _ _ fun v z hz => hin v (hF.d_mem i _ z hz)
    · exact fun i => hmap _ _ ⊥ fun v z hz => by simp [hF.d_zero i z hz]
  refine ⟨V ⊗[ℂ] W, inferInstance, inferInstance, F1, F2,
    (TensorProduct.rid ℂ V).toLinearMap ∘ₗ χ.lTensor V, hPair, fun v => ⟨v ⊗ₜ w₀, by simp [h1]⟩,
    fun c e t => ?_, fun c e t => ?_, fun j x hx hc =>
      acycR F1 F2 _ _ _ (hS n _ F1 F2 hPair) hFY j x hx hc⟩
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [F1, h01]
    | add p q hp hq => simp only [map_add, hp, hq]
  · induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f => simp [F2, h02]
    | add p q hp hq => simp only [map_add, hp, hq]

theorem cover_by_acyclic_pair : CoverR := coverR_of GlobalTheory.CompanionTheory.RealMult.BdSqProof.bdSqR

end GlobalTheory.CompanionTheory.RealMult.CovR
