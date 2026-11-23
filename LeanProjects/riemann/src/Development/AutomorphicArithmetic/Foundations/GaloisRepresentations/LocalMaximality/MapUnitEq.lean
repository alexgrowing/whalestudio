import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocDAux
variable {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]

private lemma geo_mem {W : Type} [AddCommGroup W] [Module ℂ W] (φ : S →+* Module.End ℂ W)
    (R : Subalgebra ℂ S) (P : Submodule ℂ W) (hP : ∀ s ∈ R, ∀ x ∈ P, φ s x ∈ P) {a b : S}
    (ha : a ∈ R) (hb : b ∈ R) (x : W) (h1 : φ (1 - a * b) x ∈ P) (N : ℕ)
    (hN : φ (a ^ N) x ∈ P) : x ∈ P := by
  have key : (1 : S) = b ^ N * a ^ N + (∑ i ∈ Finset.range N, (a * b) ^ i) * (1 - a * b) := by
    rw [geom_sum_mul_neg, mul_pow]; ring
  have hx : x = φ (b ^ N) (φ (a ^ N) x) +
      φ (∑ i ∈ Finset.range N, (a * b) ^ i) (φ (1 - a * b) x) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      ← LinearMap.add_apply, ← map_add, ← key]
    simp
  rw [hx]
  exact P.add_mem (hP _ (R.pow_mem hb N) _ hN)
    (hP _ (R.sum_mem fun i _ => R.pow_mem (R.mul_mem ha hb) i) _ h1)

private def pwR (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) : S →+* Module.End ℂ (ι → E) where
  toFun s := LinearMap.pi fun t => act s ∘ₗ LinearMap.proj t
  map_one' := LinearMap.ext fun c => funext fun t => by simp
  map_mul' s s' := LinearMap.ext fun c => funext fun t => by simp
  map_zero' := LinearMap.ext fun c => funext fun t => by simp
  map_add' s s' := LinearMap.ext fun c => funext fun t => by simp

private lemma pwR_apply (act : S →ₐ[ℂ] Module.End ℂ E) (ι : Type) (s : S) (c : ι → E) (t : ι) :
    pwR act ι s c t = act s (c t) := rfl

private lemma act_comm (act : S →ₐ[ℂ] Module.End ℂ E) (s s' : S) (x : E) :
    act s (act s' x) = act s' (act s x) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

variable {κ : Type} [LinearOrder κ]

private lemma kos_mem_C (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) (r : κ → S) (n : ℤ)
    (c : Finset κ → E) :
    c ∈ (kos act M r).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) := by
  simp [kos, acx, Submodule.mem_pi]

private lemma wd_pw (act : S →ₐ[ℂ] Module.End ℂ E) (r : κ → S) (s : S) (y : Finset κ → E) :
    wd (fun l => act (r l)) (pwR act _ s y) = pwR act _ s (wd (fun l => act (r l)) y) := by
  funext t
  simp only [pwR_apply, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_zsmul, act_comm act s]

private lemma kos_B_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (r : κ → S) (hSt : Stab act R M) (n : ℤ) (s : S) (hs : s ∈ R) (x : Finset κ → E)
    (hx : x ∈ (kos act M r).B n) : pwR act _ s x ∈ (kos act M r).B n := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨pwR act _ s y, ?_, wd_pw act r s y⟩
  rw [SetLike.mem_coe, kos_mem_C] at hy ⊢
  intro t
  have := hy t
  rw [pwR_apply]
  split_ifs at this ⊢ with h
  · exact hSt s hs _ this
  · simp only [Submodule.mem_bot] at this ⊢
    rw [this, map_zero]

private lemma sm_stab (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M : Submodule ℂ E)
    (T : Set S) (hSt : Stab act R M) (s : S) (hs : s ∈ R) (x : E) (hx : x ∈ sm act M T) :
    act s x ∈ sm act M T := by
  have hle : sm act M T ≤ (sm act M T).comap (act s) := by
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨m, hm, rfl⟩
    rw [Submodule.mem_comap, act_comm]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) t ht le_rfl : _ ≤ sm act M T)
      ⟨_, hSt s hs m hm, rfl⟩
  exact hle hx

private lemma unif_pow (act : S →ₐ[ℂ] Module.End ℂ E) (R : Subalgebra ℂ S) (M M' : Submodule ℂ E)
    (hSt : Stab act R M) {a : S} (ha : a ∈ R) (hloc : ∀ m ∈ M', ∃ N : ℕ, act (a ^ N) m ∈ M)
    {ι : Type} [Fintype ι] (f : ι → E) (hf : ∀ i, f i ∈ M') :
    ∃ N : ℕ, ∀ i, act (a ^ N) (f i) ∈ M := by
  choose n hn using fun i => hloc (f i) (hf i)
  refine ⟨∑ i, n i, fun i => ?_⟩
  have h : ∑ i, n i = (∑ i, n i - n i) + n i := (Nat.sub_add_cancel
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [h, pow_add, map_mul, Module.End.mul_apply]
  exact hSt _ (R.pow_mem ha _) _ (hn i)

private lemma map_unit_eq (act : S →ₐ[ℂ] Module.End ℂ E) (M' : Submodule ℂ E) (v : Sˣ)
    (hv : ∀ m ∈ M', act v m ∈ M' ∧ act (v⁻¹ : Sˣ) m ∈ M') (k : ℕ) :
    M'.map (act ((v ^ k : Sˣ) : S)) = M' := by
  have hP : ∀ k : ℕ, ∀ m ∈ M', act ((v ^ k : Sˣ) : S) m ∈ M' ∧ act (((v ^ k)⁻¹ : Sˣ) : S) m ∈ M' := by
    intro k
    induction k with
    | zero => intro m hm; simpa using hm
    | succ k ih =>
      intro m hm
      constructor
      · rw [pow_succ, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (ih _ (hv m hm).1).1
      · rw [pow_succ, mul_inv_rev, Units.val_mul, map_mul, Module.End.mul_apply]
        exact (hv _ (ih m hm).2).2
  refine le_antisymm ?_ fun m hm => ?_
  · rintro _ ⟨m, hm, rfl⟩
    exact (hP k m hm).1
  · refine ⟨_, (hP k m hm).2, ?_⟩
    change act ((v ^ k : Sˣ) : S) (act (((v ^ k)⁻¹ : Sˣ) : S) m) = m
    rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one]
    rfl

end LocDAux

theorem UpperTheory.Gal.productCup_of_system.locD_of :
    RS → Htpy → LocD := by
  intro hRS hH S E _ _ _ _ act κ _ _ R M M' r v a b l0 d hSt hr ha hb hl0 hMM hloc hv
  refine ⟨fun hKE m hm c hc => ?_, fun m hm hsm => ?_⟩
  · have hcC := hc.1
    have hcD : wd (fun l => act (r l)) c = 0 := hc.2

    let u : κ → Sˣ := fun _ => v
    let z : κ → S := fun l => r l * v
    have hrz : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ) := by
      intro l
      simp [z, u, mul_assoc]
    have hmap : ∀ L : Finset κ, M'.map (act ((∏ l ∈ L, u l : Sˣ) : S)) = M' := by
      intro L
      simp only [u, Finset.prod_const]
      exact map_unit_eq act M' v hv _
    have hT : kosT act M' u z = kos act M' z := by
      unfold kosT kos
      simp only [hmap]
    have hR := fun n c => hRS S E act κ M' u r z hrz n c
    have hcC' := (kos_mem_C act M r m c).1 hcC
    have hcZ' : c ∈ (kos act M' r).Z m := by
      refine ⟨(kos_mem_C act M' r m c).2 fun t => ?_, hc.2⟩
      have := hcC' t
      split_ifs at this ⊢ with h
      · exact hMM this
      · exact this
    have hinv : unsc act u (unsc act u⁻¹ c) = c := (hR m c).2.2.2.2
    have hZ : unsc act u⁻¹ c ∈ (kosT act M' u z).Z m :=
      (hR m (unsc act u⁻¹ c)).2.1.2 (by rw [hinv]; exact hcZ')
    have hB : unsc act u⁻¹ c ∈ (kosT act M' u z).B m := by
      rw [hT] at hZ ⊢
      exact hKE m hm hZ
    have hcB : c ∈ (kos act M' r).B m := by
      have := (hR m (unsc act u⁻¹ c)).2.2.1.1 hB
      rwa [hinv] at this
    obtain ⟨y, hy, hyc⟩ := hcB
    have hy' := (kos_mem_C act M' r (m - 1) y).1 hy
    have hyM : ∀ L, y L ∈ M' := by
      intro L
      have := hy' L
      split_ifs at this with h
      · exact this
      · rw [Submodule.mem_bot] at this
        rw [this]
        exact M'.zero_mem
    obtain ⟨N, hN⟩ := unif_pow act R M M' hSt ha hloc y hyM
    refine geo_mem (pwR act _) R ((kos act M r).B m)
      (fun s hs x hx => kos_B_stab act R M r hSt m s hs x hx) ha hb c ?_ N ?_
    · rw [← hl0]
      refine hH S E act κ R M r hSt m c hc (r l0) ⟨Pi.single l0 1, fun l => ?_, ?_⟩
      · by_cases h : l = l0
        · subst h
          simpa using R.one_mem
        · simpa [Pi.single_apply, h] using R.zero_mem
      · simp [Pi.single_apply]
    · refine ⟨pwR act _ (a ^ N) y, (kos_mem_C act M r (m - 1) _).2 fun t => ?_, ?_⟩
      · have := hy' t
        rw [pwR_apply]
        split_ifs at this ⊢ with h
        · exact hN t
        · rw [Submodule.mem_bot] at this ⊢
          rw [this, map_zero]
      · have e := wd_pw act r (a ^ N) y
        change wd (fun l => act (r l)) (pwR act _ (a ^ N) y) = pwR act _ (a ^ N) c
        rw [e]
        rw [← hyc]
        rfl
  · let T : Set S := Set.range r
    let Pn : Submodule ℂ E :=
      { carrier := {x | ∃ N : ℕ, act (a ^ N) x ∈ sm act M T}
        add_mem' := by
          rintro x y ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
          refine ⟨N₁ + N₂, ?_⟩
          rw [map_add]
          refine Submodule.add_mem _ ?_ ?_
          · rw [add_comm, pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₁
          · rw [pow_add, map_mul, Module.End.mul_apply]
            exact sm_stab act R M T hSt _ (R.pow_mem ha _) _ h₂
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro k x ⟨N, h⟩
          refine ⟨N, ?_⟩
          rw [map_smul]
          exact Submodule.smul_mem _ k h }
    have hle : sm act M' (Set.range fun l => r l * v) ≤ Pn := by
      refine iSup₂_le fun t ht => ?_
      obtain ⟨l, rfl⟩ := ht
      rintro _ ⟨m', hm', rfl⟩
      obtain ⟨N, hN⟩ := hloc _ (hv m' hm').1
      refine ⟨N, ?_⟩
      have e : act (a ^ N) (act (r l * v) m') = act (r l) (act (a ^ N) (act v m')) := by
        rw [map_mul, Module.End.mul_apply, act_comm act (a ^ N) (r l)]
      rw [e]
      exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l) ⟨l, rfl⟩ le_rfl :
        _ ≤ sm act M T) ⟨_, hN, rfl⟩
    obtain ⟨N, hN⟩ := hle hsm
    refine geo_mem act.toRingHom R (sm act M T)
      (fun s hs x hx => sm_stab act R M T hSt s hs x hx) ha hb m ?_ N hN
    change act (1 - a * b) m ∈ sm act M T
    rw [← hl0]
    exact (le_iSup₂_of_le (f := fun t _ => M.map (act t)) (r l0) ⟨l0, rfl⟩ le_rfl :
      _ ≤ sm act M T) ⟨_, hm, rfl⟩
