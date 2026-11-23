import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.MemEigenTensorSpaceIff

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Defs

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def wordE (E : Fin n → Fin n → Module.End ℂ M) (w : List (Fin n × Fin n)) : Module.End ℂ M :=
  (w.map fun p => E p.1 p.2).prod

abbrev KS (V : Submodule ℂ M) := (List (Fin n × Fin n) × Fin n) →₀ V

def sT (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) : KS (n := n) V →ₗ[ℂ] (Fin n → M) :=
  Finsupp.lsum ℂ fun p => (LinearMap.single ℂ (fun _ : Fin n => M) p.2) ∘ₗ (wordE E p.1) ∘ₗ V.subtype

def sθ {MM : Type*} [AddCommGroup MM] [Module ℂ MM] (V : Submodule ℂ M)
    (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ) : KS (n := n) V →ₗ[ℂ] (Fin n → MM) :=
  Finsupp.lsum ℂ fun p => (LinearMap.single ℂ (fun _ : Fin n => MM) p.2) ∘ₗ ℓ.smulRight (wordE EM p.1 φ)

def sES (V : Submodule ℂ M) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p => ∑ d : Fin n, Finsupp.lsingle ((p.2, d) :: p.1, d)

def adL (a b : Fin n) (p : Fin n × Fin n) : (Fin n × Fin n) →₀ ℂ :=
  (if b = p.1 then Finsupp.single (a, p.2) 1 else 0) - (if p.2 = a then Finsupp.single (p.1, b) 1 else 0)

def adLW (a b : Fin n) : List (Fin n × Fin n) → (List (Fin n × Fin n) →₀ ℂ)
  | [] => 0
  | p :: w => (adL a b p).mapDomain (· :: w) + (adLW a b w).mapDomain (p :: ·)

def sA (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (hV : IsKStableSub ε E V)
    (a b : Fin n) : Module.End ℂ (KS (n := n) V) :=
  Finsupp.lsum ℂ fun p =>
    (∑ w' ∈ (adLW a b p.1).support, adLW a b p.1 w' • Finsupp.lsingle (w', p.2)) +
    (if h : ε a = ε b then Finsupp.lsingle p ∘ₗ (E a b).restrict (fun v hv => hV a b h v hv) else 0) +
    (if p.2 = b then Finsupp.lsingle (p.1, a) else 0)

end Defs

section Basic

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {MM : Type*} [AddCommGroup MM] [Module ℂ MM]

theorem sT_single (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (w : List (Fin n × Fin n))
    (c : Fin n) (v : V) : sT E V (Finsupp.single (w, c) v) = Pi.single c (wordE E w v) := by
  simp [sT]

theorem sθ_single (V : Submodule ℂ M) (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ)
    (w : List (Fin n × Fin n)) (c : Fin n) (v : V) :
    sθ V EM φ ℓ (Finsupp.single (w, c) v) = Pi.single c (ℓ v • wordE EM w φ) := by
  simp [sθ]

theorem tensorAction_apply (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem tensorAction_apply_dual (E : Fin n → Fin n → Module.End ℂ MM) (f : Fin n → MM) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem wordAction_cons (E : Fin n → Fin n → Module.End ℂ M) (p : Fin n × Fin n) (w : List (Fin n × Fin n))
    (x : M) : wordE E (p :: w) x = E p.1 p.2 (wordE E w x) := by
  simp [wordE]

theorem wordAction_cons_dual (E : Fin n → Fin n → Module.End ℂ MM) (p : Fin n × Fin n) (w : List (Fin n × Fin n))
    (x : MM) : wordE E (p :: w) x = E p.1 p.2 (wordE E w x) := by
  simp [wordE]

theorem sT_sES (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (x : KS (n := n) V) :
    sT E V (sES V x) = eeV E (sT E V x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    funext d'
    rw [sT_single, tensorAction_apply]
    simp only [sES, Finsupp.lsum_single, LinearMap.sum_apply, Finset.sum_apply, Finsupp.lsingle_apply,
      map_sum, sT_single, wordAction_cons]
    rw [Finset.sum_eq_single d', Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'; simp [Pi.single_apply, hc']
    · simp
    · intro d _ hd; simp [Pi.single_apply, Ne.symm hd]
    · simp

theorem sθ_sES (V : Submodule ℂ M) (EM : Fin n → Fin n → Module.End ℂ MM) (φ : MM) (ℓ : V →ₗ[ℂ] ℂ)
    (x : KS (n := n) V) : sθ V EM φ ℓ (sES V x) = eeV EM (sθ V EM φ ℓ x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    funext d'
    rw [sθ_single, tensorAction_apply_dual]
    simp only [sES, Finsupp.lsum_single, LinearMap.sum_apply, Finset.sum_apply, Finsupp.lsingle_apply,
      map_sum, sθ_single, wordAction_cons_dual]
    rw [Finset.sum_eq_single d', Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'; simp [Pi.single_apply, hc']
    · simp
    · intro d _ hd; simp [Pi.single_apply, Ne.symm hd]
    · simp

theorem tensorWord_prepend (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (a b : Fin n)
    (x : KS (n := n) V) (c' : Fin n) :
    sT E V (Finsupp.mapDomain (fun p : List (Fin n × Fin n) × Fin n => ((a, b) :: p.1, p.2)) x) c' =
      E a b (sT E V x c') := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [Finsupp.mapDomain_add, map_add, Pi.add_apply, hx, hy]
  | single p v =>
    obtain ⟨w, c⟩ := p
    rw [Finsupp.mapDomain_single, sT_single, sT_single, wordAction_cons]
    by_cases h : c' = c
    · subst h; simp
    · simp [Pi.single_apply, h]

theorem sT_surj (E : Fin n → Fin n → Module.End ℂ M) (V : Submodule ℂ M) (f : Fin n → M)
    (hf : ∀ c, f c ∈ genSub E V) : ∃ x, sT E V x = f := by
  let S : Submodule ℂ M :=
    { carrier := {m | ∀ c, Pi.single c m ∈ LinearMap.range (sT E V)}
      add_mem' := by
        intro x y hx hy c
        rw [Pi.single_add]; exact add_mem (hx c) (hy c)
      zero_mem' := by intro c; simp
      smul_mem' := by
        intro r x hx c
        rw [Pi.single_smul']; exact Submodule.smul_mem _ r (hx c) }
  have hVS : V ≤ S := by
    intro v hv c
    refine ⟨Finsupp.single ([], c) ⟨v, hv⟩, ?_⟩
    rw [sT_single]; simp [wordE]
  have hst : ∀ a b, ∀ v ∈ S, E a b v ∈ S := by
    intro a b m hm c
    obtain ⟨x, hx⟩ := hm c
    refine ⟨Finsupp.mapDomain (fun p : List (Fin n × Fin n) × Fin n => ((a, b) :: p.1, p.2)) x, ?_⟩
    funext c'
    rw [tensorWord_prepend, hx]
    by_cases h : c' = c
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hgen : genSub E V ≤ S := sInf_le ⟨hVS, hst⟩
  have hmem : f ∈ LinearMap.range (sT E V) := by
    rw [← Finset.univ_sum_single f]
    exact Submodule.sum_mem _ fun c _ => hgen (hf c) c
  exact hmem

end Basic

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
