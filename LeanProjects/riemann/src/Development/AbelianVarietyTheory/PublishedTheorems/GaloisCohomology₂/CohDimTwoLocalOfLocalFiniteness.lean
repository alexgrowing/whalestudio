import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh

noncomputable section

open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.Published

def CohDimTwoGlobal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M),
    ContainsAbove S l → ContAction rhoS → ∀ n, 3 ≤ n → Subsingleton (Hn rhoS n)

def CohDimTwoLocal : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M]
    [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (rho : Representation (ZMod (l ^ r)) (Dec (F := F) A) M),
    IsPlaceOver A v → ContAction rho → ∀ n, 3 ≤ n → Subsingleton (Hn rho n)

def CohDimTwo : Prop := CohDimTwoGlobal ∧ CohDimTwoLocal

section Scalars

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {M : Type*} [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M]

theorem subsingleton_Hn_succ_iff {R : Type*} [CommRing R] [Module R M] [ContinuousConstSMul R M]
    (rho : Representation R Γ M) (n : ℕ) :
    Subsingleton (Hn rho (n + 1)) ↔
      ∀ f : (Fin (n + 1) → Γ) → M, Continuous f → dn rho (n + 1) f = 0 →
        ∃ c : (Fin n → Γ) → M, Continuous c ∧ dn rho n c = f := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  constructor
  · intro h f hf hd
    exact h (x := ⟨f, hf, hd⟩) trivial
  · intro h f _
    exact h f.1 f.2.1 f.2.2

omit [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] in

theorem dn_eq_of_action_eq {R R' : Type*} [CommRing R] [CommRing R'] [Module R M] [Module R' M]
    (rho : Representation R Γ M) (rho' : Representation R' Γ M)
    (h : ∀ g m, rho g m = rho' g m) (n : ℕ) (f : (Fin n → Γ) → M) :
    dn rho n f = dn rho' n f := by
  funext g
  show rho (g 0) (f fun i => g i.succ) + (Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)) =
    rho' (g 0) (f fun i => g i.succ) + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : R') ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases Nat.even_or_odd ((j : ℕ) + 1) with hj | hj <;> simp [hj.neg_one_pow]

theorem subsingleton_Hn_of_action_eq {R R' : Type*} [CommRing R] [CommRing R'] [Module R M]
    [Module R' M] [ContinuousConstSMul R M] [ContinuousConstSMul R' M]
    (rho : Representation R Γ M) (rho' : Representation R' Γ M)
    (h : ∀ g m, rho g m = rho' g m) (n : ℕ) (hn : 0 < n) (hs : Subsingleton (Hn rho' n)) :
    Subsingleton (Hn rho n) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [subsingleton_Hn_succ_iff] at hs ⊢
  intro f hf hd
  obtain ⟨c, hc, e⟩ := hs f hf (by rw [← dn_eq_of_action_eq rho rho' h]; exact hd)
  exact ⟨c, hc, by rw [dn_eq_of_action_eq rho rho' h]; exact e⟩

omit [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] in

def zmodRep {R : Type*} [CommRing R] [Module R M] (N : ℕ) [Module (ZMod N) M]
    (rho : Representation R Γ M) : Representation (ZMod N) Γ M where
  toFun g := (rho g).toAddMonoidHom.toZModLinearMap N
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp

end Scalars

section Consequences

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Finite M] [TopologicalSpace M] [DiscreteTopology M]

theorem CohDimTwoGlobal.of_nsmul (h : CohDimTwoGlobal) [IsTotallyComplex F] (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (rhoS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hS : ContainsAbove S l) (hc : ContAction rhoS) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rhoS n) := by
  letI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hM
  exact subsingleton_Hn_of_action_eq rhoS (zmodRep (l ^ r) rhoS) (fun _ _ => rfl) n (by omega)
    (h F Ω l r M S (zmodRep (l ^ r) rhoS) hS hc n hn)

theorem CohDimTwoLocal.of_nsmul (h : CohDimTwoLocal) (r : ℕ)
    (hM : ∀ m : M, (l ^ r) • m = 0) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (rho : Representation R (Dec (F := F) A) M)
    (hA : IsPlaceOver A v) (hc : ContAction rho) (n : ℕ) (hn : 3 ≤ n) :
    Subsingleton (Hn rho n) := by
  letI : Module (ZMod (l ^ r)) M := AddCommGroup.zmodModule hM
  exact subsingleton_Hn_of_action_eq rho (zmodRep (l ^ r) rho) (fun _ _ => rfl) n (by omega)
    (h F Ω l r M v A (zmodRep (l ^ r) rho) hA hc n hn)

end Consequences

theorem cohDimTwoLocal_of_localFiniteness (h : LocalFiniteness) : CohDimTwoLocal := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ v A rho hA hc n hn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact Module.subsingleton (ZMod (l ^ 0)) _
  · exact (h F Ω l r M A rho v hr hA hc).2.2.2 n hn

end GlobalTheory.Published
