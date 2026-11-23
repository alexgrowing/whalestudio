import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvStableChains

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) : Submodule ℂ (Cq n V) where
  carrier := {x | SuppL (inUU lev) x ∧ DegL d x ∧ ∀ A, x A ∈ S}
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    have key : ∀ A, (x + y) A ≠ 0 → x A ≠ 0 ∨ y A ≠ 0 := fun A h => by
      by_contra hc
      push Not at hc
      exact h (by simp [hc.1, hc.2])
    refine ⟨fun A h => ?_, fun A h => ?_, fun A => S.add_mem (hx3 A) (hy3 A)⟩
    · rcases key A h with h' | h'
      · exact hx1 A h'
      · exact hy1 A h'
    · rcases key A h with h' | h'
      · exact hx2 A h'
      · exact hy2 A h'
  zero_mem' := ⟨fun A h => absurd rfl h, fun A h => absurd rfl h, fun A => S.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨hx1, hx2, hx3⟩
    have key : ∀ A, (c • x) A ≠ 0 → x A ≠ 0 := fun A h h0 => h (by simp [h0])
    exact ⟨fun A h => hx1 A (key A h), fun A h => hx2 A (key A h), fun A => S.smul_mem c (hx3 A)⟩

theorem finiteDimensional_chainsInL (lev : Fin n → ℕ) (d : ℕ) (S : Submodule ℂ V) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (chainsInL lev d S) := by
  let L : chainsInL lev d S →ₗ[ℂ] (Finset (Lt n) → S) :=
    LinearMap.pi fun A => LinearMap.codRestrict S ((LinearMap.proj A).comp (chainsInL lev d S).subtype)
      fun x => x.2.2.2 A
  refine Module.Finite.of_injective L fun x y h => Subtype.ext (funext fun A => ?_)
  exact congrArg Subtype.val (congrFun h A)

theorem Lv_apply (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) (x : Cq n V)
    (A : Finset (Lt n)) :
    Lv lev E1 E2 p q x A = kA E1 E2 p q (x A) +
      ∑ l : Lt n, ∑ k : Lt n, if inUU lev l then adCL false p q l k • creL k (annL l x) A else 0 := by
  simp only [Lv, adLL, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, liftL_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp [Module.End.mul_apply]

theorem creL_annL_mem {S : Submodule ℂ V} {x : Cq n V} (hx : ∀ A, x A ∈ S) (l k : Lt n) (A : Finset (Lt n)) :
    creL k (annL l x) A ∈ S := by
  rw [creL_apply]
  split_ifs
  · refine S.smul_mem _ ?_
    rw [annL_apply]
    split_ifs
    · exact S.zero_mem
    · exact S.smul_mem _ (hx _)
  · exact S.zero_mem

theorem inUU_of_adCL {lev : Fin n → ℕ} {p q : Fin n} (hpq : lev p = lev q) {l k : Lt n}
    (h : adCL false p q l k ≠ 0) (hl : inUU lev l) : inUU lev k := by
  by_cases c1 : q = l.2.1.1 ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (p, l.2.1.2)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c1.2.2]
    show lev p < lev l.2.1.2
    rw [hpq, c1.1]
    exact hl
  by_cases c2 : l.2.1.2 = p ∧ k.1 = (false ^^ l.1) ∧ k.2.1 = (l.2.1.1, q)
  · show lev k.2.1.1 < lev k.2.1.2
    rw [c2.2.2]
    show lev l.2.1.1 < lev q
    rw [← hpq, ← c2.1]
    exact hl
  · exact absurd (by rw [adCL, if_neg c1, if_neg c2, sub_zero]) h

theorem Lv_ne {lev : Fin n → ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V} {p q : Fin n} {x : Cq n V}
    {A : Finset (Lt n)} (h : Lv lev E1 E2 p q x A ≠ 0) :
    kA E1 E2 p q (x A) ≠ 0 ∨ ∃ l k, inUU lev l ∧ adCL false p q l k ≠ 0 ∧ creL k (annL l x) A ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  rw [Lv_apply, hc.1, zero_add]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
  split_ifs with hl
  · by_cases h0 : adCL false p q l k = 0
    · rw [h0, zero_smul]
    · rw [hc.2 l k hl h0, smul_zero]
  · rfl

theorem term_suppL {lev : Fin n → ℕ} {d : ℕ} {p q : Fin n} (hpq : lev p = lev q) {x : Cq n V}
    (hx : SuppL (inUU lev) x) (hd : DegL d x) {A : Finset (Lt n)} {l k : Lt n} (h0 : adCL false p q l k ≠ 0)
    (h : creL k (annL l x) A ≠ 0) : (∀ j ∈ A, inUU lev j) ∧ A.card = d := by
  obtain ⟨hk, h1⟩ := creL_ne h
  obtain ⟨h2, h3⟩ := annL_ne h1
  have hs := hx _ h3
  have hi : inUU lev l := hs l (mem_insert_self _ _)
  refine ⟨fun j hj => ?_, ?_⟩
  · by_cases e : j = k
    · exact e ▸ inUU_of_adCL hpq h0 hi
    · exact hs j (mem_insert_of_mem (mem_erase.2 ⟨e, hj⟩))
  · have e1 := hd _ h3
    rw [card_insert_of_notMem h2] at e1
    have e2 := card_erase_add_one hk
    omega

theorem Lv_mem_chainsInL {lev : Fin n → ℕ} {d : ℕ} {E1 E2 : Fin n → Fin n → Module.End ℂ V}
    {S : Submodule ℂ V} (hS : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) {p q : Fin n} (hpq : lev p = lev q)
    {x : Cq n V} (hx : x ∈ chainsInL lev d S) : Lv lev E1 E2 p q x ∈ chainsInL lev d S := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hk : ∀ A, kA E1 E2 p q (x A) ≠ 0 → x A ≠ 0 := fun A h h0 => h (by rw [h0, map_zero])
  refine ⟨fun A h => ?_, fun A h => ?_, fun A => ?_⟩
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx1 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').1
  · rcases Lv_ne h with h' | ⟨l, k, -, h0, h'⟩
    · exact hx2 A (hk A h')
    · exact (term_suppL hpq hx1 hx2 h0 h').2
  · rw [Lv_apply]
    refine S.add_mem (hS p q _ (hx3 A)) (S.sum_mem fun l _ => S.sum_mem fun k _ => ?_)
    split_ifs
    · exact S.smul_mem _ (creL_annL_mem hx3 l k A)
    · exact S.zero_mem

theorem exists_stable : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  intro n lev V _ _ E1 E2 d y hF hy hd
  choose Sf hfd hmem hSt using hF
  let S : Submodule ℂ V := ⨆ A, Sf (y A)
  have : ∀ A, FiniteDimensional ℂ (Sf (y A)) := fun A => hfd _
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_iSup _
  have hSs : ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S := fun a b v hv =>
    (iSup_le fun A z hz => Submodule.mem_iSup_of_mem A (hSt _ a b z hz) : S ≤ S.comap (kA E1 E2 a b)) hv
  refine ⟨chainsInL lev d S, finiteDimensional_chainsInL lev d S,
    ⟨hy, hd, fun A => Submodule.mem_iSup_of_mem A (hmem _)⟩, fun x hx => ⟨hx.1, hx.2.1⟩,
    fun p q hpq x hx => Lv_mem_chainsInL hSs hpq hx⟩

end GlobalTheory.CompanionTheory.LvStableChains
