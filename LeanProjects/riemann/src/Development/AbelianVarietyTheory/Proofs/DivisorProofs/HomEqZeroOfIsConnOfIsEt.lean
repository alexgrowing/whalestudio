import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFinite
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {k : Type} [Field k]

omit [Field k] in

theorem mem_augIdeal_iff' {R A : Type} [CommRing R] [CommRing A] [Bialgebra R A] (a : A) :
    a ∈ augIdeal R A ↔ counit (R := R) a = 0 := by
  rw [augIdeal, RingHom.mem_ker, Bialgebra.counitAlgHom_apply]

theorem eq_zero_of_app_augIdeal {G H : PDivGroup p k} (f : G ⟶ H)
    (hf : ∀ n, ∀ a ∈ augIdeal k (H.A n), f.app n a = 0) : f = 0 := by
  refine hom_ext fun n => BialgHom.ext fun a => ?_
  have hmem : a - algebraMap k (H.A n) (counit (R := k) a) ∈ augIdeal k (H.A n) := by
    rw [mem_augIdeal_iff', map_sub, ← Bialgebra.counitAlgHom_apply (R := k),
      ← Bialgebra.counitAlgHom_apply (R := k), AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have h := hf n _ hmem
  rw [map_sub, AlgHomClass.commutes, sub_eq_zero] at h
  exact h

variable [Fact p.Prime] [CharP k p] [PerfectRing k p]

theorem exists_augIdeal_pow_eq {A : Type} [CommRing A] [Bialgebra k A] [Module.Finite k A]
    [IsReduced A] (r : ℕ) : ∀ a ∈ augIdeal k A, ∃ b ∈ augIdeal k A, a = b ^ p ^ r := by
  induction r with
  | zero => exact fun a ha => ⟨a, ha, by rw [pow_zero, pow_one]⟩
  | succ r ih =>
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ih a ha
    obtain ⟨c, rfl⟩ := exists_pow_char_eq_of_isReduced_finite p k A b
    refine ⟨c, ?_, by rw [← pow_mul, ← pow_succ']⟩
    rw [mem_augIdeal_iff'] at hb ⊢
    rw [← Bialgebra.counitAlgHom_apply (R := k), map_pow, Bialgebra.counitAlgHom_apply] at hb
    exact pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.1 hb

theorem eq_zero_of_isConn_of_isEt {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : G ⟶ H) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  haveI : IsNoetherianRing (G.A n) := isNoetherian_of_tower k inferInstance
  obtain ⟨N, hN⟩ := (Ideal.FG.isNilpotent_iff_le_nilradical
    (IsNoetherian.noetherian (augIdeal k (G.A n)))).2 fun x hx => mem_nilradical.2 (hG n x hx)
  obtain ⟨b, hb, rfl⟩ := exists_augIdeal_pow_eq (A := H.A n) N a ha
  have hfb : f.app n b ∈ augIdeal k (G.A n) := by
    rw [mem_augIdeal_iff', CoalgHomClass.counit_comp_apply]
    exact (mem_augIdeal_iff' b).1 hb
  have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have h1 := Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hfb (p ^ N))
  rw [hN] at h1
  rw [map_pow]
  exact (Submodule.mem_bot _).1 h1

theorem eq_zero_of_isEt_of_isConn {G H : PDivGroup p k} (hG : G.IsConn) (hH : H.IsEt)
    (f : H ⟶ G) : f = 0 := by
  refine eq_zero_of_app_augIdeal f fun n a ha => ?_
  haveI := hH n
  exact ((hG n a ha).map (f.app n)).eq_zero

end PDivGroup

theorem PDivGroup.hom_eq_zero_of_isConn_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
      (G H : PDivGroup p k), G.IsConn → H.IsEt → (∀ f : G ⟶ H, f = 0) ∧ ∀ f : H ⟶ G, f = 0 :=
  fun _ _ _ _ _ _ _ _ hG hH =>
    ⟨PDivGroup.eq_zero_of_isConn_of_isEt hG hH, PDivGroup.eq_zero_of_isEt_of_isConn hG hH⟩

end GlobalTheory
