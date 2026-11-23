import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GeomBasis

theorem basis_of_weil : ∀ (h N : ℕ) (k : Type) [Field k] (S : Scheme.{0}) (x : Sp k ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left) (z : kˣ) (e₀ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ A)), L.IsLB → Odd N → IsPrimitiveRoot z N → (∀ a a', e₀ (a + a') = e₀ a * e₀ a') → (∀ a, e₀ a = 1 ↔ ∃ a', a = N • a') → (∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e₀ a = g) → (∀ a a', e (a + a') = e a * e a') → (∀ a, e a ^ N = 1) → (∀ a a', Out.WeilIs A L N (e a) (e a') (unitOn (z ^ (2 * omegaStd a a')))) → (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ ∀ g : Over.mk x ⟶ A, g ^ N = 1 → ∃ a, e a = g := by
  intro h N k _ S x A _ _ L z e₀ e hL hN hz add₀ ker₀ onto₀ add tors weil
  have hN0 : N ≠ 0 := by rintro rfl; exact (Nat.not_even_iff_odd.2 hN) (by decide)
  haveI : NeZero N := ⟨hN0⟩
  have e0 : e 0 = 1 := GlobalTheory.LevCover.add_map_zero add
  have kerE : ∀ a, e a = 1 ↔ ∃ a', a = N • a' := by
    intro a
    constructor
    · intro ha
      apply GlobalTheory.SiegelOfPolarised.exists_smul_of_dvd
      intro b
      have w1 := weil a b
      have w0 := weil 0 b
      rw [ha] at w1
      rw [e0] at w0
      have hu := GlobalTheory.weilIs_unique_fieldPoint S A L hL k x _ _ _ _ _ w1 w0
      have h0 : omegaStd (0 : Fin h ⊕ Fin h → ℤ) b = 0 := by simp [omegaStd]
      rw [h0, mul_zero, zpow_zero] at hu
      have hd : (N : ℤ) ∣ 2 * omegaStd a b := (hz.zpow_eq_one_iff_dvd _).1 hu
      obtain ⟨m, hm⟩ := hN
      have hc : IsCoprime (N : ℤ) 2 := ⟨1, -(m : ℤ), by rw [hm]; push_cast; ring⟩
      exact hc.dvd_of_dvd_mul_left hd
    · rintro ⟨b, rfl⟩
      rw [GlobalTheory.LevCover.add_map_nsmul add, tors]
  have tors₀ : ∀ a, e₀ a ^ N = 1 := fun a => by
    rw [← GlobalTheory.LevCover.add_map_nsmul add₀]; exact (ker₀ _).2 ⟨a, rfl⟩
  let F : (Fin h ⊕ Fin h → ZMod N) → {g : Over.mk x ⟶ A // g ^ N = 1} :=
    fun c => ⟨e₀ fun i => ((c i).val : ℤ), tors₀ _⟩
  have hF : Function.Injective F := fun c c' hcc => by
    have e₁ : e₀ (fun i => ((c i).val : ℤ)) = e₀ fun i => ((c' i).val : ℤ) := congrArg Subtype.val hcc
    have e₂ := add₀ ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) fun i => ((c' i).val : ℤ)
    rw [sub_add_cancel, e₁] at e₂
    obtain ⟨b, hb⟩ := (ker₀ _).1 (mul_eq_right.1 e₂.symm)
    funext i
    have := congrArg (fun w : ℤ => (w : ZMod N)) (congrFun hb i)
    simpa [sub_eq_zero] using this
  have hF' : Function.Surjective F := by
    rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := onto₀ g hg
    refine ⟨fun i => (a i : ZMod N), Subtype.ext ?_⟩
    show e₀ (fun i => (((a i : ZMod N)).val : ℤ)) = e₀ a
    have d : ∀ i, (N : ℤ) ∣ a i - (((a i : ZMod N)).val : ℤ) := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp)
    choose b hb using d
    have hab : a - (fun i => (((a i : ZMod N)).val : ℤ)) = N • b := funext fun i => by simpa using hb i
    have := add₀ (a - fun i => (((a i : ZMod N)).val : ℤ)) fun i => (((a i : ZMod N)).val : ℤ)
    rw [sub_add_cancel, hab, (ker₀ _).2 ⟨b, rfl⟩, _root_.one_mul] at this
    exact this.symm
  have card : Nat.card {g : Over.mk x ⟶ A // g ^ N = 1} = N ^ Fintype.card (Fin h ⊕ Fin h) := by
    rw [← Nat.card_congr (Equiv.ofBijective F ⟨hF, hF'⟩), Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  exact ⟨kerE, GlobalTheory.SiegelOfPolarised.onto_torsion hN0 e add tors (fun a ha => (kerE a).1 ha) card⟩

end GlobalTheory.GeomBasis
