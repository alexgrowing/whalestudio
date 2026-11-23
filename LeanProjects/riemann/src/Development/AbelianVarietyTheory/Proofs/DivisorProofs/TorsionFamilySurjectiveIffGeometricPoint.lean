import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.TorsCount

variable {κ Q : Type} [Fintype κ] [Group Q]

theorem map_zero_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c) :
    e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_sub_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (a c : L) : e (a - c) = e a * (e c)⁻¹ := by
  have h := hadd (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

def red (M : ℕ) (e : (κ → ℤ) → Q) (hpow : ∀ a, e a ^ M = 1) : (κ → ZMod M) → {g : Q // g ^ M = 1} :=
  fun c => ⟨e fun i => ((c i).val : ℤ), hpow _⟩

theorem exists_red (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) (a : κ → ℤ) :
    ∃ c : κ → ZMod M, e (fun i => ((c i).val : ℤ)) = e a := by
  refine ⟨fun i => (a i : ZMod M), ?_⟩
  have h : e (a - fun i => (((a i : ZMod M)).val : ℤ)) = 1 := by
    refine (hker _).2 ⟨fun i => a i / (M : ℤ), funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (a i) (M : ℤ)
    linarith
  rw [map_sub_of_add e hadd, mul_inv_eq_one] at h
  exact h.symm

theorem red_injective (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) : Function.Injective (red M e hpow) := by
  intro c c' hcc
  have h1 : e (fun i => ((c i).val : ℤ)) = e (fun i => ((c' i).val : ℤ)) := congrArg Subtype.val hcc
  have h2 : e ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) = 1 := by
    rw [map_sub_of_add e hadd, h1, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (hker _).1 h2
  funext i
  have h3 := congrArg (fun x : κ → ℤ => ((x i : ℤ) : ZMod M)) hd
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_mul, ZMod.natCast_self, zero_mul] at h3
  exact sub_eq_zero.1 h3

theorem card_tors (M : ℕ) (hM : 0 < M) (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c)
    (hon : ∀ g : Q, g ^ M = 1 → ∃ a, e a = g) : Nat.card {g : Q // g ^ M = 1} = M ^ Fintype.card κ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have hb : Function.Bijective (red M e hpow) := by
    refine ⟨red_injective M e hadd hpow hker, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hon g hg
    obtain ⟨c, hc⟩ := exists_red M e hadd hker a
    exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end GlobalTheory.TorsCount

namespace GlobalTheory.HTSympCover

theorem onto_tors_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  intro p _ D R _ b N h M hM hcop S t o k _ _ y e hadd hpow hker
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (y ≫ t)
  obtain ⟨I, -⟩ := o.geom k y β hβ
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  let ev' : (Module.Free.ChooseBasisIndex ℤ D.La → ℤ) → (Over.mk y ⟶ o.A) := fun a => I.ev M (B.equivFun.symm a)
  have hadd' : ∀ a c, ev' (a + c) = ev' a * ev' c := fun a c => by
    simp only [ev', map_add]
    exact I.add M _ _
  have hpow' : ∀ a, ev' a ^ M = 1 := fun a => (I.onto M hM hcop _).2 ⟨_, rfl⟩
  have hker' : ∀ a, ev' a = 1 ↔ ∃ c, a = M • c := fun a => by
    simp only [ev']
    rw [I.ker M hM hcop]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨B.equivFun c, by rw [← map_nsmul, ← hc, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨B.equivFun.symm c, map_nsmul _ _ _⟩
  have hon' : ∀ g, g ^ M = 1 → ∃ a, ev' a = g := fun g hg => by
    obtain ⟨x, hx⟩ := (I.onto M hM hcop g).1 hg
    exact ⟨B.equivFun x, by simp only [ev', LinearEquiv.symm_apply_apply, hx]⟩
  have hcard := GlobalTheory.TorsCount.card_tors M hM ev' hadd' hpow' hker' hon'
  rw [← Module.finrank_eq_card_chooseBasisIndex] at hcard
  have hinj := GlobalTheory.TorsCount.red_injective M e hadd hpow hker
  have hdom : Nat.card (Fin h ⊕ Fin h → ZMod M) = M ^ (2 * h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, two_mul]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have h1 : M = 1 := by omega
    subst h1
    simp only [true_or, iff_true]
    intro g hg
    rw [pow_one] at hg
    exact ⟨0, by rw [hg]; exact GlobalTheory.TorsCount.map_zero_of_add e hadd⟩
  · have hMne : M ≠ 1 := by omega
    simp only [hMne, false_or]
    haveI : Finite {g : Over.mk y ⟶ o.A // g ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    constructor
    · intro hon
      have hb : Function.Bijective (GlobalTheory.TorsCount.red M e hpow) := by
        refine ⟨hinj, fun ⟨g, hg⟩ => ?_⟩
        obtain ⟨a, rfl⟩ := hon g hg
        obtain ⟨c, hc⟩ := GlobalTheory.TorsCount.exists_red M e hadd hker a
        exact ⟨c, Subtype.ext hc⟩
      have h2 := Nat.card_eq_of_bijective _ hb
      rw [hcard, hdom] at h2
      exact Nat.pow_right_injective hM2 h2
    · intro hr g hg
      have hs : Function.Surjective (GlobalTheory.TorsCount.red M e hpow) :=
        (hinj.bijective_of_nat_card_le (by rw [hcard, hdom, hr])).2
      obtain ⟨c, hc⟩ := hs ⟨g, hg⟩
      exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.HTSympCover
