import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
open scoped NumberField

namespace GlobalTheory.TateTorsion

theorem natCard_eq_of_surj_fibres {α β γ : Type*} (g : α → β) (f : α → γ)
    (hg : Function.Surjective g) (hf : Function.Surjective f)
    (h : ∀ x y, g x = g y ↔ f x = f y) : Nat.card β = Nat.card γ := by
  refine Nat.card_congr
    { toFun := fun b => f (Function.surjInv hg b)
      invFun := fun c => g (Function.surjInv hf c)
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    have h1 := Function.surjInv_eq hf (f (Function.surjInv hg b))
    show g (Function.surjInv hf (f (Function.surjInv hg b))) = b
    rw [(h _ _).mpr h1, Function.surjInv_eq hg]
  · intro c
    have h1 := Function.surjInv_eq hg (g (Function.surjInv hf c))
    show f (Function.surjInv hg (g (Function.surjInv hf c))) = c
    rw [(h _ _).mp h1, Function.surjInv_eq hf]

theorem repr_mod_eq_zero_iff {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (l : ℕ)
    (z : M) : (∀ i, ((b.equivFun z i : ℤ) : ZMod l) = 0) ↔ ∃ y, z = l • y := by
  constructor
  · intro hz
    refine ⟨b.equivFun.symm (fun i => b.equivFun z i / (l : ℤ)), ?_⟩
    apply b.equivFun.injective
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i))]
  · rintro ⟨y, rfl⟩ i
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul]
    simp

end GlobalTheory.TateTorsion

open GlobalTheory.TateTorsion in
theorem GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  intro p hp D k _ Q _ act e I l hl hne
  haveI := D.freeLa
  haveI := D.finLa
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hl0 : 0 < l := hl.pos
  have hcop : l.Coprime p := (Nat.coprime_primes hl hp.out).mpr hne
  let b := Module.finBasisOfFinrankEq ℤ D.La D.rankLa
  let g : D.La → {q : Q // q ^ l = 1} := fun x => ⟨I.ev l x, (I.onto l hl0 hcop _).mpr ⟨x, rfl⟩⟩
  let f : D.La → (Fin (D.m * D.n * Module.finrank ℚ D.F) → ZMod l) :=
    fun x i => ((b.equivFun x i : ℤ) : ZMod l)
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := (I.onto l hl0 hcop q).mp hq
    exact ⟨x, Subtype.ext hx⟩
  have hf : Function.Surjective f := by
    intro c
    refine ⟨b.equivFun.symm (fun i => ((c i).val : ℤ)), ?_⟩
    funext i
    simp only [f, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id]
  have hgf : ∀ x y, g x = g y ↔ f x = f y := by
    intro x y
    have e1 : g x = g y ↔ I.ev l (x - y) = 1 := by
      rw [Subtype.ext_iff]
      show I.ev l x = I.ev l y ↔ _
      have : I.ev l x = I.ev l (x - y) * I.ev l y := by rw [← I.add, sub_add_cancel]
      rw [this]
      constructor
      · intro h; simpa using h
      · intro h; simp [h]
    have e2 : f x = f y ↔ ∀ i, ((b.equivFun (x - y) i : ℤ) : ZMod l) = 0 := by
      simp only [f, map_sub, Pi.sub_apply, Int.cast_sub, sub_eq_zero, funext_iff]
    rw [e1, e2, repr_mod_eq_zero_iff, I.ker l hl0 hcop]
  rw [natCard_eq_of_surj_fibres g f hg hf hgf, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
