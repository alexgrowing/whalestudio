import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

abbrev VV (ι : Type) (n : ℕ) := (ι × Fin n) ⊕ (ι × Fin n)

abbrev Rw (β : Bool) := {a : Fin m // ε a = β}

def jv (β : Bool) : VV (Rw ε β) n → Fin m × Fin n × Bool :=
  Sum.elim (fun x => (x.1.1, x.2, false)) (fun x => (x.1.1, x.2, true))

def emb (β : Bool) : PV (Rw ε β) (Fin n) (Fin n) →ₐ[ℂ] PX m n := rename (jv ε β)

def act (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
    else ∑ b, C (u k.1 b) * X (b, k.2.1, false))

def blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) : Matrix (Fin m) (Fin m) ℂ := fun a b =>
  if ha : ε a = β then (if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0) else (if a = b then 1 else 0)

variable {ε}

theorem sum_rw {R : Type*} [AddCommMonoid R] (β : Bool) (F : Rw ε β → R) :
    ∑ b : Fin m, (if h : ε b = β then F ⟨b, h⟩ else 0) = ∑ b : Rw ε β, F b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b : Fin m => ε b = β)]
  have h2 : ∑ b : {b : Fin m // ¬ ε b = β}, (if h : ε b.1 = β then F ⟨b.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero (fun b _ => dif_neg b.2)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl (fun b _ => by rw [dif_pos b.2])

theorem blk_block (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a b : Fin m) (h : ε a ≠ ε b) : blk ε β v a b = 0 := by
  unfold blk
  by_cases ha : ε a = β
  · rw [dif_pos ha, dif_neg (fun hb => h (ha.trans hb.symm))]
  · rw [dif_neg ha, if_neg (fun e : a = b => h (congrArg ε e))]

theorem blk_of (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ε a = β) (b : Fin m) :
    blk ε β v a b = if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0 := by
  unfold blk; rw [dif_pos ha]

theorem blk_of_not (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (b : Fin m) :
    blk ε β v a b = if a = b then 1 else 0 := by
  unfold blk; rw [dif_neg ha]

theorem blk_unitary (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (hv : v ∈ Matrix.unitaryGroup (Rw ε β) ℂ) :
    blk ε β v ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hv ⊢
  ext a c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  by_cases ha : ε a = β
  · by_cases hc : ε c = β
    · have key := congrFun (congrFun hv ⟨a, ha⟩) ⟨c, hc⟩
      rw [Matrix.mul_apply, Matrix.one_apply] at key
      simp only [Matrix.star_apply] at key
      have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) =
          if h : ε b = β then v ⟨a, ha⟩ ⟨b, h⟩ * star (v ⟨c, hc⟩ ⟨b, h⟩) else 0 := by
        intro b
        rw [blk_of β v ha, blk_of β v hc]
        by_cases hb : ε b = β
        · rw [dif_pos hb, dif_pos hb, dif_pos hb]
        · rw [dif_neg hb, dif_neg hb, dif_neg hb, zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), sum_rw β (fun j => v ⟨a, ha⟩ j * star (v ⟨c, hc⟩ j)), key]
      by_cases hac : a = c
      · subst hac; simp
      · rw [if_neg (fun h => hac (congrArg Subtype.val h)), if_neg hac]
    · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if c = b then blk ε β v a b else 0 := by
        intro b
        rw [blk_of_not β v hc b]
        by_cases hcb : c = b
        · rw [if_pos hcb, if_pos hcb, star_one, mul_one]
        · rw [if_neg hcb, if_neg hcb, star_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [blk_block β v a c (by rw [ha]; exact fun h => hc h.symm), if_neg (by rintro rfl; exact hc ha)]
  · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if a = b then star (blk ε β v c b) else 0 := by
      intro b
      rw [blk_of_not β v ha b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, one_mul]
      · rw [if_neg hab, if_neg hab, zero_mul]
    rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hc : ε c = β
    · rw [blk_block β v c a (by rw [hc]; exact fun h => ha h.symm), star_zero,
        if_neg (by rintro rfl; exact ha hc)]
    · rw [blk_of_not β v hc a]
      by_cases hca : c = a
      · subst hca; simp
      · rw [if_neg hca, star_zero, if_neg (fun h => hca h.symm)]

end PositivityTheory.Rg.Sw.FFTSteps.CycF
