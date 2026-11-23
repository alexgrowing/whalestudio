import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FlagBasis.GramLift
open Formalism.L2.SG.Pf.unitaryCongruence

theorem hatL_eq (I : AutInst) : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩; exact ⟨y, hy, rfl⟩

theorem col_mem (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hF : IsFrame β I.L) (j : Fin I.n) :
    (fun i => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j) ∈ I.Lf := by
  rw [← hatL_eq]
  refine (hF _).2 fun i => ?_
  have h1 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β = 1 := Units.inv_mul β
  have h2 : ((β⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)).mulVec
      (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j) i = (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j := by
    rw [← h1]; rfl
  have h3 : (1 : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ IntAf I.F I.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← h2] at h3
  exact h3

section
variable (I : AutInst) (g : ℕ)

theorem Z_of_eq {a b : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : a = b) (hb : ZMod' I g b) : ZMod' I g a := h ▸ hb

theorem Z_symm {x y : VA I} (h : ZMod' I g (hA I x y)) : ZMod' I g (hA I y x) := by
  rw [hA_symm]; exact Z_sig I g h

theorem Z_symm_sub {x y : VA I} {c : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g (hA I x y - c)) :
    ZMod' I g (hA I y x - sigA I c) := by
  rw [hA_symm, ← map_sub]; exact Z_sig I g h

theorem Z_sub_zero {a : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (h : ZMod' I g a) : ZMod' I g (a - 0) := by rwa [sub_zero]

theorem Z_addR {x y z : VA I} (h : ZMod' I g (hA I x y)) (h' : ZMod' I g (hA I x z)) :
    ZMod' I g (hA I x (y + z)) := by
  rw [hA_add_right]; exact Z_add I g h h'

theorem idem_sum {z0 : VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hz : z0 ∈ I.Lf) (hzz : ZMod' I g (hA I z0 z0 + 1))
    (hint : ew ∈ IntAf I.F I.E) (hfull : ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g) :
    ZMod' I g (1 - ew - sigA I ew) := by
  have hc : (1 - ew - sigA I ew) ∈ IntAf I.F I.E := sub_mem (sub_mem (one_mem _) hint) (sigA_mem I hint)
  have h1 : ZMod' I g (hA I z0 ((1 - ew - sigA I ew) • z0)) := mL_Qs I g hz (hfull z0 hz)
  rw [hA_smul_right] at h1
  exact Z_of_eq I g (by ring) (Z_sub I g (Z_smul I g hc hzz) h1)

theorem middle {k : ℕ} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (horth : ew * sigA I ew = 0)
    (hbw : ∀ i, bw i = ew • bw i) (hbwd : ∀ i, bwd i = sigA I ew • bwd i)
    (hdual : ∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0))
    (hsum : ZMod' I g (1 - ew - sigA I ew)) (l m : Fin k) :
    ZMod' I g (hA I (bw l + bwd l.rev) (bw m + bwd m.rev) - if m = l.rev then 1 else 0) := by
  have hbb : hA I (bw l) (bw m) = 0 := by
    calc hA I (bw l) (bw m) = hA I (ew • bw l) (ew • bw m) := by rw [← hbw l, ← hbw m]
      _ = (ew * sigA I ew) * hA I (bw l) (bw m) := by rw [hA_smul_left, hA_smul_right]; ring
      _ = 0 := by rw [horth, zero_mul]
  have hdd : hA I (bwd l.rev) (bwd m.rev) = 0 := by
    calc hA I (bwd l.rev) (bwd m.rev) = hA I (sigA I ew • bwd l.rev) (sigA I ew • bwd m.rev) := by
          rw [← hbwd l.rev, ← hbwd m.rev]
      _ = (ew * sigA I ew) * hA I (bwd l.rev) (bwd m.rev) := by
          rw [hA_smul_left, hA_smul_right, sigA_sigA]; ring
      _ = 0 := by rw [horth, zero_mul]
  have h3 := hdual l.rev m
  have h4 := Z_symm_sub I g (hdual m.rev l)
  rw [hA_add_left, hA_add_right, hA_add_right, hbb, hdd]
  by_cases hml : m = l.rev
  · rw [if_pos hml.symm] at h3
    rw [if_pos (by rw [hml, Fin.rev_rev])] at h4
    rw [if_pos hml]
    exact Z_of_eq I g (by ring) (Z_sub I g (Z_add I g h3 h4) hsum)
  · rw [if_neg (fun h => hml h.symm)] at h3
    rw [if_neg (fun h => hml (by rw [← h, Fin.rev_rev])), map_zero] at h4
    rw [if_neg hml]
    exact Z_of_eq I g (by ring) (Z_add I g h3 h4)

end

theorem flagVec_cases {V : Type} [AddCommGroup V] {ρ k : ℕ} (e0 f0 : Fin ρ → V) (z0 : V) (bw bwd : Fin k → V)
    (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    (∃ a : Fin ρ, j = a.1 ∧ dualIdx ρ k j = 2 * ρ + k - a.1 ∧ flagVec e0 f0 z0 bw bwd j = e0 a) ∨
    (∃ l : Fin k, j = ρ + l.1 ∧ dualIdx ρ k j = ρ + (k - (l.1 + 1)) ∧
      flagVec e0 f0 z0 bw bwd j = bw l + bwd l.rev) ∨
    (j = ρ + k ∧ dualIdx ρ k j = ρ + k ∧ flagVec e0 f0 z0 bw bwd j = z0) ∨
    (∃ a : Fin ρ, j = 2 * ρ + k - a.1 ∧ dualIdx ρ k j = a.1 ∧ flagVec e0 f0 z0 bw bwd j = f0 a) := by
  by_cases h1 : j < ρ
  · refine Or.inl ⟨⟨j, h1⟩, rfl, ?_, ?_⟩
    · unfold dualIdx; rw [if_pos h1]
    · unfold flagVec; rw [dif_pos h1]
  by_cases h2 : j - ρ < k
  · refine Or.inr (Or.inl ⟨⟨j - ρ, h2⟩, ?_, ?_, ?_⟩)
    · show j = ρ + (j - ρ); omega
    · show dualIdx ρ k j = ρ + (k - (j - ρ + 1)); unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dif_neg h1, dif_pos h2]
  by_cases h3 : j = ρ + k
  · refine Or.inr (Or.inr (Or.inl ⟨h3, ?_, ?_⟩))
    · unfold dualIdx; split_ifs <;> omega
    · unfold flagVec; rw [dif_neg h1, dif_neg h2, if_pos h3]
  have h4 : 2 * ρ + k - j < ρ := by omega
  refine Or.inr (Or.inr (Or.inr ⟨⟨2 * ρ + k - j, h4⟩, ?_, ?_, ?_⟩))
  · show j = 2 * ρ + k - (2 * ρ + k - j); omega
  · show dualIdx ρ k j = 2 * ρ + k - j; unfold dualIdx; split_ifs <;> omega
  · unfold flagVec; rw [dif_neg h1, dif_neg h2, if_neg h3, dif_pos h4]

section
variable {R : Type} [CommRing R] {n ρ k : ℕ} {i j : Fin n}

theorem flagGram_zero (h : j.val ≠ dualIdx ρ k i.val) : flagGram R n ρ k i j = 0 := if_neg h

theorem flagGram_neg (h : j.val = dualIdx ρ k i.val) (h' : i.val = ρ + k) : flagGram R n ρ k i j = -1 :=
  (if_pos h).trans (if_pos h')

theorem flagGram_ite {p : Prop} [Decidable p] (h : j.val = dualIdx ρ k i.val ↔ p) (h' : i.val ≠ ρ + k) :
    flagGram R n ρ k i j = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp]; exact (if_pos (h.2 hp)).trans (if_neg h')
  · rw [if_neg hp]; exact if_neg fun hh => hp (h.1 hh)

end

section
variable {I : AutInst} {g : ℕ} {ρ k : ℕ} {e0 f0 : Fin ρ → VA I} {z0 : VA I} {bw bwd : Fin k → VA I} {ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)}

theorem flagVec_mem (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) (j : ℕ) (hj : j < 2 * ρ + k + 1) :
    flagVec e0 f0 z0 bw bwd j ∈ I.Lf := by
  obtain ⟨⟨hef, hz, hb⟩, -⟩ := hR
  rcases flagVec_cases e0 f0 z0 bw bwd j hj with ⟨a, -, -, hv⟩ | ⟨l, -, -, hv⟩ | ⟨-, -, hv⟩ | ⟨a, -, -, hv⟩ <;> rw [hv]
  · exact (hef a).1
  · exact add_mem (hb l).1 (hb _).2
  · exact hz
  · exact (hef a).2

theorem flagVec_gram (hR : IsRefFrame I g e0 f0 z0 bw bwd ew) {n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    ZMod' I g (hA I (flagVec e0 f0 z0 bw bwd i.val) (flagVec e0 f0 z0 bw bwd j.val) - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) n ρ k i j) := by
  obtain ⟨⟨hef, hz, hb⟩, hgram, ⟨hzz, hez⟩, hW, ⟨hid, horth, hint, hfull⟩, ⟨hbw, hbwd⟩, hdual, -⟩ := hR
  have hsum := idem_sum I g hz hzz hint hfull
  have hec : ∀ a m, ZMod' I g (hA I (e0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).1 ((hW m.rev).2.2 a).2.2.1
  have hfc : ∀ a m, ZMod' I g (hA I (f0 a) (bw m + bwd m.rev)) := fun a m =>
    Z_addR I g ((hW m).2.2 a).2.1 ((hW m.rev).2.2 a).2.2.2
  have hzc : ∀ m, ZMod' I g (hA I z0 (bw m + bwd m.rev)) := fun m =>
    Z_addR I g (hW m).1 (hW m.rev).2.1
  have hi0 : i.val < 2 * ρ + k + 1 := hn ▸ i.isLt
  have hj0 : j.val < 2 * ρ + k + 1 := hn ▸ j.isLt
  rcases flagVec_cases e0 f0 z0 bw bwd i hi0 with ⟨a, hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ | ⟨hi, hd, hv⟩ | ⟨a, hi, hd, hv⟩ <;>
    rcases flagVec_cases e0 f0 z0 bw bwd j hj0 with ⟨b, hj, -, hw⟩ | ⟨b, hj, -, hw⟩ | ⟨hj, -, hw⟩ | ⟨b, hj, -, hw⟩ <;>
    rw [hv, hw]
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).1
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hec a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).1
  · rw [flagGram_ite (p := a = b) (by rw [Fin.ext_iff]; omega) (by omega)]; exact (hgram a b).2.2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hec b a))
  · rw [flagGram_ite (p := b = a.rev) (by rw [Fin.ext_iff, Fin.val_rev]; omega) (by omega)]
    exact middle I g horth hbw hbwd hdual hsum a b
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hzc a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hfc b a))
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).1)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hzc b)
  · rw [flagGram_neg (by omega) hi, sub_neg_eq_add]; exact hzz
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (Z_symm I g (hez b).2)
  · rw [flagGram_ite (p := b = a) (by rw [Fin.ext_iff]; omega) (by omega)]
    have h := Z_symm_sub I g (hgram b a).2.2
    rwa [apply_ite (sigA I), map_one, map_zero] at h
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hfc a b)
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hez a).2
  · rw [flagGram_zero (by omega)]; exact Z_sub_zero I g (hgram a b).2.1

end

theorem gramIn_lift : ∀ (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsRefFrame I g e0 f0 z0 bw bwd ew → I.n = 2 * ρ + k + 1 →
    ∀ β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β →
      ZMod' I g (1 - ew - sigA I ew) ∧
        (∀ i j, ZMod' I g (gramIn I β i j - flagGram (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) I.n ρ k i j)) := by
  intro I g ρ k e0 f0 z0 bw bwd ew hR hn β hL
  refine ⟨idem_sum I g hR.1.2.1 hR.2.2.1.1 hR.2.2.2.2.1.2.2.1 hR.2.2.2.2.1.2.2.2, fun i j => ?_⟩
  have h0 := flagVec_gram hR hn i j
  have hi0 : i.val < 2 * ρ + k + 1 := by have := i.isLt; omega
  have h1 := Z_symm I g (mL_Qs I g (col_mem I hL.1 j) (hL.2 i))
  have h2 : ZMod' I g (hA I _ _) := mL_Qs I g (flagVec_mem hR i hi0) (hL.2 j)
  rw [hA_sub_right] at h2
  have h3 := hA_add_left I ((fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l i) - flagVec e0 f0 z0 bw bwd i.val)
    (flagVec e0 f0 z0 bw bwd i.val) (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) l j)
  rw [sub_add_cancel] at h3
  refine Z_of_eq I g ?_ (Z_add I g (Z_add I g h1 h2) h0)
  unfold gramIn
  rw [h3]; ring

end GlobalTheory.FlagBasis.GramLift
end
