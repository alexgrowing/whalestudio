import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag

noncomputable section

open NumberField Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.PosYGlobal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def bform (d : GL (Fin n) E) (x v : Fin n → E) : E :=
  ∑ i, conjE E (x i) * ((d⁻¹ : GL (Fin n) E).val *ᵥ v) i

theorem conj_conj (z : E) : conjE E (conjE E z) = z := IsCMField.complexConj_apply_apply E z

theorem mem_perpD_iff (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) (v : Fin n → E) :
    v ∈ perpD (conjE E) d W ↔ ∀ x ∈ W, bform d x v = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ x hx
    have h : (d⁻¹ : GL (Fin n) E).val *ᵥ (Matrix.toLin' d.val y) = y := by
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    simp only [bform, h]
    exact hy x hx
  · intro h
    refine ⟨(d⁻¹ : GL (Fin n) E).val *ᵥ v, fun x hx => h x hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem bform_nrm (d : GL (Fin n) E) (x v : Fin n → E) :
    bform d x ((nrm d).val *ᵥ v) = conjE E (bform d v x) := by
  have h : (d⁻¹ : GL (Fin n) E).val *ᵥ ((nrm d).val *ᵥ v) =
      (((d⁻¹ : GL (Fin n) E).val).map (conjE E))ᵀ *ᵥ v := by
    rw [Matrix.mulVec_mulVec, nrm, ← Units.val_mul, inv_mul_cancel_left, thetaR_val]
  simp only [bform]
  rw [h]
  simp only [map_sum, map_mul, conj_conj, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem bform_nrm_nrm (d : GL (Fin n) E) (x v : Fin n → E) :
    bform d ((nrm d).val *ᵥ x) ((nrm d).val *ᵥ v) = bform d x v := by
  rw [bform_nrm, bform_nrm, conj_conj]

abbrev Stb (d : GL (Fin n) E) (W : Submodule E (Fin n → E)) : Prop := img (nrm d) W = W

theorem stb_mem {d : GL (Fin n) E} {W : Submodule E (Fin n → E)} (h : Stb d W) {x : Fin n → E} (hx : x ∈ W) :
    (nrm d).val *ᵥ x ∈ W := by
  rw [← h]
  exact ⟨x, hx, by simp [Matrix.toLin'_apply]⟩

theorem stb_ex {d : GL (Fin n) E} {W : Submodule E (Fin n → E)} (h : Stb d W) {x : Fin n → E} (hx : x ∈ W) :
    ∃ y ∈ W, (nrm d).val *ᵥ y = x := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, by simp [Matrix.toLin'_apply]⟩

theorem perpD_anti (d : GL (Fin n) E) {A B : Submodule E (Fin n → E)} (h : A ≤ B) :
    perpD (conjE E) d B ≤ perpD (conjE E) d A := fun v hv =>
  (mem_perpD_iff d A v).2 fun x hx => (mem_perpD_iff d B v).1 hv x (h hx)

theorem perpD_flip {d : GL (Fin n) E} {A B : Submodule E (Fin n → E)} (hB : Stb d B)
    (h : A ≤ perpD (conjE E) d B) : B ≤ perpD (conjE E) d A := by
  intro b hb
  refine (mem_perpD_iff d A b).2 fun a ha => ?_
  obtain ⟨c, hc, rfl⟩ := stb_ex hB hb
  rw [bform_nrm, (mem_perpD_iff d B a).1 (h ha) c hc, map_zero]

theorem stb_sup {d : GL (Fin n) E} {A B : Submodule E (Fin n → E)} (hA : Stb d A) (hB : Stb d B) : Stb d (A ⊔ B) := by
  simp only [Stb, img, Submodule.map_sup] at *
  rw [hA, hB]

theorem stb_perpD {d : GL (Fin n) E} {B : Submodule E (Fin n → E)} (hB : Stb d B) :
    Stb d (perpD (conjE E) d B) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    refine (mem_perpD_iff d B _).2 fun b hb => ?_
    obtain ⟨c, hc, rfl⟩ := stb_ex hB hb
    rw [Matrix.toLin'_apply, bform_nrm_nrm]
    exact (mem_perpD_iff d B v).1 hv c hc
  · intro v hv
    have hinv : (nrm d).val *ᵥ ((nrm d)⁻¹.val *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    refine ⟨(nrm d)⁻¹.val *ᵥ v, (mem_perpD_iff d B _).2 fun b hb => ?_, by rw [Matrix.toLin'_apply, hinv]⟩
    rw [← bform_nrm_nrm, hinv]
    exact (mem_perpD_iff d B v).1 hv _ (stb_mem hB hb)

theorem stb_inf {d : GL (Fin n) E} {A B : Submodule E (Fin n → E)} (hA : Stb d A) (hB : Stb d B) : Stb d (A ⊓ B) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply]
    exact ⟨stb_mem hA hv.1, stb_mem hB hv.2⟩
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := stb_ex hA hv.1
    obtain ⟨b, hb, hab⟩ := stb_ex hB hv.2
    have : a = b := by
      have := congrArg ((nrm d)⁻¹.val *ᵥ ·) hab
      simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using this.symm
    subst this
    exact ⟨a, ⟨ha, hb⟩, by rw [Matrix.toLin'_apply]⟩

theorem iso_of_le {d : GL (Fin n) E} {W W' : Submodule E (Fin n → E)} (hW : IsoStab d W) (hs : Stb d W') (h : W' ≤ W) :
    IsoStab d W' :=
  ⟨hs, h.trans (hW.2.trans (perpD_anti d h))⟩

theorem iso_sup {d : GL (Fin n) E} {A B : Submodule E (Fin n → E)} (hA : IsoStab d A) (hB : IsoStab d B)
    (h : A ≤ perpD (conjE E) d B) : IsoStab d (A ⊔ B) := by
  have hS : Stb d (A ⊔ B) := stb_sup hA.1 hB.1
  refine ⟨hS, sup_le ?_ ?_⟩
  · exact perpD_flip hA.1 (sup_le hA.2 (perpD_flip hB.1 h))
  · exact perpD_flip hB.1 (sup_le h hB.2)

def Comp {m : ℕ} (e f : Fin m → SignType) : Prop := ∀ i, e i ≠ 0 → f i ≠ 0 → e i = f i

section Poset

variable {d : GL (Fin n) E} {m : ℕ} {Wof : (Fin m → SignType) → Submodule E (Fin n → E)}

theorem sle_of_le (hiso : ∀ e, IsoStab d (Wof e)) (hu : ∀ W, IsoStab d W → ∃! e, Wof e = W)
    (hmeet : ∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') {e e' : Fin m → SignType} (h : Wof e ≤ Wof e') : SLe e e' := by
  have h1 : Wof (sMeet e e') = Wof e := by rw [hmeet, inf_eq_left.2 h]
  have h2 : sMeet e e' = e := (hu _ (hiso e)).unique h1 rfl
  intro i hi
  have h3 := congrFun h2 i
  simp only [sMeet] at h3
  by_contra hne
  split_ifs at h3 with hc
  · exact hne hc.symm
  · exact hi h3.symm

theorem orth_of_comp (hiso : ∀ e, IsoStab d (Wof e)) (hmono : ∀ e e', SLe e e' → Wof e ≤ Wof e')
    {e f : Fin m → SignType} (h : Comp e f) : Wof e ≤ perpD (conjE E) d (Wof f) := by
  let u : Fin m → SignType := fun i => if e i = 0 then f i else e i
  have h1 : SLe e u := fun i hi => by simp [u, hi]
  have h2 : SLe f u := fun i hi => by
    by_cases he : e i = 0
    · simp [u, he]
    · simp [u, he, h i he hi]
  exact (hmono _ _ h1).trans ((hiso u).2.trans (perpD_anti d (hmono _ _ h2)))

theorem comp_of_orth (hiso : ∀ e, IsoStab d (Wof e)) (hu : ∀ W, IsoStab d W → ∃! e, Wof e = W)
    (hmeet : ∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') {e f : Fin m → SignType}
    (h : Wof e ≤ perpD (conjE E) d (Wof f)) : Comp e f := by
  obtain ⟨g, hg, -⟩ := hu _ (iso_sup (hiso e) (hiso f) h)
  have h1 : SLe e g := sle_of_le hiso hu hmeet (hg ▸ le_sup_left)
  have h2 : SLe f g := sle_of_le hiso hu hmeet (hg ▸ le_sup_right)
  exact fun i hi hj => (h1 i hi).symm.trans (h2 i hj)

theorem radical_eq (hiso : ∀ e, IsoStab d (Wof e)) (hu : ∀ W, IsoStab d W → ∃! e, Wof e = W)
    (hmeet : ∀ e e', Wof (sMeet e e') = Wof e ⊓ Wof e') (hmono : ∀ e e', SLe e e' → Wof e ≤ Wof e')
    (e e' : Fin m → SignType) :
    (Wof e ⊔ Wof e') ⊓ perpD (conjE E) d (Wof e ⊔ Wof e') = Wof (sJoin e e') := by
  set j := sJoin e e' with hj
  set S := Wof e ⊔ Wof e' with hS
  have hSs : Stb d S := stb_sup (hiso e).1 (hiso e').1
  have hCe : Comp j e := by
    intro i
    simp only [hj, sJoin]
    generalize e i = a
    generalize e' i = b
    revert a b
    decide
  have hCe' : Comp j e' := by
    intro i
    simp only [hj, sJoin]
    generalize e i = a
    generalize e' i = b
    revert a b
    decide

  have hJS : Wof j ≤ S := by
    have hT : Wof (sMeet e j) ⊔ Wof (sMeet e' j) ≤ Wof j := by
      rw [hmeet, hmeet]
      exact sup_le inf_le_right inf_le_right
    have hTs : Stb d (Wof (sMeet e j) ⊔ Wof (sMeet e' j)) := stb_sup (hiso _).1 (hiso _).1
    obtain ⟨h, hh, -⟩ := hu _ (iso_of_le (hiso j) hTs hT)
    have h1 : SLe (sMeet e j) h := sle_of_le hiso hu hmeet (hh ▸ le_sup_left)
    have h2 : SLe (sMeet e' j) h := sle_of_le hiso hu hmeet (hh ▸ le_sup_right)
    have h3 : SLe j h := by
      intro i hi
      have key : (sMeet e j i ≠ 0 ∧ sMeet e j i = j i) ∨ (sMeet e' j i ≠ 0 ∧ sMeet e' j i = j i) := by
        revert hi
        simp only [hj, sJoin, sMeet]
        generalize e i = a
        generalize e' i = b
        revert a b
        decide
      rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
      · rw [h1 i k1, k2]
      · rw [h2 i k1, k2]
    calc Wof j ≤ Wof h := hmono _ _ h3
      _ = _ := hh
      _ ≤ S := by
        rw [hmeet, hmeet]
        exact sup_le_sup inf_le_left inf_le_left
  have hJP : Wof j ≤ perpD (conjE E) d S :=
    perpD_flip (hiso j).1 (sup_le (perpD_flip (hiso e).1 (orth_of_comp hiso hmono hCe))
      (perpD_flip (hiso e').1 (orth_of_comp hiso hmono hCe')))
  have hS0 : IsoStab d (S ⊓ perpD (conjE E) d S) :=
    ⟨stb_inf hSs (stb_perpD hSs), inf_le_right.trans (perpD_anti d inf_le_left)⟩
  obtain ⟨g, hg, -⟩ := hu _ hS0
  have hjg : SLe j g := sle_of_le hiso hu hmeet (hg ▸ le_inf hJS hJP)
  have hgS : Wof g ≤ S := hg ▸ inf_le_left
  have hgP : Wof g ≤ perpD (conjE E) d S := hg ▸ inf_le_right
  have hCg : Comp g e := comp_of_orth hiso hu hmeet (hgP.trans (perpD_anti d le_sup_left))
  have hCg' : Comp g e' := comp_of_orth hiso hu hmeet (hgP.trans (perpD_anti d le_sup_right))
  have hgj : SLe g j := by
    intro i hi
    by_cases hji : j i = 0
    · exfalso
      by_cases hz : e i = 0 ∧ e' i = 0
      · let f : Fin m → SignType := Pi.single i (-(g i))
        have hf : ∀ k, f k ≠ 0 → k = i := fun k hk => by
          by_contra hne
          exact hk (Pi.single_eq_of_ne hne _)
        have c1 : Comp e f := fun k hk hfk => absurd (hf k hfk ▸ hz.1) hk
        have c2 : Comp e' f := fun k hk hfk => absurd (hf k hfk ▸ hz.2) hk
        have o : S ≤ perpD (conjE E) d (Wof f) :=
          sup_le (orth_of_comp hiso hmono c1) (orth_of_comp hiso hmono c2)
        have c3 : Comp g f := comp_of_orth hiso hu hmeet (hgS.trans o)
        have hfi : f i = -(g i) := Pi.single_eq_same _ _
        have c4 := c3 i hi (by
          rw [hfi]
          revert hi
          generalize g i = c
          revert c
          decide)
        rw [hfi] at c4
        revert hi c4
        generalize g i = c
        revert c
        decide
      · have a1 := hCg i hi
        have a2 := hCg' i hi
        revert hji hz hi a1 a2
        simp only [hj, sJoin]
        generalize e i = a
        generalize e' i = b
        generalize g i = c
        revert a b c
        decide
    · exact (hjg i hji).symm
  exact le_antisymm (hg ▸ hmono _ _ hgj) (le_inf hJS hJP)

end Poset

theorem logSize_nonneg' (g : GA E n) : 0 ≤ logSize g := by
  have h : ∀ A : Matrix (Fin n) (Fin n) (Ad E), 0 ≤ logSizeM A := fun A =>
    add_nonneg (Finset.sum_nonneg fun _ _ => Real.posLog_nonneg) (finsum_nonneg fun _ => Real.posLog_nonneg)
  exact add_nonneg (h _) (h _)

theorem deg_bot' (x : GA E n) : deg x (⊥ : Submodule E (Fin n → E)) = 0 := by
  have h : ∀ (k : ℕ) (M : Matrix (Fin n) (Fin k) E), k = 0 → degM x M = 0 := by
    rintro _ M rfl
    exact degM_zero x M
  exact h _ _ (by simp)

theorem prof_concave (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) {a w w' s : ℕ} (h : w + w' = s + a) (h1 : a ≤ w) (h2 : a ≤ w') :
    prof n τ a + prof n τ s ≤ prof n τ w + prof n τ w' := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain rfl : s = a + p + q := by omega
  have key : prof n τ (a + p) + prof n τ (a + q) - (prof n τ a + prof n τ (a + p + q)) = 2 * τ * p * q := by
    simp only [prof]
    push_cast
    ring
  have : 0 ≤ 2 * τ * p * q := by positivity
  linarith

theorem prof_step {n : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) {j s : ℕ} (h : j < s) (hs : s ≤ n) :
    prof n τ j + 2 * τ ≤ prof n τ s := by
  have h1 : (j : ℝ) + 1 ≤ s := by exact_mod_cast h
  have h2 : (s : ℝ) ≤ n := by exact_mod_cast hs
  have key : prof n τ s - prof n τ j = τ * (((s : ℝ) - j) * (2 * n + 1 - s - j)) := by
    simp only [prof]
    ring
  have h3 : 2 ≤ ((s : ℝ) - j) * (2 * n + 1 - s - j) := by nlinarith
  nlinarith

theorem posY_of (h1 : DegSubmod) (h2 : DegPairing) : PosY := by
  intro E _ _ _ n
  obtain ⟨C₀, hC⟩ := h2 E n
  refine ⟨max C₀ 0, ?_⟩
  intro d m Wof hiso hu h0 hmeet hmono _ τ x hτ
  have hsz := logSize_nonneg' (twConj (thetaA E n) x (ratGL E n d))
  have hτ0 : 0 ≤ τ := le_trans (mul_nonneg (le_max_right _ _) (by linarith)) hτ
  have hτ1 : C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ :=
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hτ
  refine ⟨?_, fun e e' => ?_⟩
  · simp [h0, prof, deg_bot']
  · have hS : Stb d (Wof e ⊔ Wof e') := stb_sup (hiso e).1 (hiso e').1
    have hr := radical_eq hiso hu hmeet hmono e e'
    have hJS : Wof (sJoin e e') ≤ Wof e ⊔ Wof e' := hr ▸ inf_le_left
    have d1 := h1 E n x (Wof e) (Wof e')
    have d2 := (hC x d).1 _ hS
    rw [hr] at d2
    have r1 := Submodule.finrank_sup_add_finrank_inf_eq (Wof e) (Wof e')
    have r2 : Module.finrank E (Wof e ⊓ Wof e' : Submodule E (Fin n → E)) ≤ Module.finrank E (Wof e) :=
      Submodule.finrank_mono inf_le_left
    have r3 : Module.finrank E (Wof e ⊓ Wof e' : Submodule E (Fin n → E)) ≤ Module.finrank E (Wof e') :=
      Submodule.finrank_mono inf_le_right
    have pc := prof_concave n hτ0 r1.symm r2 r3
    beta_reduce
    rw [hmeet e e']
    rcases (Submodule.finrank_mono hJS).lt_or_eq with hlt | heq
    · have hs : Module.finrank E (Wof e ⊔ Wof e' : Submodule E (Fin n → E)) ≤ n := by
        simpa using Submodule.finrank_le (Wof e ⊔ Wof e')
      have ps := prof_step hτ0 hlt hs
      linarith
    · have hJ : Wof (sJoin e e') = Wof e ⊔ Wof e' := Submodule.eq_of_le_of_finrank_eq hJS heq
      rw [hJ]
      linarith

end GlobalTheory.CompanionTheory.PosYGlobal

end
