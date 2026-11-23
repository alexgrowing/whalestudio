import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumPf

noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbSumPf

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut MeasureTheory
open Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

section Iso

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def isoComp (M : Loc.Model F E) {m : ℕ} {X Y W : M.Mat (m + 1)} (φ : M.Iso X Y) : M.Iso X W ≃ M.Iso Y W where
  toFun ψ := ⟨φ.1.symm.trans ψ.1, by
      have h : φ.1.symm (M.eCls Y) = M.eCls X := (LinearEquiv.symm_apply_eq _).2 φ.2.1.symm
      refine ⟨(congrArg ψ.1 h).trans ψ.2.1, fun v => ?_⟩
      refine (ψ.2.2 (φ.1.symm v)).trans ?_
      rw [← φ.2.2 (φ.1.symm v), LinearEquiv.apply_symm_apply]⟩
  invFun χ := ⟨φ.1.trans χ.1, ⟨(congrArg χ.1 φ.2.1).trans χ.2.1, fun v => (χ.2.2 (φ.1 v)).trans (φ.2.2 v)⟩⟩
  left_inv ψ := Subtype.ext (LinearEquiv.ext fun v => by simp)
  right_inv χ := Subtype.ext (LinearEquiv.ext fun v => by simp)

theorem nIso_out (M : Loc.Model F E) {m : ℕ} (X : M.Mat (m + 1)) (c : M.Cls m) :
    M.nIso X (Quotient.out c) = if Quotient.mk (M.isoSetoid m) X = c then M.nAut c else 0 := by
  by_cases h : Quotient.mk (M.isoSetoid m) X = c
  · rw [if_pos h]
    have hn : Nonempty (M.Iso X (Quotient.out c)) :=
      Quotient.exact (s := M.isoSetoid m) (h.trans (Quotient.out_eq (s := M.isoSetoid m) c).symm)
    obtain ⟨φ⟩ := hn
    exact Nat.card_congr (isoComp M φ)
  · rw [if_neg h]
    refine Nat.card_eq_zero.2 (Or.inl ⟨fun φ => h ?_⟩)
    exact (Quotient.sound (s := M.isoSetoid m) (show Nonempty (M.Iso X (Quotient.out c)) from ⟨φ⟩)).trans
      (Quotient.out_eq (s := M.isoSetoid m) c)

end Iso

section Glue

variable {D : Formalism.BasicNotions.D7}

theorem nIsoO_some (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)
    (c : (M p).Cls D.R.rS) (o : Option ((M p).Cls D.R.rS)) :
    nIsoO M p (some c) o = if o = some c then (M p).nAut c else 0 := by
  cases o with
  | none => simp [nIsoO]
  | some d =>
    show (M p).nIso (Quotient.out c) (Quotient.out d) = _
    have hc : Quotient.mk ((M p).isoSetoid D.R.rS) (Quotient.out c) = c := Quotient.out_eq (s := (M p).isoSetoid D.R.rS) c
    rw [nIso_out, hc]
    split_ifs with h1 h2 h2
    · subst h1; rfl
    · exact absurd (by rw [h1]) h2
    · exact absurd (Option.some.inj h2).symm h1
    · rfl

theorem mul_of_mul {R : Type} [CommRing R] {n : ℕ} (l ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (s : R)
    (hl : ∀ i, l i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hρ : ∀ j, ρ (Fin.last n) j = if j = Fin.last n then 1 else 0) :
    l * (Matrix.of fun a b => if a = Fin.last n ∧ b = Fin.last n then s else 0) * ρ =
      Matrix.of fun a b => if a = Fin.last n ∧ b = Fin.last n then s else 0 := by
  have h1 : ∀ i k, (l * (Matrix.of fun a b => if a = Fin.last n ∧ b = Fin.last n then s else 0)) i k =
      if i = Fin.last n ∧ k = Fin.last n then s else 0 := by
    intro i k
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
    · rw [hl i, Matrix.of_apply]
      by_cases hi : i = Fin.last n <;> by_cases hk : k = Fin.last n <;> simp [hi, hk]
    · intro b _ hb
      rw [Matrix.of_apply, if_neg (fun h => hb h.1), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n)]
  · rw [h1, hρ j, Matrix.of_apply]
    by_cases hi : i = Fin.last n <;> by_cases hj : j = Fin.last n <;> simp [hi, hj]
  · intro b _ hb
    rw [h1, if_neg (fun h => hb h.2), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem last_of_low {R : Type} [CommRing R] {n : ℕ} (l : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h1 : ∀ a, l a a = 1) (h2 : ∀ a b, a < b → l a b = 0) (i : Fin (n + 1)) :
    l i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
  by_cases hi : i = Fin.last n
  · rw [if_pos hi, hi, h1]
  · rw [if_neg hi]; exact h2 _ _ (lt_of_le_of_ne (Fin.le_last i) hi)

theorem last_of_up {R : Type} [CommRing R] {n : ℕ} (ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h1 : ∀ a, ρ a a = 1) (h2 : ∀ a b, b < a → ρ a b = 0) (j : Fin (n + 1)) :
    ρ (Fin.last n) j = if j = Fin.last n then 1 else 0 := by
  by_cases hj : j = Fin.last n
  · rw [if_pos hj, hj, h1]
  · rw [if_neg hj]; exact h2 _ _ (lt_of_le_of_ne (Fin.le_last j) hj)

theorem uLow_last {R : Type} [CommRing R] {n : ℕ} (x : Loc.IL (n + 1) → R) (i : Fin (n + 1)) :
    Loc.uLow x i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
  refine last_of_low _ (fun a => by simp [Loc.uLow]) (fun a b hab => ?_) i
  simp only [Loc.uLow]
  rw [if_neg (ne_of_lt hab), dif_neg (not_lt.2 hab.le)]

theorem uUp_last {R : Type} [CommRing R] {n : ℕ} (w : Loc.Pt R (n + 1)) (y : Loc.IN w → R) (j : Fin (n + 1)) :
    Loc.uUp w y (Fin.last n) j = if j = Fin.last n then 1 else 0 := by
  refine last_of_up _ (fun a => by simp [Loc.uUp]) (fun a b hab => ?_) j
  simp only [Loc.uUp]
  rw [if_neg (ne_of_gt hab), dif_neg (fun h => (not_lt.2 hab.le) h.1)]

end Glue

section Main

variable {D : Formalism.BasicNotions.D7}

theorem mul_shM {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)}
    (l ρ : MatP D p) (hl : ∀ i, l i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0)
    (hρ : ∀ j, ρ (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0) :
    l * shM δ T T' p w * ρ = shM δ T T' p w :=
  mul_of_mul l ρ _ hl hρ

theorem shM_mem (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (i j : Fin (D.R.rS + 1)) :
    shM δ T T' p w i j ∈ (M p).R := by
  simp only [shM, Matrix.of_apply]
  split_ifs
  · unfold cornerSh
    split_ifs
    · exact (M p).R.zero_mem
    · exact natCast_mem _ _
  · exact (M p).R.zero_mem

theorem mem_orbR_iff (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Z : MatP D p) :
    Z ∈ orbR (M p) (Y + shM δ T T' p w) ↔ Z - shM δ T T' p w ∈ kkOrb M p Y := by
  constructor
  · rintro ⟨l, ρ, hl, hρ, rfl⟩
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [mul_add, add_mul, mul_shM l ρ (last_of_low l hl.1 hl.2.1) (last_of_up ρ hρ.1 hρ.2.1), add_sub_cancel_right]
  · rintro ⟨l, ρ, hl, hρ, h⟩
    refine ⟨l, ρ, hl, hρ, ?_⟩
    rw [mul_add, add_mul, mul_shM l ρ (last_of_low l hl.1 hl.2.1) (last_of_up ρ hρ.1 hρ.2.1), ← h, sub_add_cancel]

theorem zAt_eq {δ : ∀ p : PlF D, (D.s.atP p).Fp} {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)}
    {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)} (hmat : a.mat = modMat δ T T' p w + shM δ T T' p w)
    (xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep)) :
    zAt a xy = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 + shM δ T T' p w := by
  unfold zAt
  rw [hmat, mul_add, add_mul, mul_shM _ _ (uLow_last xy.1) (uUp_last a xy.2)]

theorem intLow_one (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) :
    Formalism.MainNotions.S.TieN.IntLow (M p) (1 : MatP D p) := by
  refine ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_lt h), fun a b => ?_⟩
  by_cases h : a = b
  · rw [h, Matrix.one_apply_eq]; exact (M p).R.one_mem
  · rw [Matrix.one_apply_ne h]; exact (M p).R.zero_mem

theorem intUp_one (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (1 : MatP D p) := by
  refine ⟨fun a => Matrix.one_apply_eq a, fun a b h => Matrix.one_apply_ne (ne_of_gt h), fun a b => ?_⟩
  by_cases h : a = b
  · rw [h, Matrix.one_apply_eq]; exact (M p).R.one_mem
  · rw [Matrix.one_apply_ne h]; exact (M p).R.zero_mem

def shE (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) :
    Set (MatP D p) ≃ Set (MatP D p) where
  toFun O := {Z | Z - shM δ T T' p w ∈ O}
  invFun O := {Y | Y + shM δ T T' p w ∈ O}
  left_inv O := by ext Y; simp
  right_inv O := by ext Z; simp

theorem fL_hasSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (hS : ModShift δ T T' p w)
    (hO : ∀ (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (c : (M p).Cls D.R.rS), OrbCut (M p) a c)
    (τ : Option ((M p).Cls D.R.rS)) :
    HasSum (fL M δ T T' p w τ) (BBtop M δ T T' p w τ) ∧ Summable (fun O => ‖fL M δ T T' p w τ O‖) := by
  cases ha : modPt δ T T' p w with
  | none =>
    have h0 : fL M δ T T' p w τ = fun _ => 0 := by
      funext O
      unfold fL
      rw [if_neg]
      rintro ⟨Y, -, ⟨w₀, hw₀, -⟩, -⟩
      rw [ha] at hw₀
      cases hw₀
    have hB : BBtop M δ T T' p w τ = 0 := by simp only [BBtop, ha]
    rw [h0, hB]
    exact ⟨hasSum_zero, by simpa using (summable_zero : Summable (fun _ : Set (MatP D p) => (0 : ℝ)))⟩
  | some a =>
    cases τ with
    | none =>
      have h0 : fL M δ T T' p w none = fun _ => 0 := by
        funext O
        unfold fL
        split_ifs <;> simp [nIsoO]
      have hB : BBtop M δ T T' p w none = 0 := by simp only [BBtop, ha]
      rw [h0, hB]
      exact ⟨hasSum_zero, by simpa using (summable_zero : Summable (fun _ : Set (MatP D p) => (0 : ℝ)))⟩
    | some c =>
      have hmat := hS a ha
      let V : Set (MatP D p) → ℂ := fun O => fL M δ T T' p w (some c) ((shE δ T T' p w).symm O)
      have hfV : fL M δ T T' p w (some c) = V ∘ shE δ T T' p w := by
        funext O
        simp only [V, Function.comp_apply, Equiv.symm_apply_apply]
      have hB : BBtop M δ T T' p w (some c) = dfac M δ T T' p w * (M p).BB a c := by simp only [BBtop, ha]
      have key := hO a c (dfac M δ T T' p w) V ?h0 ?h1
      · rw [hfV, hB]
        refine ⟨(Equiv.hasSum_iff (shE δ T T' p w)).2 key.1, ?_⟩
        exact (Equiv.summable_iff (shE δ T T' p w) (f := fun O => ‖V O‖)).2 key.2
      case h0 =>
        intro O hO'
        show fL M δ T T' p w (some c) {Y | Y + shM δ T T' p w ∈ O} = 0
        unfold fL
        rw [if_neg]
        rintro ⟨Y, hY, ⟨w₀, hw₀, xy, hxy⟩, hOY⟩
        rw [ha] at hw₀
        cases hw₀
        apply hO'
        refine ⟨xy, fun i j => ?_, ?_⟩
        · rw [zAt_eq hmat, ← hxy]
          exact add_mem (hY i j) (shM_mem M δ T T' p w i j)
        · have h1 : ∀ Z, Z ∈ O ↔ Z - shM δ T T' p w ∈ kkOrb M p Y := fun Z => by
            rw [← hOY]; simp
          ext Z
          rw [h1, zAt_eq hmat, ← hxy, mem_orbR_iff]
      case h1 =>
        rintro O ⟨xy0, hint0, rfl⟩
        have hL : IsLCls M δ T T' p w {Y | Y + shM δ T T' p w ∈ orbR (M p) (zAt a xy0)} := by
          refine ⟨zAt a xy0 - shM δ T T' p w, fun i j => sub_mem (hint0 i j) (shM_mem M δ T T' p w i j),
            ⟨a, ha, xy0, by rw [zAt_eq hmat, add_sub_cancel_right]⟩, ?_⟩
          ext Y
          have h := mem_orbR_iff M δ T T' p w (zAt a xy0 - shM δ T T' p w) (Y + shM δ T T' p w)
          rw [sub_add_cancel, add_sub_cancel_right] at h
          exact h
        set rep := hL.choose with hrepdef
        have hspec : IntP M p rep ∧ InOrbP δ T T' p w rep ∧
            {Y | Y + shM δ T T' p w ∈ orbR (M p) (zAt a xy0)} = kkOrb M p rep := hL.choose_spec
        obtain ⟨hrepI, ⟨w₀, hw₀, xy1, hrep⟩, hrepO⟩ := hspec
        rw [ha] at hw₀
        cases hw₀
        have hX : ∃ xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep),
            rep = Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 := ⟨xy1, hrep⟩
        have hZ : rep + shM δ T T' p w = Loc.uLow hX.choose.1 * a.mat * Loc.uUp a hX.choose.2 := by
          have h := zAt_eq hmat hX.choose
          unfold zAt at h
          rw [h, ← hX.choose_spec]
        refine ⟨hX.choose, ?_, ?_⟩
        · have hmem : rep ∈ kkOrb M p rep := ⟨1, 1, intLow_one M p, intUp_one M p, by simp⟩
          rw [← hrepO] at hmem
          rw [zAt_eq hmat hX.choose, ← hX.choose_spec]
          exact hmem
        · show fL M δ T T' p w (some c) {Y | Y + shM δ T T' p w ∈ orbR (M p) (zAt a xy0)} = _
          have hr : repL M δ T T' p w {Y | Y + shM δ T T' p w ∈ orbR (M p) (zAt a xy0)} = rep := by
            unfold repL; exact dif_pos hL
          have hph : phL M δ T T' p w rep = dfac M δ T T' p w *
              (M p).psiR (Loc.simpleLow (Loc.uLow hX.choose.1) + Loc.simpleUp (Loc.uUp a hX.choose.2)) := by
            unfold phL; simp only [ha]; rw [dif_pos hX]
          have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
              Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p rep} =
              {xy | zAt a xy ∈ orbR (M p) (zAt a xy0)} := by
            ext xy
            simp only [← hrepO, zAt_eq hmat xy, Set.mem_ofPred_eq]
          have hwt : wtL M δ T T' p w rep = wtZ (M p) a (orbR (M p) (zAt a xy0)) := by
            unfold wtL wtZ muA; simp only [ha]; rw [hset]
          have hZi : ∀ i j, (Loc.uLow hX.choose.1 * a.mat * Loc.uUp a hX.choose.2) i j ∈ (M p).R := by
            intro i j; rw [← hZ]; exact add_mem (hrepI i j) (shM_mem M δ T T' p w i j)
          have hZd : IsUnit (Loc.uLow hX.choose.1 * a.mat * Loc.uUp a hX.choose.2).det := by
            rw [Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det,
              one_mul, mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]
            exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
          have hth : thL M δ T T' p w rep = clsOf (M p) (Loc.uLow hX.choose.1 * a.mat * Loc.uUp a hX.choose.2) := by
            show clsOf (M p) (rep + shM δ T T' p w) = _
            rw [hZ]
          have hbb : (M p).bbIntegrand a c hX.choose =
              ((M p).nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat (M p) _ hZi hZd) (Quotient.out c) : ℂ) *
                (M p).psiR (Loc.simpleLow (Loc.uLow hX.choose.1) + Loc.simpleUp (Loc.uUp a hX.choose.2)) := by
            rw [Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.GG, dif_pos ⟨hZi, hZd⟩]
          have hcl : clsOf (M p) (Loc.uLow hX.choose.1 * a.mat * Loc.uUp a hX.choose.2) =
              some (Quotient.mk _ (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat (M p) _ hZi hZd) : (M p).Cls D.R.rS) := by
            unfold clsOf; rw [dif_pos ⟨hZi, hZd⟩]; rfl
          unfold fL
          rw [if_pos hL, hr, hph, hwt, hth, hcl, hbb, nIso_out]
          erw [nIsoO_some]
          split_ifs with h1 h2 h2
          · ring
          · exact absurd (Option.some.inj h1) h2
          · exact absurd (congrArg some h2) h1
          · simp

end Main

section Assembly

variable {D : Formalism.BasicNotions.D7}

theorem gL_mul (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (c : (M p).Cls D.R.rS) (O : Set (MatP D p)) :
    gL M δ T T' p w (some c) O * ((M p).nAut c : ℂ) = fL M δ T T' p w (some c) O := by
  unfold gL fL
  by_cases hL : IsLCls M δ T T' p w O
  · by_cases ht : thL M δ T T' p w (repL M δ T T' p w O) = some c
    · rw [if_pos ⟨hL, ht⟩, if_pos hL, ht]
      erw [nIsoO_some]
      rw [if_pos rfl]
    · rw [if_neg (fun h => ht h.2), if_pos hL]
      erw [nIsoO_some]
      rw [if_neg ht]
      simp
  · rw [if_neg (fun h => hL h.1), if_neg hL, zero_mul]

theorem gL_hasSum (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (c : (M p).Cls D.R.rS) (hN : (M p).nAut c ≠ 0)
    (hf : HasSum (fL M δ T T' p w (some c)) (BBtop M δ T T' p w (some c)) ∧
      Summable (fun O => ‖fL M δ T T' p w (some c) O‖)) :
    HasSum (gL M δ T T' p w (some c)) (BBtop M δ T T' p w (some c) / Pf.autP M p (some c)) ∧
      Summable (fun O => ‖gL M δ T T' p w (some c) O‖) := by
  have hn : ((M p).nAut c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hg : gL M δ T T' p w (some c) = fun O => fL M δ T T' p w (some c) O / ((M p).nAut c : ℂ) := by
    funext O
    rw [← gL_mul, mul_div_cancel_right₀ _ hn]
  have ha : Pf.autP M p (some c) = ((M p).nAut c : ℂ) := rfl
  rw [hg, ha]
  refine ⟨hf.1.div_const _, ?_⟩
  simp only [norm_div]
  exact hf.2.div_const _

theorem locOrbSum_of (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (u u' : D.what₂.Word) (hS : ∀ p w, ModShift δ (D.mem u).A.T (D.mem u').A.T p w)
    (hO : ∀ (p : PlF D) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (c : (M p).Cls D.R.rS), OrbCut (M p) a c)
    (hN : ∀ p, NAutNe M p) : LocOrbSum M δ u u' := by
  intro w _ p τ
  obtain ⟨h1, h2⟩ := fL_hasSum M δ _ _ p w (hS p w) (hO p) τ
  refine ⟨h1, h2, fun hτ => ?_⟩
  cases τ with
  | none => exact absurd rfl hτ
  | some c => exact gL_hasSum M δ _ _ p w c (hN p c) ⟨h1, h2⟩

theorem nAutNe_of (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D) (hOK : (M p).OK) :
    NAutNe M p := by
  intro c
  haveI := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hD := Formalism.MainNotions.LocalModelPeriodLattices.datum_of_OK (M p) hOK
  have hI : Formalism.DoubleCosetMeasures.IsInt (M p).R ((Quotient.out c).Z.map (M p).R.subtype) := fun i j => ((Quotient.out c).Z i j).2
  have hfin := (Formalism.DoubleCosetMeasures.Final.isoFinite _ (M p).R (Formalism.FourierDecayAlt.P.A5x3.finite_quot hD) _ _ hI (Quotient.out c).unit).2
    ((M p).Cok (Quotient.out c)) ((M p).eCls (Quotient.out c)) (Formalism.MainNotions.LocalOrbitGerms.Cls.lamK (M p) (Quotient.out c))
  haveI : Finite ((M p).Iso (Quotient.out c) (Quotient.out c)) :=
    (Equiv.finite_iff (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv (M p) (Quotient.out c) (Quotient.out c))).2 hfin.to_subtype
  haveI : Nonempty ((M p).Iso (Quotient.out c) (Quotient.out c)) := ⟨⟨LinearEquiv.refl _ _, rfl, fun _ => rfl⟩⟩
  exact Nat.card_pos.ne'

end Assembly

end Formalism.L2.SG.Pf.LocOrbSumPf
