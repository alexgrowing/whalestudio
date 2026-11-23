import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolarisationOperatorApplyVariable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JointHarmonicOfHookNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HookREqHookProd

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

namespace GlobalTheory.LowRowFock

open MvPolynomial

theorem fock_one {σ : Type} : Formalism.E.fock (1 : MvPolynomial σ ℂ) 1 = 1 := by
  simp [Formalism.E.fock, Formalism.A.mfact]

theorem fock_rename_inj {σ τ : Type} {f : σ → τ} (hf : Function.Injective f) (P P' : MvPolynomial σ ℂ) :
    Formalism.E.fock (rename f P) (rename f P') = Formalism.E.fock P P' := by
  have h := GlobalTheory.JointHarm.fock_rename_mul (g := (fun e : Empty => e.elim : Empty → τ)) hf
    (fun x => x.elim) (fun _ y => y.elim) P P' 1 1
  simpa [fock_one] using h

theorem fock_mul_of_supported {σ : Type} {A B : Set σ} (hAB : Disjoint A B) {P P' Q Q' : MvPolynomial σ ℂ}
    (hP : P ∈ supported ℂ A) (hP' : P' ∈ supported ℂ A) (hQ : Q ∈ supported ℂ B) (hQ' : Q' ∈ supported ℂ B) :
    Formalism.E.fock (P * Q) (P' * Q') = Formalism.E.fock P P' * Formalism.E.fock Q Q' := by
  rw [supported_eq_range_rename] at hP hP' hQ hQ'
  obtain ⟨P₀, rfl⟩ := (AlgHom.mem_range _).mp hP
  obtain ⟨P₁, rfl⟩ := (AlgHom.mem_range _).mp hP'
  obtain ⟨Q₀, rfl⟩ := (AlgHom.mem_range _).mp hQ
  obtain ⟨Q₁, rfl⟩ := (AlgHom.mem_range _).mp hQ'
  rw [GlobalTheory.JointHarm.fock_rename_mul Subtype.val_injective Subtype.val_injective
      (fun x y h => Set.disjoint_left.mp hAB x.2 (h ▸ y.2)),
    fock_rename_inj Subtype.val_injective, fock_rename_inj Subtype.val_injective]

theorem fock_prod_of_supported {σ ι : Type} [DecidableEq ι] (A : ι → Set σ) (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (F G : ι → MvPolynomial σ ℂ) (hF : ∀ i, F i ∈ supported ℂ (A i)) (hG : ∀ i, G i ∈ supported ℂ (A i))
    (s : Finset ι) :
    Formalism.E.fock (∏ i ∈ s, F i) (∏ i ∈ s, G i) = ∏ i ∈ s, Formalism.E.fock (F i) (G i) := by
  induction s using Finset.induction_on with
  | empty => simp [fock_one]
  | insert a s ha ih =>
    have hd : Disjoint (A a) (⋃ i ∈ s, A i) :=
      Set.disjoint_iUnion₂_right.mpr fun i hi => hA (fun e => ha (e ▸ hi))
    have hmem : ∀ H : ι → MvPolynomial σ ℂ, (∀ i, H i ∈ supported ℂ (A i)) →
        ∏ i ∈ s, H i ∈ supported ℂ (⋃ i ∈ s, A i) := fun H hH =>
      Subalgebra.prod_mem _ fun i hi => supported_mono (Set.subset_biUnion_of_mem hi) (hH i)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha,
      fock_mul_of_supported hd (hF a) (hG a) (hmem F hF) (hmem G hG), ih]

theorem rename_mem_supported {σ τ : Type} (f : σ → τ) (s : Set τ) (hs : ∀ x, f x ∈ s) (P : MvPolynomial σ ℂ) :
    rename f P ∈ supported ℂ s := by
  classical
  rw [mem_supported]
  intro v hv
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp (vars_rename f P hv)
  exact hs w

variable {D : D7} {m n : ℕ}

theorem minorPlus_eq (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) (hpn : p ≤ n) (i : Fin p) :
    minorPlus (D := D) (m := m) (n := n) τ (i + 1) =
      rename (fun v : Fin n × Fin p => ((τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor hpn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.topMinor, AlgHom.map_det]
  unfold minorPlus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dif_pos ⟨by omega, by omega⟩]

theorem minorMinus_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hqn : q ≤ n) (i : Fin q) :
    minorMinus (D := D) (m := m) (n := n) τ p (i + 1) =
      rename (fun v : Fin n × Fin q => ((τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1) : FVar D m n))
        (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor hqn i) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.bottomMinor, AlgHom.map_det]
  unfold minorMinus
  congr 1
  ext α β
  have := α.2
  have := β.2
  have := i.2
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, rename_X, varF]
  rw [dif_pos ⟨by omega, by omega⟩]

def embTop (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Fin n × Fin p → FVar D m n :=
  fun v => (τ, ⟨v.2, lt_of_lt_of_le v.2.2 hpm⟩, v.1)

def embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) : Fin n × Fin q → FVar D m n :=
  fun v => (τ, ⟨p + v.2, by have := v.2.2; omega⟩, v.1)

theorem embTop_injective (τ : D.what₂.Tau) {p : ℕ} (hpm : p ≤ m) : Function.Injective (embTop (n := n) τ hpm) := by
  intro x y e
  simp only [embTop, Prod.mk.injEq, Fin.mk.injEq] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embBot_injective (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) :
    Function.Injective (embBot (n := n) τ (q := q) hm) := by
  intro x y e
  simp only [embBot, Prod.mk.injEq, Fin.mk.injEq, add_right_inj] at e
  exact Prod.ext e.2.2 (Fin.ext e.2.1)

theorem embTop_ne_embBot (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (x : Fin n × Fin p) (y : Fin n × Fin q) :
    embTop τ (by omega) x ≠ embBot τ hm y := by
  intro e
  simp only [embTop, embBot, Prod.mk.injEq, Fin.mk.injEq] at e
  have := x.2.2
  omega

theorem minorProduct_rename_mem_supported_place (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (P : MvPolynomial (Fin n × Fin p) ℂ)
    (Q : MvPolynomial (Fin n × Fin q) ℂ) :
    rename (embTop τ (by omega)) P * rename (embBot τ hm) Q ∈ supported ℂ {v : FVar D m n | v.1 = τ} :=
  Subalgebra.mul_mem _ (rename_mem_supported (embTop τ (by omega)) {v : FVar D m n | v.1 = τ} (fun x => by simp [embTop]) P)
    (rename_mem_supported (embBot τ hm) {v : FVar D m n | v.1 = τ} (fun x => by simp [embBot]) Q)

theorem deltaAt_eq (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ) :
    deltaAt (D := D) (m := m) (n := n) τ p ap q am =
      rename (embTop τ (by omega)) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop hpn (fun i : Fin p => ap i)) *
        rename (embBot τ hm) (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom hqn (fun i : Fin q => am i)) := by
  unfold deltaAt GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delTop GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.delBottom
  rw [map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorPlus_eq τ (by omega) hpn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, minorMinus_eq τ hm hqn i]
    congr 1
    try (unfold GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart; split_ifs <;> rfl)

theorem hookOf_eq_hookProd (l : ℕ) (a : ℕ → ℕ) (ha : Antitone a) :
    (hookOf l a : ℂ) = ((GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) : ℚ) : ℂ) := by
  have ha' : ∀ x y, x ≤ y → y < l → a y ≤ a x := fun x y h _ => ha h
  have hant : Antitone (fun i : Fin l => a i) := fun i j h => ha (Fin.le_iff_val_le_val.mp h)
  suffices h : (hookOf l a : ℚ) = GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd (fun i : Fin l => a i) by
    rw [← h]; push_cast; rfl
  rw [GlobalTheory.HookDiagram.hookOf_eq l a ha', GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookProd,
    eq_div_iff (GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos hant).ne']
  have key := congrArg (Nat.cast : ℕ → ℚ) (GlobalTheory.LiftSizeCompare.hookProd_mul l a ha')
  push_cast [Nat.cast_prod] at key
  have hden : (∏ r ∈ Finset.range l, ∏ j ∈ Finset.Ioo r l, ((a r - a j + (j - r) : ℕ) : ℚ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen (fun i : Fin l => a i) := by
    rw [Finset.prod_range, GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen]
    refine Finset.prod_congr rfl fun i _ => ?_
    symm
    refine Finset.prod_bij (fun j _ => (j : ℕ)) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_Ioo.mpr ⟨Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj), j.2⟩
    · intro j _ j' _ e
      exact Fin.ext e
    · intro b hb
      have := Finset.mem_Ioo.mp hb
      exact ⟨⟨b, this.2⟩, Finset.mem_Ioi.mpr (Fin.lt_iff_val_lt_val.mpr this.1), rfl⟩
    · intro j hj
      have hij : (i : ℕ) < j := Fin.lt_iff_val_lt_val.mp (Finset.mem_Ioi.mp hj)
      have h1 : a j ≤ a i := ha hij.le
      rw [Nat.cast_add, Nat.cast_sub h1, Nat.cast_sub hij.le]
      ring
  have hnum : (∏ r ∈ Finset.range l, (((a r + l - 1 - r).factorial : ℕ) : ℚ)) =
      ∏ i : Fin l, (((a i + (l - ((i : ℕ) + 1))).factorial : ℕ) : ℚ) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := i.2
    congr 3
    omega
  rw [← hden, ← hnum]
  exact_mod_cast key

theorem fock_deltaAt (τ : D.what₂.Tau) {p q : ℕ} (hm : p + q ≤ m) (hpn : p ≤ n) (hqn : q ≤ n) (ap am : ℕ → ℕ)
    (hap : Antitone ap) (ham : Antitone am) :
    Formalism.E.fock (deltaAt (D := D) (m := m) (n := n) τ p ap q am) (deltaAt τ p ap q am) =
      (hookOf p ap : ℂ) * (hookOf q am : ℂ) := by
  have hp : Antitone (fun i : Fin p => ap i) := fun i j h => hap (Fin.le_iff_val_le_val.mp h)
  have hq : Antitone (fun i : Fin q => am i) := fun i j h => ham (Fin.le_iff_val_le_val.mp h)
  rw [deltaAt_eq τ hm hpn hqn, GlobalTheory.JointHarm.fock_rename_mul (embTop_injective τ _) (embBot_injective τ hm)
      (embTop_ne_embBot τ hm),
    GlobalTheory.MinorNorm.hookNorm _ _ _ _ hp, GlobalTheory.MinorNorm.hookNormBottom _ _ _ _ hq,
    hookOf_eq_hookProd _ _ hap, hookOf_eq_hookProd _ _ ham]

theorem fock_delta (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ)
    (h1 : ∀ τ, p τ + q τ ≤ m) (h2 : ∀ τ, p τ ≤ n ∧ q τ ≤ n) (h3 : ∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) :
    Formalism.E.fock (Formalism.IndefR.Datum.delta (D := D) (m := m) (n := n) p q ap am) (Formalism.IndefR.Datum.delta p q ap am) =
      ∏ τ, ((hookOf (p τ) (ap τ) : ℂ) * (hookOf (q τ) (am τ) : ℂ)) := by
  classical
  have hmem : ∀ τ, deltaAt (D := D) (m := m) (n := n) τ (p τ) (ap τ) (q τ) (am τ) ∈
      supported ℂ {v : FVar D m n | v.1 = τ} := fun τ => by
    rw [deltaAt_eq τ (h1 τ) (h2 τ).1 (h2 τ).2]
    exact minorProduct_rename_mem_supported_place τ (h1 τ) _ _
  unfold Formalism.IndefR.Datum.delta
  rw [fock_prod_of_supported (fun τ => {v : FVar D m n | v.1 = τ})
    (fun a b hab => Set.disjoint_left.mpr fun v ha hb => hab (ha.symm.trans hb)) _ _ hmem hmem Finset.univ]
  exact Finset.prod_congr rfl fun τ _ =>
    fock_deltaAt τ (h1 τ) (h2 τ).1 (h2 τ).2 _ _ (h3 τ).1 (h3 τ).2

end GlobalTheory.LowRowFock
