import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CDelta

variable {l : ℕ} [hl : Fact l.Prime] {L Q : Type} [CommRing L] [CommRing Q] {i : L →+* Q} {J : Ideal L}

omit hl in

theorem smul_top_eq (n : ℕ) : ((J.map i) ^ n • ⊤ : Submodule Q Q) = (J ^ n).map i := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

omit hl in

theorem eq_of_forall (hc : IsCompl i J) {u v : Q} (h : ∀ n, u - v ∈ (J ^ n).map i) : u = v := by
  refine sub_eq_zero.1 (hc.complete.toIsHausdorff.haus (u - v) fun n => ?_)
  rw [SModEq.sub_mem, sub_zero, smul_top_eq]; exact h n

omit hl in
theorem mem_succ {x : Q} {n : ℕ} (h : x ∈ (J ^ (n + 1)).map i) : x ∈ (J ^ n).map i :=
  Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) h

theorem key (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) {x : Q} {a b : L} {n : ℕ}
    (ha : x - i a ∈ (J ^ (n + 1)).map i) (hb : x - i b ∈ (J ^ (n + 1)).map i) :
    i (D.δ a) - i (D.δ b) ∈ (J ^ n).map i := by
  have hab : a - b ∈ J ^ (n + 1) := hc.ker _ _ (by
    have := sub_mem hb ha
    rw [map_sub]; convert this using 1; ring)
  have h := GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ l L D J hlJ n b (a - b) hab
  rw [add_sub_cancel] at h
  rw [← map_sub]; exact Ideal.mem_map_of_mem _ h

theorem exists_lim (hc : IsCompl i J) (hlJ : (l : L) ∈ J) (D : Delta l L) (x : Q) :
    ∃ z : Q, ∀ (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i → z - i (D.δ a) ∈ (J ^ n).map i := by
  choose ap hap using hc.surj x
  obtain ⟨z, hz⟩ := hc.complete.toIsPrecomplete.prec (f := fun n => i (D.δ (ap (n + 1)))) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_top_eq]
    exact key hc hlJ D (hap (m + 1)) (Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hap (n + 1)))
  refine ⟨z, fun n a ha => ?_⟩
  have h1 := hz n
  rw [SModEq.sub_mem, smul_top_eq] at h1
  have h2 := key hc hlJ D (hap (n + 1)) ha
  have := sub_mem h2 h1
  convert this using 1; ring

end GlobalTheory.BSP.CDelta

open GlobalTheory.BSP.CDelta in

theorem GlobalTheory.BSP.exists_delta_completion : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q]
    (i : L →+* Q) (J : Ideal L), IsCompl i J → (l : L) ∈ J → ∀ D : Delta l L, ∃ D' : Delta l Q, IsδMap D D' i := by
  intro l _ L _ Q _ i J hc hlJ D
  choose d hd using exists_lim hc hlJ D
  have sep : ∀ u v : W2 l Q, (∀ n, W2.map (Ideal.Quotient.mk ((J ^ n).map i)) u =
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) v) → u = v := by
    intro u v h
    have h1 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.fst = Ideal.Quotient.mk ((J ^ n).map i) v.fst :=
      fun n => congrArg W2.fst (h n)
    have h2 : ∀ n, Ideal.Quotient.mk ((J ^ n).map i) u.snd = Ideal.Quotient.mk ((J ^ n).map i) v.snd :=
      fun n => congrArg W2.snd (h n)
    exact W2.ext (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h1 n))
      (eq_of_forall hc fun n => Ideal.Quotient.eq.1 (h2 n))
  have ap : ∀ (x : Q) (n : ℕ) (a : L), x - i a ∈ (J ^ (n + 1)).map i →
      W2.map (Ideal.Quotient.mk ((J ^ n).map i)) (⟨x, d x⟩ : W2 l Q) =
        W2.map ((Ideal.Quotient.mk ((J ^ n).map i)).comp i) (deltaSectionToWittLengthTwo D a) := by
    intro x n a ha
    have h1 : Ideal.Quotient.mk ((J ^ n).map i) x = Ideal.Quotient.mk ((J ^ n).map i) (i a) :=
      Ideal.Quotient.eq.2 (mem_succ ha)
    have h2 : Ideal.Quotient.mk ((J ^ n).map i) (d x) = Ideal.Quotient.mk ((J ^ n).map i) (i (D.δ a)) :=
      Ideal.Quotient.eq.2 (hd x n a ha)
    exact W2.ext h1 h2
  let s : Q →+* W2 l Q :=
    { toFun := fun x => ⟨x, d x⟩
      map_one' := sep _ _ fun n => by
        rw [ap 1 n 1 (by simp), map_one, map_one, map_one]
      map_zero' := sep _ _ fun n => by
        rw [ap 0 n 0 (by simp), map_zero, map_zero, map_zero]
      map_add' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x + y - i (a + b) ∈ (J ^ (n + 1)).map i := by
          rw [map_add]; convert add_mem ha hb using 1; ring
        show W2.map _ (⟨x + y, d (x + y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) + ⟨y, d y⟩)
        rw [ap _ n _ hab, map_add (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_add (deltaSectionToWittLengthTwo D),
          map_add]
      map_mul' := fun x y => sep _ _ fun n => by
        obtain ⟨a, ha⟩ := hc.surj x (n + 1)
        obtain ⟨b, hb⟩ := hc.surj y (n + 1)
        have hab : x * y - i (a * b) ∈ (J ^ (n + 1)).map i := by
          have : x * y - i (a * b) = y * (x - i a) + i a * (y - i b) := by rw [map_mul]; ring
          rw [this]; exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
        show W2.map _ (⟨x * y, d (x * y)⟩ : W2 l Q) = W2.map _ ((⟨x, d x⟩ : W2 l Q) * ⟨y, d y⟩)
        rw [ap _ n _ hab, map_mul (W2.map (Ideal.Quotient.mk _)), ap x n a ha, ap y n b hb, map_mul (deltaSectionToWittLengthTwo D),
          map_mul] }
  refine ⟨deltaStructureOfWittLengthTwoSection s fun _ => rfl, fun a => ?_⟩
  show i (D.δ a) = d (i a)
  exact (eq_of_forall hc fun n => hd (i a) n a (by simp)).symm
