import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

theorem prod_mem_pdPow {b : Base} {L : b.Fun} (T : Thick L) : ∀ (n : ℕ) (f : Fin n → T.B), (∀ k, f k ∈ T.J) →
    ∏ k, f k ∈ T.pdPow n
  | 0, f, _ => by rw [Fin.prod_univ_zero, T.pdPow_zero]; trivial
  | n + 1, f, hf => by
    rw [Fin.prod_univ_succ, Pb.pdPow_eq]
    have := dividedPowerFiltration_mul T.δ 1 n (T.J_le_pdPow_one (hf 0)) (prod_mem_pdPow T n _ fun k => hf k.succ)
    rwa [Nat.add_comm] at this

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem lift_sub_mem (Λ : Lifts q V) {T T' : (inU q V).FullSubcategory} (f : T ⟶ T') (g : Sec q V) :
    f.hom.φ (Λ.v T g) - Λ.v T' g ∈ T'.obj.J := by
  rw [← Ideal.Quotient.eq, Λ.hv T' g]
  have e : Ideal.Quotient.mk T'.obj.J (f.hom.φ (Λ.v T g)) =
      Ideal.quotientMap T'.obj.J f.hom.φ f.hom.hle (Ideal.Quotient.mk T.obj.J (Λ.v T g)) := rfl
  rw [e, Λ.hv T g]
  exact (GlobalTheory.CompanionTheory.GrForm.ev_nat f.hom T.property T'.property g).symm

theorem lift_mul_mem (Λ : Lifts q V) (T : (inU q V).FullSubcategory) (g h : Sec q V) :
    Λ.v T g * Λ.v T h - Λ.v T (g * h) ∈ T.obj.J := by
  rw [← Ideal.Quotient.eq, map_mul, Λ.hv, Λ.hv, Λ.hv]
  exact (map_mul _ g h).symm

theorem comp_φ {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) {i j k : Fin (n + 1)} (hij : i ≤ j)
    (hjk : j ≤ k) (y : (s.obj i).obj.B) :
    (s.map (homOfLE hjk)).hom.φ ((s.map (homOfLE hij)).hom.φ y) = (s.map (homOfLE (hij.trans hjk))).hom.φ y := by
  rw [show (homOfLE (hij.trans hjk) : i ⟶ k) = homOfLE hij ≫ homOfLE hjk from rfl, s.map_comp]
  rfl

def lv (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1)) (x : Sec q V) :
    (s.obj (Fin.last n)).obj.B :=
  (s.map (homOfLE (Fin.le_last i))).hom.φ (Λ.v _ x)

theorem lv_sub_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - Λ.v _ x ∈ (s.obj (Fin.last n)).obj.J :=
  lift_sub_mem Λ _ x

theorem lv_diff_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (i j : Fin (n + 1))
    (x : Sec q V) : lv Λ s i x - lv Λ s j x ∈ (s.obj (Fin.last n)).obj.J := by
  have := sub_mem (lv_sub_mem Λ s i x) (lv_sub_mem Λ s j x)
  rwa [sub_sub_sub_cancel_right] at this

theorem lv_last (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x : Sec q V) :
    lv Λ s (Fin.last n) x = Λ.v _ x := by
  unfold lv
  rw [show (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ from rfl, s.map_id]
  rfl

theorem form_eq (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) :
    Λ.form x₀ x s = Λ.v _ x₀ * ∏ k : Fin n, (lv Λ s k.succ (x k) - lv Λ s k.castSucc (x k)) := rfl

theorem form_mem (Λ : Lifts q V) {n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n) (x₀ : Sec q V)
    (x : Fin n → Sec q V) : Λ.form x₀ x s ∈ (s.obj (Fin.last n)).obj.pdPow n := by
  rw [form_eq]
  exact Ideal.mul_mem_left _ _ (prod_mem_pdPow _ n _ fun k => lv_diff_mem Λ s _ _ _)

theorem form_map (Λ : Lifts q V) {m n : ℕ} (s : ComposableArrows (inU q V).FullSubcategory n)
    (e : Fin (m + 1) → Fin (n + 1)) (he : Monotone e) (x₀ : Sec q V) (x : Fin m → Sec q V) :
    (s.map (homOfLE (Fin.le_last (e (Fin.last m))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)) =
      lv Λ s (e (Fin.last m)) x₀ * ∏ k : Fin m, (lv Λ s (e k.succ) (x k) - lv Λ s (e k.castSucc) (x k)) := by
  rw [Lifts.form, map_mul, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_sub]
  congr 1
  · exact comp_φ s (he (Fin.le_last k.succ)) (Fin.le_last _) _
  · exact comp_φ s (he (Fin.le_last k.castSucc)) (Fin.le_last _) _

theorem key (Λ : Lifts q V) {a a' : ℕ} (g₀ h₀ : Sec q V) (g : Fin a → Sec q V) (h : Fin a' → Sec q V)
    (s : ComposableArrows (inU q V).FullSubcategory (a + a')) :
    (s.map (homOfLE (Fin.le_last (CH.front (rfl : a + a' = a + a') (Fin.last a))))).hom.φ
        (Λ.form g₀ g ((CH.front_mono (rfl : a + a' = a + a')).functor ⋙ s)) *
      (s.map (homOfLE (Fin.le_last (CH.back (rfl : a + a' = a + a') (Fin.last a'))))).hom.φ
        (Λ.form h₀ h ((CH.back_mono (rfl : a + a' = a + a')).functor ⋙ s)) -
      Λ.form (g₀ * h₀) (Fin.append g h) s ∈ (s.obj (Fin.last (a + a'))).obj.pdPow (a + a' + 1) := by
  rw [form_map Λ s _ (CH.front_mono rfl), form_map Λ s _ (CH.back_mono rfl), form_eq Λ s, Fin.prod_univ_add]
  have e1 : ∀ k : Fin a, (Fin.castAdd a' k).succ = CH.front (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.front])
  have e2 : ∀ k : Fin a, (Fin.castAdd a' k).castSucc = CH.front (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.front])
  have e3 : ∀ k : Fin a', (Fin.natAdd a k).succ = CH.back (rfl : a + a' = a + a') k.succ :=
    fun k => Fin.ext (by simp [CH.back]; omega)
  have e4 : ∀ k : Fin a', (Fin.natAdd a k).castSucc = CH.back (rfl : a + a' = a + a') k.castSucc :=
    fun k => Fin.ext (by simp [CH.back])
  have e5 : CH.back (rfl : a + a' = a + a') (Fin.last a') = Fin.last (a + a') := Fin.ext (by simp [CH.back])
  simp only [Fin.append_left, Fin.append_right, e1, e2, e3, e4, e5, lv_last]
  have hF := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a
    (fun k => lv Λ s (CH.front rfl k.succ) (g k) - lv Λ s (CH.front rfl k.castSucc) (g k))
    fun k => lv_diff_mem Λ s _ _ _
  have hB := prod_mem_pdPow (s.obj (Fin.last (a + a'))).obj a'
    (fun k => lv Λ s (CH.back rfl k.succ) (h k) - lv Λ s (CH.back rfl k.castSucc) (h k))
    fun k => lv_diff_mem Λ s _ _ _
  have hl : lv Λ s (CH.front rfl (Fin.last a)) g₀ * Λ.v _ h₀ - Λ.v _ (g₀ * h₀) ∈
      (s.obj (Fin.last (a + a'))).obj.J := by
    have := add_mem (Ideal.mul_mem_right (Λ.v _ h₀) _ (lv_sub_mem Λ s (CH.front rfl (Fin.last a)) g₀))
      (lift_mul_mem Λ _ g₀ h₀)
    convert this using 1
    ring
  have := dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ 1 (a + a')
    ((s.obj (Fin.last (a + a'))).obj.J_le_pdPow_one hl) (dividedPowerFiltration_mul (s.obj (Fin.last (a + a'))).obj.δ a a' hF hB)
  rw [show 1 + (a + a') = a + a' + 1 by omega] at this
  rw [Pb.pdPow_eq]
  convert this using 1
  ring

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto.FormCupProduct

open CrystallineSemistableComparison.Onto Pb HT

variable {K : Type} [Field K] {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens}

theorem term_eq (Λ : Lifts q V) {a n : ℕ}
    (f : CH.Cn (Pb.sq ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι) ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι)) a) (x₀ : Sec q V) (x : Fin a → Sec q V)
    (hf : ∀ s, (show sqM ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι)
      ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι) _ from f s).1 = Ideal.Quotient.mk _ (Λ.form x₀ x s))
    (s : ComposableArrows (inU q V).FullSubcategory n) (e : Fin (a + 1) → Fin (n + 1)) (he : Monotone e) :
    CH.term _ s f e he = sqMk (thFil (smFun Z q) (a : ℤ)) (thFil (smFun Z q) ((a : ℤ) + 1))
      ((s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ (Λ.form x₀ x (he.functor ⋙ s)))
      ((thFil (smFun Z q) (a : ℤ)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom
        (form_mem Λ (he.functor ⋙ s) x₀ x)) := by
  apply Subtype.ext
  exact congrArg (Ideal.quotientMap ((thFil (smFun Z q) ((a : ℤ) + 1)).S (s.obj (Fin.last n)).obj)
    (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom.φ
    (fun z hz => (thFil (smFun Z q) ((a : ℤ) + 1)).map_mem (s.map (homOfLE (Fin.le_last (e (Fin.last a))))).hom hz))
    (hf (he.functor ⋙ s))

end CrystallineSemistableComparison.Onto.FormCupProduct

namespace CrystallineSemistableComparison.Onto

open Pb HT FormCupProduct

theorem formCup_pf : FormCup := by
  intro K _ Z q V a a' g₀ h₀ g h x y hx hy Hx Hy
  let P : CH.Pairing ((inU q V).ι ⋙ G q a) ((inU q V).ι ⋙ G q a') ((inU q V).ι ⋙ G q (a + a')) :=
    ⟨fun T => (grOk (smFun Z q) (rfl : a + a' = a + a')).pair.μ T.obj, fun φ => (grOk (smFun Z q) rfl).pair.nat φ.hom⟩
  obtain ⟨hz, ez⟩ := CrystallineSemistableComparison.P.cup_cls P rfl x y hx hy
  refine ⟨hz, fun Λ => ?_⟩
  obtain ⟨f, hf, ef, hfs⟩ := Hx Λ
  obtain ⟨f', hf', ef', hfs'⟩ := Hy Λ
  obtain ⟨hz', ez'⟩ := CrystallineSemistableComparison.P.cup_cls P rfl f f' hf hf'
  refine ⟨P.cupC rfl f f', hz', ez.symm.trans ((congrArg₂ (P.cup rfl) ef ef').trans ez'), fun s => ?_⟩
  change ((grOk (smFun Z q) (rfl : a + a' = a + a')).mul (CH.term _ s f (CH.front rfl) (CH.front_mono rfl))
    (CH.term _ s f' (CH.back rfl) (CH.back_mono rfl))).1 = _
  rw [term_eq Λ f g₀ g hfs s _ (CH.front_mono rfl), term_eq Λ f' h₀ h hfs' s _ (CH.back_mono rfl), MulOk.mul_mk]
  exact Ideal.Quotient.eq.2 (key Λ g₀ h₀ g h s)

end CrystallineSemistableComparison.Onto
