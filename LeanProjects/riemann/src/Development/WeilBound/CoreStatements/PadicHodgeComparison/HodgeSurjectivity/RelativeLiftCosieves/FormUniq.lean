import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.LiftsNonempty
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

universe u v

namespace CrystallineSemistableComparison.Onto.FormUniqueness

open CrystallineSemistableComparison.Onto Pb HT CH

section Gen

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C]

def Fm (A : C ⥤ CommAlgCat.{0} R) (ℓ' : Cn (modF A) 0) : ∀ k : ℕ, (Fin k → Cn (modF A) 0) → Cn (modF A) k
  | 0, _ => ℓ'
  | k + 1, ℓ => (mulP A).cupC (p := 1) (q := k) (n := k + 1) (Nat.add_comm 1 k) (d (modF A) 0 (ℓ 0))
      (Fm A ℓ' k fun j => ℓ j.succ)

variable (A : C ⥤ CommAlgCat.{0} R)

theorem Fm_succ (ℓ' : Cn (modF A) 0) (k : ℕ) (ℓ : Fin (k + 1) → Cn (modF A) 0) :
    Fm A ℓ' (k + 1) ℓ = (mulP A).cupC (p := 1) (q := k) (n := k + 1) (Nat.add_comm 1 k) (d (modF A) 0 (ℓ 0))
      (Fm A ℓ' k fun j => ℓ j.succ) := rfl

def tv {m p : ℕ} (s : ComposableArrows C m) (f : Cn (modF A) p) (g : Fin (p + 1) → Fin (m + 1)) (hg : Monotone g) :
    A.obj (s.obj (Fin.last m)) := term (modF A) s f g hg

theorem tv_congr {m p : ℕ} (s : ComposableArrows C m) (f : Cn (modF A) p) {g g' : Fin (p + 1) → Fin (m + 1)}
    (hg : Monotone g) (hg' : Monotone g') (e : ∀ t, (g t : ℕ) = g' t) : tv A s f g hg = tv A s f g' hg' :=
  term_congr _ s f hg hg' (funext fun t => Fin.ext (e t))

theorem tv_cupC {p p' n m : ℕ} (h : p + p' = n) (s : ComposableArrows C m) (f : Cn (modF A) p) (f' : Cn (modF A) p')
    (k : Fin (n + 1) → Fin (m + 1)) (hk : Monotone k) :
    tv A s ((mulP A).cupC h f f') k hk = tv A s f (k ∘ front h) (hk.comp (front_mono h)) *
      tv A s f' (k ∘ back h) (hk.comp (back_mono h)) :=
  CrystallineSemistableComparison.Auxff.term_cupC (mulP A) h s f f' k hk

theorem tv_d {p m : ℕ} (s : ComposableArrows C m) (f : Cn (modF A) p) (g : Fin (p + 2) → Fin (m + 1)) (hg : Monotone g) :
    tv A s (d (modF A) p f) g hg = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
      tv A s f (g ∘ i.succAbove) (hg.comp (Fin.strictMono_succAbove i).monotone) :=
  CrystallineSemistableComparison.Auxff.term_d (modF A) s f g hg

theorem term_Fm (ℓ' : Cn (modF A) 0) : ∀ (k : ℕ) (ℓ : Fin k → Cn (modF A) 0) {m : ℕ} (s : ComposableArrows C m)
    (g : Fin (k + 1) → Fin (m + 1)) (hg : Monotone g),
    tv A s (Fm A ℓ' k ℓ) g hg = tv A s ℓ' (fun _ => g (Fin.last k)) monotone_const *
      ∏ j : Fin k, (tv A s (ℓ j) (fun _ => g j.succ) monotone_const - tv A s (ℓ j) (fun _ => g j.castSucc) monotone_const)
  | 0, ℓ, m, s, g, hg => by
      rw [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      exact tv_congr A s ℓ' hg monotone_const (fun t => by
        rw [show t = Fin.last 0 from Fin.ext (by have := t.isLt; simp only [Fin.val_last]; omega)])
  | k + 1, ℓ, m, s, g, hg => by
      rw [Fm_succ, tv_cupC, tv_d, Fin.sum_univ_two, term_Fm ℓ' k, Fin.prod_univ_succ]
      have ge : ∀ {x y : Fin (k + 1 + 1)}, (x : ℕ) = y → (g x : ℕ) = g y := fun h => by rw [Fin.ext h]
      have t0 : ∀ t : Fin (0 + 1), t = 0 := fun t => Fin.ext (by have := t.isLt; simp only [Fin.val_zero]; omega)
      have e1 : tv A s (ℓ 0) ((g ∘ front (Nat.add_comm 1 k)) ∘ (0 : Fin 2).succAbove)
          ((hg.comp (front_mono _)).comp (Fin.strictMono_succAbove _).monotone) =
          tv A s (ℓ 0) (fun _ => g (0 : Fin (k + 1)).succ) monotone_const :=
        tv_congr A s _ _ _ (fun t => by
          rw [t0 t]; exact ge (by simp [front]))
      have e0 : tv A s (ℓ 0) ((g ∘ front (Nat.add_comm 1 k)) ∘ (1 : Fin 2).succAbove)
          ((hg.comp (front_mono _)).comp (Fin.strictMono_succAbove _).monotone) =
          tv A s (ℓ 0) (fun _ => g (0 : Fin (k + 1)).castSucc) monotone_const :=
        tv_congr A s _ _ _ (fun t => by
          rw [t0 t]; exact ge (by simp [front]))
      have eL : tv A s ℓ' (fun _ => (g ∘ back (Nat.add_comm 1 k)) (Fin.last k)) monotone_const =
          tv A s ℓ' (fun _ => g (Fin.last (k + 1))) monotone_const :=
        tv_congr A s _ _ _ (fun t => ge (by simp [back]; omega))
      have eP : ∀ j : Fin k,
          tv A s (ℓ j.succ) (fun _ => (g ∘ back (Nat.add_comm 1 k)) j.succ) monotone_const -
            tv A s (ℓ j.succ) (fun _ => (g ∘ back (Nat.add_comm 1 k)) j.castSucc) monotone_const =
          tv A s (ℓ j.succ) (fun _ => g j.succ.succ) monotone_const -
            tv A s (ℓ j.succ) (fun _ => g j.succ.castSucc) monotone_const := fun j => by
        rw [tv_congr A s _ _ _ (fun t => show ((g ∘ back (Nat.add_comm 1 k)) j.succ : ℕ) = (g j.succ.succ : ℕ) from
              ge (by simp [back]; omega)),
          tv_congr A s _ _ _ (fun t => show ((g ∘ back (Nat.add_comm 1 k)) j.castSucc : ℕ) = (g j.succ.castSucc : ℕ) from
              ge (by simp [back]; omega))]
      rw [e1, e0, eL, Finset.prod_congr rfl fun j _ => eP j]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
      ring

end Gen

section Spec

variable {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens)

abbrev AF : (inU q V).FullSubcategory ⥤ CommAlgCat.{0} K := (inU q V).ι ⋙ thA (smFun Z q)

def InF {n : ℕ} (r : ℕ) (x : Cn (modF (AF q V)) n) : Prop :=
  ∀ s : ComposableArrows (inU q V).FullSubcategory n,
    (x s : (s.obj (Fin.last n)).obj.B) ∈ (s.obj (Fin.last n)).obj.pdPow r

variable {q V}

theorem tv_mem {m p r : ℕ} (s : ComposableArrows (inU q V).FullSubcategory m) (f : Cn (modF (AF q V)) p)
    (hf : InF q V r f) (g : Fin (p + 1) → Fin (m + 1)) (hg : Monotone g) :
    (tv (AF q V) s f g hg : (s.obj (Fin.last m)).obj.B) ∈ (s.obj (Fin.last m)).obj.pdPow r :=
  dividedPowerFiltration_map (s.map (homOfLE (Fin.le_last (g (Fin.last p))))).hom.dp r (hf (hg.functor ⋙ s))

theorem InF.lev0 {n : ℕ} (x : Cn (modF (AF q V)) n) : InF q V 0 x := fun s => by
  rw [Thick.pdPow_zero]; trivial

theorem InF.zero {n r : ℕ} : InF q V r (0 : Cn (modF (AF q V)) n) := fun s => Submodule.zero_mem _

theorem InF.add {n r : ℕ} {x y : Cn (modF (AF q V)) n} (hx : InF q V r x) (hy : InF q V r y) : InF q V r (x + y) :=
  fun s => Submodule.add_mem _ (hx s) (hy s)

theorem InF.neg {n r : ℕ} {x : Cn (modF (AF q V)) n} (hx : InF q V r x) : InF q V r (-x) :=
  fun s => Submodule.neg_mem _ (hx s)

theorem InF.sub {n r : ℕ} {x y : Cn (modF (AF q V)) n} (hx : InF q V r x) (hy : InF q V r y) : InF q V r (x - y) :=
  fun s => Submodule.sub_mem _ (hx s) (hy s)

theorem InF.zsmul {n r : ℕ} (c : ℤ) {x : Cn (modF (AF q V)) n} (hx : InF q V r x) : InF q V r (c • x) :=
  fun s => zsmul_mem (hx s) c

theorem InF.cob {n r : ℕ} {x : Cn (modF (AF q V)) n} (hx : InF q V r x) : InF q V r (d (modF (AF q V)) n x) := fun s => by
  have e : @Eq (s.obj (Fin.last (n + 1))).obj.B (d (modF (AF q V)) n x s) (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      (tv (AF q V) s x i.succAbove (Fin.strictMono_succAbove i).monotone : (s.obj (Fin.last (n + 1))).obj.B)) := rfl
  rw [e]
  refine Ideal.sum_mem ((s.obj (Fin.last (n + 1))).obj.pdPow r) fun i _ => ?_
  exact zsmul_mem (tv_mem s x hx _ _) _

theorem InF.cup {p p' n r r' r'' : ℕ} (h : p + p' = n) (hr : r + r' = r'') {f : Cn (modF (AF q V)) p}
    {f' : Cn (modF (AF q V)) p'} (hf : InF q V r f) (hf' : InF q V r' f') :
    InF q V r'' ((mulP (AF q V)).cupC h f f') := fun s => by
  subst hr
  have := dividedPowerFiltration_mul (s.obj (Fin.last n)).obj.δ r r' (tv_mem s f hf (front h) (front_mono h))
    (tv_mem s f' hf' (back h) (back_mono h))
  exact this

def cz (v : ∀ T : (inU q V).FullSubcategory, T.obj.B) : Cn (modF (AF q V)) 0 := fun s => v (s.obj (Fin.last 0))

def IsL (g : Sec q V) (v : ∀ T : (inU q V).FullSubcategory, T.obj.B) : Prop :=
  ∀ T, Ideal.Quotient.mk T.obj.J (v T) =
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g

theorem tv_cz_last {m : ℕ} (v : ∀ T : (inU q V).FullSubcategory, T.obj.B) (s : ComposableArrows (inU q V).FullSubcategory m) :
    (tv (AF q V) s (cz v) (fun _ => Fin.last m) monotone_const : (s.obj (Fin.last m)).obj.B) = v (s.obj (Fin.last m)) := by
  have e : s.map (homOfLE (Fin.le_last (Fin.last m))) = 𝟙 _ := by rw [← s.map_id]; rfl
  show (s.map (homOfLE (Fin.le_last (Fin.last m)))).hom.φ (v (s.obj (Fin.last m))) = _
  rw [e]
  rfl

theorem mk_tv {g : Sec q V} {v : ∀ T : (inU q V).FullSubcategory, T.obj.B} (hv : IsL g v) {m : ℕ}
    (s : ComposableArrows (inU q V).FullSubcategory m) (k : Fin (0 + 1) → Fin (m + 1)) (hk : Monotone k) :
    Ideal.Quotient.mk (s.obj (Fin.last m)).obj.J (tv (AF q V) s (cz v) k hk) =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (s.obj (Fin.last m)).obj
        (s.obj (Fin.last m)).property g := by
  have e : Ideal.Quotient.mk (s.obj (Fin.last m)).obj.J (tv (AF q V) s (cz v) k hk) =
      Ideal.quotientMap _ (s.map (homOfLE (Fin.le_last (k (Fin.last 0))))).hom.φ
        (s.map (homOfLE (Fin.le_last (k (Fin.last 0))))).hom.hle
        (Ideal.Quotient.mk (s.obj (k (Fin.last 0))).obj.J (v (s.obj (k (Fin.last 0))))) := rfl
  rw [e, hv]
  exact (GlobalTheory.CompanionTheory.GrForm.ev_nat (s.map (homOfLE (Fin.le_last (k (Fin.last 0))))).hom _ _ g).symm

theorem dcz_mem {g : Sec q V} {v : ∀ T : (inU q V).FullSubcategory, T.obj.B} (hv : IsL g v) :
    InF q V 1 (d (modF (AF q V)) 0 (cz v)) := fun s => by
  have e : @Eq (s.obj (Fin.last 1)).obj.B (d (modF (AF q V)) 0 (cz v) s) (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
      (tv (AF q V) s (cz v) i.succAbove (Fin.strictMono_succAbove i).monotone : (s.obj (Fin.last 1)).obj.B)) := rfl
  rw [e, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, ← sub_eq_add_neg]
  exact Thick.J_le_pdPow_one _ (Ideal.Quotient.eq.1 ((mk_tv hv s _ _).trans (mk_tv hv s _ _).symm))

theorem czdiff_mem {g : Sec q V} {v v' : ∀ T : (inU q V).FullSubcategory, T.obj.B} (hv : IsL g v) (hv' : IsL g v') :
    InF q V 1 (cz v' - cz v) := fun s =>
  Thick.J_le_pdPow_one _ (Ideal.Quotient.eq.1 ((hv' _).trans (hv _).symm))

theorem Fm_mem (ℓ' : Cn (modF (AF q V)) 0) : ∀ (k : ℕ) (ℓ : Fin k → Cn (modF (AF q V)) 0),
    (∀ j, InF q V 1 (d _ 0 (ℓ j))) → InF q V k (Fm (AF q V) ℓ' k ℓ)
  | 0, ℓ, _ => InF.lev0 _
  | k + 1, ℓ, hℓ => InF.cup _ (Nat.add_comm 1 k) (hℓ 0) (Fm_mem ℓ' k _ fun j => hℓ j.succ)

theorem dFm_mem (ℓ' : Cn (modF (AF q V)) 0) (h₀ : InF q V 1 (d _ 0 ℓ')) : ∀ (k : ℕ) (ℓ : Fin k → Cn (modF (AF q V)) 0),
    (∀ j, InF q V 1 (d _ 0 (ℓ j))) → InF q V (k + 1) (d _ k (Fm (AF q V) ℓ' k ℓ))
  | 0, ℓ, _ => h₀
  | k + 1, ℓ, hℓ => by
    have e := CrystallineSemistableComparison.P.leibniz (mulP (AF q V)) (Nat.add_comm 1 k) (d _ 0 (ℓ 0)) (Fm (AF q V) ℓ' k fun j => ℓ j.succ)
    have hdd : d (modF (AF q V)) 1 (d (modF (AF q V)) 0 (ℓ 0)) = 0 := d_d _ 0 _
    rw [Fm_succ, e, hdd, map_zero, LinearMap.zero_apply, zero_add]
    exact InF.zsmul _ (InF.cup _ (by omega) (hℓ 0) (dFm_mem ℓ' h₀ k _ fun j => hℓ j.succ))

theorem Fm_diff (ℓ₀ ℓ₀' : Cn (modF (AF q V)) 0) (hw₀ : InF q V 1 (ℓ₀' - ℓ₀)) (hd₀' : InF q V 1 (d _ 0 ℓ₀')) :
    ∀ (m : ℕ) (ℓ ℓ' : Fin (m + 1) → Cn (modF (AF q V)) 0), (∀ j, InF q V 1 (d _ 0 (ℓ j))) →
      (∀ j, InF q V 1 (d _ 0 (ℓ' j))) → (∀ j, InF q V 1 (ℓ' j - ℓ j)) →
      ∃ (h : Cn (modF (AF q V)) m) (r : Cn (modF (AF q V)) (m + 1)),
        Fm (AF q V) ℓ₀' (m + 1) ℓ' - Fm (AF q V) ℓ₀ (m + 1) ℓ = d _ m h + r ∧ InF q V (m + 1) h ∧ InF q V (m + 2) r := by
  intro m
  induction m with
  | zero =>
    intro ℓ ℓ' hℓ hℓ' hw
    have L1 : d (modF (AF q V)) 0 ((mulP (AF q V)).cupC (p := 0) (q := 0) (n := 0) rfl (ℓ' 0 - ℓ 0) ℓ₀') =
        (mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0) (d _ 0 (ℓ' 0 - ℓ 0)) ℓ₀' +
        (mulP (AF q V)).cupC (p := 0) (q := 1) (n := 0 + 1) (by omega) (ℓ' 0 - ℓ 0) (d _ 0 ℓ₀') := by
      have := CrystallineSemistableComparison.P.leibniz (mulP (AF q V)) (p := 0) (q := 0) (n := 0) rfl (ℓ' 0 - ℓ 0) ℓ₀'
      rw [pow_zero, one_smul] at this
      exact this
    refine ⟨(mulP (AF q V)).cupC (p := 0) (q := 0) (n := 0) rfl (ℓ' 0 - ℓ 0) ℓ₀',
      -(mulP (AF q V)).cupC (p := 0) (q := 1) (n := 0 + 1) (by omega) (ℓ' 0 - ℓ 0) (d _ 0 ℓ₀') +
        (mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0) (d _ 0 (ℓ 0)) (ℓ₀' - ℓ₀), ?_, ?_, ?_⟩
    · show (mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0) (d _ 0 (ℓ' 0)) ℓ₀' -
          (mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0) (d _ 0 (ℓ 0)) ℓ₀ = _
      rw [L1, map_sub (d (modF (AF q V)) 0) (ℓ' 0) (ℓ 0),
        map_sub ((mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0)), LinearMap.sub_apply,
        map_sub ((mulP (AF q V)).cupC (p := 1) (q := 0) (n := 0 + 1) (Nat.add_comm 1 0) (d _ 0 (ℓ 0)))]
      abel
    · exact InF.cup _ (by omega) (hw 0) (InF.lev0 _)
    · exact (InF.cup _ (by omega) (hw 0) hd₀').neg.add (InF.cup _ (by omega) (hℓ 0) hw₀)
  | succ m ih =>
    intro ℓ ℓ' hℓ hℓ' hw
    obtain ⟨h₁, r₁, e₁, hh₁, hr₁⟩ := ih (fun j => ℓ j.succ) (fun j => ℓ' j.succ) (fun j => hℓ j.succ)
      (fun j => hℓ' j.succ) (fun j => hw j.succ)
    have L1 : d (modF (AF q V)) (m + 1) ((mulP (AF q V)).cupC (p := 0) (q := m + 1) (n := m + 1) (Nat.zero_add _)
        (ℓ' 0 - ℓ 0) (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ)) =
        (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ' 0 - ℓ 0))
          (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ) +
        (mulP (AF q V)).cupC (p := 0) (q := m + 1 + 1) (n := m + 1 + 1) (Nat.zero_add _) (ℓ' 0 - ℓ 0)
          (d _ (m + 1) (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ)) := by
      have := CrystallineSemistableComparison.P.leibniz (mulP (AF q V)) (p := 0) (q := m + 1) (n := m + 1) (Nat.zero_add _) (ℓ' 0 - ℓ 0)
        (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ)
      rw [pow_zero, one_smul] at this
      exact this
    have L2 : d (modF (AF q V)) (m + 1) ((mulP (AF q V)).cupC (p := 1) (q := m) (n := m + 1) (Nat.add_comm 1 m)
        (d _ 0 (ℓ 0)) h₁) =
        -(mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0)) (d _ m h₁) := by
      have := CrystallineSemistableComparison.P.leibniz (mulP (AF q V)) (p := 1) (q := m) (n := m + 1) (Nat.add_comm 1 m) (d _ 0 (ℓ 0)) h₁
      have hdd : d (modF (AF q V)) 1 (d (modF (AF q V)) 0 (ℓ 0)) = 0 := d_d _ 0 _
      rw [hdd, map_zero, LinearMap.zero_apply] at this
      rw [this, pow_one, neg_smul, one_smul]
      exact zero_add _
    have key : (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0))
          (Fm (AF q V) ℓ₀ (m + 1) fun j => ℓ j.succ) =
        (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0))
          (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ) -
        ((mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0)) (d _ m h₁) +
          (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0)) r₁) := by
      rw [← map_add ((mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1))
        (d _ 0 (ℓ 0))), ← e₁, map_sub]
      abel
    refine ⟨(mulP (AF q V)).cupC (p := 0) (q := m + 1) (n := m + 1) (Nat.zero_add _) (ℓ' 0 - ℓ 0)
        (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ) -
        (mulP (AF q V)).cupC (p := 1) (q := m) (n := m + 1) (Nat.add_comm 1 m) (d _ 0 (ℓ 0)) h₁,
      -(mulP (AF q V)).cupC (p := 0) (q := m + 1 + 1) (n := m + 1 + 1) (Nat.zero_add _) (ℓ' 0 - ℓ 0)
          (d _ (m + 1) (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ)) +
        (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0)) r₁,
      ?_, ?_, ?_⟩
    · show (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ' 0))
          (Fm (AF q V) ℓ₀' (m + 1) fun j => ℓ' j.succ) -
          (mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1)) (d _ 0 (ℓ 0))
          (Fm (AF q V) ℓ₀ (m + 1) fun j => ℓ j.succ) = _
      rw [key, map_sub (d (modF (AF q V)) (m + 1)), L1, L2, map_sub (d (modF (AF q V)) 0) (ℓ' 0) (ℓ 0),
        map_sub ((mulP (AF q V)).cupC (p := 1) (q := m + 1) (n := m + 1 + 1) (Nat.add_comm 1 (m + 1))),
        LinearMap.sub_apply]
      abel
    · exact (InF.cup _ (by omega) (hw 0) (Fm_mem ℓ₀' (m + 1) _ fun j => hℓ' j.succ)).sub
        (InF.cup _ (by omega) (hℓ 0) hh₁)
    · exact (InF.cup _ (by omega) (hw 0) (dFm_mem ℓ₀' hd₀' (m + 1) _ fun j => hℓ' j.succ)).neg.add
        (InF.cup _ (by omega) (hℓ 0) hr₁)

end Spec

section Quot

variable {K : Type} [Field K] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens)

abbrev SqF (a : ℕ) : (inU q V).FullSubcategory ⥤ ModuleCat.{0} K :=
  sq ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι) ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι)

variable {q V}

def mkC {n a : ℕ} (z : Cn (modF (AF q V)) n) (hz : InF q V a z) : Cn (SqF q V a) n :=
  fun s => sqMk _ _ (z s) (hz s)

theorem InF.anti {n r r' : ℕ} (h : r ≤ r') {x : Cn (modF (AF q V)) n} (hx : InF q V r' x) : InF q V r x :=
  fun s => Thick.pdPow_anti _ h (hx s)

theorem mkC_congr {n a : ℕ} {z z' : Cn (modF (AF q V)) n} (e : z = z') (hz : InF q V a z) (hz' : InF q V a z') :
    mkC z hz = mkC z' hz' := by
  subst e; rfl

theorem mkC_sub {n a : ℕ} (z z' : Cn (modF (AF q V)) n) (hz : InF q V a z) (hz' : InF q V a z') :
    mkC (z - z') (hz.sub hz') = mkC z hz - mkC z' hz' :=
  funext fun s => Subtype.ext (map_sub (Ideal.Quotient.mk ((s.obj (Fin.last n)).obj.pdPow ((a : ℤ) + 1).toNat))
    (z s : (s.obj (Fin.last n)).obj.B) (z' s))

theorem mkC_add {n a : ℕ} (z z' : Cn (modF (AF q V)) n) (hz : InF q V a z) (hz' : InF q V a z') :
    mkC (z + z') (hz.add hz') = mkC z hz + mkC z' hz' :=
  funext fun s => Subtype.ext (map_add (Ideal.Quotient.mk ((s.obj (Fin.last n)).obj.pdPow ((a : ℤ) + 1).toNat))
    (z s : (s.obj (Fin.last n)).obj.B) (z' s))

theorem mkC_eq_zero {n a : ℕ} (z : Cn (modF (AF q V)) n) (hz : InF q V a z) (hz' : InF q V (a + 1) z) :
    mkC z hz = 0 := by
  funext s
  apply Subtype.ext
  show Ideal.Quotient.mk ((s.obj (Fin.last n)).obj.pdPow ((a : ℤ) + 1).toNat) (z s) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  show (z s : (s.obj (Fin.last n)).obj.B) ∈ (s.obj (Fin.last n)).obj.pdPow ((a : ℤ) + 1).toNat
  rw [show ((a : ℤ) + 1).toNat = a + 1 by omega]
  exact hz' s

theorem d_mkC {n a : ℕ} (z : Cn (modF (AF q V)) n) (hz : InF q V a z) :
    d (SqF q V a) n (mkC z hz) = mkC (d _ n z) hz.cob := by
  funext s
  have e : d (SqF q V a) n (mkC z hz) s = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
      term (SqF q V a) s (mkC z hz) i.succAbove (Fin.strictMono_succAbove i).monotone := rfl
  rw [e]
  apply Subtype.ext
  rw [Submodule.coe_sum]
  show _ = Ideal.Quotient.mk _ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
    (tv (AF q V) s z i.succAbove (Fin.strictMono_succAbove i).monotone : (s.obj (Fin.last (n + 1))).obj.B))
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  rfl

theorem mkC_cocycle {a : ℕ} (z : Cn (modF (AF q V)) a) (hz : InF q V a z) (hd : InF q V (a + 1) (d _ a z)) :
    d (SqF q V a) a (mkC z hz) = 0 := by
  rw [d_mkC]
  exact mkC_eq_zero _ _ hd

variable (q V) in

abbrev FL (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) : Cn (modF (AF q V)) a :=
  Fm (AF q V) (cz fun T => Λ.v T g₀) a fun j => cz fun T => Λ.v T (g j)

theorem isL (Λ : Lifts q V) (x : Sec q V) : IsL x (fun T => Λ.v T x) := fun T => Λ.hv T x

theorem FL_mem (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) : InF q V a (FL q V Λ g₀ g) :=
  Fm_mem _ a _ fun j => dcz_mem (isL Λ (g j))

theorem FL_dmem (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) :
    InF q V (a + 1) (d _ a (FL q V Λ g₀ g)) :=
  dFm_mem _ (dcz_mem (isL Λ g₀)) a _ fun j => dcz_mem (isL Λ (g j))

variable (q V) in

def clsL (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) : CH.H (SqF q V a) a :=
  (CH.cx (SqF q V a)).cls (mkC (FL q V Λ g₀ g) (FL_mem Λ g₀ g)) (mkC_cocycle _ _ (FL_dmem Λ g₀ g))

theorem clsL_eq (Λ Λ' : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) :
    clsL q V Λ g₀ g = clsL q V Λ' g₀ g := by
  unfold clsL
  rw [(CrystallineSemistableComparison.P.cls_surj (CH.cx (SqF q V a)) a).2.2.1]
  cases a with
  | zero =>
    have h1 : InF q V 1 (FL q V Λ g₀ g - FL q V Λ' g₀ g) := czdiff_mem (isL Λ' g₀) (isL Λ g₀)
    rw [← mkC_sub, mkC_eq_zero _ _ h1]
    exact zero_mem _
  | succ m =>
    obtain ⟨h, r, e, hh, hr⟩ := Fm_diff (cz fun T => Λ'.v T g₀) (cz fun T => Λ.v T g₀)
      (czdiff_mem (isL Λ' g₀) (isL Λ g₀)) (dcz_mem (isL Λ g₀)) m (fun j => cz fun T => Λ'.v T (g j))
      (fun j => cz fun T => Λ.v T (g j)) (fun j => dcz_mem (isL Λ' (g j))) (fun j => dcz_mem (isL Λ (g j)))
      (fun j => czdiff_mem (isL Λ' (g j)) (isL Λ (g j)))
    have key : mkC (FL q V Λ g₀ g) (FL_mem Λ g₀ g) - mkC (FL q V Λ' g₀ g) (FL_mem Λ' g₀ g) =
        d (SqF q V (m + 1)) m (mkC h hh) := by
      rw [← mkC_sub, mkC_congr e ((FL_mem Λ g₀ g).sub (FL_mem Λ' g₀ g)) (hh.cob.add (InF.anti (by omega) hr)),
        mkC_add (d _ m h) r hh.cob (InF.anti (by omega) hr),
        mkC_eq_zero r (InF.anti (by omega) hr) hr, add_zero, d_mkC]
    rw [key]
    exact ⟨mkC h hh, rfl⟩

theorem form_eq (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V)
    (s : ComposableArrows (inU q V).FullSubcategory a) :
    Λ.form g₀ g s = (FL q V Λ g₀ g s : (s.obj (Fin.last a)).obj.B) := by
  have e1 := CrystallineSemistableComparison.Auxff.term_id (modF (AF q V)) s (FL q V Λ g₀ g) id monotone_id (fun _ => rfl)
  have e2 := term_Fm (AF q V) (cz fun T => Λ.v T g₀) a (fun j => cz fun T => Λ.v T (g j)) s id monotone_id
  have e3 : (FL q V Λ g₀ g s : (s.obj (Fin.last a)).obj.B) = tv (AF q V) s (FL q V Λ g₀ g) id monotone_id :=
    e1.symm
  rw [e3, e2]
  simp only [id]
  rw [tv_cz_last]
  rfl

theorem isForm_clsL (Λ₀ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) :
    IsForm q V g₀ g (clsL q V Λ₀ g₀ g) := fun Λ =>
  ⟨mkC (FL q V Λ g₀ g) (FL_mem Λ g₀ g), mkC_cocycle _ _ (FL_dmem Λ g₀ g), clsL_eq Λ₀ Λ g₀ g,
    fun s => congrArg (Ideal.Quotient.mk _) (form_eq Λ g₀ g s).symm⟩

end Quot

end CrystallineSemistableComparison.Onto.FormUniqueness

namespace CrystallineSemistableComparison.Onto

open FormUniqueness

theorem formUniq_pf : FormUniq := by
  intro K _ Z q V
  refine ⟨OmegaRestriction.lifts_nonempty q V, fun a g₀ g => ?_⟩
  obtain ⟨Λ₀⟩ := OmegaRestriction.lifts_nonempty q V
  exact ⟨clsL q V Λ₀ g₀ g, isForm_clsL Λ₀ g₀ g, fun c hc => OmegaRestriction.form_uniq q hc (isForm_clsL Λ₀ g₀ g)⟩

end CrystallineSemistableComparison.Onto
