import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
import BuildAid.D3

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZSwap

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {r r' N : ℕ} (hr : r = r') (v : Fin r → IrrGL k) (w : Fin r' → IrrGL k)
    (hvw : ∀ i, v i = w (Fin.cast hr i)) (hv : ∑ a, (v a).1 = N) (hw : ∑ a, (w a).1 = N) :
    Nonempty ((prodIrr v hv).Equiv (prodIrr w hw)) := by
  subst hr
  have e : v = w := funext fun i => (hvw i).trans (congrArg w (Fin.ext rfl))
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem flatten {s h N : ℕ} (t : Fin s → ℕ) (u : ∀ a, Fin (t a) → IrrGL k) (d : Fin s → ℕ)
    (hd : ∀ a, ∑ b, (u a b).1 = d a) (hN : ∑ a, d a = N) (F : Fin h ≃o Σₗ a, Fin (t a))
    (x : Fin h → IrrGL k) (hx : ∀ c, u (ofLex (F c)).1 (ofLex (F c)).2 = x c) (hxN : ∑ a, (x a).1 = N) :
    Nonempty ((multiProd (stdBlocks d hN) fun a => prodIrr (u a) (hd a)).Equiv (prodIrr x hxN)) := by
  have e : (fun c => u (ofLex (F c)).1 (ofLex (F c)).2) = x := funext hx
  subst e
  have hS := GlobalTheory.SmGL.Stages.stages_equiv (k := k) s d t (fun a b => (u a b).1)
    (fun a => stdBlocks (fun b => (u a b).1) (hd a)) (fun a b => (u a b).2.rep.V) (fun a b => (u a b).rep)
    (Fin N) (stdBlocks d hN)
  refine Exists.elim hS fun E0 hχ => ?_
  let E : (Σ c : Fin h, Fin (u (ofLex (F c)).1 (ofLex (F c)).2).1) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (u (ofLex c).1 (ofLex c).2).1) F.toEquiv).trans E0
  have hω := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F F.strictMono F.surjective E0 E
    (fun _ _ => rfl) fun c => (u (ofLex c).1 (ofLex c).2).rep
  refine hχ.elim fun χ => hω.elim fun ω => ?_
  refine (GlobalTheory.ProdReorder.multiProd_placing (k := k) E (stdBlocks (fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).1) hxN)
    fun c => (u (ofLex (F c)).1 (ofLex (F c)).2).rep).elim fun p => ?_
  exact ⟨(χ.trans ω).trans p⟩

def grp (h j : ℕ) : Fin 3 → ℕ := ![j, 2, h - (j + 2)]

def off (j : ℕ) : Fin 3 → ℕ := ![0, j, j + 2]

theorem off_add_grp_le {h j : ℕ} (hj : j + 1 < h) (a : Fin 3) : off j a + grp h j a ≤ h := by
  fin_cases a <;> simp [off, grp] <;> omega

theorem off_add_grp_le_off {h j : ℕ} (hj : j + 1 < h) {a a' : Fin 3} (haa : a < a') :
    off j a + grp h j a ≤ off j a' := by
  fin_cases a <;> fin_cases a' <;> simp [off, grp] at haa ⊢

def place {h j : ℕ} (hj : j + 1 < h) (c : Σₗ a, Fin (grp h j a)) : Fin h :=
  ⟨off j (ofLex c).1 + (ofLex c).2, by
    have := off_add_grp_le hj (ofLex c).1
    have := (ofLex c).2.2
    omega⟩

theorem place_strictMono {h j : ℕ} (hj : j + 1 < h) : StrictMono (place hj) := by
  intro c c' hc
  obtain ⟨a, b⟩ := c
  obtain ⟨a', b'⟩ := c'
  rcases Sigma.Lex.lt_def.1 hc with hlt | ⟨e, hlt⟩
  · have h1 : off j a + grp h j a ≤ off j a' := off_add_grp_le_off hj hlt
    have h2 : (b : ℕ) < grp h j a := b.2
    show off j a + b < off j a' + b'
    omega
  · obtain rfl : a = a' := e
    have : (b : ℕ) < b' := hlt
    show off j a + b < off j a + b'
    omega

theorem card_lex {h j : ℕ} (hj : j + 1 < h) : Fintype.card (Σₗ a, Fin (grp h j a)) = h := by
  rw [Fintype.card_lex, Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_three]
  show j + 2 + (h - (j + 2)) = h
  omega

theorem place_bijective {h j : ℕ} (hj : j + 1 < h) : Function.Bijective (place hj) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨(place_strictMono hj).injective, by simp [card_lex hj]⟩

def order {h j : ℕ} (hj : j + 1 < h) : Fin h ≃o Σₗ a, Fin (grp h j a) :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).symm

theorem place_order {h j : ℕ} (hj : j + 1 < h) (c : Fin h) : place hj (order hj c) = c :=
  ((place_strictMono hj).orderIsoOfSurjective _ (place_bijective hj).2).apply_symm_apply c

theorem sum_place {h j : ℕ} (hj : j + 1 < h) (g : Fin h → ℕ) :
    ∑ a, ∑ b : Fin (grp h j a), g (place hj (toLex ⟨a, b⟩)) = ∑ c, g c := by
  rw [← Fintype.sum_sigma (fun p : Σ a, Fin (grp h j a) => g (place hj (toLex p)))]
  exact Equiv.sum_comp (toLex.trans (Equiv.ofBijective _ (place_bijective hj))) g

theorem fin_three_forall {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (a : Fin 3) : P a := by
  fin_cases a
  exacts [h0, h1, h2]

section Main

variable {h N j M : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL k)

def fac (a : Fin 3) (b : Fin (grp h j a)) : IrrGL k := x (place hj (toLex ⟨a, b⟩))

def fac' (a : Fin 3) (b : Fin (grp h j a)) : IrrGL k :=
  x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ (place hj (toLex ⟨a, b⟩)))

theorem fac'_zero : fac' hj x 0 = fac hj x 0 := by
  funext b
  have hb : (b : ℕ) < j := b.2
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 0 + b ≠ j
    simp [off]; omega
  · show off j 0 + b ≠ j + 1
    simp [off]; omega

theorem fac'_two : fac' hj x 2 = fac hj x 2 := by
  funext b
  refine congrArg x (Equiv.swap_apply_of_ne_of_ne (Fin.ne_of_val_ne ?_) (Fin.ne_of_val_ne ?_))
  · show off j 2 + b ≠ j
    simp [off]; omega
  · show off j 2 + b ≠ j + 1
    simp [off]; omega

theorem place_one_zero : place hj (toLex ⟨1, (0 : Fin 2)⟩) = ⟨j, by omega⟩ := Fin.ext (by
  show off j 1 + 0 = j
  simp [off])

theorem place_one_one : place hj (toLex ⟨1, (1 : Fin 2)⟩) = ⟨j + 1, hj⟩ := Fin.ext (by
  show off j 1 + 1 = j + 1
  simp [off])

theorem fac_one : (fac hj x 1 : Fin 2 → IrrGL k) = ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] := by
  funext b
  fin_cases b
  · exact congrArg x (place_one_zero hj)
  · exact congrArg x (place_one_one hj)

theorem fac'_one : (fac' hj x 1 : Fin 2 → IrrGL k) = ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] := by
  funext b
  fin_cases b
  · refine congrArg x ?_
    refine (congrArg _ (place_one_zero hj)).trans (Equiv.swap_apply_left _ _)
  · refine congrArg x ?_
    refine (congrArg _ (place_one_one hj)).trans (Equiv.swap_apply_right _ _)

end Main

theorem swap_core {h N j : ℕ} (hj : j + 1 < h) (x : Fin h → IrrGL k) (d : Fin 3 → ℕ)
    (s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a) (s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a) (hN : ∑ a, d a = N)
    (hd : ∑ a, (x a).1 = N)
    (hd' : ∑ a, (x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)).1 = N)
    (φ : ∀ a, Nonempty ((prodIrr (fac hj x a) (s₁ a)).Equiv (prodIrr (fac' hj x a) (s₂ a)))) :
    Nonempty ((prodIrr x hd).Equiv (prodIrr (fun a => x (Equiv.swap ⟨j, by omega⟩ ⟨j + 1, hj⟩ a)) hd')) := by
  have hJ : j < h := by omega
  have key : ∀ c, fac' hj x (ofLex (order hj c)).1 (ofLex (order hj c)).2 =
      x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ c) := fun c =>
    congrArg (fun y => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ y)) (place_order hj c)
  refine (flatten (grp h j) (fac hj x) d s₁ hN (order hj) x
    (fun c => congrArg x (place_order hj c)) hd).elim fun p => ?_
  refine (flatten (grp h j) (fac' hj x) d s₂ hN (order hj) (fun a => x (Equiv.swap (⟨j, hJ⟩ : Fin h) ⟨j + 1, hj⟩ a))
    key hd').elim fun q => ?_
  let Φ : (multiProd (stdBlocks d hN) fun a => prodIrr (fac hj x a) (s₁ a)).Equiv
      (multiProd (stdBlocks d hN) fun a => prodIrr (fac' hj x a) (s₂ a)) :=
    multiProdEquiv (stdBlocks d hN) fun a => (φ a).some
  exact ⟨p.symm.trans (Φ.trans q)⟩

theorem swapProd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZSeg.SwapProd k := by
  intro k _ _ _ _ h N x hd j hj M hd2 hd2' hd' hyp
  have t₁ : ∑ b : Fin 2, ((fac hj x 1 : Fin 2 → IrrGL k) b).1 = M := by
    rw [fac_one hj x]; exact hd2
  have t₂ : ∑ b : Fin 2, ((fac' hj x 1 : Fin 2 → IrrGL k) b).1 = M := by
    rw [fac'_one hj x]; exact hd2'
  let d : Fin 3 → ℕ := ![∑ b, (fac hj x 0 b).1, M, ∑ b, (fac hj x 2 b).1]
  have s₁ : ∀ a, ∑ b, (fac hj x a b).1 = d a := fin_three_forall rfl t₁ rfl
  have s₂ : ∀ a, ∑ b, (fac' hj x a b).1 = d a :=
    fin_three_forall (by rw [fac'_zero hj x]; rfl) t₂ (by rw [fac'_two hj x]; rfl)
  have hN : ∑ a, d a = N :=
    (Finset.sum_congr rfl fun a _ => (s₁ a).symm).trans ((sum_place hj fun c => (x c).1).trans hd)
  refine swap_core hj x d s₁ s₂ hN hd hd' (fin_three_forall ?_ ?_ ?_)
  · exact prodIrr_congr rfl _ _ (fun i => (congrFun (fac'_zero hj x).symm i).trans (congrArg _ (Fin.ext rfl))) _ _
  · have e₁ : Nonempty ((prodIrr (fac hj x 1 : Fin 2 → IrrGL k) t₁).Equiv (prodIrr ![x ⟨j, by omega⟩, x ⟨j + 1, hj⟩] hd2)) :=
      prodIrr_congr rfl _ _ (fun i => (congrFun (fac_one hj x) i).trans (congrArg _ (Fin.ext rfl))) _ _
    have e₂ : Nonempty ((prodIrr ![x ⟨j + 1, hj⟩, x ⟨j, by omega⟩] hd2').Equiv (prodIrr (fac' hj x 1 : Fin 2 → IrrGL k) t₂)) :=
      prodIrr_congr rfl _ _ (fun i => (congrFun (fac'_one hj x).symm i).trans (congrArg _ (Fin.ext rfl))) _ _
    obtain ⟨a⟩ := e₁
    obtain ⟨b⟩ := hyp
    obtain ⟨c⟩ := e₂
    exact ⟨(a.trans b).trans c⟩
  · exact prodIrr_congr rfl _ _ (fun i => (congrFun (fac'_two hj x).symm i).trans (congrArg _ (Fin.ext rfl))) _ _

end GlobalTheory.CompanionTheory.BZSwap
