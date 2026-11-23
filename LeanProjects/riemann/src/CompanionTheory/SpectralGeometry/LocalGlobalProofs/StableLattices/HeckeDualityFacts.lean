import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhHecke.Dual

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

def twE {A : Type*} [Ring A] (E : Fin n → Fin n → A) (a b : Fin n) : A := -E b a

theorem glRel_twE {A : Type*} [Ring A] {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (twE E) := by
  intro a b c d
  have := h b a d c
  simp only [twE, neg_mul_neg]
  rw [this]
  clear this
  have k1 : (a = d) ↔ (d = a) := eq_comm
  have k2 : (c = b) ↔ (b = c) := eq_comm
  simp only [k1, k2]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel

theorem capEntry_twE {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (y : ℂ) (a b : Fin n) :
    capEntry (twE E) y a b = -capEntry E (-y) b a := by
  by_cases h : a = b
  · subst h; simp [capEntry, twE, add_comm]
  · simp [capEntry, twE, h, Ne.symm h]

theorem ofFn_neg_prod {A : Type*} [Ring A] : ∀ {p : ℕ} (f : Fin p → A),
    (List.ofFn fun j => -f j).prod = (-1) ^ p * (List.ofFn f).prod := by
  intro p
  induction p with
  | zero => intro f; simp
  | succ p ih =>
    intro f
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih]
    rcases neg_one_pow_eq_or A p with h | h <;> simp [h, pow_succ]

theorem capelliC_twE {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (hE : GlRelR E) (x : ℂ) :
    capelliC (twE E) x = (-1) ^ n * capelliC E ((n : ℂ) - 1 - x) := by
  unfold capelliC
  rw [cminor_eq_rminor E hE]
  unfold cminor rminor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have e : (fun j : Fin n => capEntry (twE E) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      fun j : Fin n => -capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) (id j) (id (σ j)) := by
    funext j
    rw [capEntry_twE]
    congr 2
    ring
  rw [e, ofFn_neg_prod, mul_smul_comm]

def tw (X : GMod n) : GMod n := ⟨X.V, twE X.E, glRel_twE X.gl⟩

theorem capelliPoly_neg (χ : Fin n → ℂ) (Y : ℂ) : Formalism.QuantumDeterminants.capP (-χ) Y = (-1) ^ n * Formalism.QuantumDeterminants.capP χ (-Y) := by
  unfold Formalism.QuantumDeterminants.capP
  have : ∀ s : Fin n, Y + (-χ) s = (-1) * (-Y + χ s) := fun s => by simp; ring
  simp only [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem hasChar_tw {X : GMod n} {χ : Fin n → ℂ} (h : HasChar X χ) : HasChar (tw X) (-χ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, fun Y => ?_⟩
  have h0 := hk (-Y)
  show (qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V)) ^ k = 0
  have e : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (-χ) Y • (1 : Module.End ℂ X.V) =
      (-1 : Module.End ℂ X.V) ^ n *
        (qdet X.E (-Y + ((n : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP χ (-Y) • (1 : Module.End ℂ X.V)) := by
    have h1 : qdet (twE X.E) (Y + ((n : ℂ) - 1) / 2) =
        (-1 : Module.End ℂ X.V) ^ n * qdet X.E (-Y + ((n : ℂ) - 1) / 2) := by
      rw [qdet_eq_capelliC, qdet_eq_capelliC]
      have := capelliC_twE X.E X.gl (Y + ((n : ℂ) - 1) / 2)
      have e2 : (n : ℂ) - 1 - (Y + ((n : ℂ) - 1) / 2) = -Y + ((n : ℂ) - 1) / 2 := by ring
      rw [e2] at this
      exact this
    rw [h1, capelliPoly_neg, mul_sub]
    congr 1
    rcases Nat.even_or_odd n with h | h <;> simp [h.neg_one_pow]
  rw [e, ((Commute.neg_one_left _).pow_left n).mul_pow, h0, mul_zero]

theorem capelliC_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (E : Fin n → Fin n → A) (x : ℂ) : φ (capelliC E x) = capelliC (fun a b => φ (E a b)) x := by
  unfold capelliC cminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_zsmul, map_list_prod, List.map_ofFn]
  have e : (⇑φ ∘ fun j : Fin n => capEntry E (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j)) =
      fun j : Fin n => capEntry (fun a b => φ (E a b)) (x - ((j : ℕ) : ℂ)) (id (σ j)) (id j) := by
    funext j
    simp only [Function.comp, capEntry, map_add]
    split_ifs <;> simp
  rw [e]

theorem hasChar_of_iso {X X' : GMod n} {χ : Fin n → ℂ} (h : Iso X X') (hX : HasChar X χ) : HasChar X' χ := by
  obtain ⟨e, he⟩ := h
  obtain ⟨k, hk⟩ := hX
  refine ⟨k, fun Y => ?_⟩
  let φ : Module.End ℂ X.V →ₐ[ℂ] Module.End ℂ X'.V := (LinearEquiv.conjAlgEquiv ℂ e).toAlgHom
  have hE : (fun a b => φ (X.E a b)) = X'.E := by
    funext a b
    refine LinearMap.ext fun y => ?_
    have := he a b (e.symm y)
    simpa [φ, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply] using this
  have h1 : ∀ x : ℂ, qdet X'.E x = φ (qdet X.E x) := fun x => by
    rw [qdet_eq_capelliC, qdet_eq_capelliC, capelliC_map φ, hE]
  have := congrArg φ (hk Y)
  simpa [map_pow, map_sub, h1] using this

theorem om_tw (X : GMod n) : om (tw X) = omD X := by
  refine LinearMap.ext fun (u : Fin n → X.V) => funext fun b => ?_
  show ∑ a, (-X.E b a) (u a) = eeVd X.E u b
  rw [eeVd_apply']
  simp

theorem stepSub_tw (X : GMod n) (z : ℂ) : stepSub (tw X) (-z) = backSub X z := by
  unfold stepSub backSub
  rw [om_tw]
  rfl

theorem dual_cayley (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) :
    ∃ K : ℕ, ((List.ofFn fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V))).prod) ^ K = 0 := by
  obtain ⟨K, hK⟩ := GlobalTheory.T.CayleyHamiltonHk n (tw X) (-χ) (hasChar_tw h)
  refine ⟨K, ?_⟩
  have e : (fun t : Fin n => om (tw X) - ((-χ) t - cn n) • (1 : Module.End ℂ (Fin n → (tw X).V))) =
      fun t : Fin n => omD X - (-χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V)) := by
    funext t
    rw [om_tw]
    rfl
  rw [e] at hK
  exact hK

theorem dual_nonvan (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) (s : Fin n) (hne : Nontrivial X.V)
    (hfree : ∀ r, χ r ≠ χ s - 1) : backSub X (χ s) ≠ ⊥ := by
  have := GlobalTheory.T.HeckeNonVanishing n (tw X) (-χ) s (hasChar_tw h) hne (fun r e => hfree r (by
    simp only [Pi.neg_apply] at e
    linear_combination -e))
  have t : stepSub (tw X) (-χ s) ≠ ⊥ := this
  rw [stepSub_tw] at t
  exact t

theorem tw_tens (X : GMod n) (a b : Fin n) (y : Fin n → X.V) :
    -(tensE (tw X) b a y) = ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b y := by
  have e3 : ∀ p q : X.V, -(-p + q) = p - q := fun p q => by abel
  funext i
  rw [ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd_apply']
  exact e3 (X.E a b (y i)) (if i = b then y a else 0)

set_option maxHeartbeats 200000 in
theorem iso_back (X : GMod n) (z : ℂ) (hB : ∀ a b, ∀ x ∈ backSub X z, (tensD X).E a b x ∈ backSub X z) :
    Iso (tw (step (tw X) (-z))) (back X z hB) := by
  let S : Submodule ℂ (Fin n → X.V) := stepSub (tw X) (-z)
  let e : ↥S ≃ₗ[ℂ] ↥(backSub X z) := LinearEquiv.ofEq S (backSub X z) (stepSub_tw X z)
  have l0 : ∀ w : ↥S, Subtype.val (e w) = Subtype.val w := fun w => LinearEquiv.coe_ofEq_apply _ w
  refine ⟨e, ?_⟩
  intro a b x
  apply Subtype.ext
  let y : Fin n → X.V := Subtype.val (show ↥S from x)
  have l1 : Subtype.val (show ↥S from (tw (step (tw X) (-z))).E a b x) = -(tensE (tw X) b a y) := rfl
  have r1 : ∀ w : ↥(backSub X z), Subtype.val ((back X z hB).E a b w) =
      ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b w.val := fun _ => rfl
  exact (l0 _).trans (l1.trans ((tw_tens X a b y).trans
    ((congrArg (ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.tensVd X.E a b) (l0 x).symm).trans (r1 (e x)).symm)))

theorem dual_char (X : GMod n) (χ : Fin n → ℂ) (h : HasChar X χ) (s : Fin n)
    (hB : ∀ a b, ∀ x ∈ backSub X (χ s), (tensD X).E a b x ∈ backSub X (χ s)) :
    HasChar (back X (χ s) hB) (χ - Pi.single s 1) := by
  have hT : HasChar (tw (step (tw X) (-χ s))) (-(-χ + Pi.single s 1)) :=
    hasChar_tw (GlobalTheory.T.InfinitesimalCharacterStatement n (tw X) (-χ) s (hasChar_tw h))
  have e : -(-χ + Pi.single s 1) = χ - Pi.single s 1 := by
    rw [neg_add, neg_neg, sub_eq_add_neg]
  rw [e] at hT
  exact hasChar_of_iso (iso_back X (χ s) hB) hT

theorem dualFacts : DualFacts := fun _ X χ h =>
  ⟨dual_cayley X χ h, fun s hB => dual_char X χ h s hB, fun s hne hf => dual_nonvan X χ h s hne hf⟩

end GlobalTheory.CompanionTheory.RgExhHecke.Dual
