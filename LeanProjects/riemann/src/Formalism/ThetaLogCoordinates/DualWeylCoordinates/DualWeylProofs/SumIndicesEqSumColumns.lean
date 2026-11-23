import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LWedge

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_E (lo : ℤ) (N : ℕ) (F : ℤ → Finset (Fin n)) : Fin N → Finset (Fin n) := fun j => F (lo + 1 + (j : ℕ))

lemma ql_prod_Ioc {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by
  symm
  refine Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_
  · intro j _; have := j.2; simp only [mem_Ioc]; omega
  · intro i _ j _ h; ext; omega
  · intro c hc
    simp only [mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩
  · intro j _; rfl

def ql_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : lo < c ∧ c ≤ lo + N then f ⟨(c - lo - 1).toNat, by omega⟩ else if c ≤ lo then univ else ∅

lemma ql_E_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by
  funext j
  have := j.2
  simp only [ql_E, ql_fill]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  show (lo + 1 + (j : ℕ) - lo - 1).toNat = j
  omega

lemma ql_sum_L {M : Type*} [AddCommMonoid M] {b : ℕ} (φ : Finset (Fin n) → M) (hφ : ∀ L, L.card ≠ b → φ L = 0) :
    ∑ L : LamIdx n b, φ L.1 = ∑ L, φ L := by
  refine Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro L hL
  exact hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩

variable [NeZero n]

lemma ql_fill_card {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by
  unfold ql_fill
  split_ifs with h h'
  · rw [hf]; congr 1
    show lo + 1 + ((c - lo - 1).toNat : ℤ) = c
    omega
  · rw [qs_colH_low hmu (h'.trans h1)]; simp
  · rw [qs_colH_high hmu (by omega)]; simp

lemma ql_E_card {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := qs_ext_card hmu I _

lemma sum_indices_eq_sum_columns {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by
  refine Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)
  · intro I I' h
    funext c
    apply Subtype.ext
    rw [← qs_ext_mem, ← qs_ext_mem]
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have := congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩
    have e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1 := by omega
    simp only [ql_E, e] at this
    exact this
  · intro f hf
    apply hφ
    by_contra hc
    push Not at hc
    exact hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by
      simp only [qs_ext_res hmu, ql_E_fill]⟩

lemma ql_TMat {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by
  rw [qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]; rfl

lemma ql_mem_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by
  rw [qs_ext_can hmu, ← qb_lt_colH_iff hmu]; simp [qs_ini]

end Formalism.InvariantFactorPaths.ColumnFamilies
