import Development.EtaleCohomology.EtaleSheaves.QuotAcycCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.ProdAcycPf

theorem zero_acyc (H : LateralTheory.E.t_E2Cut.Hyp) (q : ℕ) (A : Type) [CommRing A] [Subsingleton A] : Acyc q (sp A) := by
  intro n i hn
  refine ⟨fun x y => ?_⟩
  have h0 : ∀ x : Ht q (sp A) n i, x = 0 := by
    intro x
    obtain ⟨Y, f, -, -, hx⟩ := H.a5 (ZMod q) (Spec (CommRingCat.of A)) (tw q i) n hn x
    have : IsEmpty (Spec (CommRingCat.of A)) := inferInstanceAs (IsEmpty (PrimeSpectrum A))
    have : IsIso (sch.map f) := inferInstance
    have hy : pull _ (inv (sch.map f)) _ _ (pull _ (sch.map f) _ _ x) = x := by
      rw [← pull_comp, IsIso.inv_hom_id, pull_id]
    rw [← hy, hx, map_zero]
  rw [h0 x, h0 y]

def Bin : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1],
  Nonempty (A ≃+* R0 × R1) → Acyc q (sp R0) → Acyc q (sp R1) → Acyc q (sp A)

def splitFirst (n : ℕ) (R : Fin (n + 1) → Type) [∀ k, CommRing (R k)] :
    (∀ k, R k) ≃+* R 0 × ∀ k : Fin n, R k.succ where
  toFun f := (f 0, fun k => f k.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by simp
  map_mul' f g := rfl
  map_add' f g := rfl

theorem prod_of (hB : Bin) : LateralTheory.E.QuotAcycCut.ProdAcyc := by
  intro H q A _ n
  induction n generalizing A with
  | zero =>
    intro R _ ⟨e⟩ _
    have : Subsingleton A := e.injective.subsingleton
    exact zero_acyc H q A
  | succ n ih =>
    intro R _ ⟨e⟩ hR
    refine hB H q A (R 0) (∀ k : Fin n, R k.succ) ⟨e.trans (splitFirst n R)⟩ (hR 0) ?_
    exact ih (∀ k : Fin n, R k.succ) (fun k => R k.succ) ⟨RingEquiv.refl _⟩ fun k => hR k.succ

end LateralTheory.E.ProdAcycPf
