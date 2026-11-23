import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open Polynomial LateralTheory.E.PartDiagCut GlobalTheory.EtC

namespace LateralTheory.E.PartCPf

def Split : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B →
  ∀ (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)), p.Monic →
    ∃ (n : ℕ) (r : Fin n → PiLocalization₂ I P), p = ∏ l, (X - C (r l))

def Idem : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (n : ℕ) (y : Fin n → PiLocalization₂ I P),
  ∏ l, y l ∈ I.map (βP I P) →
  IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, y m)) →
  ∃ f : Fin n → B, (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) ∧
    (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) ∧
    ∑ l, Ideal.Quotient.mk I (f l) = 1 ∧ ∀ l, βP I P (f l) * y l ∈ I.map (βP I P)

def Lift : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (P : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (p : Polynomial (PiLocalization₂ I P)) (a₀ : PiLocalization₂ I P)
  (n : ℕ) (r : Fin n → PiLocalization₂ I P) (f : Fin n → B), p = ∏ l, (X - C (r l)) →
  (∀ l, IsIdempotentElem (Ideal.Quotient.mk I (f l))) →
  (∀ l m, l ≠ m → Ideal.Quotient.mk I (f l) * Ideal.Quotient.mk I (f m) = 0) →
  ∑ l, Ideal.Quotient.mk I (f l) = 1 → (∀ l, βP I P (f l) * (a₀ - r l) ∈ I.map (βP I P)) →
  ∃ (Q : LateralTheory.E.PartDiagCut.Part (B ⧸ I)) (h : P ≤ Q) (a : PiLocalization₂ I Q), (p.map (stageMap I h)).IsRoot a ∧
    a - stageMap I h a₀ ∈ I.map (βP I Q)

theorem eval_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (∏ l, (X - C (r l))).eval x = ∏ l, (x - r l) := by
  simp [eval_prod]

theorem deriv_prod_lin {R : Type} [CommRing R] (n : ℕ) (r : Fin n → R) (x : R) :
    (derivative (∏ l, (X - C (r l)))).eval x = ∑ l, ∏ m ∈ Finset.univ.erase l, (x - r m) := by
  classical
  rw [derivative_prod_finset]
  simp [eval_finsetSum, eval_prod]

theorem PartC_of (hs : Split) (hi : Idem) (hl : Lift) : LateralTheory.E.PartDiagCut.PartC := by
  intro B _ _ I hB P p a₀ hm hev hder
  obtain ⟨n, r, hp⟩ := hs B I hB P p hm
  have h1 : ∏ l, (a₀ - r l) ∈ I.map (βP I P) := by
    rw [← eval_prod_lin n r a₀, ← hp]; exact hev
  have h2 : IsUnit (Ideal.Quotient.mk (I.map (βP I P)) (∑ l, ∏ m ∈ Finset.univ.erase l, (a₀ - r m))) := by
    rw [← deriv_prod_lin n r a₀, ← hp]; exact hder
  obtain ⟨f, hfi, hfo, hfs, hfy⟩ := hi B I P n (fun l => a₀ - r l) h1 h2
  exact hl B I P p a₀ n r f hp hfi hfo hfs hfy

theorem idem_of (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) : Idem := by
  intro B _ I P n y hprod hsum
  let φ := RingEquiv.ofBijective (Ideal.quotientMap (I.map (βP I P)) (βP I P) Ideal.le_comap_map) (hA B I P)
  obtain ⟨e, hei, heo, hes, hey⟩ := hIP (PiLocalization₂ I P ⧸ I.map (βP I P)) n
    (fun l => Ideal.Quotient.mk (I.map (βP I P)) (y l))
    (by rw [← map_prod]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hprod)
    (by simpa [map_sum, map_prod] using hsum)
  choose f hf using fun l => Ideal.Quotient.mk_surjective (φ.symm (e l))
  refine ⟨f, fun l => ?_, fun l m hlm => ?_, ?_, fun l => ?_⟩
  · unfold IsIdempotentElem; rw [hf, ← map_mul, (hei l).eq]
  · rw [hf, hf, ← map_mul, heo l m hlm, map_zero]
  · simp_rw [hf]; rw [← map_sum, hes, map_one]
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    have h1 : φ (Ideal.Quotient.mk I (f l)) = e l := by rw [hf]; exact φ.apply_symm_apply _
    have h2 : Ideal.Quotient.mk (I.map (βP I P)) (βP I P (f l)) = e l := by
      rw [← h1]; simp [φ, Ideal.quotientMap_mk]
    rw [h2]; exact hey l

theorem PartC_of' (hs : Split) (hIP : LateralTheory.E.HensCut.IdemPart) (hA : LateralTheory.E.PartDiagCut.PartA) (hl : Lift) :
    LateralTheory.E.PartDiagCut.PartC :=
  PartC_of hs (idem_of hIP hA) hl

end LateralTheory.E.PartCPf
