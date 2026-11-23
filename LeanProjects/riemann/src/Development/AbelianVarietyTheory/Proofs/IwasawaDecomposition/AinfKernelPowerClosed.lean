import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfQuotFontaineXiPowTorsionFreeSeparatedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem image_kerP_pow_separated : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.Ainf l), (∀ k : ℕ, ∃ b : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) (a - ((l : ℕ) : Per.Ainf l) ^ k * b) ∈ Per.kerP l ^ n) → algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  intro l _ n a h
  obtain ⟨e, he⟩ : ∃ e : Per.Fl l, IsEps e := Model.exists_isEps l
  obtain ⟨-, -, -, -, -, hinj, hk⟩ := thetaP_facts l
  obtain ⟨h1, h2⟩ := GlobalTheory.T.ainf_quot_fontaineXi_pow_torsionFree_separated l e he n
  have h3 : ∀ (j : ℕ) (c : Per.Ainf l), xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) ^ j * c → xi e ^ n ∣ c := by
    intro j
    induction j with
    | zero => intro c hc; simpa using hc
    | succ j ih =>
      intro c hc
      refine h1 c (ih _ ?_)
      rwa [← mul_assoc, ← pow_succ]
  have key : ∀ c : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) c ∈ Per.kerP l ^ n ↔
      xi e ^ n ∣ c := by
    intro c
    rw [hk e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    refine ⟨fun ⟨y, hy⟩ => ?_, fun hc => map_dvd _ hc⟩
    obtain ⟨j, d, hd⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    refine h3 j c ⟨d, hinj ?_⟩
    rw [map_mul, map_mul, ← hd, hy, map_pow, map_pow]
    ring
  refine (key a).2 (h2 a fun k => ?_)
  obtain ⟨b, hb⟩ := h k
  exact ⟨b, (key _).1 hb⟩

end GlobalTheory.MemLoc
