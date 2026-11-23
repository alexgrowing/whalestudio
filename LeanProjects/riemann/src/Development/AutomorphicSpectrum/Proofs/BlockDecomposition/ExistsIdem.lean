import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TiltIdem

variable {B R : Type} [CommRing B] [CommRing R]

theorem idem_eq (i : B →* R)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {x y : B} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : ∀ p : PrimeSpectrum R, i x ∉ p.asIdeal ↔ i y ∉ p.asIdeal) : x = y := by
  have hix : IsIdempotentElem (i x) := by
    change i x * i x = i x
    rw [← map_mul, hx.eq]
  have hiy : IsIdempotentElem (i y) := by
    change i y * i y = i y
    rw [← map_mul, hy.eq]
  have hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y) := by
    ext p
    exact h p
  have e : i x = i y := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb
  exact (hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩

theorem exists_idem (i : B →* R) (h0 : i 0 = 0)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {ι : Type} [Fintype ι] (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧
      (∀ (a : ι) (p : PrimeSpectrum R), i (e a) ∉ p.asIdeal ↔ f p = a) ∧
      ∀ (e' : B) (a : ι), IsIdempotentElem e' →
        (∀ p : PrimeSpectrum R, i e' ∉ p.asIdeal → f p = a) → e' * e a = e' := by
  classical
  have hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a := by
    intro a
    have hc : IsClopen (f ⁻¹' {a}) := f.isLocallyConstant.isClopen_fiber a
    obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.1 hc
    obtain ⟨e₀, ⟨he₀, rfl⟩, -⟩ := hidem ε hε
    refine ⟨e₀, he₀, fun p => ?_⟩
    have : p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀) := by rw [hs]; rfl
    exact this.symm
  choose e he hp using hfib
  have hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal) := fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)
  have hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal := by
    intro x y p
    rw [map_mul, p.isPrime.mul_mem_iff_mem_or_mem]
    tauto
  have hort : OrthogonalIdempotents e := by
    refine ⟨he, fun a b hab => ?_⟩
    refine idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    obtain ⟨h1, h2⟩ := (hmul _ _ p).1 h
    exact hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))
  have hsum : IsIdempotentElem (∑ a, e a) := hort.isIdempotentElem_sum
  have hc : IsIdempotentElem (1 - ∑ a, e a) := hsum.one_sub
  have hce : ∀ a, (1 - ∑ b, e b) * e a = 0 := by
    intro a
    rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]
    · exact fun b _ hb => hort.ortho hb
    · exact fun h => absurd (Finset.mem_univ a) h
  have hone : 1 - ∑ a, e a = 0 := by
    refine idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    have h1 : i (e (f p)) ∉ p.asIdeal := (hp (f p) p).2 rfl
    have h2 := (hmul _ _ p).2 ⟨h, h1⟩
    rw [hce] at h2
    exact hnot0 p h2
  refine ⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩
  refine idem_eq i hidem (he'.mul (he a)) he' fun p => ?_
  rw [hmul]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩

theorem sharp_zero' {l : ℕ} [Fact l.Prime] (A : PAlg l) : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem lcIdem : CrystallineSemistableComparison.E.LcIdem := by
  intro l _ H A hA ι _ f
  let i : A.A →* A.Ug := (algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp
  have h0 : i 0 = 0 := by
    change algebraMap A.U A.Ug (A.sharp 0) = 0
    rw [sharp_zero', map_zero]
  let f' : LocallyConstant (PrimeSpectrum A.Ug) ι := ⟨f, f.isLocallyConstant⟩
  exact exists_idem i h0 (H.idem A hA) f'

end GlobalTheory.CompanionTheory.TiltIdem
