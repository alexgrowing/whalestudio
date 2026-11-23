import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.Topology.JacobsonSpace

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem fibre_closed {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (m : Ideal B) [m.IsMaximal] (W : Set (PrimeSpectrum A)) (hW : IsLocallyClosed W) (p : PrimeSpectrum A)
    (hp : p ∈ W) (hm : m ≤ p.asIdeal.comap (algebraMap B A)) :
    ∃ x ∈ W, m ≤ x.asIdeal.comap (algebraMap B A) ∧ x.asIdeal.IsMaximal := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hW
  obtain ⟨hpU, hpZ⟩ := hp
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hpf, hfU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpU hU
  have hqmax : (p.asIdeal.comap (algebraMap B A)).IsMaximal := by
    have e := Ideal.IsMaximal.eq_of_le ‹m.IsMaximal› (Ideal.IsPrime.comap (algebraMap B A)).ne_top hm
    rw [← e]
    infer_instance
  letI := Ideal.Quotient.field (p.asIdeal.comap (algebraMap B A))
  haveI : IsJacobsonRing (A ⧸ p.asIdeal) :=
    isJacobsonRing_of_finiteType (A := B ⧸ p.asIdeal.comap (algebraMap B A))
  have hbot : (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson = ⊥ :=
    isJacobsonRing_iff_prime_eq.1 ‹_› ⊥ Ideal.bot_prime
  have hf0 : Ideal.Quotient.mk p.asIdeal f ∉ (⊥ : Ideal (A ⧸ p.asIdeal)).jacobson := by
    rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hpf
  have hf1 : ¬ ∀ J ∈ {J : Ideal (A ⧸ p.asIdeal) | ⊥ ≤ J ∧ J.IsMaximal}, Ideal.Quotient.mk p.asIdeal f ∈ J :=
    fun h => hf0 (Ideal.mem_sInf.2 h)
  push_neg at hf1
  obtain ⟨J, ⟨-, hJ⟩, hfJ⟩ := hf1
  haveI := hJ
  haveI := hJ.isPrime
  have hle : p.asIdeal ≤ J.comap (Ideal.Quotient.mk p.asIdeal) := fun a ha => by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact J.zero_mem
  refine ⟨⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩, ⟨hfU ?_, ?_⟩, ?_,
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  · exact hfJ
  · have hpx : p ≤ ⟨J.comap (Ideal.Quotient.mk p.asIdeal), Ideal.IsPrime.comap _⟩ := hle
    exact hZ.closure_subset_iff.2 (Set.singleton_subset_iff.2 hpZ) ((PrimeSpectrum.le_iff_mem_closure _ _).1 hpx)
  · exact hm.trans (Ideal.comap_mono hle)

theorem UpperTheory.V.Fr.jac :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ C : Set (PrimeSpectrum S.A), IsClosed C → ∀ U : Set (PrimeSpectrum S.A), IsOpen U → (C ∩ U ∩ S.BB).Nonempty → ∃ x ∈ C ∩ U ∩ S.BB, x.asIdeal.IsMaximal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C hC U hU hne
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  haveI : S.mB.IsMaximal := hmax ▸ IsLocalRing.maximalIdeal.isMaximal S.B
  obtain ⟨p, ⟨hpC, hpU⟩, hpm, hpT⟩ := hne
  have hO : IsOpen {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal} :=
    (PrimeSpectrum.isClosed_zeroLocus (S.u.triP : Set S.A)).isOpen_compl
  have hW : IsLocallyClosed (C ∩ U ∩ {x : PrimeSpectrum S.A | ¬ S.u.triP ≤ x.asIdeal}) :=
    (hC.isLocallyClosed.inter hU.isLocallyClosed).inter hO.isLocallyClosed
  obtain ⟨x, ⟨⟨hxC, hxU⟩, hxT⟩, hxm, hxmax⟩ := fibre_closed S.mB _ hW p ⟨⟨hpC, hpU⟩, hpT⟩ hpm
  exact ⟨x, ⟨⟨hxC, hxU⟩, hxm, hxT⟩, hxmax⟩
