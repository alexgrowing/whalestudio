import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitsConjOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
open Matrix GlobalTheory.LKRes
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes.CentComm

theorem commute_of_commute_of_separable {A : Type} [CommRing A] [Finite (MaximalSpectrum A)] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) A) (hs : g.charpoly.Separable) (X Y : Matrix (Fin n) (Fin n) A)
    (hX : Commute X g) (hY : Commute Y g) : X * Y = Y * X := by
  obtain ⟨v, hv⟩ := GlobalTheory.SemilocalConj.exists_isUnit_det_krylov g hs
  obtain ⟨q, rfl⟩ := GlobalTheory.BCT.FinCentComm.eq_aeval_of_cyclic g v hv Y hY
  exact (GlobalTheory.BCT.FinCentComm.commute_aeval hX q).eq

theorem finite_maximalSpectrum_KQ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (r : ℕ) (hr : 0 < r) : Finite (MaximalSpectrum (KQ p K r)) := by
  haveI : FiniteDimensional ℚ_[p] (Qr p r) :=
    ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  haveI : Module.Finite ℚ_[p] (KQ p K r) := inferInstanceAs (Module.Finite ℚ_[p] (K ⊗[ℚ_[p]] Qr p r))
  haveI : IsArtinianRing (KQ p K r) := IsArtinianRing.of_finite ℚ_[p] (KQ p K r)
  infer_instance

theorem centralizer_comm : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a := by
  intro p _ K hK n r hr N hs a ha b hb
  haveI := hK
  haveI := finite_maximalSpectrum_KQ p K r hr
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hX : Commute a.val N.val := by
    show a.val * N.val = N.val * a.val
    have := congrArg Units.val ha; simpa using this
  have hY : Commute b.val N.val := by
    show b.val * N.val = N.val * b.val
    have := congrArg Units.val hb; simpa using this
  exact Units.ext (by simpa using commute_of_commute_of_separable N.val hs a.val b.val hX hY)

end GlobalTheory.LKRes.CentComm

example : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r →
    ∀ N : GL (Fin n) (GlobalTheory.LKRes.KQ p K r), N.val.charpoly.Separable →
    ∀ a ∈ Subgroup.centralizer {N}, ∀ b ∈ Subgroup.centralizer {N}, a * b = b * a :=
  GlobalTheory.LKRes.CentComm.centralizer_comm
