import Formalism.PeriodIntegrals.ScXuExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.MemLocFrom

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

def Hyps (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  1 ≤ g ∧
  (∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2) ∧
  I.n = 2 * r + k + 1 ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧
    Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0) ∧
  (∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) ∧
  (∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a))) ∧
  InAt I g 1 (incl I z)

def LocConcl (I : AutInst) (g r : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (z0 : Fin I.n → I.E ⊗[I.F] Af I.F) (v : HeightOneSpectrum (𝓞 I.F)) : Prop :=
  ∃ y : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    y ∈ PI.UnitaryGroupMassFormula.AdIndexEq.Uv I v ∧ y ∈ PI.UnitaryGroupMassFormula.AdIndexEq.Kv I v ∧
    (∀ a, (y : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (e a)) =
        PI.FinKW.vecV I v (incl I (e a)) ∧
      (y : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I (f a)) =
        PI.FinKW.vecV I v (incl I (f a))) ∧
    ∃ w ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)),
      ((y⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ PI.FinKW.vecV I v (incl I z) -
          PI.FinKW.vecV I v z0 = ((g : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E) • w

def LocXu : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal → LocConcl I g r e f z Rf.z0 v

def Glue : Prop := LocXu → _root_.PI.ScXuExists.Target

def LocIdem : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (Rf : RefData I g r k e f),
    1 ≤ g → I.n = 2 * r + k + 1 →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      PI.FinKW.psiV I v Rf.ew + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 1

def LocCore : Prop :=
  ∀ (I : AutInst) (g r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (Rf : RefData I g r k e f), Hyps I g r k e f z →
    ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      PI.FinKW.psiV I v Rf.ew + PI.UnitaryGroupMassFormula.AdIndexEq.sigV I v (PI.FinKW.psiV I v Rf.ew) = 1 →
      LocConcl I g r e f z Rf.z0 v

theorem hyps_of {I : AutInst} {g r k : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E}
    (h1 : 1 ≤ g)
    (hs : ∀ v : HeightOneSpectrum (𝓞 I.F), (g : 𝓞 I.F) ∈ v.asIdeal →
      Nat.card {w : HeightOneSpectrum (𝓞 I.E) //
        w.asIdeal.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = v.asIdeal} = 2)
    (hn : I.n = 2 * r + k + 1)
    (hee : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0)
    (hff : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0)
    (hef : ∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0)
    (hz : ∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧
      Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0)
    (ht : ∃ t : ℕ, t ≡ 1 [MOD g] ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E))
    (hi : ∀ a, InAt I g 1 (incl I (e a)) ∧ InAt I g 1 (incl I (f a)))
    (hiz : InAt I g 1 (incl I z)) : Hyps I g r k e f z :=
  ⟨h1, hs, hn, hee, hff, hef, hz, ht, hi, hiz⟩

theorem locXu_of (hI : LocIdem) (hC : LocCore) : LocXu := by
  intro I g r k e f z Rf hH v hv
  exact hC I g r k e f z Rf hH v hv (hI I g r k e f Rf hH.1 hH.2.2.1 v hv)

theorem target_of (hI : LocIdem) (hC : LocCore) (hG : Glue) : _root_.PI.ScXuExists.Target :=
  hG (locXu_of hI hC)

end PI.UnitaryGroupMassFormula.ScXuExists
