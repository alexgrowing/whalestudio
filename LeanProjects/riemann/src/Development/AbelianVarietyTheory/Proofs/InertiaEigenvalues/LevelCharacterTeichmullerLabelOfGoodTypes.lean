import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.CharLabTransport

theorem teich_inv {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (c : (ZMod g)ˣ) :
    L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((c⁻¹ : (ZMod g)ˣ) : ZMod g)) =
      (L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (c : ZMod g)))⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem charLab_of_value {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (θ : (ZMod g)ˣ →* ℂˣ)
    (t : (ZMod g)ˣ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (h : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 →
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = ((θ u : ℂˣ) : ℂ) ∨
      L.teich (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (t : ZMod g)) = (((θ u)⁻¹ : ℂˣ) : ℂ)) :
    ∃ c : ZMod g, GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp θ) c ∧
      (c = (t : ZMod g) ∨ c = ((t⁻¹ : (ZMod g)ˣ) : ZMod g)) := by
  by_cases hex : ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1
  · obtain ⟨u₀, hu₀⟩ := hex
    have huniq : ∀ u : (ZMod g)ˣ, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 → u = u₀ := by
      intro u hu
      apply Units.ext
      exact (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective (hu.trans hu₀.symm)
    rcases hε with rfl | rfl <;> rcases h u₀ hu₀ with hv | hv
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨(t⁻¹).ne_zero, fun u hu => ?_⟩, Or.inr rfl⟩
      rw [huniq u hu, teich_inv, hv]; simp
    · refine ⟨_, ⟨t.ne_zero, fun u hu => ?_⟩, Or.inl rfl⟩
      rw [huniq u hu, hv]; simp
  · exact ⟨_, ⟨t.ne_zero, fun u hu => (hex ⟨u, hu⟩).elim⟩, Or.inl rfl⟩

theorem charLab_of_goodTypes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R → ∀ (k : Fin 2) (v : D.nd.PlG k) (i : Fin D.R.m) (PP : Pl D.host.E),
    R.C.P.Div k PP → ∀ (iso : ZMod (D.host.g k) ≃+* kP PP) (ε : ℤ), (ε = 1 ∨ ε = -1) →
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ∃ L : GlobalTheory.GLq.LabelDatum (D.host.g k), (∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC L D.R.r f) ∧
      ∃ c : ZMod (D.host.g k),
        GlobalTheory.GLp.IsCharLab L ((zpowGroupHom ε).comp ((R.chi ((i : ℕ) + 1) PP).comp
          (Units.map (iso : ZMod (D.host.g k) →* kP PP)))) c ∧
        (c = ((D.nd.chiT k v i : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) ∨
          c = (((D.nd.chiT k v i)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hg k v i PP hdiv iso ε hε
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨L, -, hser, hchi⟩ := hg k
  refine ⟨L, hser, ?_⟩
  apply charLab_of_value L _ _ ε hε
  intro u hu
  have h1 : (((u : ZMod (D.host.g k)).val : ℕ) : ZMod (D.host.g k)) = u := ZMod.natCast_zmod_val _
  refine hchi v i PP hdiv (u : ZMod (D.host.g k)).val
    (Units.map (iso : ZMod (D.host.g k) →* kP PP) u) ?_ ?_
  · rw [← hu, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), h1]
  · rw [← map_natCast iso, h1]; rfl

end GlobalTheory.CharLabTransport
