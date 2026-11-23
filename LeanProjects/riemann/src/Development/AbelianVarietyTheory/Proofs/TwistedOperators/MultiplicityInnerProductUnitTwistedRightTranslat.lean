import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isMultiplicityInner_of_unit_twist_shift : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S), ∀ J χ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (κ : GA D V) (a : ℂ), ‖a‖ = 1 → Measure.map (fun g => g * κ) μ = μ → ∀ T ∈ Mult θ M J χ, ∀ T' ∈ Mult θ M J χ, ∀ U U' : MMap M, (∀ v g, U v g = a * T v (g * κ)) → (∀ v g, U' v g = a * T' v (g * κ)) → ∀ c, IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 U U' c := by
  intro D V S θ M J χ μ 𝓕 hμ h𝓕 κ a ha hκ T hT T' hT' U U' hU hU' c hc
  obtain ⟨hLC, hSC, hB, hC⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  unfold IsMultIP at hc ⊢
  intro v v'
  have haa : star a * a = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hfun : (fun g => star (U v g) * U' v' g) = fun g => star (T v (g * κ)) * T' v' (g * κ) := by
    funext g
    rw [hU, hU', star_mul']
    calc star a * star (T v (g * κ)) * (a * T' v' (g * κ))
        = (star a * a) * (star (T v (g * κ)) * T' v' (g * κ)) := by ring
      _ = star (T v (g * κ)) * T' v' (g * κ) := by rw [haa, one_mul]
  have hinv : ∀ γ ∈ GQ V, ∀ g, star (T v (γ * g)) * T' v' (γ * g) = star (T v g) * T' v' g := by
    intro γ hγ g
    rw [(GlobalTheory.mult_value_left_cont_level θ M J χ T hT v).1 γ hγ g,
      (GlobalTheory.mult_value_left_cont_level θ M J χ T' hT' v').1 γ hγ g]
  have key := GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 κ hκ
    (fun g => star (T v g) * T' v' g) hinv (hc v v').1
  rw [hfun]
  exact ⟨key.1, key.2.trans (hc v v').2⟩

end GlobalTheory
