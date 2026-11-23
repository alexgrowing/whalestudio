import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitCont

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.LTChar

theorem char_cont : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T K x h1 h2 c hc
  obtain ⟨-, -, hsh, -, -, -, -, hact, -⟩ := GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨S, θ, hS, -, hker, hOm, hθ⟩ := GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
    have := (hsh 1 (-1) _).1 h1
    simpa using this
  have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
    intro h
    apply h2
    rw [hsh 2 (-1)]
    simpa using h
  set u : S := ⟨tz P (-1) * P.ιB x, (hS _).2 hu0⟩ with hu
  have hy : θ u ≠ 0 := fun h => hu1 ((hker u).1 h)
  have key : ∀ g : ↥(GK K), (((c g : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) * Formalism.Per.σC (g : GQ l) (θ u) / θ u := by
    intro g
    obtain ⟨hg, hg'⟩ := hθ g u
    obtain ⟨ha, ha'⟩ := hOm (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨hb, hb'⟩ := hOm ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)
    have e : (⟨_, ha⟩ : S) * ⟨_, hg⟩ = ⟨_, hb⟩ * u := by
      apply Subtype.ext
      show algebraMap (Om l) P.R.BdR _ * P.actQdR g (tz P (-1) * P.ιB x) = kd P (c g) * (tz P (-1) * P.ιB x)
      rw [map_mul, hact, ← iota_act, hc, map_mul, iota_kur, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul]
      simp only [zpow_neg, zpow_one, mul_inv_cancel, Units.val_one, map_one]
      ring
    have e' := congrArg θ e
    rw [map_mul θ, map_mul θ, ha', hb', hg'] at e'
    rw [eq_div_iff hy, ← e']
    rfl
  have hemb : Topology.IsEmbedding (fun y : Om l => (y : ℂ_[l])) :=
    UniformSpace.Completion.coe_isometry.isEmbedding
  refine hemb.continuous_iff.2 ?_
  have : ((fun y : Om l => (y : ℂ_[l])) ∘ fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)) = _ := funext key
  rw [this]
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact (continuous_algebraMap ℚ_[l] ℂ_[l]).comp
      ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
  · exact (orbit_cont (θ u)).comp continuous_subtype_val

end GlobalTheory.LTChar
