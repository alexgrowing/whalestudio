import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryOfTraceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGramStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.TwistInt

set_option maxHeartbeats 1000000 in

theorem mul_twist_mem_intForms : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ C : Cover T j T.σ₀, C.IsUnif → (∃ φ : D.host.K →+* C.d.c₂.F, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ C.d.l₂.M) → ∀ xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsTwist C.σ₂ C.d.pd xi → ∀ (wa : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (S : Set (HeightOneSpectrum (𝓞 C.d.c₂.F))), ∀ φ ∈ C.intForms wa n S, (fun g => ((xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) : ℂˣ) : ℂ) * φ g) ∈ C.intForms wa n S := by
  intro D T hL j hj C hU hRay xi hxi wa n S φ hφ
  have hP : T.Q.Pins := hL.pins
  have hlev : C.d.l₂.M = T.Q.l.M * C.d.pd := hU.1.2.1
  have hM3 : 3 ≤ C.d.l₂.M := C.d.l₂.three_le
  have hpd : 0 < C.d.pd := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hlev; omega

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [show T.Q.H.d = D.host.d from hP.1.1]
    apply Subtype.ext
    have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
    simpa using hb
  obtain ⟨φK, hφK⟩ := hRay
  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K C.d.c₂.F φK C.d.c₂.F.val.toRingHom (Formalism.L2.Pj.LPb.finrank_K D) hsq
    C.d.l₂.M hM3 hφK).1
  have hWc : GlobalTheory.FinalJoin.WeberIn T.Q.H C.d.c₂.F C.d.l₂.M := fun P hP' => by
    have hsub : ∀ z ∈ C.d.c₂.F.val.toRingHom.toRatAlgHom.fieldRange, z ∈ C.d.c₂.F := fun z hz' => by
      obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.1 hz'
      exact y.2
    obtain ⟨a1, a2⟩ := hW P hP'
    exact ⟨hsub _ a1, fun s hs => hsub _ (a2 s hs)⟩

  have hno : ∀ g : GA D (T.V j T.σ₀),
      GlobalTheory.FinalJoin.NormOne (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) := fun g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).1 g
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact GlobalTheory.NormOneTwist.normOne_finQuot x
  obtain ⟨m, hm, hexp⟩ := GlobalTheory.XiCounterexample.fin_of_rat_tame D C.d.pd hpd xi hxi.rat hxi.cond
  choose w hw using fun g => hxi.val _ (hno g)
  have hinj : ∀ g g', xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g)) =
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) g')) → w g = w g' :=
    fun g g' h => C.σ₂.injective (by rw [hw, hw, h])
  have hleft : ∀ γ ∈ GQ (T.V j T.σ₀), xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) γ)) = 1 := by
    intro γ hγ
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (T.V j T.σ₀)).2.2.1 γ hγ
    rw [← GlobalTheory.NormOneTwist.finQuot_of_isDetRoot hx]
    exact hxi.rat _ _ (GlobalTheory.NormOneTwist.finQuot_incA x) (GlobalTheory.NormOneTwist.normOne_finQuot _)
  have hright : ∀ u : GA D (T.V j T.σ₀), GlobalTheory.Member.FinCong (T.V j T.σ₀) C.d.l₂.M u →
      xi (Matrix.GeneralLinearGroup.det (finHom (T.V j T.σ₀) u)) = 1 := by
    intro u hu
    obtain ⟨k1, -, k3, k4, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D (T.V j T.σ₀)
    obtain ⟨w', hw', e⟩ := GlobalTheory.CharRead.det_cong_one D.host.F (GlobalTheory.Member.latC (T.V j T.σ₀)) k3 k4 C.d.l₂.M (by omega)
      (finHom (T.V j T.σ₀) u).1 (by rw [← k1]; exact hu)
    refine hxi.cond _ (hno u) ⟨T.Q.l.M • w', AddSubgroup.nsmul_mem _ (GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers D ▸ hw') _, ?_⟩
    rw [smul_smul, mul_comm, ← hlev]
    exact e
  have key := (GlobalTheory.CoverComp.forms_mul_comp D T hL j hj T.σ₀ rfl C hU C.d.l₂.M (by omega) dvd_rfl (Or.inl hWc) w
    (fun h h' hh => hinj _ _ (by rw [hh]))
    (fun γ hγ h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hleft γ hγ, one_mul]))
    (fun u _ hu2 h => hinj _ _ (by rw [map_mul, map_mul, map_mul, hright u hu2, mul_one])) wa n).2 S ?_ φ hφ
  · simpa only [hw] using key
  · intro la _ h
    have hpow : w h ^ m = 1 := C.σ₂.injective (by
      rw [map_pow, hw, map_one, ← Units.val_pow_eq_pow_val, hexp _ (hno h), Units.val_one])
    have hint : IsIntegral ℤ (w h) := IsIntegral.of_pow hm (by rw [hpow]; exact isIntegral_one)
    have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := C.d.c₂.F) la (⟨w h, hint⟩ : 𝓞 C.d.c₂.F)
    exact this

end GlobalTheory.TwistInt
