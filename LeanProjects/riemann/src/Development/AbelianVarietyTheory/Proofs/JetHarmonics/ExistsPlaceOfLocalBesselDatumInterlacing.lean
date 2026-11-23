import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsPlaceWithVectors
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliParamMemIntAddHalf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapParamOfIsHCTypeW
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsType
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PlExists
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNormalisedLocalBesselDatumStatement

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA

namespace GlobalTheory.PlaceOfLocalBesselType

theorem isType_of_isHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (U : ℕ → ℝ) (Wp : Type)
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (π : B.Mat k r → (Wp →L[ℂ] Wp))
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hπ : Formalism.MainNotions.S.IsHCTypeW k r z u π)
    (hU : ∀ i : Fin k, U (i.val + 1) = u i) : Q.IsType k r z π U := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨u', h1, h2, h3, h4, h5, -⟩ := GlobalTheory.CapelliOfHC.exists_isType k r Wp z π u hz hT hπ'
  exact ⟨h1, h2, h3, h4, h5, GlobalTheory.ThA.capParam_of_isHCTypeW k r z u U Wp π hz hT hπ hU⟩

noncomputable def ext {k : ℕ} (u : Fin k → ℝ) (i : ℕ) : ℝ := if h : i - 1 < k then u ⟨i - 1, h⟩ else 0

theorem ext_succ {k : ℕ} (u : Fin k → ℝ) (i : Fin k) : ext u (i.val + 1) = u i := by
  simp [ext]

theorem add_one_le {a b c l : ℝ} (ha : ∃ m : ℤ, a = m + c) (hb : ∃ m : ℤ, b = m + c) (h1 : a < l) (h2 : l < b) :
    a + 1 ≤ b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have h : (m : ℝ) < n := by linarith
  have h' : m + 1 ≤ n := by exact_mod_cast h
  have h'' : (m : ℝ) + 1 ≤ n := by exact_mod_cast h'
  linarith

end GlobalTheory.PlaceOfLocalBesselType

namespace GlobalTheory

open PlaceOfLocalBesselType

theorem exists_place_of_locBessel : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  intro k r L μsec lam0 hk h2 hsec hI hI'
  have hk1 : 1 ≤ k := by omega
  obtain ⟨Bs, hBs⟩ := GlobalTheory.T.exists_normalised_localBesselDatum k r L μsec hk1 hsec
  obtain ⟨ν', m₀, hF⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frame_of Bs
  have hT := isType_of_isHCTypeW k r L.z L.u (ext L.u) L.Wp L.π L.hz.1 L.hz.2 L.hπ (ext_succ L.u)
  have hT' := isType_of_isHCTypeW k r L.z' L.u' (ext L.u') L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ' (ext_succ L.u')
  have hZ := GlobalTheory.capelliParam_mem_int_add_half k r L.Wp L.z L.π _ L.hz.1 L.hz.2 hT
  have hZ' := GlobalTheory.capelliParam_mem_int_add_half k r L.Wq L.z' L.π' _ L.hz'.1 L.hz'.2 hT'
  have h1 : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, hk1⟩
  have hOK : (⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ : M.Par).OK := by
    refine ⟨hk1, L.hz.2, L.hz'.2, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      obtain ⟨m, hm⟩ := hZ' i hi
      obtain ⟨n, hn⟩ := hZ 1 h1
      exact ⟨m - n, by dsimp only; rw [hm, hn]; push_cast; ring⟩
    · intro i hi
      dsimp only at hi
      rw [Finset.mem_Icc] at hi
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j + 1 < k := by omega
      have m1 : j + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have m2 : j + 1 + 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      obtain ⟨a1, a2⟩ := hI.1 j hj
      obtain ⟨b1, b2⟩ := hI'.1 j hj
      rw [← ext_succ L.u] at a1 a2
      rw [← ext_succ L.u'] at b1 b2
      dsimp only at a1 a2 b1 b2
      have c1 := add_one_le (hZ _ m2) (hZ _ m1) a2 a1
      have c2 := add_one_le (hZ _ m2) (hZ' _ m1) a2 b1
      have c3 := add_one_le (hZ' _ m2) (hZ _ m1) b2 a1
      have c4 := add_one_le (hZ' _ m2) (hZ' _ m1) b2 b1
      simp only [M.Par.lo, M.Par.hi]
      rcases max_choice (ext L.u (j + 1 + 1)) (ext L.u' (j + 1 + 1)) with e | e <;>
        rcases min_choice (ext L.u (j + 1)) (ext L.u' (j + 1)) with e' | e' <;> rw [e, e'] <;> linarith
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hBs
  obtain ⟨Cb, hCb⟩ := GlobalTheory.ThA.plExists
  obtain ⟨p, -, hp, -⟩ := hCb L.Wp L.Wq ⟨k, r, Tz k r L.z, Tz k r L.z', ext L.u, ext L.u'⟩ Bs ν' m₀ 1 le_rfl hk1 h2
    (by rw [e5]; exact L.hμW.2) (by rw [e6]; exact L.hμW'.2) e7 hF
    (by rw [e1, e2, e3, e4]; exact ⟨hOK, L.hz.1, L.hz'.1, rfl, rfl, hT, hT'⟩)
  refine ⟨ext L.u, ext L.u', p, fun i => ⟨ext_succ _ i, ext_succ _ i⟩, ?_⟩
  rw [hp]
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

end GlobalTheory
