import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem hodge_of_adapted : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K K' : FinExt l) (a : ℕ) (ρ : ↥(GK K) → Matrix (Fin a) (Fin a) (Om l)) (w : Fin a → Fin a → P.R.BdR) (k : Fin a → ℤ), (∀ i j, w i j ∈ (P.PD K).Fil (k i)) → (∀ j, ∃ u : Fin a → P.R.BdR, (∀ i, u i ∈ (P.PD K).Fil (-k i)) ∧ ∑ i, u i • w i = Pi.single j 1) → (∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → ∀ i, (ρ g).map (algebraMap (Om l) P.R.BdR) *ᵥ (fun j => P.actQdR (g : GQ l) (w i j)) = w i) → ∃ H : Hodge C ξ ρ K', ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = ∑ i, if k i = n then 1 else 0 := by
  intro l _ P AI T C hFit ξ hξ K K' a ρ w k hw hspan hinv
  classical
  set ι := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  obtain ⟨-, hinj, -, -⟩ := BdRField.bdR_isField l

  have hE : IsUnit (ι (aDp l ξ)) := by
    have hxiker : xi C.ε ∈ Ideal.span {ξ} := by
      rw [hξ, C.ker_theta]; exact Ideal.mem_span_singleton_self _
    obtain ⟨c0, hc0⟩ := Ideal.mem_span_singleton'.1 hxiker
    have h1 := GlobalTheory.MemLoc.TiedUnif.isUnit_xi (core_isEps l C)
    rw [← hc0, map_mul, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1

  set q : ℕ := ∑ i, (k i).natAbs with hq
  have hkq : ∀ i, 0 ≤ k i + q := by
    intro i
    have h1 : (k i).natAbs ≤ q := Finset.single_le_sum (f := fun i => (k i).natAbs) (by simp) (Finset.mem_univ i)
    omega
  set p : Fin a → ℕ := fun i => (k i + q).toNat with hp
  have hkp : ∀ i, k i + q = (p i : ℤ) := fun i => (Int.toNat_of_nonneg (hkq i)).symm

  have hV0 : ∀ i j, ∃ v : Per.BdRp l, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * v) :=
    fun i j => exists_xi_pow_mul l P AI T C ξ hξ K (k j) q (p j) (hkp j) (w j i) (hw j i)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin a) (Fin a) (Per.BdRp l), ∀ i j, ι (aDp l ξ) ^ q * T.eD (w j i) = ι (aDp l ξ ^ p j * V i j) :=
    ⟨fun i j => Classical.choose (hV0 i j), fun i j => Classical.choose_spec (hV0 i j)⟩

  choose u hu hsum using hspan
  have hz0 : ∀ j i, ∃ z : Per.BdRp l, ι (aDp l ξ) ^ p i * T.eD (u j i) = ι (aDp l ξ ^ q * z) :=
    fun j i => exists_xi_pow_mul l P AI T C ξ hξ K (-k i) (p i) q (by have := hkp i; omega) (u j i) (hu j i)
  choose z hz using hz0
  have key : ∀ j j', ∑ i, z j i * V j' i = if j' = j then 1 else 0 := by
    intro j j'
    apply hinj
    have hs := congrFun (hsum j) j'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
    have h1 : ι (aDp l ξ) ^ q * ι (∑ i, z j i * V j' i) =
        ι (aDp l ξ) ^ q * T.eD (∑ i, u j i * w i j') := by
      rw [map_sum, map_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have ha := hV j' i
      have hb := hz j i
      simp only [map_mul, map_pow] at ha hb ⊢
      calc ι (aDp l ξ) ^ q * (ι (z j i) * ι (V j' i))
          = (ι (aDp l ξ) ^ q * ι (z j i)) * ι (V j' i) := by ring
        _ = (ι (aDp l ξ) ^ p i * T.eD (u j i)) * ι (V j' i) := by rw [hb]
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ p i * ι (V j' i)) := by ring
        _ = T.eD (u j i) * (ι (aDp l ξ) ^ q * T.eD (w i j')) := by rw [ha]
        _ = ι (aDp l ξ) ^ q * (T.eD (u j i) * T.eD (w i j')) := by ring
    rw [(hE.pow q).mul_left_cancel h1, hs, Pi.single_apply]
    split_ifs <;> simp
  set N : Matrix (Fin a) (Fin a) (Per.BdRp l) := Matrix.of fun i j => z j i with hN
  have hVN : V * N = 1 := by
    ext j' j
    rw [Matrix.mul_apply, Matrix.one_apply, ← key j j']
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hN, Matrix.of_apply]; ring
  have hNV : N * V = 1 := mul_eq_one_comm.1 hVN
  refine ⟨⟨V, ⟨⟨V, N, hVN, hNV⟩, rfl⟩, p, q, Matrix.of fun i j => T.eD (w j i), fun i j => by simpa using hV i j, ?_⟩, ?_⟩
  · intro g hg
    ext r c
    have h := congrArg T.eD (congrFun (hinv g hg c) r)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, T.actD, hFit.o] at h
    rw [Matrix.mul_apply]
    simpa [Matrix.map_apply, Matrix.of_apply, GlobalTheory.MemLoc.Core.oD] using h
  · intro n
    have hf : (Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n) = Finset.univ.filter fun i => k i = n := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := hkp i
      omega
    show ((Finset.univ.filter fun i => ((p i : ℕ) : ℤ) - (q : ℤ) = n).card : ℤ) = _
    rw [hf, Finset.card_filter]
    push_cast
    rfl

end GlobalTheory.HodgeAt
