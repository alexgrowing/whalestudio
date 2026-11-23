import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftAtPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreSectionLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRelLift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem LiftAtPrime.proof (hC : GeneratedPow.Statement) (hA : FibreSectionLift.Statement)
    (hB : FibreRelLift.Statement) : LiftAtPrime.Statement := by
  classical
  intro K _ _ ι _ _ Ω _ _ y D N p hY hp hN
  obtain ⟨q, hq, hgen, hvan⟩ := hN
  obtain ⟨t₀, ht₀⟩ := hvan 0
  refine ⟨q, t₀, hq, fun t ht => ?_⟩
  have hga : KH.GeneratedV (ZMod p) (fibreIdeal p y) ((t * q) • N) := by
    have h := hC (ZMod p) K ι (fibreIdeal p y) (q • N) t hgen
    rwa [smul_smul] at h
  have hH1 : Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) ((t * q) • N) 1) := by
    have h := ht₀ t ht
    rwa [zero_add] at h
  have hfi : fibreIdeal p y = GenOnFibres.idealOver y (ZMod p) := rfl
  rw [hfi] at hga hH1
  choose r z u hz hu hrel using hga
  have hlift : ∀ I j, ∃ s ∈ chartLat y ((t * q) • N) 1,
      GenOnFibres.secCoch y (ZMod p) s ((t * q) • N) = z I j :=
    fun I j => hA K ι Ω y D p ((t * q) • N) hY hp hH1 (z I j) (hz I j)
  choose s hs hsz using hlift
  have : Finite (KH.Cell K ι 0) := by unfold KH.Cell; infer_instance
  have : Fintype (KH.Cell K ι 0) := Fintype.ofFinite _
  let e := (Fintype.equivFin (Σ I, Fin (r I))).symm
  refine ⟨Fintype.card (Σ I, Fin (r I)), fun j => s (e j).1 (e j).2, fun j => hs _ _, fun c hc => ?_⟩
  let J : KH.Cell K ι 0 := ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩
  have hJ : GenOnFibres.cellChart J = c :=
    funext fun k => Finset.mem_singleton.mp (GenOnFibres.cellChart_mem J k)
  have hrelJ : ∑ j, u J j * GenOnFibres.secCoch y (ZMod p) (s J j) ((t * q) • N) J = 1 := by
    rw [← hrel J]
    exact Finset.sum_congr rfl fun j _ => by rw [hsz J j]
  obtain ⟨u', v, hu', hv, hsum⟩ :=
    hB K ι Ω y p ((t * q) • N) (r J) (s J) J (u J) (hs J) (by rw [hJ]; exact hc) (hu J) hrelJ
  rw [hJ] at hu' hv hsum
  let U : (Σ I, Fin (r I)) → Ω := fun x => if h : x.1 = J then u' (Fin.cast (congrArg r h) x.2) else 0
  refine ⟨fun j => U (e j), v, fun j => ?_, hv, ?_⟩
  · simp only [U]
    split_ifs
    · exact hu' _
    · exact zero_mem _
  · rw [← hsum]
    congr 1
    rw [e.sum_comp (fun x => U x * (s x.1 x.2 * ∏ k, y ⟨k, c k⟩ ^ (-((t * q) • N) k))),
      Fintype.sum_sigma, Finset.sum_eq_single J]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp [U]
    · intro I _ hI
      exact Finset.sum_eq_zero fun j _ => by simp [U, hI]
    · intro h
      exact absurd (Finset.mem_univ J) h

end GroundTheory.Heights₂.Heights.HilbertSamuel
