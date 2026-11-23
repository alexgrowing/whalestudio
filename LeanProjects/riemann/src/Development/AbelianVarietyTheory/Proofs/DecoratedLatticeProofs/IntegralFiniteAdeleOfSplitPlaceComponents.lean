import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem GlobalTheory.IntPlaces.mem_of_idem_sum {R : Type} [CommRing R] {n : ℕ} (S : Set R) (hS0 : (0 : R) ∈ S)
    (E : Fin n → R) (hEE : ∀ i, E i * E i = E i) (hE : ∀ i j, i ≠ j → E i * E j = 0) (G : Fin n → R → Prop)
    (hint : ∀ i z, z ∈ S ↔ (1 - E i) * z ∈ S ∧ G i z) (hG : ∀ i j z, i ≠ j → G i z → G i ((1 - E j) * z)) :
    ∀ z, (∑ i, E i) * z = z → (∀ i, G i z) → z ∈ S := by
  have key : ∀ s : Finset (Fin n), ∀ z, (∑ i ∈ s, E i) * z = z → (∀ i ∈ s, G i z) → z ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      rw [Finset.sum_empty, zero_mul] at hz
      rw [← hz]
      exact hS0
    | insert a s ha ih =>
      intro z hz hzi
      rw [Finset.sum_insert ha] at hz
      refine (hint a z).2 ⟨?_, hzi a (Finset.mem_insert_self a s)⟩
      have hET : E a * ∑ i ∈ s, E i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => hE a i fun h => ha (h ▸ hi)
      have hw : (1 - E a) * z = (∑ i ∈ s, E i) * z := by
        calc (1 - E a) * z = (1 - E a) * ((E a + ∑ i ∈ s, E i) * z) := by rw [hz]
          _ = (∑ i ∈ s, E i) * z := by linear_combination (-z) * hEE a + (-z) * hET
      refine ih _ ?_ fun i hi => ?_
      · linear_combination (-1 : R) * hw + (-z) * hET
      · exact hG i a z (fun h => ha (h ▸ hi)) (hzi i (Finset.mem_insert_of_mem hi))
  exact fun z hz hzi => key Finset.univ z hz fun i _ => hzi i

open GlobalTheory.IdemSupport in

theorem GlobalTheory.IntPlaces.mem_intAf_of_split : ∀ (D : D7) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (P : Fin n → Formalism.L2.DIV.Pl D.host.E), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (P i)) → Function.Injective P → ∀ (π' : ∀ i, Formalism.IndefR.Datum.EAf D →+* k i), (∀ i a, π' i (Formalism.IndefR.Datum.toEAf D a) = (q i).pr a) → (∀ i (z : Formalism.IndefR.Datum.EAf D), z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ (1 - Formalism.IndefR.Datum.toEAf D (q i).e) * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ π' i z ∈ 𝒪[k i]) → ∀ z : Formalism.IndefR.Datum.EAf D, Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) * z = z → (∀ i, π' i z ∈ 𝒪[k i]) → z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D n k _ _ _ _ q P hI hP π' hπ hint z0 hz0 hzi0
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd : ∀ i, IsDelta ((GlobalTheory.StdFrames.toAd D).comp (Formalism.IndefR.Datum.toEAf D)) (P i) (q i).e :=
    fun i => delta_of_isIdemAt hΦ (hI i)
  have horth : ∀ i j, i ≠ j → (q i).e * (q j).e = 0 := by
    intro i j hij
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P i
    · rw [(hd j).2.2 Q (fun h => hij (hP (hQ.symm.trans h))), mul_zero]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hidem : ∀ i, (q i).e * (q i).e = (q i).e := by
    intro i
    refine hΦ.ext' (by rw [RingHom.map_mul, (hd i).1, zero_mul]) fun Q => ?_
    rw [ev_mul]
    by_cases hQ : Q = P i
    · rw [hQ, (hd i).2.1, mul_one]
    · rw [(hd i).2.2 Q hQ, zero_mul]
  have hpr : ∀ i j, i ≠ j → π' i (Formalism.IndefR.Datum.toEAf D (q j).e) = 0 := by
    intro i j hij
    rw [hπ, ← (q i).pr_sec ((q i).pr (q j).e), (q i).sec_pr, horth i j hij, map_zero]
  refine GlobalTheory.IntPlaces.mem_of_idem_sum (Formalism.L2.Herm.intAf D.host.F D.host.E : Set _) (zero_mem _)
    (fun i => Formalism.IndefR.Datum.toEAf D (q i).e) (fun i => by rw [← RingHom.map_mul, hidem])
    (fun i j hij => by rw [← RingHom.map_mul, horth i j hij, RingHom.map_zero]) (fun i z => π' i z ∈ 𝒪[k i])
    hint (fun i j z hij hz => ?_) z0 (by rw [show (∑ i, Formalism.IndefR.Datum.toEAf D (q i).e) = Formalism.IndefR.Datum.toEAf D (∑ i, (q i).e) from
      (map_sum (Formalism.IndefR.Datum.toEAf D).toAddMonoidHom (fun i => (q i).e) Finset.univ).symm]; exact hz0) hzi0
  rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hpr i j hij, sub_zero, one_mul]
  exact hz
