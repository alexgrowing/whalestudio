import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocMod.SevPl

open GlobalTheory.IdemSupport

theorem ev_sum {D : D7} {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {ι : Type}
    (s : Finset ι) (f : ι → Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (∑ i ∈ s, f i) Q = ∑ i ∈ s, Φ (f i) Q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]; exact ev_zero Q
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ev_add, ih]

theorem cP_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) : cP (D := D) (cP (D := D) P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by
    show cO D (cO D x) ∈ P.asIdeal ↔ x ∈ P.asIdeal
    rw [cO_cO])

theorem mul_conj_add_eq_zero {D : D7} {Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))} {E : Formalism.L2.Theta.AE D}
    (hE : IsIdemSum E Pg) {P P' : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Pg) (hP' : P' ∈ Pg) (hne : P ≠ P')
    {e e' : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P') :
    e * (e' + cA D e') = 0 := by
  classical
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ he
  have hd' := delta_of_isIdemAt hΦ he'
  have hc' := delta_conj hΦ hd'
  have hne2 : P ≠ cP (D := D) P' := by
    intro hPc
    obtain ⟨⟨es, hes, rfl⟩, h0⟩ := hE
    have h1 : Φ (∑ Q ∈ Pg, es Q) P = 1 := by
      rw [ev_sum, Finset.sum_eq_single_of_mem P hP fun Q hQ hQP => ?_]
      · exact (delta_of_isIdemAt hΦ (hes P hP)).2.1
      · exact (delta_of_isIdemAt hΦ (hes Q hQ)).2.2 P (Ne.symm hQP)
    have h2 : Φ (cA D (∑ Q ∈ Pg, es Q)) P = 1 := by
      rw [map_sum, ev_sum, Finset.sum_eq_single_of_mem P' hP' fun Q hQ hQP => ?_]
      · rw [hPc]; exact (delta_conj hΦ (delta_of_isIdemAt hΦ (hes P' hP'))).2.1
      · refine (delta_conj hΦ (delta_of_isIdemAt hΦ (hes Q hQ))).2.2 P fun h => hQP ?_
        have h4 := congrArg (cP (D := D)) (h.symm.trans hPc)
        rwa [cP_cP, cP_cP] at h4
    have h3 := ev_mul (Φ := Φ) (∑ Q ∈ Pg, es Q) (cA D (∑ Q ∈ Pg, es Q)) P
    rw [h0, ev_zero, h1, h2, one_mul] at h3
    exact zero_ne_one h3
  refine hΦ.ext' (by rw [map_mul, hd.1, zero_mul, map_zero]) fun Q => ?_
  rw [ev_mul, ev_add, ev_zero]
  by_cases hQ : Q = P
  · subst hQ; rw [hd'.2.2 Q hne, hc'.2.2 Q hne2, add_zero, mul_zero]
  · rw [hd.2.2 Q hQ, zero_mul]

theorem pr_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {f : Formalism.L2.Theta.AE D} (h : q.e * f = 0) : q.pr f = 0 := by
  rw [← q.pr_sec (q.pr f), q.sec_pr, h, map_zero]

theorem map_mt_eq_one {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) {e : Formalism.L2.Theta.AE D}
    (V : HSp D) (g : GA D V) (hs : Formalism.L2.Theta.SuppAt e V g) (h0 : π (e + cA D e) = 0) :
    (mt V g).map π = 1 := by
  ext i j
  have h1 := congrArg π (hs i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1.symm]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

def locHom {D : D7} {k : Type} [Field k] (π : Formalism.L2.Theta.AE D →+* k) (V : HSp D) :
    GA D V →* Matrix (Fin V.rank) (Fin V.rank) k where
  toFun g := (mt V g).map π
  map_one' := by rw [GlobalTheory.IdemSupport.mt_one]; exact Matrix.map_one π π.map_zero π.map_one
  map_mul' g h := by rw [GlobalTheory.IdemSupport.mt_mul, Matrix.map_mul]

theorem prod_map_single {M α : Type} [Monoid M] (g : α → M) (a : α) :
    ∀ l : List α, l.Nodup → a ∈ l → (∀ x ∈ l, x ≠ a → g x = 1) → (l.map g).prod = g a
  | [], _, ha, _ => by simp at ha
  | x :: l, hn, ha, h1 => by
    rw [List.map_cons, List.prod_cons]
    obtain ⟨hx, hl⟩ := List.nodup_cons.1 hn
    by_cases hxa : x = a
    · subst hxa
      rw [List.prod_eq_one fun y hy => ?_, mul_one]
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact h1 z (List.mem_cons_of_mem _ hz) fun h => hx (h ▸ hz)
    · rw [h1 x (by simp) hxa, one_mul]
      exact prod_map_single g a l hl ((List.mem_cons.1 ha).resolve_left (Ne.symm hxa))
        fun y hy => h1 y (List.mem_cons_of_mem _ hy)

end GlobalTheory.LocMod.SevPl

end
