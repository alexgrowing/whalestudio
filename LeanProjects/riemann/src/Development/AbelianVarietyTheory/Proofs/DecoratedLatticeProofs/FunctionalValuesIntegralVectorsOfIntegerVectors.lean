import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section

namespace GlobalTheory.FinPl.SplitPt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_max_iff_val_lt_one (x : 𝒪[k]) : x ∈ IsLocalRing.maximalIdeal 𝒪[k] ↔ valuation k (x : k) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem pr_incA_int_mem (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] :=
  (q.pr_mem_iff _).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he).1
    (Formalism.L2.DIV.oToS D.host.F D.host.E x).2)

theorem exists_int_approx (q : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt q.e PP)
    {u : k} (hu : u ∈ 𝒪[k]) : ∃ z : 𝓞 D.host.E, valuation k (u - q.pr (incA D (z : D.host.E))) < 1 := by
  have h1 : toEAf D (q.e * q.sec u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [map_mul]
    exact (q.pr_mem_iff (q.sec u)).1 (by rw [q.pr_sec]; exact hu)
  have h2 : q.pr (q.e * q.sec u) = u := by rw [← q.sec_pr, q.pr_sec, q.pr_sec]
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot
    (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)
  have ha : (⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈
    Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h3 := q.val_lt_of_mem_idS he ha
  have e2 : (((⟨_, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E a :
      Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (q.e * q.sec u) - toEAf D (incA D (a : D.host.E)) := rfl
  rw [e2, RingHom.map_sub, prF_toEAf, prF_toEAf, h2] at h3
  exact ⟨a, h3⟩

theorem hasVal_of_int_vectors : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ (m : ℕ) (b b' : Matrix (Fin m) (Fin m) k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) → ∀ c₀ : 𝓞 D.host.E,
    (∀ z : Fin m → D.host.E, (∀ r, IsIntegral ℤ (z r)) → ∀ r : Fin m, r.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D ((c₀ : D.host.E) * z r)) ∧
        P.HasVal (b' *ᵥ fun r' => p.pr (incA D (z r'))) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m, r0.1 + 1 = m →
      ∃ s : 𝒪[k], (s : k) = p.pr (incA D (c₀ : D.host.E)) * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s) := by
  intro D k _ _ _ _ p PP he m b b' hb _ P hlat c₀ hval u hu r0 hr0
  classical
  choose z hz using fun r => p.exists_int_approx he (hu r)
  obtain ⟨s, hs, hv⟩ := hval (fun r => (z r : D.host.E)) (fun r => (z r).isIntegral_coe) r0 hr0
  have hw : ∀ r, p.pr (incA D (z r : D.host.E)) ∈ 𝒪[k] := fun r => p.pr_incA_int_mem he (z r)
  let d : Fin m → 𝒪[k] := fun r => ⟨u r - p.pr (incA D (z r : D.host.E)), sub_mem (hu r) (hw r)⟩
  have hd : ∀ r, d r ∈ maximalIdeal 𝒪[k] := fun r => (mem_max_iff_val_lt_one (d r)).2 (hz r)
  have hcol : ∀ r, b' *ᵥ (Pi.single r 1 : Fin m → k) ∈ P.lat := fun r => (hlat _).2 fun r' => by
    rw [Matrix.mulVec_mulVec, hb, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have hker : ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) ∈ P.ker :=
    Submodule.sum_mem _ fun r _ => Pair.smul_mem_ker (hd r) (hcol r)
  have hsum : b' *ᵥ u = (b' *ᵥ fun r' => p.pr (incA D (z r' : D.host.E))) +
      ∑ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) := by
    have : ∀ r, d r • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = b' *ᵥ (Pi.single r (d r : k) : Fin m → k) := fun r => by
      change (d r : k) • (b' *ᵥ (Pi.single r 1 : Fin m → k)) = _
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun r _ => this r, ← Matrix.mulVec_sum, ← Matrix.mulVec_add, Finset.univ_sum_single]
    congr 1
    funext r
    simp [d]
  let c : 𝒪[k] := ⟨_, p.pr_incA_int_mem he c₀⟩
  refine ⟨s + c * d r0, ?_, ?_⟩
  · change (s : k) + p.pr (incA D (c₀ : D.host.E)) * (u r0 - p.pr (incA D (z r0 : D.host.E))) = _
    rw [hs, map_mul, map_mul]
    ring
  · rw [hsum, map_add, (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_left _ c (hd r0))]
    exact hv.add (Pair.mem_ker.1 hker)

end GlobalTheory.FinPl.SplitPt

end
