import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeDefinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HostBC

theorem spehSat_eq (q d : ℕ) (B : Multiset ℂˣ) : GlobalTheory.SphGal.spehSat q d B =
    ∑ k : Fin d, B.map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))) := by
  unfold GlobalTheory.SphGal.spehSat
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => Multiset.map_congr rfl fun z _ => ?_
  have hk : ((k.rev : ℕ) : ℂ) = d - (k + 1) := by
    rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt k.2)]
    push_cast
    rfl
  simp only [Fin.revPerm_apply, hk]
  congr 2
  ring

theorem bcPar_eq (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    bcPar n (fun i => (α i : ℂ)) = (GlobalTheory.LGrp.bcParam n α).map (fun z : ℂˣ => (z : ℂ)) := by
  simp [bcPar, GlobalTheory.LGrp.bcParam, Multiset.map_add, Multiset.map_map, Function.comp_def, Multiset.map_replicate]

end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC

theorem sum_map_val {c : ℕ} (q : ℕ) (d : Fin c → ℕ) (B S : Fin c → Multiset ℂˣ)
    (h : ∀ i, ∑ k : Fin (d i), (B i).map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
      (S i).map (fun z : ℂˣ => (z : ℂ))) :
    (∑ i, S i).map (fun z : ℂˣ => (z : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat q (d i) (B i) := by
  refine (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spehSat_eq, h]
  rfl

end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC

theorem baseChange_speh : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.DiscreteSpectrumGL →
    ∀ (D : D7) (n : ℕ),
    haveI := host_isCMField D.host
    ∀ U : Submodule ℂ (UA D.host.E n → ℂ), IsAutRepU U →
    ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
      (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = n ∧
      (∀ (τ : D.host.E →+* ℂ) (lam : DomWeight n), HasWeightAt U τ lam → ∃ A A' : Fin r → Multiset ℂ,
        (∀ i, (π i).HasInfChar τ (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate τ) (A' i)) ∧
        ∑ i, GlobalTheory.SphGal.spehInf (d i) (A i) = infOfWeight lam ∧
        ∑ i, GlobalTheory.SphGal.spehInf (d i) (A' i) = (infOfWeight lam).map fun z => -z) ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), IsUnramU U P → ∃ B : Fin r → Multiset ℂˣ,
        (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
        (Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal →
          ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X)
            (ρ : Representation ℂ (GL (Fin n) (P.adicCompletion D.host.E)) X),
            IsCompAlong U (locU n P) ((cLoc P).comp (locU n P).subtype) ρ ∧ ∃ Bs : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL P ρ Bs ∧
              Bs.map (fun b : ℂˣ => (b : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i)) ∧
        (Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal →
          ∀ (σ : P.adicCompletion D.host.E →+* P.adicCompletion D.host.E) (ϖ : P.adicCompletion D.host.E) (q : ℕ),
            IsConjAt P σ → IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, HasSatAt U P σ ϖ q α →
              bcPar n (fun i => (α i : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i)) := by
  intro hNT hMW D n
  haveI := host_isCMField D.host
  intro U hU
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp,
      fun τ lam _ => ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, by simp [infOfWeight], by simp [infOfWeight]⟩,
      fun Pl _ => ⟨Fin.elim0, fun i => i.elim0, fun _ => ?_, fun _ s ϖ q _ _ α _ => by simp [bcPar]⟩⟩
    have hT := GlobalTheory.LFun.Model.hasSatGL_trivial Pl 0
    have h0 : GlobalTheory.LFun.seg Pl 1 0 = 0 := Multiset.card_eq_zero.1 hT.card
    obtain ⟨φ, hφ, hφ0⟩ := (Submodule.ne_bot_iff _).1 hU.ne_bot
    have hone : ∀ x : UA D.host.E 0, x = 1 := fun x => Subtype.ext (Subsingleton.elim _ _)
    refine ⟨ℂ, _, _, Representation.trivial ℂ _ ℂ, ⟨(SmIrr.triv _).irred, LinearMap.toSpanSingleton ℂ _ φ,
      fun e => hφ0 (by simpa using LinearMap.congr_fun e 1), fun v => Submodule.smul_mem _ _ hφ, fun x v => ?_⟩,
      _, hT, by simp [h0]⟩
    rw [hone x.1]
    simp
  obtain ⟨c, N, h, V, σ, m, bc⟩ := hNT D.host.E (host_unramified D.host) n hn U hU
  choose a d P hPu hPn hPs using fun i => (hMW D.host.E (N i) (bc.pos i)).1 (V i) (bc.discrete i)
  have hNad : ∀ i, d i * a i = N i := fun i => (hPs i).mul_eq
  have hc : ∀ i, HasSpehComp (V i) (P i) (d i) := fun i =>
    (hMW D.host.E (N i) (bc.pos i)).2.2.2.2 (V i) (bc.discrete i) _ _ (P i) (hPn i) (hPs i)
  have hpos : ∀ i, 1 ≤ a i ∧ 1 ≤ d i := fun i => by
    have h1 := bc.pos i
    rw [← hNad i] at h1
    exact ⟨Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at h1, Nat.one_le_iff_ne_zero.2 fun e => by simp [e] at h1⟩
  choose ρ σ' hρ hσ' using fun i w => (hc i).exLoc w
  have hsp : ∀ i w, GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of (ρ i w).ρ (ρ i w).smooth (ρ i w).irred) (d i) (σ i w).ρ :=
    fun i w => (hc i).loc w (ρ i w) (σ i w) (hρ i w) (bc.loc i w)
  choose A hA1 hA2 using fun i τ => (hc i).inf τ
  have hmA : ∀ i τ, m i τ = GlobalTheory.SphGal.spehInf (d i) (A i τ) := fun i τ =>
    GlobalTheory.BcSpehProof.hasInfCharGL_unique (bc.discrete i).ne_bot (bc.inf i τ) (hA2 i τ)
  refine ⟨c, a, d, P, fun i => ⟨(hpos i).1, (hpos i).2,
    isCsd_of_isSpehOf hMW (bc.pos i) (bc.discrete i) (bc.csd i) (hPn i) (hPs i)⟩, ?_, ?_, ?_⟩
  · rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [← hNad i, mul_comm]
  · intro τ lam hl
    refine ⟨(A · τ), (A · (ComplexEmbedding.conjugate τ)), fun i => ⟨hA1 i τ, hA1 i _⟩, ?_, ?_⟩
    · rw [← bc.weight τ lam hl]
      exact Finset.sum_congr rfl fun i _ => (hmA i τ).symm
    · rw [← infOfWeight_dual, ← bc.weight _ _ (hasWeightAt_conjugate hn hl)]
      exact Finset.sum_congr rfl fun i _ => (hmA i _).symm
  · intro Pl hUn
    obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).1 (bc.unram Pl hUn)
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (π := fun i => (σ i Pl).ρ) (fun i => (σ i Pl).smooth)
      (fun i => (σ i Pl).irred) hf hf0
    choose B hB hBS using fun i => GlobalTheory.SatInd.exists_sat_of_isSpeh (hpos i).2 (ρ i Pl).smooth (ρ i Pl).irred
      (hsp i Pl) (hS i)
    have key : (∑ i, S i).map (fun z : ℂˣ => (z : ℂ)) =
        ∑ i, GlobalTheory.SphGal.spehSat (Formalism.ConjugateSelfDual.normV Pl) (d i) (B i) := by
      rw [GlobalTheory.BlockVal.normV_eq_absNorm]
      exact sum_map_val _ d B S hBS
    refine ⟨B, fun i => (CG.hasSat_mk _ _ _).1 ((GlobalTheory.BcSpehCompare.hasSat_iff (hρ i Pl) _).2 (hB i)), fun hne => ?_,
      fun _ s ϖ q hs hUI α hα => ?_⟩
    · have hsplit : IsSplitAt Pl := isSplitAt_of_isSplitPl ((GlobalTheory.HeckeTieCompare.isSplitPl_iff Pl).2 hne)
      have hcomp := bc.split Pl hsplit
      have hsm : GlobalTheory.PRep.IsSmooth (locProd h Pl (σ · Pl)) := GlobalTheory.SmGL.isSmooth_parInd _ _
      obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible hsm hcomp.1 (bc.unram Pl hUn)
      refine ⟨_, _, _, _, hcomp, T, hT, ?_⟩
      rw [(hT.2 f hf hf0).unique hfS, key]
    · have hs' : ∀ x : D.host.E, s (algebraMap _ _ x) = algebraMap _ _ (IsCMField.complexConj D.host.E x) := hs
      have hI := bc.inert Pl s ϖ q hs' hUI α hα
      rw [bcPar_eq, (hI.2 f hf hf0).unique hfS, key]

end GlobalTheory.HostBC

end
