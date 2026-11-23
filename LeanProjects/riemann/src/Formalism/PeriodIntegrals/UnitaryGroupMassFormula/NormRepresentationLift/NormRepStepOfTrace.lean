import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Formalism.PeriodIntegrals.NormRepLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.IntLatOfUnimod
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.PreRowvec

noncomputable section

open scoped Classical

namespace PI.NRL

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TraceOne (D : D7) : Prop := ∃ ω : 𝓞 D.host.E, (ω : D.host.E) + star (ω : D.host.E) = 1

theorem rowVec_of (D : D7) (u : D.what₂.Word) (T' : ℕ) (htr : Odd (gS D) ∨ TraceOne D) :
    RowVec D u T' := by
  intro hP F0 Λ hΛ a t
  have hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hint : IntLat Λ := intLat_of_unimod Λ hU
  have hz : F0.z ∈ Λ := hΛ.2.1.2.2.1.1
  have he : ∀ i, F0.e i ∈ Λ := fun i => e_mem_lam D F0 Λ hΛ i
  have hlocg : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      ∀ x ∈ Λ, x ∈ Submodule.span D.host.E (Set.range F0.e) →
        ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x ∈ Submodule.span (𝓞 D.host.E) (Set.range F0.e) := by
    intro P hg x hx hxE
    haveI := P.isPrime
    obtain ⟨c, _, hc1, hceq⟩ := hΛ.2.1.2.2.2.1 P
    have hxX : x ∈ XLam Λ (lf D F0) := Submodule.mem_inf.mpr ⟨hx, hxE⟩
    have hxl : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) :=
      ⟨1, (Ideal.primeCompl P.asIdeal).one_mem, by simpa using hxX⟩
    rw [hceq] at hxl
    obtain ⟨s, hs, hsx⟩ := hxl
    have hfun : (fun a => c a • (lf D F0).fl.e a) = F0.e := by
      funext a; rw [hc1 hg a, one_smul]
    rw [hfun] at hsx
    exact ⟨s, hs, hsx⟩
  have hdual := fun c => global_dual Λ hU hint F0.e F0.e_indep he ((gS D : ℕ) : 𝓞 D.host.E) hlocg c
  have hcop : Nat.Coprime (Tu D u) (gS D) :=
    (Nat.Coprime.coprime_mul_right_right hP.2.2.2.2.2.2.2.1).symm
  have hTg : ∃ x y : 𝓞 D.host.E, x * ((Tu D u : ℕ) : 𝓞 D.host.E) + y * ((gS D : ℕ) : 𝓞 D.host.E) = 1 := by
    refine ⟨((Nat.gcdA (Tu D u) (gS D) : ℤ) : 𝓞 D.host.E), ((Nat.gcdB (Tu D u) (gS D) : ℤ) : 𝓞 D.host.E), ?_⟩
    have h := Nat.gcd_eq_gcd_ab (Tu D u) (gS D)
    rw [hcop.gcd_eq_one] at h
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) h
    push_cast at this
    rw [this]; ring
  obtain ⟨v, hv, hv0, hvc⟩ := pre_rowvec Λ hint (Tu D u) (lf D F0) hz ((gS D : ℕ) : 𝓞 D.host.E)
    hdual hTg a t
  have htr' : (∃ k : ℕ, (((gS D : ℕ) : 𝓞 D.host.E) : D.host.E) = 2 * (k : D.host.E) + 1) ∨
      ∃ ω : 𝓞 D.host.E, (ω : D.host.E) + star (ω : D.host.E) = 1 := by
    rcases htr with ⟨k, hk⟩ | h
    · exact Or.inl ⟨k, by rw [coe_nat, hk]; push_cast; ring⟩
    · exact Or.inr h
  have hframe_e : ∀ i : Fin D.R.rS, frame (lf D F0) (Fin.castSucc i) = F0.e i := by
    intro i; simp [frame, FlagG.fvec]
  obtain ⟨v', hv', l, hl, hZ, hc⟩ := trace_fix Λ hint (frame (lf D F0)) ((gS D : ℕ) : 𝓞 D.host.E) htr'
    {c | c ≤ Fin.castSucc a} t v hv
    (by
      intro c hc
      have hcl : c ≠ Fin.last _ := fun h => by
        rw [h] at hc; exact absurd hc (not_le.mpr (Fin.castSucc_lt_last a))
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hcl
      rw [hframe_e]
      exact hv0 i (Fin.castSucc_le_castSucc_iff.mp hc))
    (fun c hc => hvc c (not_le.mp hc))
  refine ⟨v', hv', l, hl, fun i hi => ?_, fun c hc' => hc c (not_le.mpr hc')⟩
  rw [← hframe_e]
  exact hZ _ (Fin.castSucc_le_castSucc_iff.mpr hi)

theorem normRepStep_of_trace (D : D7) (u u' : D.what₂.Word) (hS : TermStable D u u')
    (hP : PrimeHyp D u (Tu D u')) (htr : Odd (gS D) ∨ TraceOne D) : PI.NormRepLift.NormRepStep D u u' :=
  normRepStep_of D u u' hS hP (rowVec_of D u (Tu D u') htr)

end PI.NRL
