import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridField

open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

def vPre (s : Stages) (v : HeightOneSpectrum (𝓞 s.toD7.host.F)) : HeightOneSpectrum (𝓞 s.B.toPre.host.F) := v

def toPl {P Q : Pre} (h : P = Q) (v : HeightOneSpectrum (𝓞 P.host.F)) : HeightOneSpectrum (𝓞 Q.host.F) := by
  subst h
  exact v

@[simp] theorem toPl_rfl {P : Pre} (v : HeightOneSpectrum (𝓞 P.host.F)) : toPl rfl v = v := rfl

theorem leastSplitAuxiliaryPrime_congr_preData {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : GlobalTheory.ChiGrid.q0 s.toD7 = GlobalTheory.ChiGrid.q0 s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq {s s' : Stages} {B₀ : Pre} (hs : s.B.toPre = B₀) (hs' : s'.B.toPre = B₀) {T T' : Type}
    {L : Formalism.IndefR.Links.LevCh s.toD7 T} {L' : Formalism.IndefR.Links.LevCh s'.toD7 T'} {sc : Consts} (G : GridData L sc)
    (G' : GridData L' sc) (hv : toPl hs' (vPre s' G'.pl.v0) = toPl hs (vPre s G.pl.v0)) {K : Type} [Field K]
    (e : K →+* ℂ) (hF : FieldHas G' e) : ∃ G'' : GridData L sc, G''.pl = G.pl ∧ FieldHas G'' e := by
  subst hs
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at hs'
  subst hs'
  have hv0 : G'.pl.v0 = G.pl.v0 := hv
  refine ⟨⟨G.pl, ⟨G'.ch.chiH, G'.ch.chi, G'.ch.chi_eq, G'.ch.triv, G'.ch.inf,
      fun i h1 h2 PP hPP => G'.ch.unr i h1 h2 PP ?_, G'.ch.lev1, G'.ch.wild,
      fun i h1 h2 PP hPP => G'.ch.lev0 i h1 h2 PP (hPP.trans hv0.symm)⟩, G.sp⟩, rfl, ?_⟩
  · intro h
    apply hPP
    rcases G'.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0))
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inr h)
  · refine ⟨hF.values, fun v hv => ?_⟩
    have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv0.symm) h2
      · exact absurd (h2.trans hv0) h1
      · rfl
    rw [hd]
    refine hF.roots v ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hv with h | h
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0.symm))
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inr h)

theorem exists_field_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
      (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩,
        GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  intro cDep b B₀
  classical

  let Wit : Set (HeightOneSpectrum (𝓞 B₀.host.F)) := {v | ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type)
    (L : Formalism.IndefR.Links.LevCh s.toD7 T) (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v}
  have hfin : Wit.Finite := by
    rcases Wit.eq_empty_or_nonempty with h | ⟨v₁, s₁, hs₁, T₁, L₁, G₁, -⟩
    · rw [h]
      exact Set.finite_empty
    · have hn : ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F) ≠ 0 := by
        subst hs₁
        exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec s₁.toD7).1.ne_zero
      refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F)).finite_toSet.subset ?_
      rintro _ ⟨s, hs, T, L, G, rfl⟩
      refine Formalism.L2.DIV.mem_primesOf.2 ⟨hn, ?_⟩
      subst hs
      rw [leastSplitAuxiliaryPrime_congr_preData hs₁]
      exact G.pl.basePlace_over_qZero
  have hex : ∀ v : Wit, ∃ Mv : IntermediateField ℚ ℂ, FiniteDimensional ℚ Mv ∧
      ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
        (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v ∧ FieldHas G Mv.val.toRingHom := by
    rintro ⟨v, s, hs, T, L, G, hv⟩
    obtain ⟨Mv, h1, h2⟩ := exists_fieldHas G
    exact ⟨Mv, h1, s, hs, T, L, G, hv, h2⟩
  choose Mv hMv hW using hex
  haveI := hfin.to_subtype
  haveI : ∀ v, FiniteDimensional ℚ (Mv v) := hMv
  refine ⟨⨆ v, Mv v, IntermediateField.finiteDimensional_iSup_of_finite, ?_⟩
  intro s hs _ T L G
  obtain ⟨s', hs', T', L', G', hv', hF⟩ := hW ⟨toPl hs (vPre s G.pl.v0), s, hs, T, L, G, rfl⟩
  have hF' : FieldHas G' (⨆ v, Mv v).val.toRingHom :=
    FieldHas.map (IntermediateField.inclusion (le_iSup Mv _)).toRingHom hF
  obtain ⟨G'', -, h⟩ := exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq hs hs' G G' hv' _ hF'
  exact ⟨G'', h⟩

end GlobalTheory.GridField

end
