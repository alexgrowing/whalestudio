import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardPiOfUnique
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LatLocGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PSurjF

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem localLattice_eq_iff (Zd : LocDat D) (p : PlF D) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h₁ : Submodule.IsLattice D.host.E Λ₁) (h₂ : Submodule.IsLattice D.host.E Λ₂) :
    lattice₂ D Zd.M p Λ₁ = lattice₂ D Zd.M p Λ₂ ↔
      Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₁ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ₂ := by
  haveI := p.isPrime
  constructor
  · intro h
    ext x
    rw [← baseChangeAt_mem_localLattice_iff Zd p h₁, ← baseChangeAt_mem_localLattice_iff Zd p h₂, h]
  · intro h
    have key : ∀ {A B : Submodule (𝓞 D.host.E) (VS D).V}, Submodule.IsLattice D.host.E B →
        Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B → lattice₂ D Zd.M p A ≤ lattice₂ D Zd.M p B := by
      intro A B hB hAB
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, baseChangeAt_mem_localLattice_iff Zd p hB, ← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A y).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hy⟩
    exact le_antisymm (key h₂ h) (key h₁ h.symm)

section Loc

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_of_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal)
    (B : Submodule (𝓞 D.host.E) V) {x : V} (hx : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    x ∈ PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).1 hx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, fun h => ht ?_, htx⟩
  rw [← hP]; exact h

theorem locF_of_loc (p : PlF D) (B : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      x ∈ PI.LatLocGlob.loc P B) :
    x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
  haveI := p.isPrime
  let I : Ideal (𝓞 D.host.E) :=
    { carrier := {a | a • x ∈ B}
      add_mem' := fun {a c} ha hc => by simp only [Set.mem_setOf_eq, add_smul] at *; exact B.add_mem ha hc
      zero_mem' := by simp
      smul_mem' := fun c a ha => by simp only [Set.mem_setOf_eq, smul_eq_mul, mul_smul] at *; exact B.smul_mem c ha }
  by_contra hnot
  have hle : I.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ p.asIdeal := by
    intro t ht
    by_contra htp
    exact hnot ((Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal B x).2 ⟨t, htp, ht⟩)
  obtain ⟨Q, hIQ, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal I hle
  have hQm : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 D.host.F) Q (by rw [hQp]; exact p.isMaximal)
  obtain ⟨s, hs, hsx⟩ := hx Q hQm hQp
  exact hs (hIQ hsx)

end Loc

section Patch

variable {V : Type} [AddCommGroup V] [Module (𝓞 D.host.E) V]

theorem loc_locF (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) (A : Submodule (𝓞 D.host.E) V) {x : V}
    (hx : x ∈ PI.LatLocGlob.loc P (Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A)) : x ∈ PI.LatLocGlob.loc P A := by
  haveI := p.isPrime
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).1 hsx
  refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t * s, fun h => (hPp.mem_or_mem h).elim (fun h1 => ht ?_) hs, ?_⟩
  · rw [← hP]; exact h1
  · rw [mul_smul]; exact htx

theorem loc_eq_of_locF_eq (p : PlF D) {P : Ideal (𝓞 D.host.E)} (hPp : P.IsPrime)
    (hP : P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) {A B : Submodule (𝓞 D.host.E) V}
    (h : Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) :
    PI.LatLocGlob.loc P A = PI.LatLocGlob.loc P B := by
  haveI := p.isPrime
  have sub : ∀ {A B : Submodule (𝓞 D.host.E) V}, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B →
      PI.LatLocGlob.loc P A ⊆ PI.LatLocGlob.loc P B := by
    intro A B hAB x hx
    obtain ⟨s, hs, hsx⟩ := hx
    have h1 : s • x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B := by
      rw [← hAB]
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal A _).2
        ⟨1, fun h1 => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hsx⟩
    exact loc_locF p hPp hP B ⟨s, hs, h1⟩
  exact Set.Subset.antisymm (sub h) (sub h.symm)

theorem comap_ne_bot {P : Ideal (𝓞 D.host.E)} (hP : P.IsMaximal) :
    P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.E)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral (R := 𝓞 D.host.F) a)

def plOf (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) : PlF D :=
  ⟨P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, comap_ne_bot hP⟩

theorem finite_over (p : PlF D) :
    {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal}.Finite := by
  have hmap : p.asIdeal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact p.ne_bot
  refine ((Ideal.finite_factors hmap).image HeightOneSpectrum.asIdeal).subset ?_
  rintro P ⟨hPm, hPp⟩
  have hne : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm (RingOfIntegers.not_isField D.host.E)
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_, rfl⟩
  show P ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, hPp]

end Patch

theorem latPatch_holds : Formalism.L2.SG.Pf.FrameGlobalPatching.LatPatch := by
  intro D Zd Λ₀ hΛ₀ Mf hMf hfin
  choose Λ' hΛ' hMΛ' using hMf
  have hfullΛ : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E L →
      PI.LatLocGlob.IsFullLat D.host.E L := fun L hL => ⟨hL.fg, hL.span_eq_top⟩
  let M : Ideal (𝓞 D.host.E) → Set (VS D).V := fun P =>
    if hP : P.IsMaximal then PI.LatLocGlob.loc P (Λ' (plOf P hP)) else ∅
  have hMP : ∀ P (hP : P.IsMaximal), M P = PI.LatLocGlob.loc P (Λ' (plOf P hP)) := fun P hP => by
    simp only [M, dif_pos hP]
  have hexc : {P : Ideal (𝓞 D.host.E) | P.IsMaximal ∧ M P ≠ PI.LatLocGlob.loc P Λ₀}.Finite := by
    refine (hfin.biUnion fun p _ => finite_over p).subset ?_
    rintro P ⟨hPm, hne⟩
    refine Set.mem_biUnion (x := plOf P hPm) ?_ ⟨hPm, rfl⟩
    intro heq
    apply hne
    rw [hMP P hPm]
    have h1 : lattice₂ D Zd.M (plOf P hPm) (Λ' (plOf P hPm)) = lattice₂ D Zd.M (plOf P hPm) Λ₀ := by
      rw [← hMΛ']; by_contra h; exact h (by simpa using heq) |>.elim
    exact loc_eq_of_locF_eq (plOf P hPm) hPm.isPrime rfl ((localLattice_eq_iff Zd _ (hΛ' _) hΛ₀).1 h1)
  obtain ⟨L, ⟨hLfull, hLloc⟩, huniq⟩ := latLocGlob (𝓞 D.host.E) D.host.E (VS D).V Λ₀ (hfullΛ Λ₀ hΛ₀) M
    (fun P hP => ⟨Λ' (plOf P hP), hfullΛ _ (hΛ' _), hMP P hP⟩) hexc
  have hL : Submodule.IsLattice D.host.E L := ⟨hLfull.1, hLfull.2⟩
  have hlocP : ∀ (p : PlF D) (P : Ideal (𝓞 D.host.E)), P.IsMaximal →
      P.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
      PI.LatLocGlob.loc P L = PI.LatLocGlob.loc P (Λ' p) := by
    intro p P hPm hPp
    rw [hLloc P hPm, hMP P hPm]
    have : plOf P hPm = p := HeightOneSpectrum.ext hPp
    rw [this]
  have hlocF : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Λ' p) := by
    intro p
    ext x
    constructor
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [← hlocP p P hPm hPp]
      exact loc_of_locF p hPp L hx
    · intro hx
      refine locF_of_loc p _ fun P hPm hPp => ?_
      rw [hlocP p P hPm hPp]
      exact loc_of_locF p hPp _ hx
  refine ⟨L, ⟨hL, fun p => ?_⟩, ?_⟩
  · rw [hMΛ' p]
    exact (localLattice_eq_iff Zd p hL (hΛ' p)).2 (hlocF p)
  · rintro Λ ⟨hΛ, hΛp⟩
    have h1 : ∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal L := fun p =>
      ((localLattice_eq_iff Zd p hΛ (hΛ' p)).1 ((hΛp p).trans (hMΛ' p))).trans (hlocF p).symm
    have sub : ∀ {A B : Submodule (𝓞 D.host.E) (VS D).V}, Submodule.IsLattice D.host.E B →
        (∀ p : PlF D, Formalism.HermitianLattices.Ext.L3.locF p.asIdeal A = Formalism.HermitianLattices.Ext.L3.locF p.asIdeal B) → A ≤ B := by
      intro A B hB hAB x hx
      refine PI.UnitaryGroupMassFormula.UJClassMass.interLocF (F := D.host.F) B hB x fun v => ?_
      haveI := v.isPrime
      have h2 : x ∈ Formalism.HermitianLattices.Ext.L3.locF v.asIdeal B := by
        rw [← hAB v]
        exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal A x).2
          ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hx⟩
      exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF v.asIdeal B x).1 h2
    exact le_antisymm (sub hL h1) (sub hΛ fun p => (h1 p).symm)

end Formalism.L2.SG.Pf.LocalDenominators
