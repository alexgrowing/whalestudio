import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.UnrCharAtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def UnrSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∀ f : ℕ, 0 < f → ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite →
    ∃ X : Fld E Ω, Tower S X ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → normV w' = normV w ^ f) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt u → ∀ A : ValuationSubring Ω, IsPlaceOver A u →
        ∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ

private theorem over_under {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (maximalRealSubfield E))) := by
  intro x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hA]
  rfl

private theorem dec_res {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {g : G E Ω} (hg : g ∈ Dec (F := E) A) :
    AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ Dec (F := maximalRealSubfield E) A := by
  exact hg

private theorem ine_res {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {g : G E Ω} (hg : g ∈ Ine (F := E) A) :
    AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ Ine (F := maximalRealSubfield E) A := by
  exact ⟨dec_res hg.1, hg.2⟩

theorem unrSplit_of (h1 : GroupStep) (h2 : UnrCharPP) (h3 : FreshSplit) (h4 : ExFld) (h6 : LayerOf) (h7 : DegOf)
    (h8 : SplitIff) : UnrSplit := by
  unfold UnrSplit
  intro E Ω _ _ _ _ _ _ w hw f hf S hS
  haveI := isAlgClosure_plus (E := E) (Ω := Ω)
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  obtain ⟨r, hrG, hrR, hrv⟩ := unrCharAt_of h2 f hf E Ω v
  obtain ⟨m, hm, hrm⟩ : ∃ m, 0 < m ∧ r ^ m = 1 := by
    haveI : Finite (G (maximalRealSubfield E) Ω ⧸ r.ker) :=
      Subgroup.quotient_finite_of_isOpen _ hrG.isOpen
    refine ⟨r.ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, ?_⟩
    refine MonoidHom.ext fun g => ?_
    rw [MonoidHom.pow_apply, ← map_pow, MonoidHom.one_apply]
    exact MonoidHom.mem_ker.mp (r.ker.pow_index_mem g)
  let T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :=
    insert v ((fun s : HeightOneSpectrum (𝓞 E) => s.under (𝓞 (maximalRealSubfield E))) '' S)
  have hTf : T.Finite := (hS.image _).insert v
  have mkPl : ∀ (ψ : G (maximalRealSubfield E) Ω →* ℂˣ) (n : ℕ), 2 ≤ n → RamSplit E ψ.ker →
      ∀ u, u ∉ T → (∀ A : ValuationSubring Ω, IsPlaceOver A u →
        ∃ τ ∈ Ine (F := maximalRealSubfield E) A, orderOf (ψ τ) = n) →
      (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) ∧
        ∀ A : ValuationSubring Ω, IsPlaceOver A u →
          ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g := by
    intro ψ n hn hR u huT hu
    refine ⟨fun s hs h => huT (Set.mem_insert_of_mem _ ⟨s, hs, h⟩), fun A hA => ?_⟩
    have hR' := hR
    unfold RamSplit at hR'
    rcases hR' u A hA with h | h
    · obtain ⟨τ, hτ, ho⟩ := hu A hA
      have h1' : ψ τ = 1 := MonoidHom.mem_ker.mp (h hτ)
      rw [h1', orderOf_one] at ho
      omega
    · exact h
  obtain ⟨r', hr'Gd, hr'D, X, hXc, hXT⟩ := h1 (G (maximalRealSubfield E) Ω)
    (fun H => Good H ∧ RamSplit E H)
    (fun H => ∃ X : Fld E Ω, Cuts X H ∧ Tower S X)
    {g | ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ g ∈ Dec (F := maximalRealSubfield E) A}
    {u : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) //
      (∀ s ∈ S, s.under (𝓞 (maximalRealSubfield E)) ≠ u) ∧
        ∀ A : ValuationSubring Ω, IsPlaceOver A u →
          ∀ g ∈ Dec (F := maximalRealSubfield E) A, Fixes E g}
    (fun u => {g | ∃ A : ValuationSubring Ω, IsPlaceOver A u.1 ∧ g ∈ Dec (F := maximalRealSubfield E) A})
    (fun u => {g | ∃ A : ValuationSubring Ω, IsPlaceOver A u.1 ∧ g ∈ Ine (F := maximalRealSubfield E) A})
    (by
      rintro u g ⟨A, hA, hg⟩
      exact ⟨A, hA, Ine_le_Dec A hg⟩)
    (by
      rintro H H' ⟨hG, hR⟩ ⟨hG', hR'⟩
      exact ⟨hG.inf hG', hR.inf hR'⟩)
    (by
      rintro H H' hle ⟨hG, hR⟩
      exact ⟨hG.mono hle, hR.mono hle⟩)
    (by
      rintro U ⟨hUG, -⟩ n hn
      obtain ⟨ψ, hψG, hψR, -, hψT, u, huT, hu⟩ :=
        h3 E Ω U hUG.isOpen T hTf (max n 2) (by omega)
      have hPl := mkPl ψ (max n 2) (le_max_right _ _) hψR u huT (fun A hA => (hu A hA).2)
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
      rcases Nat.lt_or_ge n 2 with h | h
      · have hn1 : n = 1 := by omega
        subst hn1
        refine ⟨1, ?_, one_pow _, fun g _ => rfl, ⟨u, hPl⟩, ?_, 1, ⟨A, hA, Subgroup.one_mem _⟩, by simp⟩
        · rw [MonoidHom.ker_one]
          exact ⟨Good.top, RamSplit.mono le_top hψR⟩
        · rintro g ⟨B, hB, hg⟩
          exact (hu B hB).1 hg
      · obtain ⟨ψ', hψ'G, hψ'R, hψ'n, hψ'T, u', hu'T, hu'⟩ :=
          h3 E Ω U hUG.isOpen T hTf n hn
        have hPl' := mkPl ψ' n h hψ'R u' hu'T (fun B hB => (hu' B hB).2)
        obtain ⟨A', hA'⟩ := exists_isPlaceOver Ω u'
        obtain ⟨τ, hτ, ho⟩ := (hu' A' hA').2
        refine ⟨ψ', ⟨hψ'G, hψ'R⟩, hψ'n, ?_, ⟨u', hPl'⟩, ?_, τ, ⟨A', hA', hτ⟩, ho⟩
        · rintro g ⟨B, hB, hg⟩
          exact hψ'T v (Set.mem_insert _ _) B hB g hg
        · rintro g ⟨B, hB, hg⟩
          exact (hu' B hB).1 hg)
    (by
      rintro H H' u ⟨-, -⟩ ⟨hG', -⟩ ⟨X, hX, hXT⟩ hle hp hDc ⟨τ, ⟨A0, hA0, hτ⟩, hτ'⟩
      obtain ⟨Y, hY⟩ := h4 E Ω H' hG'
      have hL := h6 E Ω S H H' hG' hle hp X Y hX hY u.1 u.2.1
        (fun A hA g hg => ⟨u.2.2 A hA g hg, by exact hDc ⟨A, hA, hg⟩⟩) ⟨A0, hA0, τ, hτ, hτ'⟩
      exact ⟨Y, hY, hXT.step hL.1⟩)
    ⊤ r ⟨Good.top, RamSplit.mono le_top hrR⟩ ⟨Fld.base E Ω, cuts_base, Tower.base S⟩
    ⟨hrG, hrR⟩ m hm hrm
  obtain ⟨-, hr'R⟩ := hr'Gd
  have hc : ∀ g : G E Ω, Fixes X.K g ↔
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g ∈ ⊤ ⊓ r'.ker := by
    unfold Cuts at hXc
    exact hXc
  have key : ∀ g : G E Ω, Fixes X.K g ↔
      r' (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g) = 1 := fun g =>
    ⟨fun h => MonoidHom.mem_ker.mp ((hc g).1 h).2,
      fun h => (hc g).2 ⟨Subgroup.mem_top _, MonoidHom.mem_ker.mpr h⟩⟩
  have hIne : ∀ A : ValuationSubring Ω, IsPlaceOver A w →
      ∀ τ ∈ Ine (F := E) A, Fixes (F := E) X.K τ := by
    intro A hA τ hτ
    have hA' : IsPlaceOver A v := over_under hA
    rw [key, hr'D _ ⟨A, hA', Ine_le_Dec A (ine_res hτ)⟩]
    exact MonoidHom.mem_ker.mp ((hrv A hA').1 (ine_res hτ))
  refine ⟨X, hXT, fun A hA => ⟨hIne A hA, fun w' hw' => ?_⟩, ?_⟩
  · haveI := X.tower
    have hA' : IsPlaceOver A v := over_under hA
    have hsplit := (h8 E Ω A w hA).1 hw
    obtain ⟨φ₀, hφ₀⟩ := exists_isFrob hA'
    have hvw : normV w = normV v ^ 1 :=
      h7 (maximalRealSubfield E) E Ω A v w hA' hA
        (fun τ hτ => hsplit τ (Ine_le_Dec A hτ)) φ₀ 1 one_pos hφ₀
        (fun k => ⟨fun _ => one_dvd k, fun _ => hsplit _ (Subgroup.pow_mem _ hφ₀.1 k)⟩)
    rw [pow_one] at hvw
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hφD : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) φ ∈
        Dec (F := maximalRealSubfield E) A := dec_res hφ.1
    have hφF : IsFrob A (normV v) (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) φ) := by
      refine ⟨hφD, fun x hx => ?_⟩
      have := hφ.2 x hx
      rw [hvw] at this
      exact this
    have hord := (hrv A hA').2 _ hφF
    refine h7 E X.K Ω A w w' hA hw' (hIne A hA) φ f hf hφ (fun k => ?_)
    rw [key, map_pow, map_pow, hr'D _ ⟨A, hA', hφD⟩, ← orderOf_dvd_iff_pow_eq_one, hord]
  · intro u hu A hA τ hτ
    have hA' := over_under hA
    rw [key]
    have hR := hr'R
    unfold RamSplit at hR
    rcases hR _ A hA' with h | h
    · exact MonoidHom.mem_ker.mp (h (ine_res hτ))
    · exact absurd ((h8 E Ω A u hA).2 h) hu

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
