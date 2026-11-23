import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.CharAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
import Development.WeilBound.CoreStatements.AutomorphicKernels.RamifiedExponentBounds.LocalExpBoundHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentsOfSmoothCharacters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionCharacterTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp

noncomputable section

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem valuation_unif : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact le_antisymm (le_uniformizer_iff.2 h1) (hy ▸ h2 y (hy ▸ uniformizer_lt_one))

private theorem resCard_pos : (0 : ℝ) < (resCard k : ℝ) := by
  have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
  exact_mod_cast this

private theorem norm_absPow_unif (r : ℝ) :
    ‖((absPow k (r : ℂ) (unif k) : ℂˣ) : ℂ)‖ = (resCard k : ℝ) ^ (-r) := by
  have hq := resCard_pos (k := k)
  rw [val_absPow, GlobalTheory.GLDoubling.nabs_unif valuation_unif,
    Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 hq), Complex.ofReal_re, Real.inv_rpow hq.le,
    Real.rpow_neg hq.le]

private theorem linked (θ : kˣ →* ℂˣ) :
    IsUnram (θ * (θ * absPow k 1)⁻¹) ∧
      (((θ * (θ * absPow k 1)⁻¹) (unif k) : ℂˣ) : ℂ) = (resCard k : ℂ) := by
  have e : θ * (θ * absPow k 1)⁻¹ = (absPow k 1)⁻¹ := by
    rw [mul_inv, mul_inv_cancel_left]
  rw [e]
  refine ⟨isUnram_inv (isUnram_absPow k 1), ?_⟩
  have hq : (resCard k : ℂ) ≠ 0 := by
    have := Nat.card_pos (α := IsLocalRing.ResidueField 𝒪[k])
    exact_mod_cast this.ne'
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, val_absPow, Complex.cpow_one,
    GlobalTheory.GLDoubling.nabs_unif valuation_unif]
  push_cast
  exact inv_inv _

private theorem exponent_of_unl [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (hu : IsUnitarisable ρ) (hg : IsGeneric ρ) (S : Multiset (IrrGL k)) (hS : HasSupport ρ S)
    (h1 : ∀ y ∈ S, y.1 = 1) (hun : Unl (resCard k) S) {ξ : kˣ →* ℂˣ} (hξ : ξ ∈ chars S) :
    ∃ e : ℝ, |e| < 1 / 2 ∧ ‖((ξ (unif k) : ℂˣ) : ℂ)‖ = (resCard k : ℝ) ^ (-e) := by
  obtain ⟨h, δ, Δ, s, hL, hc, hb, hd, ⟨φ⟩⟩ := PositivityTheory.JsR.localExpBound_holds k N V ρ hs hi hu hg
  let D : Fin h → Segment k := fun i => (Δ i).nu ((s i : ℝ) : ℂ)
  have hL' : ∀ i, IsLSeg (D i) ((δ i).nu ((s i : ℝ) : ℂ)).rep := fun i => GlobalTheory.isLSeg_nu (hL i) _
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport ρ (∑ i, (D i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL' i).hasSupport) hi
      (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have he := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 hS
  obtain ⟨hξ0, hm⟩ := hξ
  obtain ⟨i, -, hi'⟩ := Multiset.mem_sum.1 (he ▸ hm)
  have hmem : ∀ a : ℕ, a < (D i).len → (D i).first.nu (a : ℂ) ∈ S := fun a ha => by
    rw [← he]
    exact Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨a, ha, rfl⟩)⟩
  have hlen : (D i).len = 1 := by
    by_contra hne
    have h2 : 1 < (D i).len := by have := (D i).len_pos; omega
    have h0 := hmem 0 (D i).len_pos
    have h3 := hmem 1 h2
    rw [Nat.cast_zero, IrrGL.nu_zero] at h0
    rw [Nat.cast_one] at h3
    obtain ⟨θ, hθ, e⟩ := GlobalTheory.RoadU.PlainChars.exists_eq_ofChar (D i).first (h1 _ h0)
    rw [e] at h0 h3
    have e2 : (IrrGL.ofChar θ hθ).nu 1 = IrrGL.ofChar (θ * absPow k 1) (hθ.mul (isSmoothChar_absPow _)) :=
      IrrGL.tw_ofChar _ _ _ _
    rw [e2] at h3
    exact hun θ ⟨hθ, h0⟩ _ ⟨_, h3⟩ (linked θ).1 (linked θ).2
  rw [GlobalTheory.SphUnr.ms_eq_singleton hlen, Multiset.mem_singleton] at hi'
  have hμ : IsSmoothChar (ξ * absPow k ((-(s i) : ℝ) : ℂ)) := hξ0.mul (isSmoothChar_absPow _)
  have hfirst : (Δ i).first = IrrGL.ofChar (ξ * absPow k ((-(s i) : ℝ) : ℂ)) hμ := by
    rw [← IrrGL.tw_ofChar _ _ hξ0 (isSmoothChar_absPow _)]
    change _ = (IrrGL.ofChar ξ hξ0).nu _
    rw [hi']
    change _ = ((Δ i).first.nu ((s i : ℝ) : ℂ)).nu _
    rw [IrrGL.nu_nu]
    push_cast
    simp
  have hcc : HasCentralChar (Δ i).first.rep (ξ * absPow k ((-(s i) : ℝ) : ℂ)) := by
    rw [hfirst]
    exact GlobalTheory.LocLanglands.ExtTwist.hasCentralChar_ofChar _ hμ
  have hcen := hc i _ hcc (unif k)
  have hlen' : (Δ i).len = 1 := hlen
  rw [hlen'] at hcen
  simp only [Nat.cast_one, sub_self, mul_zero, zero_div, neg_zero, zero_mul] at hcen
  have hn0 : 0 < ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  have h4 : ‖(((ξ * absPow k ((-(s i) : ℝ) : ℂ)) (unif k) : ℂˣ) : ℂ)‖ = 1 := by
    rcases Real.log_eq_zero.1 hcen with h | h | h
    · exact absurd h hn0.ne'
    · exact h
    · linarith
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, norm_absPow_unif, neg_neg] at h4
  have hq := resCard_pos (k := k)
  refine ⟨s i, hb i, ?_⟩
  rw [Real.rpow_neg hq.le]
  exact eq_inv_of_mul_eq_one_left h4

end Loc

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winOf :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinOf := by
  intro K _ _ _ n hn π
  obtain ⟨π₀, t, hu, he⟩ := CG.exists_isUnitary_twist_absPow (CG.mk π) hn
  obtain ⟨π₀, rfl⟩ : ∃ p : CuspSub K n, CG.mk p = π₀ := ⟨π₀.out, Quotient.out_eq π₀⟩
  let χ : Formalism.L2.Host.HChar K := GlobalTheory.HeckeGal.Model.absPow K (-t)
  have hiso : CG.mk (π.twist χ) = CG.mk π₀ := by
    have e1 : CG.mk (π.twist χ) = (CG.mk π).twist χ := rfl
    rw [e1, he, ← CG.twist_mul, mul_comm, CG.absPow_neg_mul, CG.twist_one]
  have hU : (π.twist χ).IsUnitary := (CG.isUnitary_mk _).1 (hiso ▸ hu)
  obtain ⟨a, ha⟩ := charAbs K χ
  refine ⟨-a, fun v hT hL => ⟨hT, fun s hs ξ hξ => ?_⟩⟩
  haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  have hq1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hres := GlobalTheory.LFun.SatBoundGL.resCard_completion v
  obtain ⟨s', hs', -, hch, hfst⟩ := suppTw K n hn π v χ s hs
  obtain ⟨σ, hσ, hsup⟩ := hs'
  have htor := ((suppFacts K n hn π v).2.2.1 s hs).1.1 hT
  have h1 : ∀ y ∈ s', y.1 = 1 := fun y hy => by
    obtain ⟨y₀, hy₀, e⟩ := Multiset.mem_map.1 (hfst ▸ Multiset.mem_map_of_mem Sigma.fst hy)
    rw [← e]
    exact htor y₀ hy₀
  have hun : Unl (resCard (v.adicCompletion K)) s' := by
    rw [hres]
    intro ζ hζ ζ' hζ'
    obtain ⟨ξ₁, h₁, rfl⟩ := (hch ζ).1 hζ
    obtain ⟨ξ₂, h₂, rfl⟩ := (hch ζ').1 hζ'
    have e : ξ₁ * χ.loc v * (ξ₂ * χ.loc v)⁻¹ = ξ₁ * ξ₂⁻¹ := by
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    rw [e]
    exact hL s hs ξ₁ h₁ ξ₂ h₂
  obtain ⟨e, he1, he2⟩ := exponent_of_unl σ.ρ σ.smooth σ.irred
    (GlobalTheory.ResW.isUnitarisable_of_isLocComp_cusp K n _ hn hU v σ hσ)
    (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp K n _ v σ hσ) s' hsup h1 hun
    ((hch _).2 ⟨ξ, hξ, rfl⟩)
  obtain ⟨-, hav⟩ := ha v
  rw [hres, MonoidHom.mul_apply, Units.val_mul, norm_mul, hav] at he2
  have hq0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hval : ‖((ξ (unif (v.adicCompletion K)) : ℂˣ) : ℂ)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-a - e) := by
    rw [sub_eq_add_neg, Real.rpow_add hq0, ← he2, Real.rpow_neg hq0.le a]
    field_simp
  obtain ⟨hl, hr⟩ := abs_lt.1 he1
  rw [hval]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith), Real.rpow_lt_rpow_of_exponent_lt hq1 (by linarith)⟩
