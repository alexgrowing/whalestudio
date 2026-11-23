import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusDifferenceIdentity

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2K

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.Pv.LocalLengthBound
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX InI IsTrunc TCase)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem level_membership_package [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n)
    (M η σ : ℕ) (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1))
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) (hπ : W.π₀ ∈ W.AΔ) (hM1 : 1 ≤ M)
    (hηM : η ≤ (PD.p - 1) * M) (hZ : TTool2Z W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : 11 ≤ PD.p)
    (hTC : TCase PD.p 1 M η σ) (hc : IsCrys PD T.ρ)
    (h4 : ∀ x : W.DD T, x ∈ W.φpull T → (letE (c + 1) : LetA O n) • x = x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T)
    (h5 : ∀ w z : W.DD T, InI W T c w → IsTrunc W T c 1 M η σ w z →
      ∃ x : ↥(W.wachCocyclesDelta T), (x : W.DD T × W.DD T).1 = z ∧ InPN W T M (x : W.DD T × W.DD T).2)
    (w ζφ ζc t Y : W.DD T) (hw : InI W T c w)
    (hgw : W.γ T w - w = (1 : O) • ζφ + (-(((PD.p : ℕ) : O) ^ σ)) • ζc)
    (hY : Y = W.φD T w + t) (hYΔ : ∀ δ ∈ W.DelF, W.γD T δ Y = Y)
    (hφ : DL W T c ζφ ∧ InPN W T M ζφ) (hζc : DL W T c ζc ∧ InPN W T 1 ζc)
    (ht : ∃ t', IsTrZ W T c 1 M η σ ζc t' ∧ ∃ p ∈ pullJ W T c 1, t - t' = fMX W M η • p) :
    ∃ (xc : ↥(W.wachCocyclesDelta T)) (κc : G → T.V) (hκc : κc ∈ latticeCocycles T.L),
      RhoCoc W T c M η σ w κc ∧ W.clK T xc = Submodule.Quotient.mk ⟨κc, hκc⟩ ∧
      DL W T (c + 1) ((xc : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y) ∧
      InPN W T M ((xc : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y) ∧
      InPN W T M (xc : W.DD T × W.DD T).2 := by
  obtain ⟨Zex, -, Zlin, Zvan⟩ := hZ hA hp 1 M η σ hTC T hc c
  have hζw : DL W T c (W.γ T w - w) := invariantLetter_sub' W T (invariantLetter_gamma W T hw.1) hw.1
  obtain ⟨tw, htw⟩ := Zex _ hζw hw.2.2
  have htr : IsTrunc W T c 1 M η σ w (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ 1) w - tw) :=
    (isTrunc_iff W T c 1 M η σ _ _).2 ⟨tw, htw, rfl⟩
  obtain ⟨xc, hxc1, hxc2⟩ := h5 w _ hw htr
  obtain ⟨pκ, hpκ⟩ := Submodule.Quotient.mk_surjective _ (W.clK T xc)
  have hφPN1 := uniformizerLattice_antitone W T hM1 hπ hφ.2
  obtain ⟨t₁, ht₁⟩ := Zex _ hφ.1 hφPN1
  obtain ⟨p₂, hp₂, e₂⟩ := Zvan _ t₁ hφ.1 hφ.2 rfl hηM ht₁
  obtain ⟨t', ht', p₃, hp₃, e₃⟩ := ht
  obtain ⟨p₁, hp₁, e₁⟩ := Zlin 1 (-(((PD.p : ℕ) : O) ^ σ)) _ _ t₁ t' tw hφ.1 hφPN1 hζc.1 hζc.2 ht₁
    ht' (by rw [← hgw]; exact htw)
  have hp' : -(p₁ + p₂ + ((PD.p : ℕ) : O) ^ σ • p₃) ∈ pullJ W T c 1 :=
    Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.add_mem _ hp₁ hp₂)
      (Submodule.smul_of_tower_mem _ _ hp₃))
  have hdiff : (xc : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y =
      fMX W M η • (-(p₁ + p₂ + ((PD.p : ℕ) : O) ^ σ • p₃)) := by
    rw [hxc1, hY, pow_one]
    exact Step2A.difference_of_factorisations _ _ _ _ _ _ _ _ _ _ e₁ e₂ e₃
  have hΔd : ∀ δ ∈ W.DelF, W.γD T δ ((xc : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y) =
      (xc : W.DD T × W.DD T).1 - ((PD.p : ℕ) : O) ^ σ • Y := by
    intro δ hδ
    rw [map_sub, map_smul, ((RL.mem_Z1DΔ_iff W T _).1 xc.2).2 δ hδ |>.1, hYΔ δ hδ]
  refine ⟨xc, pκ.1, pκ.2, ⟨hw, pκ.2, _, xc, htr, hxc1, hxc2, hpκ.symm⟩, hpκ.symm,
    ⟨?_, hΔd⟩, frobeniusPoly_smul_mem_lattice W T hu hΔπ c M η h4 hp' hdiff hΔd, hxc2⟩
  rw [hdiff, smul_comm, RL.pullJ_letter W T c hp']

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2K

end
