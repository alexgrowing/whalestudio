import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsGenericFlagSelf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominatorStatement

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem V_eq_HT (s : CMType H ⊕ CMType H) {q : Cpt 𝔐.ξ} {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) :
    𝔐.V s q = 𝔐.HT p s q :=
  Lat.patch_of_unique S _ _ hp hq fun p' hp' h' => by
    by_contra hne
    exact Lat.not_inFibre_of_coprime q ((Nat.coprime_primes (𝔐.S_prime _ hp) (𝔐.S_prime _ hp')).2 (Ne.symm hne)) hq h'

theorem dR_le_V (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) : 𝔐.dR s q ≤ 𝔐.V s q := by
  by_cases h : ∃ p ∈ S, InFibre 𝔐.ξ p q
  · obtain ⟨p, hp, hq⟩ := h
    rw [V_eq_HT 𝔐 s hp hq]
    have hd : 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q :=
      𝔐.M.eigLat_le_htDual _ _ _ _ q
    rcases s with τ | τ
    · intro e he
      refine Submodule.subset_span ⟨he.2, fun d _ => ?_⟩
      exact Submodule.smul_mem _ (⟨_, Sandwich.emb_mem 𝔐 _ q d⟩ : regAt 𝔐.ξ q) (hd he)
    · exact hd
  · exact (Lat.patch_of_not S _ _ fun p hp hf => h ⟨p, hp, hf⟩).ge

theorem V_le_lat_of_not (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (h : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) :
    𝔐.V s q ≤ 𝔐.M.lat q := by
  have e : 𝔐.V s q = 𝔐.dR s q := Lat.patch_of_not S _ _ h
  rw [e]
  exact fun _ he => he.1

theorem smul_V_mem_lat (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) {κ : Ω}
    (hκ : HT.Sandwich 𝔐 p κ) (D₂ : ℕ) (hD : (D₂ : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {e : 𝔐.Li} (he : e ∈ 𝔐.V s q) :
    ((D₂ : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  obtain ⟨hκr, -, -, hS⟩ := hκ q hq
  have hdual : ∀ s' : CMType H ⊕ CMType H, ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s') q,
      κ • e ∈ 𝔐.M.lat q := fun s' e he => ((hS s').2 e he).1
  rw [V_eq_HT 𝔐 s hp hq] at he
  rcases s with τ | τ
  · change e ∈ 𝔐.M.htW 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) (differentIdeal ℤ (𝓞 E)) q at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      have h1 := hdual _ _ (hx.2 _ hD)
      rw [map_natCast, smul_smul, mul_comm] at h1
      exact h1
    | zero => simp
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul t a _ ha =>
      have : ((D₂ : Ω) * κ) • t • a = t • (((D₂ : Ω) * κ) • a) := by
        rw [show t • a = (t : Ω) • a from rfl, show t • (((D₂ : Ω) * κ) • a) = (t : Ω) • (((D₂ : Ω) * κ) • a) from rfl,
          smul_comm]
      rw [this]
      exact Submodule.smul_mem _ t ha
  · have h1 := hdual _ _ he
    rw [mul_smul]
    exact Submodule.smul_mem _ (⟨_, natCast_mem _ D₂⟩ : regAt 𝔐.ξ q) h1

end Loc

theorem hodge_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  intro E _ _ _
  obtain ⟨D₁, hD₁, hop⟩ := GlobalTheory.T.eigen_projector_denominator E
  have hdiff : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hD₂ : 0 < Ideal.absNorm (differentIdeal ℤ (𝓞 E)) :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hmem : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := Ideal.absNorm_mem _
  generalize Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = D₂ at hD₂ hmem
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, ?_⟩
  intro H D l Xo c Y S Ω _ K _ J _ y 𝔐 s
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  obtain ⟨T₁, hT₁, hTe, hTD⟩ := hop Ω 𝔐.Li 𝔐.ρ (𝔐.emb s)
  have hreg : ∀ (q : Cpt 𝔐.ξ) (n : ℕ) {e : 𝔐.Li}, e ∈ 𝔐.M.lat q → (n : Ω) • e ∈ 𝔐.M.lat q := fun q n _ he =>
    Submodule.smul_mem _ (⟨_, natCast_mem _ n⟩ : regAt 𝔐.ξ q) he
  refine ⟨(D₂ : Ω) • T₁, fun v hv => ?_, fun q => ⟨fun e he => ?_, fun h e he => ?_, fun p hp hq κ hκ e he => ?_⟩⟩
  · rw [LinearMap.smul_apply, hTD v hv, smul_smul]
    push_cast
    rw [mul_comm]
  · have hst : T₁ e ∈ 𝔐.M.lat q :=
      Sandwich.opRing_stable (𝔐.M.lat q).toAddSubgroup (fun a e he => Sandwich.lat_act 𝔐 q a e he)
        (fun a e he => (𝔐.M.lat q).smul_mem ⟨_, Sandwich.emb_mem 𝔐 s q a⟩ he) hT₁ e he
    exact dR_le_V 𝔐 s q ⟨hreg q D₂ hst, (eigSp 𝔐.ρ (𝔐.emb s)).smul_mem _ (hTe e)⟩
  · exact hreg q _ (V_le_lat_of_not 𝔐 s q h he)
  · have h1 := hreg q D₁ (smul_V_mem_lat 𝔐 s q hp hq hκ D₂ hmem he)
    rw [smul_smul] at h1
    have e1 : ((D₁ * D₂ : ℕ) : Ω) * κ = (D₁ : Ω) * ((D₂ : Ω) * κ) := by
      push_cast
      ring
    rw [e1]
    exact h1

end GlobalTheory.CompanionTheory.Ar.OrVert
