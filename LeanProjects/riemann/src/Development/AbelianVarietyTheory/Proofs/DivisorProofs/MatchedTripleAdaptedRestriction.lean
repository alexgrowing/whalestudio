import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WStableSSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleCharacterTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalNormIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLiftEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleThetaEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleUnramifiedIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ThetaFacRadV

theorem radV (lin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Ψ₂ ∈ GlobalTheory.ThK.PolData B G.M, ∀ c : ℂ, G.M.I om (Ψ₁ + Ψ₂) = G.M.I om Ψ₁ + G.M.I om Ψ₂ ∧ G.M.I om (c • Ψ₁) = c • G.M.I om Ψ₁) (stab : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin F v), om (g, 1) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V B.emb, om (k, 1) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v), om (1, h) Φ ∈ GlobalTheory.ThK.PolData B G.M) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, om (1, k) Φ ∈ GlobalTheory.ThK.PolData B G.M) (lieD : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∃ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0)
    (invV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField
        E] [Algebra F E] (σ : E →ₐ[F] E) (B
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om'
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.V (GlobalTheory.AdelicU.evFin
        F v), G.M.I om (om (g, 1)
        Φ) = G.M.I om Φ) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.V B.emb, G.M.I om (om
        (k, 1) Φ) = G.M.I om Φ) (lieV : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField
        F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om'
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, (∀ x, HasDerivAt (fun t : ℝ => om (γ
        (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → G.M.I om Φ₁ = 0) (lieW
        : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField
        E] [Algebra F E] (σ : E →ₐ[F] E) (B
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om'
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, (∀ x, HasDerivAt (fun t : ℝ => om (1,
        γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∀ h, HasDerivAt (fun t : ℝ => G.M.I om Φ (h * γ
        (Multiplicative.ofAdd t))) (G.M.I om Φ₁ h) 0) (cpl : GlobalTheory.ThK.KP → ∀ (F E
        : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om'
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf
        : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn
        F a (a +
        a')), (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) → N ≤ GlobalTheory.ThK.PolData B G.M → GlobalTheory.ThetaFac.WStable B om (GlobalTheory.ThK.PolData
        B G.M) N → ∃ N' : Submodule ℂ (GlobalTheory.ThK.Fn F a (a +
        a')), (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N') ∧ N' ≤ GlobalTheory.ThK.PolData B G.M ∧ GlobalTheory.ThetaFac.WStable B om (GlobalTheory.ThK.PolData
        B G.M) N' ∧ (∀ Ψ ∈ N, Ψ ∈ N' → G.M.I om Ψ = 0) ∧ GlobalTheory.ThK.PolData B G.M ≤ N ⊔ N') :
    GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Φ ≠ 0 → ∃ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N ∧ (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) ∧ Φ ∉ N := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ hI
  have lin := lin hKP F E σ B a a' G X om om' R Rf hM
  have stab := stab hKP F E σ B a a' G X om om' R Rf hM
  have lieD := lieD hKP F E σ B a a' G X om om' R Rf hM
  have invV := invV hKP F E σ B a a' G X om om' R Rf hM
  have lieV := lieV hKP F E σ B a a' G X om om' R Rf hM
  have lieW := lieW hKP F E σ B a a' G X om om' R Rf hM
  have cpl := cpl hKP F E σ B a a' G X om om' R Rf hM
  set D := GlobalTheory.ThK.PolData B G.M with hDdef
  have I0 : G.M.I om 0 = 0 := by
    have := (lin 0 D.zero_mem 0 D.zero_mem 0).2
    simpa using this
  have Isub : ∀ x ∈ D, ∀ y ∈ D, G.M.I om (x - y) = G.M.I om x - G.M.I om y := by
    intro x hx y hy
    have h1 := (lin x hx ((-1 : ℂ) • y) (D.smul_mem _ hy) 0).1
    have h2 := (lin y hy y hy (-1)).2
    rw [sub_eq_add_neg, ← neg_one_smul ℂ y, h1, h2, neg_one_smul, ← sub_eq_add_neg]
  let K : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')) :=
    { carrier := {Ψ | Ψ ∈ D ∧ G.M.I om Ψ = 0}
      add_mem' := fun {x y} hx hy => ⟨D.add_mem hx.1 hy.1, by rw [(lin x hx.1 y hy.1 0).1, hx.2, hy.2, add_zero]⟩
      zero_mem' := ⟨D.zero_mem, I0⟩
      smul_mem' := fun c x hx => ⟨D.smul_mem c hx.1, by rw [(lin x hx.1 x hx.1 c).2, hx.2, smul_zero]⟩ }
  have memK : ∀ Ψ, Ψ ∈ K ↔ Ψ ∈ D ∧ G.M.I om Ψ = 0 := fun Ψ => Iff.rfl
  have KD : K ≤ D := fun Ψ h => h.1

  have KW : GlobalTheory.ThetaFac.WStable B om D K := by
    refine ⟨fun v h hh Ψ hΨ => ?_, fun γ hγ Ψ hΨ Ψ₁ hΨ₁ hd => ?_, fun k hk Ψ hΨ => ?_⟩
    · refine ⟨(stab Ψ hΨ.1).2.2.1 v h hh, ?_⟩
      funext h₀
      rw [I_om_one, hΨ.2]
      rfl
    · refine ⟨hΨ₁, ?_⟩
      funext h₀
      have h1 := lieW γ hγ Ψ hΨ.1 Ψ₁ hΨ₁ hd h₀
      rw [hΨ.2] at h1
      exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    · refine ⟨(stab Ψ hΨ.1).2.2.2 k hk, ?_⟩
      funext h₀
      rw [I_om_one, hΨ.2]
      rfl
  have DW : GlobalTheory.ThetaFac.WStable B om D D :=
    ⟨fun v h hh Ψ hΨ => (stab Ψ hΨ).2.2.1 v h hh, fun _ _ _ _ Ψ₁ hΨ₁ _ => hΨ₁,
     fun k hk Ψ hΨ => (stab Ψ hΨ).2.2.2 k hk⟩
  have KC : GlobalTheory.ThetaFac.CoinvLe B om D K := by
    refine ⟨fun v g hg Ψ hΨ => ?_, fun γ hγ Ψ hΨ Ψ₁ hΨ₁ hd => ⟨hΨ₁, lieV γ hγ Ψ hΨ Ψ₁ hΨ₁ hd⟩, fun k hk Ψ hΨ => ?_⟩
    · have hm := (stab Ψ hΨ).1 v g hg
      exact ⟨D.sub_mem hm hΨ, by rw [Isub _ hm _ hΨ, (invV Ψ hΨ).1 v g hg, sub_self]⟩
    · have hm := (stab Ψ hΨ).2.1 k hk
      exact ⟨D.sub_mem hm hΨ, by rw [Isub _ hm _ hΨ, (invV Ψ hΨ).2 k hk, sub_self]⟩
  have hKle : ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), (∀ Ψ ∈ D, G.M.I om Ψ = 0 → Ψ ∈ N) ↔ K ≤ N :=
    fun N => ⟨fun h Ψ hΨ => h Ψ hΨ.1 hΨ.2, fun h Ψ hΨ h0 => h ⟨hΨ, h0⟩⟩
  have cpl' : ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), K ≤ N → N ≤ D → GlobalTheory.ThetaFac.WStable B om D N →
      ∃ N', K ≤ N' ∧ N' ≤ D ∧ GlobalTheory.ThetaFac.WStable B om D N' ∧ N ⊓ N' ≤ K ∧ D ≤ N ⊔ N' := by
    intro N hKN hND hW
    obtain ⟨N', h1, h2, h3, h4, h5⟩ := cpl N ((hKle N).2 hKN) hND hW
    exact ⟨N', (hKle N').1 h1, h2, h3, fun Ψ hΨ => ⟨h2 (Submodule.mem_inf.1 hΨ).2,
      h4 Ψ (Submodule.mem_inf.1 hΨ).1 (Submodule.mem_inf.1 hΨ).2⟩, h5⟩
  have hΦK : Φ ∉ K := fun h => hI h.2

  let S : Set (Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a'))) :=
    {N | GlobalTheory.ThetaFac.WStable B om D N ∧ K ≤ N ∧ N ≤ D ∧ Φ ∉ N}
  have hKS : K ∈ S := ⟨KW, le_rfl, KD, hΦK⟩
  obtain ⟨N₀, -, ⟨hN₀W, hKN₀, hN₀D, hΦN₀⟩, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
      have hne : c.Nonempty := ⟨y, hy⟩
      have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
      refine ⟨sSup c, ⟨wStable_sSup hne hc fun N hN => (hcS hN).1, (hcS hy).2.1.trans (le_sSup hy),
        sSup_le fun N hN => (hcS hN).2.2.1, fun h => ?_⟩, fun z hz => le_sSup hz⟩
      obtain ⟨N, hN, hΦN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcS hN).2.2.2 hΦN) K hKS
  have supW : ∀ N₁ N₂ : Submodule ℂ (GlobalTheory.ThK.Fn F a (a + a')), N₁ ≤ D → N₂ ≤ D →
      GlobalTheory.ThetaFac.WStable B om D N₁ → GlobalTheory.ThetaFac.WStable B om D N₂ → GlobalTheory.ThetaFac.WStable B om D (N₁ ⊔ N₂) :=
    fun N₁ N₂ l₁ l₂ h₁ h₂ => wStable_sup lieD l₁ l₂ h₁ h₂
  refine ⟨N₀, ⟨hN₀D, fun h => hΦN₀ (h ▸ hΦ), KC.casesOn fun hf hl hc => ⟨fun v g hg Ψ hΨ => hKN₀ (hf v g hg Ψ hΨ),
      fun γ hγ Ψ hΨ Ψ₁ hΨ₁ hd => hKN₀ (hl γ hγ Ψ hΨ Ψ₁ hΨ₁ hd), fun k hk Ψ hΨ => hKN₀ (hc k hk Ψ hΨ)⟩, hN₀W, ?_⟩,
    fun Ψ hΨ h0 => hKN₀ ⟨hΨ, h0⟩, hΦN₀⟩
  intro N' hN₀N' hN'D hN'W
  by_cases hΦN' : Φ ∈ N'
  · right
    by_contra hne
    obtain ⟨C, hKC, hCD, hCW, hN₀C, hDN₀C⟩ := cpl' N₀ hKN₀ hN₀D hN₀W

    have hCN' : ¬ C ≤ N' := by
      intro hle
      exact hne (le_antisymm hN'D (hDN₀C.trans (sup_le hN₀N' hle)))
    obtain ⟨c, hcC, hcN'⟩ := SetLike.not_le_iff_exists.1 hCN'
    set Rr := N' ⊓ C with hRr
    have hKR : K ≤ Rr := le_inf (hKN₀.trans hN₀N') hKC
    have hRD : Rr ≤ D := inf_le_left.trans hN'D
    obtain ⟨Rc, hKRc, hRcD, hRcW, hRRc, hDRRc⟩ := cpl' Rr hKR hRD (wStable_inf hN'W hCW)
    set Ss := C ⊓ Rc with hSs
    obtain ⟨r, hr, s', hs', hcrs⟩ := Submodule.mem_sup.1 (hDRRc (hCD hcC))
    have hrC : r ∈ C := (Submodule.mem_inf.1 hr).2
    have hs'C : s' ∈ C := by
      have : s' = c - r := by rw [← hcrs]; abel
      rw [this]; exact C.sub_mem hcC hrC
    have hs'S : s' ∈ Ss := Submodule.mem_inf.2 ⟨hs'C, hs'⟩
    have hs'N' : s' ∉ N' := by
      intro h
      apply hcN'
      rw [← hcrs]
      exact N'.add_mem (Submodule.mem_inf.1 hr).1 h
    have hSD : Ss ≤ D := inf_le_left.trans hCD
    have hSW : GlobalTheory.ThetaFac.WStable B om D Ss := wStable_inf hCW hRcW
    have hbig : N₀ ⊔ Ss ∈ S → N₀ ⊔ Ss ≤ N₀ := fun h => hmax h le_sup_left
    have hΦbig : Φ ∈ N₀ ⊔ Ss := by
      by_contra hnot
      have hle := hbig ⟨supW _ _ hN₀D hSD hN₀W hSW, hKN₀.trans le_sup_left, sup_le hN₀D hSD, hnot⟩
      exact hs'N' (hN₀N' (hle (Submodule.mem_sup_right hs'S)))
    obtain ⟨m, hm, s, hs, hms⟩ := Submodule.mem_sup.1 hΦbig
    have hsN' : s ∈ N' := by
      have : s = Φ - m := by rw [← hms]; abel
      rw [this]; exact N'.sub_mem hΦN' (hN₀N' hm)
    have hsR : s ∈ Rr := Submodule.mem_inf.2 ⟨hsN', (Submodule.mem_inf.1 hs).1⟩
    have hsK : s ∈ K := hRRc (Submodule.mem_inf.2 ⟨hsR, (Submodule.mem_inf.1 hs).2⟩)
    exact hΦN₀ (hms ▸ N₀.add_mem hm (hKN₀ hsK))
  · left
    exact le_antisymm (hmax ⟨hN'W, hKN₀.trans hN₀N', hN'D, hΦN'⟩ hN₀N') hN₀N'

theorem radV_main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Φ ≠ 0 → ∃ N, GlobalTheory.ThetaFac.IsMaxTh B om (GlobalTheory.ThK.PolData B G.M) N ∧ (∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, G.M.I om Ψ = 0 → Ψ ∈ N) ∧ Φ ∉ N :=
  radV GlobalTheory.T.matched_triple_inner_unitary_compatible GlobalTheory.T.matched_triple_character_twist GlobalTheory.T.matched_triple_local_norm_identity GlobalTheory.T.matched_triple_lift_equality GlobalTheory.T.matched_triple_theta_equality GlobalTheory.T.matched_triple_global_lift_identity GlobalTheory.T.matched_triple_unramified_identity

end GlobalTheory.ThetaFacRadV
end
