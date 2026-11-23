import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleInnerUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleCharacterTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLocalNormIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleLiftEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleThetaEqualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentityStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ThetaFacRadV

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (h h₀ : UA σ W.J) :
    M.I om (om (1, h) Φ) h₀ = M.I om Φ (h₀ * h) := by
  unfold Model.I theta
  congr 1
  funext g
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem wStable_inf {B : Base F E} {om : Rep σ Y W} {D N₁ N₂ : Submodule ℂ (Fn F n d)}
    (h₁ : GlobalTheory.ThetaFac.WStable B om D N₁) (h₂ : GlobalTheory.ThetaFac.WStable B om D N₂) :
    GlobalTheory.ThetaFac.WStable B om D (N₁ ⊓ N₂) :=
  ⟨fun v h hh Φ hΦ => Submodule.mem_inf.2 ⟨h₁.fin v h hh Φ (Submodule.mem_inf.1 hΦ).1, h₂.fin v h hh Φ (Submodule.mem_inf.1 hΦ).2⟩,
   fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => Submodule.mem_inf.2 ⟨h₁.lie γ hγ Φ (Submodule.mem_inf.1 hΦ).1 Φ₁ hΦ₁ hd,
     h₂.lie γ hγ Φ (Submodule.mem_inf.1 hΦ).2 Φ₁ hΦ₁ hd⟩,
   fun k hk Φ hΦ => Submodule.mem_inf.2 ⟨h₁.cpt k hk Φ (Submodule.mem_inf.1 hΦ).1, h₂.cpt k hk Φ (Submodule.mem_inf.1 hΦ).2⟩⟩

theorem wStable_sup {B : Base F E} {om : Rep σ Y W} {D N₁ N₂ : Submodule ℂ (Fn F n d)}
    (hD : ∀ γ ∈ Lines σ W, ∀ Φ ∈ D, ∃ Φ₁ ∈ D, ∀ x,
      HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0)
    (l₁ : N₁ ≤ D) (l₂ : N₂ ≤ D)
    (h₁ : GlobalTheory.ThetaFac.WStable B om D N₁) (h₂ : GlobalTheory.ThetaFac.WStable B om D N₂) :
    GlobalTheory.ThetaFac.WStable B om D (N₁ ⊔ N₂) := by
  refine ⟨fun v h hh Φ hΦ => ?_, fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => ?_, fun k hk Φ hΦ => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.fin v h hh y hy) (h₂.fin v h hh z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    obtain ⟨y₁, hy₁D, hy₁⟩ := hD γ hγ y (l₁ hy)
    obtain ⟨z₁, hz₁D, hz₁⟩ := hD γ hγ z (l₂ hz)
    have e : Φ₁ = y₁ + z₁ := by
      funext x
      have h2 : HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (y + z) x) (y₁ x + z₁ x) 0 := by
        have hf : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (y + z) x) =
            fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) y x + om (1, γ (Multiplicative.ofAdd t)) z x := by
          funext t
          rw [map_add, Pi.add_apply]
        rw [hf]
        exact (hy₁ x).add (hz₁ x)
      exact (hd x).unique h2
    rw [e]
    exact Submodule.add_mem_sup (h₁.lie γ hγ y hy y₁ hy₁D hy₁) (h₂.lie γ hγ z hz z₁ hz₁D hz₁)
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
    rw [map_add]
    exact Submodule.add_mem_sup (h₁.cpt k hk y hy) (h₂.cpt k hk z hz)

theorem wStable_sSup {B : Base F E} {om : Rep σ Y W} {D : Submodule ℂ (Fn F n d)} {c : Set (Submodule ℂ (Fn F n d))}
    (hne : c.Nonempty) (hc : IsChain (· ≤ ·) c) (h : ∀ N ∈ c, GlobalTheory.ThetaFac.WStable B om D N) :
    GlobalTheory.ThetaFac.WStable B om D (sSup c) := by
  have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
  refine ⟨fun v g hg Φ hΦ => ?_, fun γ hγ Φ hΦ Φ₁ hΦ₁ hd => ?_, fun k hk Φ hΦ => ?_⟩
  · obtain ⟨N, hN, hΦN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hΦ
    exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨N, hN, (h N hN).fin v g hg Φ hΦN⟩
  · obtain ⟨N, hN, hΦN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hΦ
    exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨N, hN, (h N hN).lie γ hγ Φ hΦN Φ₁ hΦ₁ hd⟩
  · obtain ⟨N, hN, hΦN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hΦ
    exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨N, hN, (h N hN).cpt k hk Φ hΦN⟩

end General

end GlobalTheory.ThetaFacRadV

end
