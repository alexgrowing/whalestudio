import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n)

structure FramepfData (T : LocLat G Qp LL O) (hh : LcQ W T π' c →ₗ[O] W.DD T)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c) : Prop where
  hγ : ∀ ℓ, W.γD T W.gam (hh ℓ) - hh ℓ ∈ PiNS W T π' M
  hmod : ∀ z hz, hh (mkL W T π' c z hz) - ((PD.p : ℕ) : O) ^ σ • z ∈ PiNS W T π' 1
  hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ)
  ΨJ : ∀ x ∈ JLA W T π' Eπ h' M c, Ψ x ∈ JP W T π' Eπ h' M c
  ΦJ : ∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c
  βα : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, Φ (Ψ x) - ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c
  αβ : ∀ y ∈ LamPS W T Eπ h' c, Ψ (Φ y) - ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ JP W T π' Eπ h' M c
  sat : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c →
    x ∈ JLA W T π' Eπ h' M c
  inj : ∀ x ∈ PiNS W T π' 1, W.γD T W.gam x - x ∈ PiNS W T π' M → x ∈ PiNS W T π' M
  loc : ∀ τ ζ, Pt c ζ τ → ∀ x y, Ψ x - y ∈ JP W T π' Eπ h' M c →
    ∀ (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a z →
    ∀ (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ), i < k + 4 * h' →
      W.levN T c ζ ⟨_, hk⟩ i =
        (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i

theorem quotientMk_eq_iff_sub_mem {T : LocLat G Qp LL O} {y y' : W.DD T} (hy : y ∈ LamPS W T Eπ h' c)
    (hy' : y' ∈ LamPS W T Eπ h' c) :
    mkP W T π' Eπ h' M c y hy = mkP W T π' Eπ h' M c y' hy' ↔ y - y' ∈ JP W T π' Eπ h' M c :=
  Submodule.Quotient.eq _

theorem framepf_mkLA_eq {T : LocLat G Qp LL O} {x x' : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hx' : x' ∈ LamLA W T π' Eπ h' c ⊤) :
    mkLA W T π' Eπ h' M c x hx = mkLA W T π' Eπ h' M c x' hx' ↔ x - x' ∈ JLA W T π' Eπ h' M c :=
  Submodule.Quotient.eq _

set_option maxHeartbeats 1000000 in

theorem framepf_frameA (hK : W.gamK = W.gam) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    {f t t' : LetA O n} (hfΔ : f ∈ W.AΔ) (hf : W.γA W.gamK π' = π' * f)
    (htΔ : t ∈ W.AΔ) (ht : W.γA W.gamK Eπ = Eπ * t)
    (ht'Δ : t' ∈ W.AΔ) (ht' : Eπ = W.γA W.gamK Eπ * t')
    (hex : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) :
    FrameA W Pt π' Eπ h' M σ c := by
  have hex' : ∀ T : LocLat G Qp LL O, ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (IsCrys PD T.ρ → FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) := by
    intro T
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨hh, Ψ, Φ, h1, h2, h3⟩ := hex T hT
      exact ⟨hh, Ψ, Φ, h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 0, fun _ _ => Submodule.zero_mem _, fun _ _ => Submodule.zero_mem _,
        fun h => absurd h hT⟩
  choose hh Ψ Φ hΨL hΦL hD using hex'
  let α : FrA W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp (LinearMap.codRestrict (LamPS W T Eπ h' c)
    (((Ψ T).restrictScalars O).comp (LamLA W T π' Eπ h' c ⊤).subtype) fun x => hΨL T x x.2)
  let β : FrB W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp
    (LinearMap.codRestrict (LamLA W T π' Eπ h' c ⊤)
      (((Φ T).restrictScalars O).comp (LamPS W T Eπ h' c).subtype) fun y => hΦL T y y.2)
  have hα : ∀ T x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy ↔
      Ψ T x - y ∈ JP W T π' Eπ h' M c := fun T x hx y hy =>
    quotientMk_eq_iff_sub_mem W π' Eπ h' M c (hΨL T x hx) hy
  have hβ : ∀ T y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx ↔
      Φ T y - x ∈ JLA W T π' Eπ h' M c := fun T y hy x hx =>
    framepf_mkLA_eq W π' Eπ h' M c (hΦL T y hy) hx
  refine ⟨α, β, fun T hT _ => ?_, fun T₁ T₂ F hT₁ hT₂ _ _ => ?_⟩
  · have D := hD T hT
    have hΨγ := framepf_Ψα_γ π' Eπ h' M c ht'Δ ht' hu huE hΔπ u huΔ hφ (hh T)
      (by rw [hK]; exact D.hγ) (Ψ T) D.hΨ
    refine ⟨fun x hx hJ => ?_, fun y hy hJ => ?_, fun x hx y hy h => ?_, fun y hy x hx h => ?_,
      fun a ha x hx y hy h hax hay => ?_, fun a ha y hy x hx h hay hax => ?_,
      fun x hx y hy h hgx hgy => ?_, fun y hy x hx h hgy hgx => ?_,
      fun τ ζ hpt x hx y hy h => D.loc τ ζ hpt x y ((hα T x hx y hy).1 h)⟩
    · exact (hα T x hx 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΨJ x hJ)
    · exact (hβ T y hy 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΦJ y hJ)
    · rw [hβ]
      have h1 := Submodule.sub_mem _ (D.βα x hx) (D.ΦJ _ ((hα T x hx y hy).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα]
      have h1 := Submodule.sub_mem _ (D.αβ y hy) (D.ΨJ _ ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα, framepf_Ψ_smulLA, ← smul_sub]
      exact framepf_JP_smul π' Eπ h' M c ha ((hα T x hx y hy).1 h)
    · rw [hβ, ← algebraMap_smul W.EE a y, map_smul, ← framepf_smulLA_alg, ← map_sub]
      exact framepf_JLA_smul π' Eπ h' M c ha ((hβ T y hy x hx).1 h)
    · rw [hα]
      have h1 := Submodule.sub_mem _
        (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht ((hα T x hx y hy).1 h)) (hΨγ x hx)
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hβ]
      have h1 := Submodule.add_mem _
        (framepf_Ψβ_γ π' Eπ h' M c hfΔ hf htΔ ht ht'Δ ht' (Ψ T) (Φ T) _ hΨγ (hΦL T) D.ΦJ D.αβ D.βα
          D.sat y hy hgy)
        (framepf_γ_JLA π' Eπ h' M c hfΔ hf htΔ ht ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_add_sub_cancel] at h1
      exact h1
  · have D₁ := hD T₁ hT₁
    have D₂ := hD T₂ hT₂
    have hFN := W.map_N F hT₁ hT₂
    have hnat := framepf_Ψα_nat F hFN π' Eπ h' M c hu huE hΔπ u huΔ hφ (hh T₁) (hh T₂)
      (framepf_hh_nat F hFN π' c M _ D₂.inj (hh T₁) (hh T₂) D₁.hγ D₂.hγ D₁.hmod D₂.hmod)
      (Ψ T₁) D₁.hΨ (Ψ T₂) D₂.hΨ
    refine ⟨fun x₁ hx₁ x₂ hx₂ y₁ hy₁ hy₂ hov h => ?_, fun y₁ hy₁ hy₂ x₁ hx₁ x₂ hx₂ hov h => ?_⟩
    · rw [hα]
      exact framepf_α_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat x₁ hx₁ x₂ y₁ hov
        ((hα T₁ x₁ hx₁ y₁ hy₁).1 h)
    · rw [hβ]
      exact framepf_β_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat (Φ T₁) (Φ T₂) _ (hΦL T₁) (hΦL T₂)
        D₂.ΦJ D₁.αβ D₂.βα D₂.sat y₁ hy₁ hy₂ x₁ x₂ hov ((hβ T₁ y₁ hy₁ x₁ hx₁).1 h)

end Local

end Formalism.MainNotions.N.Ln34

end
