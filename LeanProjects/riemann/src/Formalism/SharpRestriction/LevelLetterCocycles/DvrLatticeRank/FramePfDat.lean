import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAsm
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLocC
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHH
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfMat
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAlpha

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
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

def FramepfBack {T : LocLat G Qp LL O} (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (Eπ : LetA O n) (h' M : ℕ) : Prop :=
  ∀ (H H' K₁ K₂ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (lam : O),
    H' * H = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₁ →
    H * H' = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₂ →
    ∃ Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c,
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c) ∧
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤,
        Φ (framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x) - lam • x ∈ JLA W T π' Eπ h' M c) ∧
      ∀ y ∈ LamPS W T Eπ h' c,
        framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (Φ y) - lam • y ∈ JP W T π' Eπ h' M c

include Ct in
set_option maxHeartbeats 1000000 in

theorem framepf_data [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (hK : W.gamK = W.gam)
    (Bs : FramepfBas W T) (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hγN : ∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d)
    (Fs : PowerSeries O)
    (hFs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs))
    (hF0 : PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s')
    (hne : ∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) (aσ : O)
    (haσ : ((PD.p : ℕ) : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  have huE := framepf_E_unit hR hs
  have hEΔ := framepf_E_Δ hR
  obtain ⟨Γ, hΓ, R, hΓR⟩ := framepf_Γ Bs π' (c - 1) hπ0 hΔπ hR2 hu hγN
  obtain ⟨H, H', ⟨K1, hK1⟩, ⟨K2, hK2⟩, -, -, ⟨K5, hK5⟩, ⟨K6, hK6⟩⟩ :=
    framepf_mats _ hne Fs hF0 R M hM1 aσ _ haσ
  rw [← pow_mul, mul_comm σ 2] at hK5 hK6
  obtain ⟨Φ, hΦL, hΦJ, hβα, hαβ⟩ := hB H H' K5 K6 _ hK5 hK6
  have hγ := framepf_hhx_γ Bs π' c hπ0 hΔπ hR2 γ0 hu (PowerSeries.X * Fs) (by simp) hFs Γ hΓ H K2 M
    (by rw [hΓR]; exact hK2)
  have hmod := framepf_hhx_mod Bs π' c hπ0 hΔπ hR2 γ0 hu _ H K1 hK1
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero] at h1
    have := W.v_l
    rw [h1, AddValuation.map_zero] at this
    exact absurd this (by simp)
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.1
  refine ⟨_, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H, Φ,
    framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu _ huE hEΔ h' H, hΦL, hγ, hmod,
    framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H, framepf_Ψα_J Bs π' c hπ0 hΔπ hR2 γ0 hu _ h' M H,
    hΦJ, hβα, hαβ, fun x hx hj => ?_, fun x hx hgx => ?_, fun τ ζ hpt x y hxy m a z hrep k hk i hi => ?_⟩
  · exact framepf_JLA_sat π' c (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu) _ h' M hu huE
      (fun o ho => (mul_eq_zero.1 ho).resolve_left hp0) _ x hx hj
  · obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
    obtain ⟨Ff, hFf, -⟩ := hR2 f hfΔ
    obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Ff hFf _ (gradNPf_cc_f W s' w π' f hw hf)
    refine invLiftPf_inj W T π' f t _ hf ht hu hΔπ hγN hK M (fun y hy _ r₀ hr₀ d hd hrd => ?_) x hx
      (by rw [hK]; exact hgx)
    exact invLiftPf_nzd W T π' w s' w.isUnit hw _
      (fun o ho => (mul_eq_zero.1 ho).resolve_left (sub_ne_zero.2 (hne y hy))) Bs.r Bs.b
      (fun j => (Bs.mem j).1) Bs.uniq 1 r₀ d hr₀ hd (by rw [pow_one]; exact hrd)
  · refine framepf_locC Ct T hT hs c ζ (hprim τ ζ hpt) (fun x k hk => ?_) ?_ (fun r hr h => ?_)
      π' _ w w' s' h' M σ hs' hw w'.isUnit hw' hM _
      (fun ℓ => ((mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ)).1) hγ hmod
      _ (framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H) x y hxy m a z hrep k hk i hi
    · exact ((h4.1 (c - 1) 1 ⟨0, one_pow _⟩
        (by rw [Formalism.MainNotions.LiftingTheory.wmap_X_one W hs]; exact framepf_lev_π_one _)).1 x k).2 hk
    · rw [W.gam_gen]
      rw [hs, Nat.cast_one]
      exact zero_le_one
    · obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
      rw [zpow_natCast, ← map_pow, ← map_one (algebraMap O LL)] at h
      apply hne y (by omega)
      rw [← pow_mul, mul_comm, pow_mul, hι h, one_pow]

end Local

end Formalism.MainNotions.N.Ln34

end
