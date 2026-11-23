import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.Cnt
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

section Local

variable (K F : Type) [Field K] [Field F] [NumberField F] [Algebra F K]

def vT (T : ℕ) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((T : ℕ) : 𝓞 F)}))

def glueT (T : ℕ) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
    (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then
      (Ideal.absNorm 𝔭.1 : ℝ) ^ vT F T 𝔭.1 * (1 - etaF K F 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℝ)⁻¹) else 1)

def lamT (k T : ℕ) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
    (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then
      (Ideal.absNorm 𝔭.1 : ℝ) ^ ((k - 1) * vT F T 𝔭.1) *
        (1 - etaF K F 𝔭.1 ^ k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ))) /
        (1 - etaF K F 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℝ)⁻¹) else 1)

end Local

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowsGenus : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ →
        ∃ (V0 : Type) (_ : AddCommGroup V0) (_ : Module D.host.E V0) (_ : FiniteDimensional D.host.E V0)
          (_ : Module (𝓞 D.host.E) V0) (_ : IsScalarTower (𝓞 D.host.E) D.host.E V0)
          (h0 : V0 →ₗ⋆[D.host.E] V0 →ₗ[D.host.E] D.host.E) (L0 : Submodule (𝓞 D.host.E) V0),
          h0.IsSymm ∧ IsTotPosDef h0 ∧ finrank D.host.E V0 = D.R.k ∧ Submodule.IsLattice D.host.E L0 ∧
          Formalism.HermitianLatticesTheory.IsIntegralLat h0 L0 ∧
          Formalism.MainNotions.S.Cnt.massRows D F0 what₂ = Formalism.HermitianLatticesTheory.mass h0 L0 * glueT D.host.E D.host.F (D.mem u).A.T ∧
          lamG D.host.F h0 L0 = lamT D.host.E D.host.F D.R.k (D.mem u).A.T

def LamGlue : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [NumberField F] [Algebra F K] (k T : ℕ), 1 ≤ k → 0 < T →
    lamT K F k T * glueT K F T = (T : ℝ) ^ (k * finrank ℚ F) *
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
        (if ((T : ℕ) : 𝓞 F) ∈ 𝔭.1 then
          1 - etaF K F 𝔭.1 ^ k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) else 1)

section Const

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem massConst_unique_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {c c' : ℝ}
    (hc : MassConst K F 1 c) (hc' : MassConst K F 1 c') : c = c' := by
  have ho := stdLat_isOrtho K 1
  have hs := stdForm_isSymm K 1
  have e := hc _ (stdForm K 1) (stdLat K 1) hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
  have e' := hc' _ (stdForm K 1) (stdLat K 1) hs (isTotPosDef_of_ortho hK hs ho) (finrank_of_ortho ho)
    (isLattice_of_ortho ho) (isIntegralLat_of_ortho ho)
  rw [lamG_eq_one_of_ortho hK hF hs ho, mul_one] at e e'
  rw [← e, ← e']

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem massConst_cMass (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 1 ≤ m) :
    MassConst K F m (cMass K F m) := by
  obtain ⟨c₁, hc₁, hall⟩ := massConst_all hermRepUnram liStat hK hF
  have h1 : MassConst K F 1 c₁ := by
    have := hall 1 le_rfl
    rwa [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty, mul_one] at this
  have hex : ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := ⟨c₁, hc₁, h1⟩
  have hone : cOne K F = c₁ := by
    unfold cOne
    rw [dif_pos hex]
    exact massConst_unique_one hK hF hex.choose_spec.2 h1
  unfold cMass
  rw [hone]
  exact hall m hm

end Const

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem rowsMass_of_lamGlue (hH : HostDict) (hG : RowsGenus) (hA : LamGlue) : RowsMass := by
  intro D u u' hcong F0 what₂ hrows
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hT : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  obtain ⟨V0, _, _, _, _, _, h0, L0, hs, hpd, hr, hlat, hint, hmr, hlam⟩ :=
    hG D u u' hcong F0 what₂ hrows
  obtain ⟨hK, hF, -⟩ := hH D
  have e := massConst_cMass hK hF D.R.k hk V0 h0 L0 hs hpd hr hlat hint
  rw [hmr, e, mul_assoc, hlam, hA _ _ _ _ hk hT]
  ring

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
