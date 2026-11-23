import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VanishNConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.MemIntegersOfMemIntAd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.PrincipalCongruenceMemLevel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2 Formalism.L2.SG.Pf.SlabCoverPf
open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_base_lattice_iff_adelic {D : D7} (X : HidaSetting D) (y : (VS D).V) :
    y ∈ (VS D).L0 ↔ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
  rw [Formalism.L2.SG.Pf.LatDict.mem_hermitianStandardLattice_iff_pairing_integral X y]
  exact ⟨fun h => Formalism.L2.SG.Pf.Level.incl_mem_Lf X _ h,
    fun h => Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.mem_L_of_inclE_mem X.B.I _ h⟩

theorem noratC_holds : NOratC := by
  intro D X u s
  constructor
  · rintro ⟨γ, hG, rfl, hN, hF, hk⟩
    have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties X
    have hγK : γ.2 ∈ X.B.I.Kset := by
      have h1 : (X.xu u)⁻¹ * γ.2 * X.xu u ∈ X.B.I.Kset := hK2.2.1 _ hk
      have e : γ.2 = X.xu u * ((X.xu u)⁻¹ * γ.2 * X.xu u) * (X.xu u)⁻¹ := by group
      rw [e]
      exact unitaryCongruence.K_mul X.B.I (unitaryCongruence.K_mul X.B.I (X.xu_K u) h1) (unitaryCongruence.K_inv X.B.I (X.xu_K u))
    obtain ⟨M, hM, hinf, hfin⟩ := hG
    refine ⟨γ, matEC X M, ⟨M, hM, hinf, hfin, matE_crdC X M⟩, rfl, ?_⟩
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have hGv : ∀ y, uMat (γ.1 v) *ᵥ rvHom X.B.I v y = rvHom X.B.I v ((M : Matrix _ _ _) *ᵥ y) := by
      intro y
      rw [rvHom_apply, rvHom_apply, hinf v]
      exact rv_mulVec X v _ y
    have hsub : ∀ y, (uMat (γ.1 v) - 1) *ᵥ rv X.B.I v y = rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ y) :=
      fun y => tr_sub (rvHom X.B.I v) _ _ hGv y
    have hcrdn : ∀ y, X.crd (matEC X M y - y) = ((M : Matrix _ _ _) - 1) *ᵥ X.crd y := by
      intro y
      rw [crd_sub', matE_crdC, Matrix.sub_mulVec, Matrix.one_mulVec]
    have hback : ∀ (y : (VS D).V) (T : Set (Fin D.R.rS)),
        ((M : Matrix _ _ _) - 1) *ᵥ X.crd y ∈ Submodule.span X.B.I.E (X.eR '' T) →
        matEC X M y - y ∈ Submodule.span D.host.E (X.eX '' T) := by
      intro y T hy
      rw [← hcrdn] at hy
      have := toV_span X hy
      rwa [toV_crd] at this
    have hInN := hN v
    refine ⟨⟨matE_isomC X M hM, ?_⟩, ?_, ?_⟩
    · have key : ∀ y, matEC X M y ∈ (VS D).L0 ↔ y ∈ (VS D).L0 := by
        intro y
        rw [mem_base_lattice_iff_adelic, mem_base_lattice_iff_adelic, matE_inclC, ← hfin]
        exact (Formalism.L2.SG.Pf.UnipB.kset_apply X hγK _).symm
      show Formalism.HermitianLatticesTheory.gmap (matEC X M) (VS D).L0 = (VS D).L0
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (key z).2 hz
      · intro hy
        refine ⟨(matEC X M).symm y, (key _).1 (by simpa using hy), ?_⟩
        simp
    · intro j x hx
      change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
      change _ ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
      rw [X.Fu_e] at hx ⊢
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        have h1 := hInN.1.1 a
        rw [hsub] at h1
        have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.eR a) ∈
            Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < a.1})) := by
          rw [Set.image_image]; exact h1
        have h3 := rv_desc X v _ _ h2
        have h4 : ((M : Matrix _ _ _) - 1) *ᵥ X.crd (X.eX a) ∈
            Submodule.span X.B.I.E (X.eR '' {b | b.1 < j}) := by
          refine Submodule.span_mono (Set.image_mono fun b hb => ?_) h3
          have : a.1 < j + 1 := ha
          show b.1 < j
          have : b.1 < a.1 := hb
          omega
        exact hback _ _ h4
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add, add_sub_add_comm]
        exact add_mem ha hb
      | smul c a _ ha =>
        rw [map_smul, ← smul_sub]
        exact Submodule.smul_mem _ _ ha
    · intro x hx
      change x ∈ orth (VS D) (Submodule.span D.host.E (Set.range (X.Fu u).e)) at hx
      change _ ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e] at hx ⊢
      have hzero : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.crd x)) = 0 := by
        intro a
        rw [hJ_rv]
        have h0 : hE X (X.eR a) (X.crd x) = 0 := by
          apply X.ιE.injective
          rw [iota_hE, map_zero, HidaSetting.eR, toV_crd, toV_crd]
          exact (mem_orth_iff _ _).1 hx _ (Submodule.subset_span ⟨a, rfl⟩)
        rw [h0, map_zero]
      have h1 := hInN.2 _ hzero
      rw [hsub] at h1
      have huniv : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
      have h2 : rv X.B.I v (((M : Matrix _ _ _) - 1) *ᵥ X.crd x) ∈
          Submodule.span ℂ (rv X.B.I v '' (X.eR '' {b | b.1 < D.R.rS})) := by
        rw [Set.image_image]; exact h1
      have h3 := hback x _ (rv_desc X v _ _ h2)
      rwa [huniv, Set.image_univ] at h3
  · rintro ⟨x, n, hx, rfl, hn⟩
    have hNf := nLamNfin_holds D X u _ x n hx hn
    have hlat : ∀ y : (VS D).V, y ∈ (VS D).L0 ↔
        X.B.I.fmat (((1 : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf := by
      intro y
      rw [mem_base_lattice_iff_adelic]
      simp only [OneMemClass.coe_one, one_mul]
      exact Formalism.L2.SG.Pf.UnipB.kset_apply X (unitaryCongruence.K_inv X.B.I (X.xu_K u)) _
    have hc := (Formalism.L2.SG.Pf.VanishNConj.core X u (Formalism.L2.SG.Pf.unipotent_in_level X u) 1 hlat hn hx).1
    simp only [OneMemClass.coe_one, one_mul] at hc
    exact ⟨x, ratLink_mem X hx, rfl, nLamNinf_holds D X u _ x n hx hn, hNf, hc⟩

end Formalism.L2.SG.Pf.NcReal.JX.NOf
