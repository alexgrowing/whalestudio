import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualLeGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLatticeLocF
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFDualF

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

def InFib (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T Λ : Submodule (𝓞 K) V) :
    Prop :=
  (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

theorem mem_W_of_prO_zero {x : V} (hx : prO hc x = 0) : x ∈ orthK h U ∧ prO hc.symm x = x := by
  have e := prO_add hc x
  rw [hx, zero_add] at e
  refine ⟨?_, e⟩
  rw [← e]
  rw [prO_apply]
  first
  | exact Submodule.projection_apply_mem ..
  | exact Submodule.projection_apply_mem _ _
  | exact Submodule.projection_apply_mem _ _ _
  | exact Submodule.projection_apply_mem _
  | simp

theorem prO_symm_locF (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {y : V} (hy : y ∈ locF 𝔭 N) :
    prO hc.symm y ∈ locF 𝔭 (N.map (prO hc.symm)) := by
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp N y).mp hy
  refine (LocF.mem_locF_iff hp _ _).mpr ⟨t, ht, ?_⟩
  have hs := (prO hc.symm).map_smul (algebraMap (𝓞 F) (𝓞 K) t) y
  rw [← hs]
  exact Submodule.mem_map_of_mem hty

theorem glue_mem [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hG₀ : Good hc M T 𝔭 Λ₀) (h0 : InFib h U 𝔭 M T Λ₀)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) (hsurj : Function.Surjective P) :
    InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
  have hp := h𝔭.isPrime
  obtain ⟨⟨N₀, hN₀, hΛ₀⟩, hd₀, -, -⟩ := h0
  have hd : dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) = glue hc T 𝔭 Λ₀ P :=
    le_antisymm (dual_le_glue hs hG₀ hd₀ hM hT hP hsurj) (glue_le_dual hs hd₀ hP)
  have hIU := glue_inf_U hG₀ hd₀ hP
  have hIW := glue_inf_orthK_eq_locF (P := P) hG₀
  refine ⟨?_, hd, hIU, hIW⟩
  refine exists_lattice_locF h𝔭 (isLattice_sup hc hM hT) (L₂ := N₀ ⊔ N₀.map (prO hc.symm))
    (hN₀.fg.sup (hN₀.fg.map _)) ?_ ?_ ?_
  · conv_lhs => rw [← hd]
    rw [locF_dualF h𝔭, hd]
  · refine sup_le ?_ ?_
    · intro m hm
      have : m ∈ locF 𝔭 M := LocF.le_locF 𝔭 M hm
      rw [← hIU] at this
      exact this.1
    · intro m hm
      have : m ∈ locF 𝔭 T := LocF.le_locF 𝔭 T hm
      rw [← hIW] at this
      exact this.1
  · rintro x ⟨b, hb, y, hy, c, hcy, hU, hPc⟩
    obtain ⟨z, hz, hzb⟩ := hG₀.oW b b.2
    have hyN : y ∈ locF 𝔭 N₀ := hΛ₀ ▸ hy
    have hzN : z ∈ locF 𝔭 N₀ := hΛ₀ ▸ hz
    have ex : x = y - prO hc.symm y + prO hc.symm z := by
      have e3 : prO hc y = y - prO hc.symm y := eq_sub_of_add_eq (prO_add hc y)
      calc x = prO hc x + prO hc.symm x := (prO_add hc x).symm
        _ = prO hc y + prO hc.symm z := by rw [hU, hzb, hb]
        _ = _ := by rw [e3]
    rw [ex]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact LocF.locF_mono 𝔭 le_sup_left hyN
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hyN)
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hzN)

def isoOf (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) :
    Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) :=
  ((gam hG₀).symm.trans (gam hG)).toLinearMap

theorem isoOf_mk (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) {y w : V} (hy : y ∈ Λ₀) (hw : w ∈ Λ)
    (hwU : prO hc w = prO hc y) :
    isoOf hG₀ hG (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm w, hG.iW w hw⟩ := by
  have key : ∀ {Λ' : Submodule (𝓞 K) V} (hG' : Good hc M T 𝔭 Λ') (b : Λ'),
      gam hG' (toDisc h hc M Λ' 𝔭 hG'.iU b) = toDisc h hc.symm T Λ' 𝔭 hG'.iW b := by
    intro Λ' hG' b
    unfold gam
    simp only [LinearEquiv.trans_apply]
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ' 𝔭 hG'.iU)
        (toDisc_surj h hc M Λ' 𝔭 hG'.iU hG'.oU) b, LinearEquiv.symm_apply_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have h1 : (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩ : DiscMod h (orthK h U) T 𝔭) =
      gam hG₀ (toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩) := (key hG₀ ⟨y, hy⟩).symm
  have h2 : toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩ = toDisc h hc M Λ 𝔭 hG.iU ⟨w, hw⟩ :=
    congrArg Submodule.Quotient.mk (Subtype.ext hwU.symm)
  unfold isoOf
  rw [h1]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [h2]
  exact key hG ⟨w, hw⟩

end Formalism.L2.SG.Pf.OrthogonalProjections
