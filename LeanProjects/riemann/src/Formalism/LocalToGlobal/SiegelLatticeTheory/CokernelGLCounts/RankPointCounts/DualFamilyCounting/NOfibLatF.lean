import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemHermitianStandardLatticeIffPairingIntegral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatF

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem mem_mul_inv_of {I J : FI} (hI : I ≠ 0) {x : D.host.E} (h : ∀ c ∈ I, c * x ∈ J) : x ∈ J * I⁻¹ := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I ≤ J := by
    rw [FractionalIdeal.mul_le]
    intro s hs c hc
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
    rw [Algebra.smul_def, mul_assoc, mul_comm x c]
    exact LatA.fi_smul_mem (h c hc) z
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ J * I⁻¹ := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ J * I⁻¹ := FractionalIdeal.mul_le.mpr fun i hi j hj => FractionalIdeal.mul_mem_mul (h1 hi) hj
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ x)

theorem mul_mem_cancel {I J K : FI} (hK : K ≠ 0) {x y : D.host.E} (hx : x ∈ I * K⁻¹) (hy : y ∈ K * J) :
    x * y ∈ I * J := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  have e : I * K⁻¹ * (K * J) = I * J := by
    calc I * K⁻¹ * (K * J) = I * J * (K⁻¹ * K) := by ring
      _ = I * J := by rw [inv_mul_cancel₀ hK, mul_one]
  rwa [e] at h

variable (X : HidaSetting D)

theorem aa_ne (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.aaD_ne_zero Y a

theorem e_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ aaD D a) : c • X.eX a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hc, rfl⟩))

theorem f_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D a)⁻¹) : c • X.fY a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩)

variable {X}

theorem lattice_map_preserves_base {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    {y : (VS D).V} (hy : y ∈ (VS D).L0) : m y ∈ (VS D).L0 := by
  rw [← hL]; exact ⟨y, hy, rfl⟩

theorem gmap_symm {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0) :
    Formalism.HermitianLatticesTheory.gmap m.symm (VS D).L0 = (VS D).L0 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hL] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show m.symm (m w) ∈ (VS D).L0
    simpa using hw
  · intro hy
    exact ⟨m y, lattice_map_preserves_base hL hy, by simp⟩

theorem ex_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b d : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.eX d)) ∈ aaD D b * (aaD D d)⁻¹ := by
  refine mem_mul_inv_of (aa_ne X d) fun c hc => ?_
  have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (e_mem X hc))
  rw [map_smul, map_smul, smul_eq_mul] at h
  exact h

theorem fa_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b a : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.fY a)) ∈ aaD D b * aaD D a := by
  have hne : (aaD D a)⁻¹ ≠ 0 := inv_ne_zero (aa_ne X a)
  have := mem_mul_inv_of hne (J := aaD D b) (x := (VS D).hT (X.fY b) (m (X.fY a))) fun c hc => by
    have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (f_mem X hc))
    rw [map_smul, map_smul, smul_eq_mul] at h
    exact h
  rwa [inv_inv] at this

variable {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem Xinv (hn : NFl X u n) : Xq X n.symm * Xq X n = 1 := by
  refine Matrix.ext fun b a => ?_
  simp only [Matrix.mul_apply, Xq]
  rw [Finset.sum_congr rfl fun d _ => mul_comm _ _, ← hT_sumR]
  have e : ∑ d, (VS D).hT (X.fY d) (n (X.eX a)) • n.symm (X.eX d) = n.symm (n (X.eX a)) := by
    conv_rhs => rw [Xq_expand hn a]
    rw [map_sum]
    simp only [map_smul, Xq]
  rw [e, LinearEquiv.symm_apply_apply, hfe, Matrix.one_apply]

theorem rows_mem (hL : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) (b : Fin D.R.rS) : xq X n b ∈ aaLb X b := by
  have hβ : ∀ β ∈ (aaD D b)⁻¹, β • xq X n b ∈ X.Lb := by
    intro β hβ
    have h := lattice_map_preserves_base (gmap_symm hL) (f_mem X hβ)
    rw [map_smul] at h
    have := ((LatA.mem_hermitianStandardLattice_iff_pairing_integral X _).1 h).2.2
    rwa [pW_smul] at this
  have h1 : (1 : D.host.E) ∈ aaD D b * (aaD D b)⁻¹ := by
    rw [mul_inv_cancel₀ (aa_ne X b)]; exact FractionalIdeal.one_mem_one _
  have key : ∀ t ∈ ((aaD D b * (aaD D b)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E),
      t • xq X n b ∈ aaLb X b := by
    intro t ht
    rw [FractionalIdeal.coe_mul] at ht
    refine Submodule.mul_induction_on ht (fun α hα β hβ' => ?_) (fun s t hs ht => ?_)
    · rw [mul_smul]
      exact Submodule.subset_span ⟨α, hα, β • xq X n b, hβ β hβ', rfl⟩
    · rw [add_smul]; exact add_mem hs ht
  simpa using key 1 h1

end LatF

open Alg LatF in

theorem dictLatF_holds : DictLatF := by
  intro D X u n hn hL
  refine ⟨fun b a _ => ex_shape hL b a, fun b => rows_mem hL b, fun b a => ?_⟩
  have hinv : (Xq X n)⁻¹ = Xq X n.symm := Matrix.inv_eq_left_inv (Xinv hn)
  show ((Xq X n)⁻¹ * Aq X n) b a ∈ _
  rw [hinv, Matrix.mul_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  exact mul_mem_cancel (aa_ne X d) (ex_shape (gmap_symm hL) b d) (fa_shape hL d a)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
