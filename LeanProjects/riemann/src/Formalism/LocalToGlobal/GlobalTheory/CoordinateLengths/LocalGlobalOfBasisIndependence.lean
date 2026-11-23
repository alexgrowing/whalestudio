import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB.G0

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

def BwLocGlob0 (Tt : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (y : ((D.fm u).lat i).V),
    (∀ c, ∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B ∧
      ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i y c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi h0).eY z)) →
    y ∈ (D.fm u).S i w

def BwBasisInd0 (Tt : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B₂ : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B₂ →
    ∀ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z,
      fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi h0).eY z) =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q₂ ((Tt.val i hi h0).eY z)

theorem local_global_of_basis_independence (Tt : Forms0 D u) (hI : BwBasisInd0 D u Tt) : BwLocGlob0 D u Tt := by
  intro w hw i hi h0 y hy
  show y ∈ locW D.what₂.places w ((D.fm u).lat i).L
  rw [D.mem_locW_iff]
  obtain ⟨-, -, hsp⟩ := (D.fm u).lat_good i
  obtain ⟨d, hd, hdy⟩ := Formalism.L2.DIV.lc_exists_smul_mem ((D.fm u).lat i).L (x := y) (by rw [hsp]; trivial)
  obtain ⟨t, ht, htw⟩ := Formalism.L2.DIV.lc_primeTo d hd (D.plEq w)
  refine ⟨t, ht, ?_⟩
  refine ((Tt.val i hi h0).lat _).2 fun w' c B hB => ?_
  by_cases hw' : w' = w
  · subst hw'
    obtain ⟨B₀, hB₀, Q, hQ, hyQ⟩ := hy c
    have hB' : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B := by
      rw [bwG_Ld_coe, ← hw]
      exact hB
    obtain ⟨Q₂, hQ₂, he⟩ := hI w' hw i hi h0 c B₀ B hB₀ hB' Q hQ
    refine ⟨_, bwG_intSpan_smul D w' _ _ (bwG_int_mem D w' t) hQ₂, fun z => ?_⟩
    rw [← algebraMap_smul D.what₂.LL t y, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hyQ z, he z,
      LinearMap.map_smul]
    rfl
  · have hne : D.plEq w' ≠ D.plEq w := fun h => hw' (D.plEq.injective h)
    obtain ⟨r, hr, k, hk⟩ := htw _ hne
    obtain ⟨P, hP, hdP⟩ := ((Tt.val i hi h0).lat _).1 hdy w' c B hB
    have hr0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL r ≠ 0 := by
      intro h
      apply hr
      have : r = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [h, map_zero])
      rw [this]
      exact zero_mem _
    have e : t • y = ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ * algebraMap (𝓞 D.what₂.LL) D.what₂.LL k) • (d • y) := by
      rw [← algebraMap_smul D.what₂.LL t y, ← algebraMap_smul D.what₂.LL d y, smul_smul]
      congr 1
      have hk' := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) hk
      rw [map_mul, map_mul] at hk'
      field_simp
      rw [mul_comm, hk', mul_comm]
    refine ⟨_, bwG_intSpan_smul D w' _ _ (mul_mem (bwG_inv_mem D w' hr) (bwG_int_mem D w' k)) hP, fun z => ?_⟩
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hdP z, LinearMap.map_smul]
    rfl

theorem bwBasisInd_of_stab0 (Tt : Forms0 D u) (hS : ∀ w, OverT D u w → BwGLStab D w) : BwBasisInd0 D u Tt := by
  intro w hw i hi h0 c B B₂ hB hB₂ Q hQ
  set N : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B⁻¹ * B₂ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN
  set N' : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B₂⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin (D.R.N i)) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u i) τ) * subP N Q,
    bwG_intSpan_allSubP D w _ N _ (fun τ g hg => hS w hw _ _ _ (N τ) (N' τ) (hNN' τ)
      (bwG_change_mem D u w hw τ hB₂ hB) (bwG_change_mem D u w hw τ hB hB₂) g hg) Q hQ, fun z => ?_⟩
  rw [← fnOf_mul]
  have hM : atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) =
      fun τ => N τ * atInf (embT D) ((B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ := by
    funext τ
    simp only [hN, atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

theorem local_global_lattice_level_zero (Tt : Forms0 D u) : BwLocGlob0 D u Tt :=
  local_global_of_basis_independence D u Tt (bwBasisInd_of_stab0 D u Tt fun w _ => local_GL_stabilises_lattice D w)

end Formalism.L2.GlobalTheoryTheory.LemB.G0
