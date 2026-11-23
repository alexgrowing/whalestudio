import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrthProjectionOfMemCompl

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem h_UW {x y : V} (hx : x ∈ U) (hy : y ∈ orthK h U) : h x y = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact hy x hx

theorem h_WU (hs : h.IsSymm) {x y : V} (hx : x ∈ orthK h U) (hy : y ∈ U) : h x y = 0 := by
  rw [← LinearMap.isSymm_def.1 hs y x, h_UW hy hx, map_zero]

theorem prO_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc' x = x := by
  have e := prO_add hc' x
  rw [prO_symm_of_mem_U (hc' := hc') hx, add_zero] at e
  exact e

theorem split (hs : h.IsSymm) (hc' : IsCompl U (orthK h U)) (x y : V) :
    h x y = h (prO hc' x) (prO hc' y) + h (prO hc'.symm x) (prO hc'.symm y) := by
  conv_lhs => rw [← prO_add hc' x, ← prO_add hc' y]
  simp only [map_add, LinearMap.add_apply]
  rw [h_UW (prO_mem hc' x) (prO_symm_mem hc' y), h_WU hs (prO_symm_mem hc' x) (prO_mem hc' y)]
  ring

theorem form_mem_of_dual (hd : dualF h 𝔭 Λ = Λ) {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hb' : b ∈ dualF h 𝔭 Λ := by rw [hd]; exact hb
  exact hb' a ha

theorem mem_T_of (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ) {b : V} (hb : b ∈ orthK h U)
    (H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    b ∈ locF 𝔭 T := by
  have hbΛ : b ∈ Λ := by
    rw [← hd]
    intro y hy
    rw [← prO_add hc y, map_add, LinearMap.add_apply, h_UW (prO_mem hc y) hb, zero_add]
    exact H _ (hG.iW y hy)
  rw [← hG.cW]
  exact Submodule.mem_inf.2 ⟨hbΛ, hb⟩

def FP (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) : Prop :=
  ∀ x y x' y' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
    Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
    Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
    h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

theorem FP.injective (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) : Function.Injective P := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨z, -, hz⟩ := hG.oW (x : V) x.2
  have hxW : (x : V) ∈ orthK h U := hz ▸ prO_symm_mem hc z
  have H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro b' hb'
    obtain ⟨b'', hb''⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk ⟨b', hb'⟩))
    have e := hP ⟨b', hb'⟩ x b'' 0 hb'' (by rw [hq, Submodule.Quotient.mk_zero])
    simpa using e
  have hxT := mem_T_of hG hd hxW H
  rw [← Submodule.Quotient.mk_zero, mk_eq_iff]
  simpa using hxT

theorem fp_of (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hd : dualF h 𝔭 Λ = Λ)
    (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭))
    (H : ∀ b x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk b) →
      ∃ z ∈ Λ₀, ∃ w ∈ Λ, prO hc.symm z = b ∧ prO hc.symm w = x' ∧ prO hc z = prO hc w) : FP P := by
  intro x y x' y' hx hy
  obtain ⟨z₁, hz₁, w₁, hw₁, hq₁, hq₁', hp₁⟩ := H x x' hx
  obtain ⟨z₂, hz₂, w₂, hw₂, hq₂, hq₂', hp₂⟩ := H y y' hy
  have e₁ := split hs hc w₁ w₂
  have e₂ := split hs hc z₁ z₂
  rw [hq₁', hq₂', ← hp₁, ← hp₂] at e₁
  rw [hq₁, hq₂] at e₂
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) = h w₁ w₂ - h z₁ z₂ := by
    rw [e₁, e₂]
    ring
  rw [e]
  exact sub_mem (form_mem_of_dual hd hw₁ hw₂) (form_mem_of_dual hd₀ hz₁ hz₂)

def glue (hc' : IsCompl U (orthK h U)) (T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (Λ₀ : Submodule (𝓞 K) V) (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) :
    Submodule (𝓞 K) V where
  carrier := {x | ∃ b : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (b : V) = prO hc'.symm x ∧
    ∃ y ∈ Λ₀, ∃ c : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (c : V) = prO hc'.symm y ∧
      prO hc' y = prO hc' x ∧ Submodule.Quotient.mk b = P (Submodule.Quotient.mk c)}
  zero_mem' := ⟨0, by simp, 0, Λ₀.zero_mem, 0, by simp, by simp, by simp⟩
  add_mem' := by
    rintro x x' ⟨b, hb, y, hy, c, hcy, hU, hP⟩ ⟨b', hb', y', hy', c', hcy', hU', hP'⟩
    refine ⟨b + b', by simp [hb, hb'], y + y', Λ₀.add_mem hy hy', c + c', by simp [hcy, hcy'],
      by simp [hU, hU'], ?_⟩
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add, hP, hP']
  smul_mem' := by
    rintro r x ⟨b, hb, y, hy, c, hcy, hU, hP⟩
    refine ⟨r • b, by simp [hb], r • y, Λ₀.smul_mem r hy, r • c, by simp [hcy], by simp [hU], ?_⟩
    rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, hP]

end Formalism.L2.SG.Pf.OrthogonalProjections
