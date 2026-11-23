import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem card_eq [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hgood : ∀ Λ, InFib h U 𝔭 M T Λ → Good hc M T 𝔭 Λ)
    (h0 : InFib h U 𝔭 M T Λ₀) :
    Nat.card {Λ // InFib h U 𝔭 M T Λ} =
      Nat.card {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) // FP P} := by
  classical
  have G0 : Good hc M T 𝔭 Λ₀ := hgood Λ₀ h0
  have hd₀ : dualF h 𝔭 Λ₀ = Λ₀ := h0.2.1

  have hTW : ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ orthK h U := by
    intro d hd
    have : d ∈ Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [G0.cW]; exact hd
    exact this.2
  have hTL : ∀ {Λ : Submodule (𝓞 K) V}, Good hc M T 𝔭 Λ → ∀ {d : V}, d ∈ locF 𝔭 T → d ∈ Λ := by
    intro Λ hG d hd
    have : d ∈ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by rw [hG.cW]; exact hd
    exact this.1
  have hsW : ∀ {d : V}, d ∈ orthK h U → prO hc.symm d = d := fun hd =>
    (mem_W_of_prO_zero (hc := hc) (orth_projection_of_mem_compl hd)).2

  have hFP : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), FP (isoOf G0 (hgood Λ hΛ)) := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    refine fp_of (hc := hc) hs hd₀ hΛ.2.1 _ ?_
    intro b x' hx'
    obtain ⟨z, hz, hzb⟩ := G0.oW b b.2
    obtain ⟨w, hw, hwz⟩ := hG.oU (prO hc z) (G0.iU z hz)
    have hb : b = ⟨prO hc.symm z, G0.iW z hz⟩ := Subtype.ext hzb.symm
    rw [hb, isoOf_mk G0 hG hz hw hwz, Submodule.Quotient.eq, Submodule.mem_comap] at hx'
    have hd : (x' : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hx'
    have hdW := hTW hd
    refine ⟨z, hz, w + ((x' : V) - prO hc.symm w), Λ.add_mem hw (hTL hG hd), hzb, ?_, ?_⟩
    · rw [map_add, hsW hdW]; abel
    · rw [map_add, orth_projection_of_mem_compl hdW, add_zero, hwz]
  have hglue : ∀ P, FP P → InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
    intro P hP
    obtain ⟨N₀, hN₀, hloc⟩ := h0.1
    haveI : Finite (DiscMod h (orthK h U) T 𝔭) :=
      Formalism.L2.SG.Pf.ProjectionDiscriminantModule.discMod_finite hc h𝔭 hM hT hN₀ hloc G0.cW G0.iW G0.oW
    exact glue_mem hs h𝔭 hM hT G0 h0 hP (Finite.surjective_of_injective (FP.injective G0 hd₀ hP))
  have hleft : ∀ Λ (hΛ : InFib h U 𝔭 M T Λ), glue hc T 𝔭 Λ₀ (isoOf G0 (hgood Λ hΛ)) = Λ := by
    intro Λ hΛ
    have hG := hgood Λ hΛ
    ext x
    constructor
    · rintro ⟨b, hb, y, hy, c, hcy, hU, hP⟩
      obtain ⟨w, hw, hwy⟩ := hG.oU (prO hc y) (G0.iU y hy)
      have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hcy
      rw [hc', isoOf_mk G0 hG hy hw hwy, Submodule.Quotient.eq, Submodule.mem_comap] at hP
      have hd : (b : V) - prO hc.symm w ∈ locF 𝔭 T := by simpa using hP
      rw [hb] at hd
      exact mem_of_proj hG hw (hwy.trans hU) hd
    · intro hx
      obtain ⟨y, hy, hyx⟩ := G0.oU (prO hc x) (hG.iU x hx)
      exact ⟨⟨prO hc.symm x, hG.iW x hx⟩, rfl, y, hy, ⟨prO hc.symm y, G0.iW y hy⟩, rfl, hyx,
        (isoOf_mk G0 hG hy hx hyx.symm).symm⟩
  have hright : ∀ P (hP : FP P), isoOf G0 (hgood _ (hglue P hP)) = P := by
    intro P hP
    have hG := hgood _ (hglue P hP)
    refine LinearMap.ext fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
    obtain ⟨y, hy, hyc⟩ := G0.oW c c.2
    have hc' : c = ⟨prO hc.symm y, G0.iW y hy⟩ := Subtype.ext hyc.symm
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk c))
    rw [hc'] at hx' ⊢
    have hmem := mem_glue_of (P := P) G0 hy x' hx'
    have hx'W : (x' : V) ∈ orthK h U := memW G0 x'.2
    have hUeq : prO hc (prO hc y + x') = prO hc y := by
      rw [map_add, prO_of_mem_U (prO_mem hc y), orth_projection_of_mem_compl hx'W, add_zero]
    rw [isoOf_mk G0 hG hy hmem hUeq, ← hx']
    congr 1
    apply Subtype.ext
    have e := prO_add hc (prO hc y)
    rw [prO_of_mem_U (prO_mem hc y)] at e
    have e0 : prO hc.symm (prO hc y) = 0 := by
      have := congrArg (fun v => v - prO hc y) e
      simpa using this
    simp only [map_add, e0, zero_add, hsW hx'W]
  exact Nat.card_congr
    { toFun := fun Λ => ⟨isoOf G0 (hgood Λ.1 Λ.2), hFP Λ.1 Λ.2⟩
      invFun := fun P => ⟨glue hc T 𝔭 Λ₀ P.1, hglue P.1 P.2⟩
      left_inv := fun Λ => Subtype.ext (hleft Λ.1 Λ.2)
      right_inv := fun P => Subtype.ext (hright P.1 P.2) }

end Formalism.L2.SG.Pf.OrthogonalProjections
