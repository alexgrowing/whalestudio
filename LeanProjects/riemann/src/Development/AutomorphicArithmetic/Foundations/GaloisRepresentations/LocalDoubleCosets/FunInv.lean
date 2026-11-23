import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow

noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

section Stable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem mem_Cc {f : G → ℂ} : f ∈ Cc G ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  GroundTheory.Automorphic.mem_locallyConstantCompactSupport

private theorem Cc_comp_homeo {f : G → ℂ} (hf : f ∈ Cc G) (e : G ≃ₜ G) : f ∘ e ∈ Cc G := by
  rw [mem_Cc] at hf ⊢
  exact ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

private def homeoOf (s : G →* G) (p : ℕ) (hp : 0 < p) (hs : Continuous s) (hsp : ∀ g, s^[p] g = g) : G ≃ₜ G where
  toFun := s
  invFun := s^[p - 1]
  left_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply] at this
  right_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply'] at this
  continuous_toFun := hs
  continuous_invFun := hs.iterate _

end Stable

theorem funInv (hBi : BiInv) (hMem : PrMem) (hLeft : PrLeft) (hAuto : PrAuto) (hSurj : PrSurj) (hEta : EtaEx) :
    FunInv := by
  intro G _ _ _ _ _ _ _ B N hB hN K hKo hKc hBK s p hp hs hsp hsB hsN hC χ θ hχ hθ hχs hθs l hl φ hφ
  letI : MeasurableSpace B := borel B
  haveI : BorelSpace B := ⟨rfl⟩
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  set μ : Measure B := Measure.haar with hμ
  obtain ⟨hmem, hadd⟩ := hMem G B hB μ χ hχ
  obtain ⟨f, hf, rfl⟩ := hSurj G B hB μ χ K hKo hKc hBK φ hφ
  by_cases hne : ∃ f ∈ Cc G, ∃ g, pr B μ χ f g ≠ 0
  swap
  · push_neg at hne
    have h0 : pr B μ χ f = 0 := funext (hne f hf)
    rw [h0]
    rfl
  obtain ⟨κ, hκ, hκs⟩ := hAuto G B hB μ χ s p hp hs hsp hsB hχs
  obtain ⟨hκ1, η, hη, hηL, hηs⟩ :=
    hEta G B s p hp hsp (pr B μ χ) κ hκ hκs (fun b => hLeft G B hB μ χ b) hne
  let prL : Cc G →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => pr B μ χ f
      map_add' := fun f f' => hadd f f.2 f' f'.2
      map_smul' := fun c f => by
        funext g
        simp only [pr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext b
        ring }
  obtain ⟨q, hq⟩ := (Cc G).exists_isCompl
  let D : (G → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ prL ∘ₗ (Cc G).projectionOnto q hq
  have hDf : ∀ f' (hf' : f' ∈ Cc G), D f' = l (pr B μ χ f') := by
    intro f' hf'
    show l (prL ((Cc G).projectionOnto q hq f')) = _
    rw [show (Cc G).projectionOnto q hq f' = ⟨f', hf'⟩ from
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f', hf'⟩]
    rfl
  have hCs : f ∘ s ∈ Cc G := Cc_comp_homeo hf (homeoOf s p hp hs hsp)
  have hDleft : ∀ (b : B), ∀ f' ∈ Cc G, (D fun x => f' ((b : G)⁻¹ * x)) = η b * D f' := by
    intro b f' hf'
    have hmL : (fun x => f' ((b : G)⁻¹ * x)) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulLeft ((b : G)⁻¹))
    have he : pr B μ χ (fun x => f' ((b : G)⁻¹ * x)) = η b • pr B μ χ f' :=
      funext fun g => hη b f' g
    rw [hDf _ hmL, hDf f' hf', he, map_smul, smul_eq_mul]
  have hDright : ∀ (u : N), ∀ f' ∈ Cc G, (D fun x => f' (x * (u : G))) = (θ u : ℂ) * D f' := by
    intro u f' hf'
    have hmR : (fun x => f' (x * (u : G))) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulRight (u : G))
    have he : pr B μ χ (fun x => f' (x * (u : G))) = fun x => pr B μ χ f' (x * (u : G)) := by
      funext g
      simp only [pr, mul_assoc]
    rw [hDf _ hmR, hDf f' hf', he]
    exact hl u _ (hmem f' hf')
  have hps : pr B μ χ (f ∘ s) = pr B μ χ f ∘ s := by
    funext g
    rw [hκs, hκ1]
    simp
  rw [← hps, ← hDf _ hCs, ← hDf f hf]
  exact hBi G B N hB hN s p hp hs hsp hsB hsN hC η θ hηL hθ hηs hθs D hDleft hDright f hf

end UpperTheory.Gal.LocD

end
