import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

namespace GlobalTheory.VB

theorem isFrame_of_epi_mono_principal {Y : Scheme.{0}} [IsIntegral Y] {E M L : Y.Modules}
    [E.IsQuasicoherent] [M.IsQuasicoherent] (π : E ⟶ M) (m : M ⟶ L) [Epi π] [Mono m]
    {V : Y.Opens} {l : Fin 1 → Γ(L, V)} {g : Γ(Y, V)} {t : Γ(E, V)} (hl : IsFrame l) (hg : g ≠ 0)
    (ht : (π ≫ m).app V t = g • l 0)
    (hs : ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
      (π ≫ m).app W s = a • resM L h (g • l 0)) :
    IsFrame (fun _ : Fin 1 => π.app V t) := by
  have hc (W : Y.Opens) (s : Γ(E, W)) : (π ≫ m).app W s = m.app W (π.app W s) := rfl
  refine isFrame_of_forall_exists fun V' h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  have hWV : W ≤ V := hle.trans h
  have : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hm (a : Fin 1 → Γ(Y, W)) :
      m.app W (Fintype.linearCombination Γ(Y, W) (fun _ : Fin 1 => resM M hWV (π.app V t)) a) =
        a 0 • resM L hWV (g • l 0) := by
    rw [Fintype.linearCombination_apply, Fin.sum_univ_one, Scheme.Modules.Hom.app_smul, app_resM,
      ← hc, ht]
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have h1 := hm a
    rw [ha, map_zero, resM_smul, smul_smul] at h1
    have h2 := (hl W hWV).1 (a₁ := fun _ => a 0 * resG Y hWV g) (a₂ := 0) (by
      rw [map_zero, Fintype.linearCombination_apply, Fin.sum_univ_one]
      exact h1.symm)
    have h3 : a 0 * resG Y hWV g = 0 := congrFun h2 0
    have h4 : resG Y hWV g ≠ 0 := fun h0 =>
      hg (map_injective_of_isIntegral Y (homOfLE hWV) (h0.trans (map_zero _).symm))
    funext i
    rw [Subsingleton.elim i 0]
    exact (mul_eq_zero.1 h3).resolve_right h4
  · intro s
    obtain ⟨u, rfl⟩ := QCoh.surjective_app_of_epi π hW s
    obtain ⟨a, ha⟩ := hs W hWV u
    refine ⟨fun _ => a, QCoh.injective_app_of_mono m W ?_⟩
    rw [hm, ← hc, ha]

theorem isSubbundle_kernel_of_locally_principal :
    ∀ (Y : Scheme.{0}) [IsIntegral Y] (E L : Y.Modules) (ψ : E ⟶ L) (n : ℕ), IsVB E (n + 1) →
      IsVB L 1 → (∀ y : Y, ∃ (V : Y.Opens) (l : Fin 1 → Γ(L, V)) (g : Γ(Y, V)) (t : Γ(E, V)),
        y ∈ V ∧ IsFrame l ∧ g ≠ 0 ∧ (ψ).app V t = g • l 0 ∧
        ∀ (W : Y.Opens) (h : W ≤ V) (s : Γ(E, W)), ∃ a : Γ(Y, W),
          (ψ).app W s = a • GlobalTheory.Twist.resM (L) h (g • l 0)) →
      IsSubbundle (Limits.kernel.ι ψ) ∧ IsVB (Limits.kernel ψ) n := by
  intro Y _ E L ψ n hE hL H
  have := hE.isQuasicoherent
  have := hL.isQuasicoherent
  have hM : IsVB (cokernel (kernel.ι ψ)) 1 := by
    intro y
    obtain ⟨V, l, g, t, hy, hl, hg, ht, hs⟩ := H y
    have e : cokernel.π (kernel.ι ψ) ≫ Abelian.factorThruCoimage ψ = ψ := Abelian.coimage.fac ψ
    exact ⟨V, _, hy, isFrame_of_epi_mono_principal (cokernel.π (kernel.ι ψ))
      (Abelian.factorThruCoimage ψ) hl hg (by rw [e]; exact ht) (by rw [e]; exact hs)⟩
  refine ⟨⟨inferInstance, 1, hM⟩, ?_⟩
  have hS : (ShortComplex.mk _ _ (cokernel.condition (kernel.ι ψ))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  exact isVB_X₁_of_shortExact Y _ n 1 hS hE hM

end GlobalTheory.VB
