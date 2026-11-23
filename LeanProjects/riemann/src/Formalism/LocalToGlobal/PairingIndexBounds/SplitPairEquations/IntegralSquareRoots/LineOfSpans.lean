import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.FinrankRow

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.J

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def GaussRow (B : Ker.Base D cc δ) : Prop :=
  ∀ (N : ℕ) (γ : Matrix.unitaryGroup (Fin N) D.host.E) (Ae : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1), Even N →
    (∀ x, Ae x = x - (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1).symm x) →
    ∀ S : Finset (TaylorLogMetric.VC D N 1), IsReps (latA (La0 B N 1) (phiU γ 1) Ae) (La0 B N 1) S →
      gaussC (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) Ae S ^ 2 = 1

def Lat0IsLat (B : Ker.Base D cc δ) (N N' : ℕ) : Prop := IsLat (La0 B N N')

theorem exists_cay {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (φ : V ≃ₗ[ℂ] V)
    (h : ∀ x, φ.symm x = x → x = 0) : ∃ Ae : V ≃ₗ[ℂ] V, ∀ x, Ae x = x - φ.symm x := by
  have hinj : Function.Injective ((LinearMap.id - (φ.symm : V →ₗ[ℂ] V)) : V →ₗ[ℂ] V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have : x - φ.symm x = 0 := hx
    exact h x (sub_eq_zero.mp this).symm
  exact ⟨LinearEquiv.ofInjectiveEndo _ hinj, fun x => rfl⟩

variable {B : Ker.Base D cc δ}

theorem line_of_spans {N N' : ℕ} (hSp : B.ThZeroSpans N N') :
    AtMostLine (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (La0 B N N') := by
  intro θ hθ hθ0 F hF
  obtain ⟨a, ha⟩ := hSp θ hθ
  obtain ⟨b, hb⟩ := hSp F hF
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [ha, zero_smul])
  exact ⟨b * a⁻¹, by rw [ha, hb, smul_smul, inv_mul_cancel_right₀ ha0]⟩

theorem unitaryData (hL : B.LatAll) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (Ae : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') (hA : ∀ x, Ae x = x - (phiU γ γ').symm x) :
    UnitaryData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N') (La0 B N N') (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (phiU γ γ') Ae := by
  have a0 : TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')
  have a1 : TaylorLogMetric.admitted D N N' (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) :=
    admissible_of_integral_conj_le hN hN' (smulSD D N _ γ (sd0 N)) (smulSD D N' _ γ' (sd0 N'))
  have hi : imgLat ((phiU γ γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  exact
    { herm := formV_herm' _ _ _ _
      pos := formV_pos (area_pos' B) _ _ _
      selfDual := (hL.1 N N' _ _ a0).1
      semi := (hL.1 N N' _ _ a0).2
      isom := phiL_isom _ _ _ _ _ _ _
      semi' := by rw [hi]; exact (hL.1 N N' _ _ a1).2
      inv := fun x _ => al_phi _ _ _ _ _ _ x
      idx₁ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a1 a0).1
      idx₂ := by rw [hi]; exact (hL.2 N N' _ _ _ _ a0 a1).1
      cay := hA }

theorem J1at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (hγ : (1 - (γ : Matrix (Fin N) (Fin N) D.host.E)).det ≠ 0) : J1at B N N' γ := by
  obtain ⟨Ae, hA⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') (nofix γ hγ)
  obtain ⟨Ae₁, hA₁⟩ := exists_cay (phiU γ 1 : TaylorLogMetric.VC D N 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N 1) (nofix γ hγ)
  have c : Copies (rowE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N N') (La0 B N 1) (phiU γ 1) Ae (phiU γ 1) Ae₁ :=
    { form := form_row _ N N'
      char := al_row B hS N N'
      lat := lat_row B N N'
      map := map_row γ
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (rowE D N N') _ _ (map_row γ)] }
  have h := const_copies hLat (unitaryData hL hN hN' γ 1 Ae hA) (line_of_spans hSp) c (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ (by rw [Fintype.card_fin]; exact hN')
    (by rw [finrank_row]; exact hN.mul_left _) (fun S₁ hS₁ => hG N γ Ae₁ hN hA₁ S₁ hS₁) (B.thZero N N')
    (B.thZeroMem hS N N')
  rw [det_row, Fintype.card_fin] at h
  have hi : imgLat ((phiU γ 1 : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (1 : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  rw [hi, Formalism.BasicNotions.Examples₂.smulLat_one] at h
  exact h

theorem J2at_of_ne (hS : B.StdOK) (hL : B.LatAll) (hG : GaussRow B) {N N' : ℕ} (hN : Even N) (hN' : Even N')
    (hLat : Lat0IsLat B N N') (hSp : B.ThZeroSpans N N') (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (hγ : (1 - (γ' : Matrix (Fin N') (Fin N') D.host.E)).det ≠ 0) : J2at B N N' γ' := by
  have hfix₁ := nofix (N' := 1) (cjU γ') (ne_cjU γ' hγ)
  have hfix : ∀ x : TaylorLogMetric.VC D N N', (phiU 1 γ').symm x = x → x = 0 := by
    intro x hx
    apply (colE D N N').injective
    funext j
    rw [map_zero]
    refine hfix₁ _ ?_
    rw [← symm_coord (colE D N N') _ _ (map_col γ'), hx]
  obtain ⟨Ae, hA⟩ := exists_cay (phiU 1 γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') hfix
  obtain ⟨Ae₁, hA₁⟩ := exists_cay (phiU (cjU γ') 1 : TaylorLogMetric.VC D N' 1 ≃ₗ[ℂ] TaylorLogMetric.VC D N' 1) hfix₁
  have c : Copies (colE D N N') (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N N')
      (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.tor0 D cc δ).abelian₂) D.what₂.Tau N' 1) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ)) (TaylorLogMetric.al D (TaylorLogMetric.tor0 D cc δ))
      (La0 B N N') (La0 B N' 1) (phiU 1 γ') Ae (phiU (cjU γ') 1) Ae₁ :=
    { form := form_col _ N N'
      char := al_col B hS N N'
      lat := lat_col B N N'
      map := map_col γ'
      cay := fun x i => by
        rw [hA, hA₁, map_sub, Pi.sub_apply, symm_coord (colE D N N') _ _ (map_col γ')] }
  have h := const_copies hLat (unitaryData hL hN hN' 1 γ' Ae hA) (line_of_spans hSp) c (formV_herm' _ _ _ _)
    (formV_pos (area_pos' B) _ _ _) (phiL_isom _ _ _ _ _ _ _) hA₁ (by rw [Fintype.card_fin]; exact hN)
    (by rw [finrank_row]; exact hN'.mul_left _) (fun S₁ hS₁ => hG N' (cjU γ') Ae₁ hN' hA₁ S₁ hS₁) (B.thZero N N')
    (B.thZeroMem hS N N')
  rw [det_row, Fintype.card_fin, det_cjU, star_star] at h
  have hi : imgLat ((phiU 1 γ' : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N') : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N') (La0 B N N') =
      TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (1 : Matrix (Fin N) (Fin N) D.host.E) (StandardLatticesGL3.stdL D N))
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) (StandardLatticesGL3.stdL D N')) := la_img _ _ _ _ _ _ _ _
  rw [hi, Formalism.BasicNotions.Examples₂.smulLat_one] at h
  exact h

end Formalism.L2.PairingIndexBounds.Eq.J
