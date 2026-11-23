import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}

set_option maxHeartbeats 4000000 in

theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
