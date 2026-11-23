import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.UnframeForms

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev movedS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ => (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ) }

def movedIso (i : Fin D.R.m) : NX.FormsIso ((movedS YS w).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk := (YS.fi i).wk
  mkK := (YS.fi i).mkK
  rho := (YS.fi i).rho
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((YS.fi i).e x)) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply]

def movedYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG (movedS YS w) where
  fi := movedIso YS w
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem evW_moved (j : Fin D.R.m) (x : S.WL ((j : ℕ) + 1)) :
    evW (movedYS YS w) v₀ j x = evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x) := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((Rl.FW j).ρ (w j (sg0 D A3.A)) ((YS.fi j).e x))) (v₀ j _) =
    (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A _).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) x)))
      (v₀ j _)
  rw [(YS.fi j).rho, MulEquiv.apply_symm_apply]

theorem evK_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) :
    ∃ y, evK (movedYS YS w) v₀ hρ i j b x = evK YS v₀ hρ i j b y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    refine ⟨a ⊗ₜ (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A))) (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
      YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), ?_⟩
    exact congrArg (ρ.e i b a • ·) (evW_moved YS w v₀ j _)

theorem realRd_moved {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ)
    (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    ∃ f', realRd (movedYS YS w) v₀ hρ i j b ν f = realRd YS v₀ hρ i j b ν f' := by
  obtain ⟨y, hy⟩ := evK_moved YS w v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  refine ⟨(YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y, ?_⟩
  change ν⁻¹ • evK (movedYS YS w) v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) =
    ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm y))
  rw [hy]
  exact congrArg (fun z => ν⁻¹ • evK YS v₀ hρ i j b z)
    ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply (show NX.Fm S i ((j : ℕ) + 1) b from y)).symm

end GlobalTheory.UnframeForms

namespace GlobalTheory.UnframeForms

open GlobalTheory.ExportSeries

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X} (hρ : ρ.Good)
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} {rd rd' : Rd ρ Y i j b}

theorem rdK_sub (h : ∀ f, ∃ f', rd' f = rd f') (k : ℕ) (x : X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b) :
    ∃ x', rdK rd' hρ k x = rdK rd hρ k x' := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨x', ex⟩ := hx
    obtain ⟨y', ey⟩ := hy
    exact ⟨x' + y', (map_add _ _ _).trans ((congrArg₂ (· + ·) ex ey).trans (map_add _ _ _).symm)⟩
  | tmul a f =>
    obtain ⟨f', e⟩ := h f
    exact ⟨a ⊗ₜ f', by rw [rdK_tmul, rdK_tmul, e]⟩

theorem rat_of_sub (h : ∀ f, ∃ f', rd' f = rd f') (h' : Rat hρ rd') : Rat hρ rd := by
  obtain ⟨h1, h2, h3⟩ := h'
  refine ⟨fun s g P hd => ?_, fun k Q ψ hk hQ s g P hd x hx => ?_, fun Q M hQ s g P hd hs a => ?_⟩
  · obtain ⟨f, hf⟩ := h1 s g P hd
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩
  · obtain ⟨y, hy⟩ := h2 k Q ψ hk hQ s g P hd hx
    obtain ⟨y', e⟩ := rdK_sub hρ h k y
    exact ⟨y', e.symm.trans hy⟩
  · obtain ⟨f, hf⟩ := h3 Q M hQ s g P hd hs a
    obtain ⟨f', e⟩ := h f
    exact ⟨f', e.symm.trans hf⟩

end GlobalTheory.UnframeForms

theorem GlobalTheory.UnframeForms.ratRow_back : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ), (∀ i σ, w i σ ∈ Subgroup.center Γ) → ∃ (S' : NX.RatDat D.ntw) (YS' : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w) cG S'), ∀ (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), RatRow YS' v₀ hρ i j b → RatRow YS v₀ hρ i j b :=
  fun Rl _ _ YS w _ => ⟨GlobalTheory.UnframeForms.movedS YS w, GlobalTheory.UnframeForms.movedYS YS w, fun v₀ _ hρ i j b ⟨ν, hn, hr⟩ =>
    ⟨ν, hn, GlobalTheory.UnframeForms.rat_of_sub hρ (GlobalTheory.UnframeForms.realRd_moved YS w v₀ hρ i j b ν) hr⟩⟩
