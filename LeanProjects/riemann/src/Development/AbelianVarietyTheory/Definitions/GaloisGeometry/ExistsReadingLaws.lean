import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Irr (n : ℕ) : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  π : Representation ℂ (GL (Fin n) k) V
  smooth : IsSmooth π
  irr : π.IsIrreducible

attribute [instance] Irr.acg Irr.mod

variable {k} in

def Irr.ofDet (n : ℕ) (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _

variable {k} in

@[simp] theorem Irr.ofDet_π (n : ℕ) (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) :
    (Irr.ofDet n χ h).π = detRep (Fin n) χ := rfl

instance (n : ℕ) : Inhabited (Irr k n) := ⟨Irr.ofDet n 1 (isSmoothChar_of_isUnram fun _ _ => rfl)⟩

variable {k} in

@[reducible] def Irr.toIrrRep {n : ℕ} (π : Irr k n) : IrrRep (GL (Fin n) k) := ⟨π.V, π.π, π.smooth, π.irr⟩

variable {k} in

@[reducible] def Irr.ofIrrRep {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : Irr k n := ⟨σ.V, σ.ρ, σ.smooth, σ.irr⟩

variable {k} in

@[simp] theorem Irr.toIrrRep_ρ {n : ℕ} (π : Irr k n) : π.toIrrRep.ρ = π.π := rfl

variable {k} in

@[simp] theorem Irr.ofIrrRep_π {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : (Irr.ofIrrRep σ).π = σ.ρ := rfl

def Irr.equivIrrRep (n : ℕ) : Irr k n ≃ IrrRep (GL (Fin n) k) where
  toFun := Irr.toIrrRep
  invFun := Irr.ofIrrRep
  left_inv _ := rfl
  right_inv _ := rfl

variable {k} in

theorem Irr.toIrrRep_equiv_iff {n : ℕ} (π π' : Irr k n) :
    π.toIrrRep ≈ π'.toIrrRep ↔ Nonempty (π.π.Equiv π'.π) := Iff.rfl

example (n : ℕ) (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) :
    (Irr.ofDet n χ h).toIrrRep = IrrRep.ofChar (detChar (Fin n) χ) h.detChar := rfl

def TameSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  ¬ IsUnram χ → v ≠ 0 → IsParahoricVec χ π.π v →
  ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₁.π ∧ IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))

variable {k} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def speh (a : WD h) (d : ℕ) : WD h :=
  (List.range d).foldr (fun j acc => (a.lpTw (((d : ℝ) - 1) / 2 - j)).lpSum acc) (WD.lpZero h)

example (a : WD h) : speh a 0 = WD.lpZero h := rfl

example (a : WD h) : speh a 2 = (a.lpTw (1 / 2)).lpSum ((a.lpTw (-1 / 2)).lpSum (WD.lpZero h)) := by
  simp only [speh, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.foldr]
  norm_num

structure RecLaws (rc : ∀ n, Irr k n → WD h) : Prop where
  dim : ∀ n π, (rc n π).lpDim = n
  iso : ∀ n (π π' : Irr k n), rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π)
  prod : ∀ r t (σ : Irr k r) (τ : Irr k t) (π : Irr k (r + t)), Nonempty (π.π.Equiv (prod₂ σ.π τ.π)) →
    rc (r + t) π = (rc r σ).lpSum (rc t τ)
  det : ∀ t (χ : kˣ →* ℂˣ) (c : Irr k 1) (τ : Irr k t), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (τ.π.Equiv (detRep (Fin t) χ)) → rc t τ = speh (rc 1 c) t
  twist : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c)
  sph : ∀ n (π : Irr k n), (rc n π).unr ↔ IsSpherical π.π
  sat : ∀ n (π : Irr k n) (α : Fin n → ℂˣ), HasSatake π.π α →
    (rc n π).frobEig = Finset.univ.val.map fun i => ((α i)⁻¹ : ℂˣ).1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

structure ReadAt (T : WDTie N A) (i : N.Loc) (w : PlE H) : Type 1 where

  rc : ∀ n, Irr (w.adicCompletion H.E) n → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

  row : what₂.FT → Irr (w.adicCompletion H.E) R.r

  rep : A.AV i → Irr (w.adicCompletion H.E) (R.r + R.t)

  mu : (w.adicCompletion H.E)ˣ →* ℂˣ
  eta : (w.adicCompletion H.E)ˣ →* ℂˣ
  mu_ok : IsSmoothChar mu ∧ IsUnitaryChar mu
  eta_ok : IsSmoothChar eta ∧ IsUnram eta
  locW : ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ → T.e w (A.locW i σ w) = rc _ (row σ)
  locV : ∀ P, T.e w (A.locV i P w) = rc _ (rep P)
  locMu : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) mu)) →
    T.e w (A.locG (A.muC i) w) = rc 1 c
  locEta : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) eta⁻¹)) →
    T.e w (A.locG A.etaTinv w) = rc 1 c

theorem exists_readAt (T : WDTie N A) (i : N.Loc) (w : PlE H)
    (rc : ∀ n, Irr (w.adicCompletion H.E) n → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w))
    (hrc : RecLaws rc) (hs : ∀ n a, WD.lpDim a = n → ∃ π, rc n π = a)
    (hW : ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ → A.lpDim (A.locW i σ w) = R.r)
    (hV : ∀ P, A.lpDim (A.locV i P w) = R.r + R.t)
    (hmu : ∃ (χ : _) (h : IsSmoothChar χ), IsUnitaryChar χ ∧
      rc 1 (Irr.ofDet 1 χ h) = T.e w (A.locG (A.muC i) w))
    (heta : ∃ (χ : _) (h : IsSmoothChar χ), rc 1 (Irr.ofDet 1 χ h) = T.e w (A.locG A.etaTinv w)) :
    ∃ S : ReadAt T i w, S.rc = rc := by
  classical
  obtain ⟨μ, hμ, hu, eμ⟩ := hmu
  obtain ⟨η, hη, eη⟩ := heta
  have hun : IsUnram η := by
    have := (hrc.sph 1 (Irr.ofDet 1 η hη)).1 (by rw [eη]; exact (T.unr w _).1 (A.etaTinv_def w).1)
    intro x hx
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
    have hI : (fun _ : Fin 1 => x) ∈ torusO (w.adicCompletion H.E) (Fin 1) := fun _ => hx
    have h2 := hv ⟨_, iwahori_le_KO _ _ (diagT_mem_iwahori hI)⟩
    have h3 : Matrix.GeneralLinearGroup.det (diagT (w.adicCompletion H.E) (Fin 1) fun _ => x) = x := by
      ext; simp [val_diagT]
    have h4 : (η x : ℂ) * (show ℂ from v) = (show ℂ from v) := by
      have h5 : detRep (Fin 1) η (diagT (w.adicCompletion H.E) (Fin 1) fun _ => x) v = (show ℂ from v) := by
        exact h2.trans (by simp)
      have h6 := (ofChar_apply (detChar (Fin 1) η) (diagT (w.adicCompletion H.E) (Fin 1) fun _ => x)
        (show ℂ from v)).symm.trans h5
      rw [detChar_apply, h3] at h6
      exact h6
    ext
    exact (mul_eq_right₀ hv0).1 h4
  choose rep hrep using fun P => hs _ (T.e w (A.locV i P w)) ((T.dim w _).trans (hV P))
  have hrow : ∀ σ, ∃ π, what₂.isot (N.j i) σ ≠ ⊥ → T.e w (A.locW i σ w) = rc R.r π := fun σ => by
    by_cases hσ : what₂.isot (N.j i) σ ≠ ⊥
    · obtain ⟨π, hπ⟩ := hs _ (T.e w (A.locW i σ w)) ((T.dim w _).trans (hW σ hσ))
      exact ⟨π, fun _ => hπ.symm⟩
    · exact ⟨default, fun h => absurd h hσ⟩
  choose row hrow using hrow
  refine ⟨⟨rc, row, rep, μ, η⁻¹, ⟨hμ, hu⟩, ⟨hη.inv, fun x hx => by simp [hun x hx]⟩, hrow,
    fun P => (hrep P).symm, fun c hc => ?_, fun c hc => ?_⟩, rfl⟩
  · rw [← eμ]; exact ((hrc.iso 1 c (Irr.ofDet 1 μ hμ)).2 hc).symm
  · rw [← eη]; rw [inv_inv] at hc; exact ((hrc.iso 1 c (Irr.ofDet 1 η hη)).2 hc).symm

abbrev Reading (T : WDTie N A) : Type 1 := ∀ (i : N.Loc) (w : PlE H), IsSplitPl H w → ReadAt T i w

variable {T : WDTie N A} (S : Reading T)

def Laws : Prop := ∀ i w hw, RecLaws (S i w hw).rc

theorem exists_reading_laws (T : WDTie N A)
    (rc : ∀ (w : PlE H) n, Irr (w.adicCompletion H.E) n →
      WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w))
    (hrc : ∀ w, IsSplitPl H w → RecLaws (rc w))
    (hs : ∀ w, IsSplitPl H w → ∀ n a, WD.lpDim a = n → ∃ π, rc w n π = a)
    (hW : ∀ i w, IsSplitPl H w → ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ → A.lpDim (A.locW i σ w) = R.r)
    (hV : ∀ i w, IsSplitPl H w → ∀ P, A.lpDim (A.locV i P w) = R.r + R.t)
    (hmu : ∀ i w, IsSplitPl H w → ∃ (χ : _) (h : IsSmoothChar χ), IsUnitaryChar χ ∧
      rc w 1 (Irr.ofDet 1 χ h) = T.e w (A.locG (A.muC i) w))
    (heta : ∀ w, IsSplitPl H w → ∃ (χ : _) (h : IsSmoothChar χ),
      rc w 1 (Irr.ofDet 1 χ h) = T.e w (A.locG A.etaTinv w)) :
    ∃ S : Reading T, Laws S ∧ ∀ i w hw, (S i w hw).rc = rc w := by
  choose S hS using fun i w hw =>
    exists_readAt T i w (rc w) (hrc w hw) (hs w hw) (hW i w hw) (hV i w hw) (hmu i w hw) (heta w hw)
  exact ⟨S, fun i w hw => by rw [hS]; exact hrc w hw, hS⟩

def RowUnit : Prop := ∀ i w hw σ, what₂.isot (N.j i) σ ≠ ⊥ → IsUnitarisable ((S i w hw).row σ).π

def PairRead : Prop := ∀ i w hw σ P, Pairs N A i σ P →
  ThetaPair (S i w hw).mu ((S i w hw).row σ).π
    (twist ((S i w hw).rep P).π (detChar (Fin (R.r + R.t)) (S i w hw).eta))

def TypeTame (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ¬ IsUnram (S i w hw).mu ∧
    ∀ P, ∃ v, v ≠ 0 ∧ IsParahoricVec (S i w hw).mu ((S i w hw).rep P).π v

def TameSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), TameSplit (w.adicCompletion E)

end GlobalTheory.SplitRead
