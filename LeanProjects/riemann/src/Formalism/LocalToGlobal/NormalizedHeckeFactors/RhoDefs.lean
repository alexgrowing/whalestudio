import Formalism.LocalToGlobal.GaloisLevelStructure.NGalTied
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual NumberField IsDedekindDomain Polynomial

namespace Formalism.L2.NR

section frame

variable {E Ω L : Type} [Field E] [Field Ω] [Algebra E Ω] [Field L]

def FrameOver (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) : Prop :=
  ∀ x : E, k (algebraMap L (AlgebraicClosure L) (j x)) = algebraMap E Ω x

def toRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k) :
    (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) →* (Ω ≃ₐ[E] Ω) where
  toFun σ := AlgEquiv.ofRingEquiv (f := (k.symm.trans (σ : AlgebraicClosure L ≃+* AlgebraicClosure L)).trans k)
    (fun x => by
      simp only [RingEquiv.trans_apply]
      rw [← hk x, RingEquiv.symm_apply_apply]
      simp)
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp

theorem toRec_apply (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k)
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) (x : Ω) : toRec j k hk σ x = k (σ (k.symm x)) := rfl

def ofRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k) :
    (Ω ≃ₐ[E] Ω) →* (AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) where
  toFun g := AlgEquiv.ofRingEquiv (f := (k.trans (g : Ω ≃+* Ω)).trans k.symm)
    (fun y => by
      have h := hk (j.symm y)
      rw [RingEquiv.apply_symm_apply] at h
      simp only [RingEquiv.trans_apply]
      rw [h]
      simp only [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
      rw [← h, RingEquiv.symm_apply_apply])
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp

theorem ofRec_apply (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k)
    (g : Ω ≃ₐ[E] Ω) (x : AlgebraicClosure L) : ofRec j k hk g x = k.symm (g (k x)) := rfl

theorem toRec_ofRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k) (g : Ω ≃ₐ[E] Ω) :
    toRec j k hk (ofRec j k hk g) = g := by
  ext x
  simp [toRec_apply, ofRec_apply]

theorem ofRec_toRec (j : E ≃+* L) (k : AlgebraicClosure L ≃+* Ω) (hk : FrameOver j k)
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L) : ofRec j k hk (toRec j k hk σ) = σ := by
  ext x
  simp [toRec_apply, ofRec_apply]

end frame

def reindexGL {R : Type} [CommRing R] {a b : ℕ} (h : a = b) : GL (Fin a) R →* GL (Fin b) R :=
  Units.map (Matrix.reindexAlgEquiv R R (finCongr h)).toAlgHom.toRingHom.toMonoidHom

def IsRepOfSigI (D : D7) (ℓ : ℕ) [Fact ℓ.Prime] (ι : Qbar ℓ ≃+* ℂ) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar ℓ)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin b) (Qbar ℓ)) : Matrix (Fin b) (Fin b) (Qbar ℓ))) ∧
  Formalism.MainNotions.N.IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin b) (Fin b) (Qbar ℓ)).charpoly.map ι.toRingHom =
      Formalism.MainNotions.N.galPol D.naut (D.naut.lpTw (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig w) ((1 - (b : ℝ)) / 2))

def IsRepOfSigQ (D : D7) (i : D.nd.Loc) (b : ℕ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))) : Prop :=
  IsRepOfSigI D (D.nd.l i) (D.naut.iotaQC i) b Sig ρ

def IsRepOfSigSh (D : D7) (i : D.nd.Loc) (b : ℕ) (sh : ℝ) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (D.nd.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin b) (D.nd.O i)) : Matrix (Fin b) (Fin b) (D.nd.O i))) ∧
  Formalism.MainNotions.N.IsSSRep (Formalism.MainNotions.N.mapRep (algebraMap (D.nd.O i) (Formalism.MainNotions.N.Kf D.nd i)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin b) (Fin b) (D.nd.O i)).charpoly.map (Formalism.MainNotions.N.iotaO D.nd D.naut i) =
      Formalism.MainNotions.N.galPol D.naut (D.naut.lpTw (Formalism.MainNotions.N.isoLoc D.nd D.naut Sig w) sh)

def InducesPl (D : D7) (lam : D.what₂.places.Pl) {ℓ : ℕ} [Fact ℓ.Prime] (ι : Qbar ℓ ≃+* ℂ) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val lam x ↔ ‖ι.symm (D.what₂.embLL x)‖ ≤ 1

def IsRedQ {ℓ : ℕ} [Fact ℓ.Prime] {k : Type} [Field k] (κ : Qbar ℓ → k) : Prop :=
  κ 1 = 1 ∧ (∀ x y : Qbar ℓ, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → κ (x + y) = κ x + κ y ∧ κ (x * y) = κ x * κ y) ∧
    ∀ x : Qbar ℓ, ‖x‖ ≤ 1 → (κ x = 0 ↔ ‖x‖ < 1)

def twistRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) :
    Γ →* GL (Fin n) K where
  toFun g := Units.map (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    have key : ∀ (c : K) (M : Matrix (Fin n) (Fin n) K),
        (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c * M = M * (algebraMap K (Matrix (Fin n) (Fin n) K)).toMonoidHom c :=
      fun c M => Algebra.commutes c M
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, mul_assoc]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← key]

theorem twistRep_apply {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ : Γ →* GL (Fin n) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((twistRep ρ χ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      algebraMap K (Matrix (Fin n) (Fin n) K) (χ g : K) * (ρ g : Matrix (Fin n) (Fin n) K) := rfl

def IsConjRep {Γ K : Type} [Group Γ] [CommRing K] {n : ℕ} (ρ₁ ρ₂ : Γ →* GL (Fin n) K) : Prop :=
  ∃ P : GL (Fin n) K, ∀ g, ρ₁ g = P * ρ₂ g * P⁻¹

theorem one_le_r (D : D7) : 1 ≤ D.R.r := by
  have := D.R.two_le_m
  show 1 ≤ D.R.k + D.R.m - 1
  omega

def GalRepEx (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)), IsRepOfSigQ D i a [⟨a, π, 1⟩] ρ

def ClassFieldHeckeAlgebraic (D : D7) : Prop :=
  ∀ i (χ : D.naut.CG 1) (s : ℝ), (∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG χ τ, ∃ k : ℤ, z + (s : ℂ) = (k : ℂ)) →
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i)), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ ∧
      (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s) ∧
      ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (D.naut.locG χ w) s ∧
        ∀ τ, Formalism.MainNotions.N.InducesW D.nd i τ w → (D.naut.jumpsW i ρ τ).map (fun n : ℤ => (n : ℂ)) =
          (D.naut.infG χ ((D.naut.iotaQC i).toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)))

def EtaShiftInt (D : D7) : Prop :=
  ∀ τ : D.host.E →+* ℂ, ∀ z ∈ D.naut.infG D.naut.etaTinv τ, ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ)

def RowPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ Sig : List (Part D.naut.CG),
    Formalism.MainNotions.N.HasParamW D.nd D.naut i σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def IsRowPar (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) (Sig : List (Part D.naut.CG)) : Prop :=
  Formalism.MainNotions.N.HasParamW D.nd D.naut a σ Sig ∧ (D.nd.goodRow σ → ∀ p ∈ Sig, D.naut.csd p.π ∧ D.naut.ralg p.π)

def rowSig (D : D7) (a : D.nd.Loc) (σ : D.what₂.FT) : List (Part D.naut.CG) :=
  Classical.epsilon (IsRowPar D a σ)

theorem rowSig_isRowPar (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    IsRowPar D a σ (rowSig D a σ) :=
  Classical.epsilon_spec (hP a σ hσ)

theorem rowSig_spec (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥) :
    Formalism.MainNotions.N.HasParamW D.nd D.naut a σ (rowSig D a σ) :=
  (rowSig_isRowPar D hP a σ hσ).1

theorem rowSig_csd_ralg (D : D7) (hP : RowPar D) (a : D.nd.Loc) (σ : D.what₂.FT) (hσ : D.what₂.isot (D.nd.j a) σ ≠ ⊥)
    (hg : D.nd.goodRow σ) (π : D.naut.CG D.R.r) (hS : rowSig D a σ = [⟨D.R.r, π, 1⟩]) : D.naut.csd π ∧ D.naut.ralg π :=
  (rowSig_isRowPar D hP a σ hσ).2 hg ⟨D.R.r, π, 1⟩ (by rw [hS]; exact List.mem_singleton_self _)

def rowRho (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  Classical.choose (hG a D.R.r (one_le_r D) π hc hr)

theorem rowRho_spec (D : D7) (hG : GalRepEx D) (a : D.nd.Loc) (π : D.naut.CG D.R.r) (hc : D.naut.csd π)
    (hr : D.naut.ralg π) : IsRepOfSigQ D a D.R.r [⟨D.R.r, π, 1⟩] (rowRho D hG a π hc hr) :=
  Classical.choose_spec (hG a D.R.r (one_le_r D) π hc hr)

def etaChar (D : D7) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc) : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (Qbar (D.nd.l a))ˣ :=
  Matrix.GeneralLinearGroup.det.comp (Classical.choose (hC a D.naut.etaTinv (-(D.R.t : ℝ) / 2) hη))

def rhoOfRow (D : D7) (hG : GalRepEx D) (hC : ClassFieldHeckeAlgebraic D) (hη : EtaShiftInt D) (a : D.nd.Loc)
    (π : D.naut.CG D.R.r) (hc : D.naut.csd π) (hr : D.naut.ralg π) :
    Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar (D.nd.l a)) :=
  twistRep (rowRho D hG a π hc hr) (etaChar D hC hη a)

end Formalism.L2.NR
