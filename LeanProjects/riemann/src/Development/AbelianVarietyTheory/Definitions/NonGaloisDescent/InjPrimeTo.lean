import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalRingCardinality.DataTies

noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def SerLoc (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]),
    ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F ≠ 0 → f = D.ntypes.labPar k σ' v

def TameOcc (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k), D.ntypes.cuspidal σ →
    Formalism.MainNotions.N.TameGen D.nd (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) →
    ∀ i : D.nd.Loc, D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
      Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
          Matrix (Fin D.R.r) (Fin D.R.r) _) =
        ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x =>
          X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod ∧
      ∃ φ : G D.host.E D.nd.Om,
        D.ntypes.rbar σ (D.nd.w i) (φ * D.ntypes.tg k v * φ⁻¹) = D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) ^ D.host.g k

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def InjPrimeTo {A B : Type} [MonoidWithZero A] [Monoid B] (l : ℕ) (ι : A →* B) : Prop :=
  ∀ x y : A, x ≠ 0 → y ≠ 0 → (orderOf x).Coprime l → (orderOf y).Coprime l → ι x = ι y → x = y

abbrev labSig (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) (k : Fin 2) (v : D.nd.PlG k) : (ZMod (D.host.g k))[X] :=
  D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameFixed (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i), InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
    ∃ φ : G D.host.E D.nd.Om,
      redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k

def TameAnyAt (D : D7) (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG))
    (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) (k : Fin 2) (w : PlE D.host) : Prop :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
    (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧ InjPrimeTo (D.nd.l i) ι ∧
    Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
        Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
      ((Formalism.CyclotomicNorms.rootsBar (labSig D Sig k v)).map
        fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
    D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
      ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
        (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
          ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂

def FullLab (D : D7) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), (labSig D Sig k v).natDegree =
    D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))

def TameSum (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)), (∃ x, HasParamX D.nd D.naut i x Sig) → FullLab D Sig →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i Sig ρ k ∧
      ∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) → TameAnyAt D i Sig ρ k w

def WildOne (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (L : D.naut.LP (D.naut.plGw k v)),
    (D.naut.items₂ k _ L).natDegree = D.naut.lpDim L →
      ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
        s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.naut.inePol L s = (X - 1) ^ D.naut.lpDim L

def GalAway (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i)),
      Continuous (fun g => ((r g : GL (Fin a) (Qbar (D.nd.l i))) : Matrix (Fin a) (Fin a) (Qbar (D.nd.l i)))) ∧
      ∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
        D.naut.wdOf i r w = D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)

def FrobDense (D : D7) : Prop :=
  ∀ T : Set (PlE D.host), T.Finite → Dense {s : G D.host.E D.nd.Om | ∃ w : PlE D.host, w ∉ T ∧ IsSplitPl D.host w ∧
    ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) s}

def PointPar (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (π : D.naut.CG D.R.r), HasParamX D.nd D.naut i x [⟨D.R.r, π, 1⟩] →
    D.naut.csd π ∧ D.naut.ralg π

def RedVia (D : D7) (i : D.nd.Loc) (k : Fin 2)
    (ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i)) : Prop :=
  ∀ (p : (D.nd.O i)[X]) (s : Multiset (Fb (D.host.g k) (D.host.g_prime k))),
    p.map (iotaO D.nd D.naut i) = (s.map fun x => X - C (D.ntypes.teichC k x)).prod →
    p.map ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) = (s.map fun x => X - C (ι x)).prod

def IotaLoc (D : D7) : Prop :=
  ∀ i : D.nd.Loc, ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+*
      Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i))),
    (∀ y : D.nd.O i, ∃ h : iotaO D.nd D.naut i y ∈ B,
      fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
    ∀ k v x, ∃ h : D.ntypes.teichC k x ∈ B, D.ntypes.iota k v (D.nd.w i) x = κ (IsLocalRing.residue B ⟨_, h⟩)

def RowModel (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ →
    ∃ (i' : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i')),
      D.nd.w i' = D.nd.w i ∧ HasParamW D.nd D.naut i' σ [⟨D.R.r, π, 1⟩] ∧ D.naut.csd π ∧ D.naut.ralg π ∧
      IsRepOfSig D.nd D.naut i' [⟨D.R.r, π, 1⟩] ρ

def TwistInv (D : D7) : Prop :=
  (∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaT) D.naut.etaTinv = π) ∧
  ∀ (a : ℕ) (π : D.naut.CG a), 1 ≤ a → D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π

def CharLaws (D : D7) : Prop :=
  ∀ (w : PlE D.host) (a χ χ' : D.naut.LP w), D.naut.lpDim χ = 1 → D.naut.lpDim χ' = 1 →
    D.naut.lpChar (D.naut.lpChar a χ) χ' = D.naut.lpChar a (D.naut.lpChar χ χ') ∧
    D.naut.lpChar a (D.naut.lpUnr w {1}) = a

def MultOne (D : D7) : Prop :=
  ∀ (a : ℕ) (π π' : D.naut.CG a), 1 ≤ a → (∀ w, D.naut.locG π w = D.naut.locG π' w) → π = π'

def GoodBase (D : D7) : Prop := ∀ σ, D.nd.goodRow (D.what₂.ft0 σ)

end GlobalTheory.TypeLeaf
