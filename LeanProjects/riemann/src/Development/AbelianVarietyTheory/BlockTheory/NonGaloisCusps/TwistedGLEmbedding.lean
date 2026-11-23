import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

section Weight

variable {R : Ranks} (P : HCParam R) (a : Fin R.m)

def pW : ℚ := ((R.sigW (a.1 + 1)).1 : ℚ)

def qW : ℚ := ((R.sigW (a.1 + 1)).2 : ℚ)

def rhoN (R : Ranks) (s : ℚ) : ℚ := ((R.nV : ℚ) + 1 - 2 * s) / 2

def dTw : ℚ := (pW a - qW a) / 2 - P.e a - 1 / 2

def aPlus (y s : ℚ) : ℚ := (y + P.e a) - ((R.nV : ℚ) + 1 - 2 * s) / 2 - (pW a - qW a) / 2

def aMinus (b c : ℚ) : ℚ := (b - P.e a) + (1 - (R.t : ℚ) - 2 * c) / 2

def lamWt : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map
      (fun i => aPlus P a (P.v i) ((i.1 : ℚ) + 1) + dTw P a + rhoN R ((i.1 : ℚ) + 1)) +
    (Finset.univ : Finset (Fin R.m)).val.map
      (fun h => if h ≤ a then
          aPlus P a (-P.b h) ((R.k : ℚ) + h.1) + dTw P a + rhoN R ((R.k : ℚ) + h.1)
        else
          -aMinus P a (P.b h) ((h.1 : ℚ) - a.1) + dTw P a + rhoN R (pW a + R.t + ((h.1 : ℚ) - a.1))) +
    (Finset.range R.t).val.map (fun c : ℕ => 0 + dTw P a + rhoN R (pW a + ((c : ℚ) + 1)))

def sigPar : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun h => -P.b h)

def runPar : Multiset ℚ :=
  (Finset.range R.t).val.map (fun c : ℕ => -P.e a + ((R.t : ℚ) - 1) / 2 - c)

def fullPar : Multiset ℚ := sigPar P + runPar P a

theorem pW_eq : pW a = (R.k : ℚ) + a.1 := by
  simp [pW, Ranks.sigW]

theorem qW_eq : qW a = (R.m : ℚ) - a.1 - 1 := by
  have h : a.1 + 1 ≤ R.m := a.2
  simp only [qW, Ranks.sigW]
  rw [Nat.cast_sub h]
  push_cast
  ring

theorem nV_eq (R : Ranks) : (R.nV : ℚ) = (R.k : ℚ) + R.m - 1 + R.t := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  simp only [Ranks.nV, Ranks.r]
  push_cast [Nat.cast_sub h]
  ring

theorem lamWt_eq : lamWt P a = (fullPar P a).map (· - 1 / 2) := by
  simp only [lamWt, fullPar, sigPar, runPar, Multiset.map_add, Multiset.map_map]
  congr 1
  · congr 1
    · refine Multiset.map_congr rfl fun i _ => ?_
      simp only [aPlus, dTw, rhoN, Function.comp]
      ring
    · refine Multiset.map_congr rfl fun h _ => ?_
      simp only [aPlus, aMinus, dTw, rhoN, Function.comp, pW_eq, qW_eq, nV_eq]
      split_ifs <;> ring
  · refine Multiset.map_congr rfl fun c _ => ?_
    simp only [dTw, rhoN, Function.comp, pW_eq, qW_eq, nV_eq]
    ring

end Weight

section GLs

variable {Γ O : Type} [Group Γ] [CommRing O]

def charGL (χ : Γ →* Oˣ) : Γ →* GL (Fin 1) O := (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp χ

def twGL {n : ℕ} (r : Γ →* GL (Fin n) O) (χ : Γ →* Oˣ) : Γ →* GL (Fin n) O where
  toFun g := Matrix.GeneralLinearGroup.scalar (Fin n) (χ g) * r g
  map_one' := by simp
  map_mul' g h := by
    have hc : r g * Matrix.GeneralLinearGroup.scalar (Fin n) (χ h) =
        Matrix.GeneralLinearGroup.scalar (Fin n) (χ h) * r g := by
      apply Units.ext
      simp only [Units.val_mul]
      exact ((Matrix.scalar_commute ((χ h : Oˣ) : O) (fun y => Commute.all _ y) _).eq).symm
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (r g), ← mul_assoc (Matrix.GeneralLinearGroup.scalar (Fin n) (χ h)), hc]

end GLs

section Record

variable (D : D7)

def jIx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embPsi (ρ : D.what₂.Tau) : D.host.E →+* ℂ :=
  D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def embBar (ρ : D.what₂.Tau) : D.host.E →+* ℂ :=
  (embPsi D ρ).comp (D.host.conj : D.host.E →+* D.host.E)

def eAt (i : D.nd.Loc) (ρ : D.what₂.Tau) : ℚ := (D.hc ρ).e (jIx D i)

def WeightTie : Prop := ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
  D.naut.infWt i (embPsi D ρ) = (lamWt (D.hc ρ) (jIx D i)).map (fun q : ℚ => (q : ℂ)) ∧
  D.naut.infWt i (embBar D ρ) = (lamWt (D.hc ρ) (jIx D i)).map (fun q : ℚ => -(q : ℂ))

def CharTie : Prop := ∀ ρ : D.what₂.Tau,
  (∀ i : D.nd.Loc, D.naut.infG (D.naut.muC i) (embPsi D ρ) = {-((eAt D i ρ : ℚ) : ℂ)} ∧
    D.naut.infG (D.naut.muC i) (embBar D ρ) = {((eAt D i ρ : ℚ) : ℂ)}) ∧
  D.naut.infG D.naut.etaTinv (embPsi D ρ) = {-(1 / 2 : ℂ)} ∧
  D.naut.infG D.naut.etaTinv (embBar D ρ) = {(1 / 2 : ℂ)}

variable {D} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev Emb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cxEmb (τ : Emb i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    ((algebraMap (Br.LL D.nbr i w hw) (Qbar (D.nd.l i))).comp
      ((τ : Br.Kw D.nbr i w hw →+* Br.LL D.nbr i w hw).comp (Br.cEw D.nbr i w hw)))

def HasJumps {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i)) (τ : Emb i w hw) (J : Multiset ℚ) : Prop :=
  (∀ q ∈ J, ∃ a : ℤ, q = a) ∧
    ∀ a : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ a = (J.count (a : ℚ) : ℤ)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

open Classical in

def WeightsAt (τ : Emb i w hw) : Prop :=
  ∃ J : Finset ℤ, J.card = D.R.nV ∧
    J.val.map (fun a : ℤ => (a : ℂ)) =
      (D.naut.infWt i (cxEmb i w hw τ)).map (fun z => ((D.R.nV : ℂ) - 1) / 2 - z) ∧
    (∀ x a, Br.jumpMult D.loc D.nbr i w hw (r x) τ a = if a ∈ J then 1 else 0) ∧
    ∃ w₁ : ℤ,
      (∀ c : ℕ, 1 ≤ c → c ≤ D.R.t → w₁ + ((c : ℤ) - 1) ∈ J ∧
        HasJumps i w hw (charGL (D.nd.chi i c)) τ {((w₁ + ((c : ℤ) - 1) : ℤ) : ℚ)}) ∧
      w₁ - 1 ∉ J ∧ w₁ + (D.R.t : ℤ) ∉ J

def ExplicitAt (τ : Emb i w hw) (ρ : D.what₂.Tau) (s : ℚ) : Prop :=
  (∀ x, HasJumps i w hw (r x) τ
    ((fullPar (D.hc ρ) (jIx D i)).map fun p => ((D.R.nV : ℚ) - 1) / 2 - s * (p - 1 / 2))) ∧
  (∀ c : ℕ, 1 ≤ c → c ≤ D.R.t →
    HasJumps i w hw (charGL (D.nd.chi i c)) τ
      {s * (eAt D i ρ + 1 / 2) + (D.R.r : ℚ) / 2 + ((c : ℚ) - 1)} ∧
    HasJumps i w hw (charGL (D.nd.chi i c * (D.nd.chi i 1)⁻¹)) τ {(c : ℚ) - 1}) ∧
  (∀ x, HasJumps i w hw (twGL (r x) (D.nd.chi i 1)⁻¹) τ
    ((fullPar (D.hc ρ) (jIx D i)).map fun p => ((D.R.t : ℚ) - 1) / 2 - s * (p + eAt D i ρ))) ∧
  ∀ h : Fin (D.R.k - 1),
    (s = 1 → ((D.R.t : ℚ) - 1) / 2 - s * ((D.hc ρ).v h + eAt D i ρ) < 0) ∧
    (s = -1 → (D.R.t : ℚ) - 1 < ((D.R.t : ℚ) - 1) / 2 - s * ((D.hc ρ).v h + eAt D i ρ))

def DeRhamAt : Prop :=
  (∀ x, Br.IsdRW D.loc D.nbr i w hw (r x)) ∧
  ∀ τ : Emb i w hw, WeightsAt i w hw r τ ∧
    ∀ ρ : D.what₂.Tau,
      (cxEmb i w hw τ = embPsi D ρ → ExplicitAt i w hw r τ ρ 1) ∧
      (cxEmb i w hw τ = embBar D ρ → ExplicitAt i w hw r τ ρ (-1))

variable (D)

def CrysPart : Prop :=
  ∀ (i : D.nd.Loc), (∀ k, D.nd.l i ≠ D.host.g k) →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      (∀ x, Br.IsCrysW D.loc D.nbr i w hw (r x)) ∧ DeRhamAt i w hw r

def TypePart : Prop :=
  ∀ (i : D.nd.Loc), (∃ k, D.nd.l i = D.host.g k) →
    ∀ r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), GoodR D.nd i r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      DeRhamAt i w hw r ∧
      ∀ (x : D.nd.X i) (Pi : D.naut.AV i), D.naut.ptV i Pi = some x →
        (Br.IsPotCrysW D.loc D.nbr i w hw (r x) ↔ D.naut.mono0 (D.naut.locV i Pi w))

def Weights_at : Prop := WeightTie D → CharTie D → CrysPart D ∧ TypePart D

end Record

def WeightsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Weights_at (Fm.D x i)

def WeightsClosed (𝒞 : FamClass) : Prop := Closed 𝒞 (fun Fm _ => WeightsF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.TwistedGLEmbedding

end
