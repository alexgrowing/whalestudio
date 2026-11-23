import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

section Param

variable {R : Ranks}

def run (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Multiset.range R.t).map fun k : ℕ => -P.e j + ((R.t : ℚ) + 1) / 2 - ((k : ℚ) + 1)

def param (P : HCParam R) (j : Fin R.m) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v +
    (Finset.univ : Finset (Fin R.m)).val.map (fun i => -P.b i) + run P j

def sgnOf (ep b : Bool) : ℚ := if ep = b then 1 else -1

end Param

variable (D : D7)

def liftIdx (i : D.nd.Loc) : Fin D.R.m :=
  ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩

def embOver (ρ : D.what₂.Tau) (b : Bool) : D.host.E →+* ℂ :=
  if b then
    (D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)).comp (D.host.conj : D.host.E →+* D.host.E)
  else D.host.emb ((D.eTau ρ : D.R.Psi) : D.R.GG)

def PP (i : D.nd.Loc) (ρ : D.what₂.Tau) : Multiset ℚ := param (D.hc ρ) (liftIdx D i)

def blockPP (i : D.nd.Loc) (ρ : D.what₂.Tau) : Multiset ℚ := run (D.hc ρ) (liftIdx D i)

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

abbrev LocEmb : Type := Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw

def cxEmb (τ : LocEmb D i w hw) : D.host.E →+* ℂ :=
  (D.naut.iotaQC i).toRingHom.comp
    ((D.nbr i w hw).LL.1.val.toRingHom.comp (τ.toRingHom.comp (Br.cEw D.nbr i w hw)))

def JumpsAre {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i)) (τ : LocEmb D i w hw) (J : Multiset ℚ) : Prop :=
  (∀ q ∈ J, ∃ a : ℤ, q = (a : ℚ)) ∧
  (∀ a : ℤ, Br.IsJumpW D.loc D.nbr i w hw r τ a ↔ (a : ℚ) ∈ J) ∧
  ∀ a : ℤ, Br.jumpMult D.loc D.nbr i w hw r τ a = (J.count (a : ℚ) : ℤ)

end Local

def chiGL (i : D.nd.Loc) (c : ℕ) : GE D.nd →* GL (Fin 1) (D.nd.O i) :=
  (Units.map (Matrix.scalar (Fin 1) : D.nd.O i →+* Matrix (Fin 1) (Fin 1) (D.nd.O i)).toMonoidHom).comp
    (D.nd.chi i c)

def IsSummand (i : D.nd.Loc) {n : ℕ} (r : GE D.nd →* GL (Fin n) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ) :
    Prop :=
  ∃ (v : Fin n → KK D.nd i) (W : Submodule (KK D.nd i) (Fin n → KK D.nd i)), v ≠ 0 ∧
    (∀ g, matRep (mapM (toK D.nd i) ((Units.coeHom _).comp r)) g v =
      toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • v) ∧
    Stable (matRep (mapM (toK D.nd i) ((Units.coeHom _).comp r))) W ∧
    IsCompl (Submodule.span (KK D.nd i) {v}) W

def DeRham_at : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Br.IsdRW D.loc D.nbr i w hw r

def JumpsWith (ep : Bool) (c : ℕ → D.what₂.places.Pl → (D.host.E →+* ℂ) → ℤ) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
      (τ : LocEmb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cxEmb D i w hw τ = embOver D ρ b →
      JumpsAre D i w hw r τ ((PP D i ρ).map fun p =>
        sgnOf ep b * p + (c (D.nd.j i) (D.nd.w i) (embOver D ρ b) : ℚ))

def BlockWith (ep : Bool) (c : ℕ → D.what₂.places.Pl → (D.host.E →+* ℂ) → ℤ) : Prop :=
  ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (∀ k, 1 ≤ k → k ≤ D.R.t → Br.IsdRW D.loc D.nbr i w hw (chiGL D i k)) ∧
    ∀ (τ : LocEmb D i w hw) (ρ : D.what₂.Tau) (b : Bool), cxEmb D i w hw τ = embOver D ρ b →
      ∃ a₁ : ℤ,
        (∀ k : ℕ, 1 ≤ k → k ≤ D.R.t →
          JumpsAre D i w hw (chiGL D i k) τ {(a₁ : ℚ) + ((k : ℚ) - 1)}) ∧
        ((blockPP D i ρ).map fun p => sgnOf ep b * p + (c (D.nd.j i) (D.nd.w i) (embOver D ρ b) : ℚ)) =
          (Multiset.range D.R.t).map fun k : ℕ => (a₁ : ℚ) + (k : ℚ)

def Summand_at : Prop :=
  ∀ (i : D.nd.Loc) (π : D.nd.X i), π ∈ D.nd.Z i →
    ∀ r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i), IsHeckeGalois D.nd i π r →
      ∀ k, 1 ≤ k → k ≤ D.R.t → IsSummand D i r (D.nd.chi i k)

def JumpDict_at : Prop :=
  DeRham_at D ∧
  (∃ (ep : Bool) (c : ℕ → D.what₂.places.Pl → (D.host.E →+* ℂ) → ℤ), JumpsWith D ep c ∧ BlockWith D ep c) ∧
  Summand_at D

def Crys_at : Prop :=
  ∀ (i : D.nd.Loc), (∀ k, D.nd.l i ≠ D.host.g k) →
    ∀ (x : D.nd.X i) (r : GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      Br.IsCrysW D.loc D.nbr i w hw r

def JumpDictCrys_at : Prop := JumpDict_at D ∧ Crys_at D

def WeightParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infWt i (embOver D ρ false) = (PP D i ρ).map (fun p => ((p - 1 / 2 : ℚ) : ℂ)) ∧
    D.naut.infWt i (embOver D ρ true) = (PP D i ρ).map (fun p => ((-(p - 1 / 2) : ℚ) : ℂ))

def BlockCharParam : Prop :=
  ∀ (i : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ false) =
      {((-(D.hc ρ).e (liftIdx D i) - 1 / 2 : ℚ) : ℂ)} ∧
    D.naut.infG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (embOver D ρ true) =
      {(((D.hc ρ).e (liftIdx D i) + 1 / 2 : ℚ) : ℂ)}

def JumpDictionaryAt : Prop := WeightParam D → BlockCharParam D → JumpDict_at D

def JumpDictF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, JumpDict_at (Fm.D x i)

def JumpDictClosed (C : FamClass) : Prop := Closed C (fun Fm _ => JumpDictF Fm)

end GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

end
