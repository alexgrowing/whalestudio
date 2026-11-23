import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.InfiniteAdeleRingMapInfiniteAdeleRingMap
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)

open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂

def fN (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : (Af L)ˣ →* (Af K)ˣ :=
  (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))).comp ((GroundTheory.Global.ideleNorm K L).comp
    (Units.map (MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))))

abbrev Kx {E : Type} [Field E] [NumberField E] (x : E) : Type := ↥(IntermediateField.adjoin ℚ {x})

def NormGlob : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L], Continuous (fN K L) ∧
    (∀ k : Lˣ, ((fN K L (diagF L k) : (Af K)ˣ) : Af K) = algebraMap K (Af K) (Algebra.norm K (k : L))) ∧
    ∀ (M : Type) [Field M] [NumberField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] (y : (Af M)ˣ),
      fN K L (fN L M y) = fN K M y

def NormLoc : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (w : Plc L) (y : (w.adicCompletion L)ˣ) (u : Plc L),
    (u.under (𝓞 K) ≠ w.under (𝓞 K) → finiteAdeleMap K L ((fN K L (sgl w y) : (Af K)ˣ) : Af K) u = 1) ∧
    (IsUnitAt w y → Valued.v (finiteAdeleMap K L ((fN K L (sgl w y) : (Af K)ˣ) : Af K) u) = 1) ∧
    (IsUnifAt w y → u.under (𝓞 K) = w.under (𝓞 K) →
      Valued.v ((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : (w.under (𝓞 K)).adicCompletion K) = WithZero.exp (-1 : ℤ) →
      Valued.v (finiteAdeleMap K L ((fN K L (sgl w y) : (Af K)ˣ) : Af K) u) =
        Valued.v ((Ideal.absNorm w.asIdeal : ℕ) : u.adicCompletion L))

def ConjLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : Af E) (u : Plc E),
    (a (cj u) = 1 → conjFin (conjE E) a u = 1) ∧ Valued.v (conjFin (conjE E) a u) = Valued.v (a (cj u)) ∧
    (∀ m : ℕ, Valued.v ((m : ℕ) : u.adicCompletion E) = Valued.v ((m : ℕ) : (cj u).adicCompletion E)) ∧
    conjFin (conjE E) (conjFin (conjE E) a) = a ∧ Continuous (conjFin (conjE E))

def QuadConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) → ∀ z : (Af (Kx x))ˣ,
    finiteAdeleMap (Kx x) E (z : Af (Kx x)) * conjFin (conjE E) (finiteAdeleMap (Kx x) E (z : Af (Kx x))) =
      finiteAdeleMap ℚ E ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ)

def KPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) →
    (∀ w w' : Plc E, SameK x w w' ↔ w.under (𝓞 (Kx x)) = w'.under (𝓞 (Kx x))) ∧
    ∀ w : Plc E, ¬ SameK x (cj w) w →
      Valued.v ((Ideal.absNorm (w.under (𝓞 (Kx x))).asIdeal : ℕ) : (w.under (𝓞 (Kx x))).adicCompletion (Kx x)) = WithZero.exp (-1 : ℤ)

def NormEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (x : E), 0 < d → x ^ 2 = -(d : E) → ∀ k : Eˣ,
    (∀ φ : E →+* ℂ, φ (conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)))) =
      ∏ φ' ∈ Finset.univ.filter (fun φ' : E →+* ℂ => φ' x = -φ x), φ' k) ∧
    ((Algebra.norm ℚ (k : E) : ℚ) : ℂ) = ∏ φ' : E →+* ℂ, φ' k ∧ 0 < Algebra.norm ℚ (k : E) ∧
    algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E)) * conjE E (algebraMap (Kx x) E (Algebra.norm (Kx x) (k : E))) =
      algebraMap ℚ E (Algebra.norm ℚ (k : E))

end UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
