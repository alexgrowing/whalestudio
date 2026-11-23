import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

def Near1 {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Plc E) (e : ℕ) (g : GLw n w) : Prop :=
  ∀ i k, InId w (w.asIdeal ^ e) ((g.val - 1) i k)

def NearNbhd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (O : Set (GLw n w)), IsOpen O → 1 ∈ O →
    ∃ e : ℕ, ∀ e', e ≤ e' → ∀ g ∈ KGL w n, Near1 w e' g → g ∈ O

def StabOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S)
    (x : E) (U : Submodule ℂ (UA E n → ℂ)) (w₀ : Plc E) (Up : Plc E → Prop) (V : Vec x U w₀ Up),
    Off V p → ∃ (T : Finset (Plc E)) (e : ℕ), (∀ u ∈ T, (p : 𝓞 E) ∉ u.asIdeal ∧ (u ∈ V.S ∨ F.a u ∉ KGL u n)) ∧
      ∀ k' : GUf E n, F.j k' ∈ S.L.KN 1 → (∀ u ∈ T, Near1 u e (F.a u * comp u k' * (F.a u)⁻¹)) → Stab F V (F.j k')

def InIdBasic : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (w : Plc E) (𝔟 : Ideal (𝓞 E)), 𝔟 ≠ ⊥ →
    (∃ e : ℕ, ∀ y, InId w 𝔟 y ↔ Valued.v y ≤ WithZero.exp (-(e : ℤ))) ∧
    (∀ (e : ℕ) y, InId w (w.asIdeal ^ e) y ↔ Valued.v y ≤ WithZero.exp (-(e : ℤ))) ∧
    (𝔟 ⊔ w.asIdeal = ⊤ → ∀ y, InId w 𝔟 y ↔ y ∈ w.adicCompletionIntegers E) ∧
    (∀ 𝔟' y, 𝔟 ≤ 𝔟' → InId w 𝔟 y → InId w 𝔟' y) ∧
    ∀ 𝔠 : Ideal (𝓞 E), 𝔠 ⊔ w.asIdeal = ⊤ → ∀ y, InId w (𝔠 * 𝔟) y ↔ InId w 𝔟 y

def IdHat : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (𝔟 : Ideal (𝓞 E)), 𝔟 ≠ ⊥ →
    ∀ v, v ∈ idHat S.D 𝔟 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i, InId w 𝔟 (F.vec w v i)

end UpperTheory.Gal.Int.Geo.Pl
