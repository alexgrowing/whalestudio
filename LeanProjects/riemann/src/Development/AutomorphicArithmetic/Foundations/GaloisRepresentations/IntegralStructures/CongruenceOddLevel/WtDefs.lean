import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWPhi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CAllFin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.CongW

namespace UpperTheory.Gal.Int.Cong

def WtTo (Q : ∀ a : ℕ, DomWeight a → Prop) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (v' : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → Apart v' w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → (∀ x ∈ locU a v', cLoc v' x ∈ GlobalTheory.LFun.KGL v' a → x ∈ K) →
    ∀ (Kv : Subgroup (GL (Fin a) (v'.adicCompletion E))), IsOpen (Kv : Set (GL (Fin a) (v'.adicCompletion E))) →
    ∀ (lam : (E →+* ℂ) → DomWeight a) (Jx : Type) (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, UpperTheory.Gal.Gen.Loc.IntL ι lam (t j)) →
      (∀ j, ∀ g ∈ (t j).support, (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧ ∀ u, ¬ Apart u v' → cLoc u g = 1) →
      ActsBy (K ⊓ Kv.comap (cLoc v')) t η →
    ∀ τ₀ : E →+* ℂ, OverPl ι τ₀ v' → ∀ U, OfType lam (K ⊓ Kv.comap (cLoc v')) U →
      PolyApprox (fun j => ι.symm (η U j)) {ϑ | ∃ (U' : Submodule ℂ (UA E a → ℂ)) (mu : (E →+* ℂ) → DomWeight a),
        (∀ τ, mu τ ≠ lam τ → OverPair ι v' τ) ∧ Q a (mu τ₀) ∧ OfType mu K U' ∧ ϑ = fun j => ι.symm (η U' j)}

def GapWt (a : ℕ) (lam : DomWeight a) : Prop :=
  ∀ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) → GapJ a J

def WtChgEx : Prop := WtTo fun _ _ => True

def WtLacEx : Prop := WtTo GapWt

end UpperTheory.Gal.Int.Cong

end
