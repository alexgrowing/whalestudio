import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.PolyApproxCut

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep
open ValuativeRel

namespace UpperTheory.Gal.CharacterCongruences

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

structure IsLevel (C : Subgroup (UA E a)) : Prop where
  fin : C ≤ finU E a
  compact : IsCompact (C : Set (UA E a))
  isOpen : ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E a ⊆ C

def NearOne {C : Subgroup (UA E a)} {D : Type} [Group D] (lam : C →* D) : Prop :=
  ∃ N : Set (UA E a), IsOpen N ∧ 1 ∈ N ∧ ∀ c : C, c.1 ∈ N → lam c = 1

def RatNeat {C : Subgroup (UA E a)} {D : Type} [Group D] (lam : C →* D) : Prop :=
  ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c : C, ∀ x ∈ infU E a, γ * g = g * c * x → lam c = 1

def TorsFreeAt (K : Subgroup (UA E a)) (u : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ k ∈ K, IsOfFinOrder (cLoc u k) → cLoc u k = 1

def Rel {C : Subgroup (UA E a)} (A : Set (C →₀ ℂ)) (ψ : C →* ℂˣ) (φ : UA E a → ℂ) : Prop :=
  ∀ r ∈ A, (r.sum fun c z => (z * (((ψ c)⁻¹ : ℂˣ) : ℂ)) • RU E a c φ) = 0

structure OfVec (lam : (E →+* ℂ) → DomWeight a) (p : (UA E a → ℂ) → Prop) (U : Submodule ℂ (UA E a → ℂ)) : Prop where
  aut : IsAutRepU U
  wt : ∀ τ, HasWeightAt U τ (lam τ)
  vec : ∃ φ ∈ U, φ ≠ 0 ∧ p φ

def ActsOn {J : Type} (p : (UA E a → ℂ) → Prop) (t : J → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → J → ℂ) : Prop :=
  ∀ U, IsAutRepU U → ∀ φ ∈ U, p φ → ∀ j, opOf (RU E a) (t j) φ = η U j • φ

def CongFor (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (N m : ℕ) (p : Ch (l ^ N) → (UA E a → ℂ) → Prop)
    (q : Submodule ℂ (UA E a → ℂ) → Prop) : Prop :=
  ∀ (lam : (E →+* ℂ) → DomWeight a) (J : Type) (t : J → (UA E a →₀ ℂ))
    (η : Ch (l ^ N) → Submodule ℂ (UA E a → ℂ) → J → ℂ), (∀ j, IsIntegralOp ι (t j)) →
    (∀ ξ : Ch (l ^ N), ξ = 1 ∨ ξ ^ (l ^ (N - m)) ≠ 1 → ActsOn (p ξ) t (η ξ)) → ∀ U, OfVec lam (p 1) U →
    PolyApproxAt (‖(l : Qbar l)‖ ^ m) (sys ι (η 1 U) (1 : Ch (l ^ N)))
      {z | ∃ ξ : Ch (l ^ N), ξ ^ (l ^ (N - m)) ≠ 1 ∧ ∃ U', OfVec lam (p ξ) U' ∧ q U' ∧ z = sys ι (η ξ U') ξ}

def CongC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ (C : Subgroup (UA E a)), IsLevel C → ∀ lam : C →* Multiplicative (ZMod (l ^ N)), NearOne lam → RatNeat lam →
    ∀ A : Set (C →₀ ℂ), CongFor l ι N m (fun ξ => Rel A (ξ.comp lam)) fun _ => True

def charRel {C : Type} [Group C] (χ : C →* ℂˣ) : Set (C →₀ ℂ) :=
  Set.range fun c => Finsupp.single c 1 - Finsupp.single 1 (χ c : ℂ)

def TypeW (w : HeightOneSpectrum (𝓞 E)) {K : Subgroup (UA E a)} (A : Set (K →₀ ℂ)) (ψ : K →* ℂˣ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (χ : J →* ℂˣ) (φ : UA E a → ℂ) : Prop :=
  Rel A ψ φ ∧ ∀ x ∈ locU a w, ∀ hx : cLoc w x ∈ J, RU E a x φ = (χ ⟨_, hx⟩ : ℂ) • φ

def CongW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ K : Subgroup (UA E a), IsLevelAway w K →
    ∀ (A : Set (K →₀ ℂ)) (lamK : K →* Multiplicative (ZMod (l ^ N))), NearOne lamK →
    ∀ J : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ((∃ u, Apart u w ∧ TorsFreeAt K u) ∨ ∀ x ∈ J, IsOfFinOrder x → x = 1) →
    ∀ (χ : J →* ℂˣ) (lam : J →* Multiplicative (ZMod (l ^ N))), IsOpen (lam.ker : Set J) →
    CongFor l ι N m (fun ξ => TypeW w A (ξ.comp lamK) (χ * ξ.comp lam)) fun _ => True

def CongSc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), 1 ≤ a → m ≤ N →
    ∀ w₀ : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ∀ K : Subgroup (UA E a), IsLevelAway w₀ K →
    ∀ (A : Set (K →₀ ℂ)) (lamK : K →* Multiplicative (ZMod (l ^ N))), NearOne lamK →
    CongFor l ι N m (fun ξ => Rel A (ξ.comp lamK)) fun U => ScU U w₀

def blockChar {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s a : ℕ} {d : Fin s → ℕ}
    (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a) {M : Type} [CommGroup M] (ω : Fin s → (𝓀[k])ˣ →* M) : parahoric k e →* M :=
  ∏ b : Fin s, (ω b).comp ((Matrix.GeneralLinearGroup.det).comp
    ((Pi.evalMonoidHom (fun b => GL (Fin (d b)) 𝓀[k]) b).comp (parahoricProj k e)))

def CongP : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a N m : ℕ), m ≤ N →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ K : Subgroup (UA E a), IsLevelAway w K →
    ∀ u, Apart u w → TorsFreeAt K u → ∀ (A : Set (K →₀ ℂ)) (s : ℕ) (d : Fin s → ℕ) (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a)
    (ω : Fin s → (𝓀[w.adicCompletion E])ˣ →* ℂˣ) (ψ : (𝓀[w.adicCompletion E])ˣ →* Multiplicative (ZMod (l ^ N))) (n : Fin s → ℕ),
    CongFor l ι N m (fun ξ => TypeW w A 1 (blockChar e fun b => ω b * (ξ.comp ψ) ^ n b)) fun _ => True

def EllNeat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C →
    ∀ (D : Type) [AddCommGroup D] (lam : C →* Multiplicative D), NearOne lam → RatNeat lam →
    ∃ ℓ : UA E a → Multiplicative D, (∀ g, ∀ x ∈ infU E a, ℓ (g * x) = ℓ g) ∧ (∀ g (c : C), ℓ (g * c) = ℓ g * lam c) ∧
      ∀ F : Multiplicative D → ℂ, IsAutFormU fun g => F (ℓ g)

def NeatOfPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)), IsLevel C → ∀ u, TorsFreeAt C u →
    ∀ g : UA E a, ∀ γ ∈ ratU E a, ∀ c ∈ C, ∀ x ∈ infU E a, γ * g = g * c * x → c = 1

def FormIn : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (lam : (E →+* ℂ) → DomWeight a) (Y U : Submodule ℂ (UA E a → ℂ)),
    (∀ x ∈ infU E a, ∀ φ ∈ Y, RU E a x φ ∈ Y) → OfVec lam (· ∈ Y) U →
    ∃ (W : Wt E a) (f : algForms W), (∀ τ, W.at τ = lam τ) ∧ f ≠ 0 ∧ ∀ v, f.1 v ∈ U ∧ f.1 v ∈ Y

def DecompKill : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (W : Wt E a) (f : algForms W),
    ∃ (I : Finset (AutSub E a)) (F : AutSub E a → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ f = ∑ π ∈ I, F π ∧
      ∀ T : Module.End ℂ (UA E a → ℂ), (∀ U, IsAutRepU U → ∀ φ ∈ U, T φ ∈ U) → ∀ v, T (f.1 v) = 0 → ∀ π ∈ I, T ((F π).1 v) = 0

def LevelW : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
    ∀ K : Subgroup (UA E a), IsLevelAway w K → ∀ J : Subgroup (GL (Fin a) (w.adicCompletion E)),
    IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) → IsCompact (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ∃ (C : Subgroup (UA E a)) (p : C →* K), IsLevel C ∧ K ≤ C ∧ (∀ x ∈ locU a w, cLoc w x ∈ J → x ∈ C) ∧ (∀ c ∈ C, cLoc w c ∈ J) ∧
      Continuous p ∧ (∀ c : C, c.1 ∈ K → (p c).1 = c.1) ∧ (∀ c : C, c.1 ∈ locU a w → p c = 1) ∧
      ∀ c : C, ((p c).1)⁻¹ * c.1 ∈ locU a w

def RelChar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)) (χ ψ : C →* ℂˣ) (φ : UA E a → ℂ),
    Rel (charRel χ) ψ φ ↔ ∀ c : C, RU E a c φ = ((χ * ψ) c : ℂ) • φ

def NearOneLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (C : Subgroup (UA E a)) (w : HeightOneSpectrum (𝓞 E))
    (J : Subgroup (GL (Fin a) (w.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w.adicCompletion E))) →
    ∀ (hC : ∀ c ∈ C, cLoc w c ∈ J) (D : Type) [Group D] (lam : J →* D), IsOpen (lam.ker : Set J) →
    NearOne (lam.comp (((cLoc w).comp C.subtype).codRestrict J fun c => hC c.1 c.2))

def BlockOpen : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s a : ℕ) (d : Fin s → ℕ)
    (e : (Σ b : Fin s, Fin (d b)) ≃ Fin a) (M : Type) [CommGroup M] (ω : Fin s → (𝓀[k])ˣ →* M),
    IsOpen ((blockChar e ω).ker : Set (parahoric k e))

end UpperTheory.Gal.CharacterCongruences

end
