import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def memFn {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X) : ℂ :=
  (Nat.card {k : K ⧸ KM.subgroupOf K // h * (k.out : X) * y ∈ K₀} : ℕ)

def MemSum : Prop := ∀ (X : Type) [Group X] (K KM K₀ : Subgroup X) (h : X), K₀ ≤ K → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) →
  memFn K KM K₀ h ∈ Hecke ℂ K₀ ∧ (∀ y, memFn K KM K₀ h y ≠ 0 → ∃ k ∈ K, h * k * y ∈ K₀) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K₀, ∀ g, Φ (g * k) = Φ g) → ∀ g,
    hAct K₀ (memFn K KM K₀ h) Φ g = ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹)

def SumDoset : Prop := ∀ (X : Type) [Group X] (K KM : Subgroup X) (h : X), KM ≤ K → KM.relIndex K ≠ 0 →
  (∀ u ∈ KM, h * u * h⁻¹ ∈ K) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) →
    (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ g,
    ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹) =
      ((KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) : ℂ) • hAct K (dosetInd ℂ K h⁻¹) Φ g

def TyLev.Acts {X M : Type} [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X) : Prop :=
  ψ ∈ Hecke ℂ T.K₀ ∧ T.L.pr h = 1 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → hAct T.K₀ ψ Φ = c • hAct T.K₀ (T.tf h) Φ

def TyLev.Triv {X M : Type} [Group X] [Group M] (T : TyLev X M) (K : Subgroup X) : Prop :=
  K ≤ T.K ∧ ∀ k ∈ K, ∀ h, T.ψ ⟨T.L.pr k, h⟩ = 1

def MemAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ K KM : Subgroup X, T.Triv K → L'.Fact K Kw → T.K₀ ≤ K → KM ≤ T.K₀ → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ (t : M') (z h : X), T.Cen z → h⁻¹ = L'.loc t * z →
  (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ T.K₀) →
  T.Acts (memFn K KM T.K₀ h) (KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) (L'.loc t * z)

def MemDeck : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (K : Subgroup X), T.Triv K → ∀ k ∈ K,
  (∀ u ∈ T.K₀, k * u * k⁻¹ ∈ T.K₀) → T.Acts (memFn T.K₀ T.K₀ T.K₀ k) 1 1

def RelOf : Prop := ∀ (X M J : Type) [Group X] [Group M] (T : TyLev X M) (ψ : J → X → ℂ) (c : J → ℂ) (h : J → X) (hu : X) (u' : X → ℂ),
  (∀ j, T.Acts (ψ j) (c j) (h j)) → T.L.pr hu = 1 → u' ∈ Hecke ℂ T.K₀ →
  (∀ i j, conv T.K₀ (T.tf (h i)) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf (h i))) →
  (∀ j, conv T.K₀ (T.tf hu) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf hu)) → conv T.K₀ u' (T.tf hu) = T.tf 1 →
  Spc.Rel (conv T.K₀) ψ (T.tf 1) (T.tf hu) u'

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (t t' : GL (Fin n) (w.adicCompletion E)),
  conv (KGL w n) (dosetInd ℂ (KGL w n) t) (dosetInd ℂ (KGL w n) t') = conv (KGL w n) (dosetInd ℂ (KGL w n) t') (dosetInd ℂ (KGL w n) t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Tr.lv (T : Tr S) (K : Subgroup (GUf E n)) : Subgroup S.G.GAf := K.comap T.sec

def AtApart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal),
  (∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x) ∧
  ∀ (w' : Plc E) (hw' : IsSplitAt w') (hp' : (p : 𝓞 E) ∉ w'.asIdeal), GlobalTheory.Cong.Apart w w' → (T.at hc w hw hp).Apart (T.at hc w' hw' hp')

def LevFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E)))
  (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal), CertificateRingHomMap.cj w ∉ S₀ →
  (w ∈ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (Kw w)) ∧ (w ∉ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (KGL w n))

def IntConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E), 0 < n →
  (sim g ∈ ZU → comp w g ∈ KGL w n → comp (CertificateRingHomMap.cj w) g ∈ KGL (CertificateRingHomMap.cj w) n) ∧
  ((∀ u, comp u g ∈ KGL u n) → sim g ∈ ZU) ∧ {u : Plc E | comp u g ∉ KGL u n}.Finite

def LevRefine : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 0 < n → ∀ (S₀ U : Finset (Plc E))
  (Kw Kw' : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E))), (∀ u ∈ U, u ∉ S₀ ∧ CertificateRingHomMap.cj u ∉ S₀) → (∀ w ∈ S₀, Kw' w = Kw w) →
  (∀ u ∈ U, Kw' u ≤ KGL u n ∧ IsOpen (Kw' u : Set (GL (Fin n) (u.adicCompletion E)))) →
  IsOpen (lev S₀ Kw : Set (GUf E n)) → IsCompact (lev S₀ Kw : Set (GUf E n)) →
  lev (S₀ ∪ U) Kw' ≤ lev S₀ Kw ∧ IsOpen (lev (S₀ ∪ U) Kw' : Set (GUf E n)) ∧ IsCompact (lev (S₀ ∪ U) Kw' : Set (GUf E n))

def KNOpen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsOpen (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n))

def KNIdx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsCommensurated (S.L.KN N) ∧ ∀ K : Subgroup (GUf E n), IsCompact (K : Set (GUf E n)) →
    IsOpen (K : Set (GUf E n)) → (S.L.KN N).relIndex (T.lv K) ≠ 0

def KNBasis : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (O : Subgroup (GUf E n)), IsOpen (O : Set (GUf E n)) → ∃ N : ℕ, 0 < N ∧ N.Coprime p ∧ S.L.KN N ≤ T.lv O

def PPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n), ∃ k : GUf E n, g = T.sec (T.j g) * k ∧ (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) ∧
    (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k = comp w g) ∧ ∀ h, T.sec h * k = k * T.sec h

def HasEigOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (GL (Fin n) E × ℚˣ) V) (Φ : GUf E n → V),
  (∀ (γ : Gam0 E n) g, Φ (rat γ * g) = ξ γ (Φ g)) →
  (∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w n) →
    ∀ g, Φ (g * k) = Φ g) →
  (∃ g₀, Φ g₀ ≠ 0 ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g₀ ∈ KGL w n) →
  ∀ K₀ : Subgroup S.G.GAf, IsCommensurated K₀ → (∀ k ∈ K₀, ∀ h, Φ (T.sec (h * k)) = Φ (T.sec h)) →
  ∀ (J : Type) (ψ : J → S.G.GAf → ℂ) (θ : J → ℂ) (e : S.G.GAf → ℂ), (∀ j, ψ j ∈ Hecke ℂ K₀) → e ∈ Hecke ℂ K₀ →
    hAct K₀ e (fun h => Φ (T.sec h)) = (fun h => Φ (T.sec h)) →
    (∀ j, hAct K₀ (ψ j) (fun h => Φ (T.sec h)) = θ j • fun h => Φ (T.sec h)) →
  Spc.HasEig S.G (V := V) ξ K₀ ψ θ e

end UpperTheory.Gal.W2.Seed
