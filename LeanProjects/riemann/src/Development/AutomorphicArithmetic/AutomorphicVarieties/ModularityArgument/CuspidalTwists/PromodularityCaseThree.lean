import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu

def aA : Finset (ℤ × ℤ) := {-wBe, -wPs, -wTh}

def yY : Finset (ℤ × ℤ) := {wBe, -wBe, wTh, -wTh}

def InA {ι Γ R : Type} [Group Γ] [CommRing R] (P : PD ι Γ R) : Prop := Supp aA P.r ∧ ∀ v, P.n v 1 0 ≠ 0

section

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)

def Good4 (P : PD Φ.ι Γ R) : Prop :=
  Φ.Good a P ∨ (InA P ∧ Ent P.r (-wPs)) ∨ (InA P ∧ Ent P.r (-wBe) ∧ Ent P.r (-wTh))

def Chain4 [TopologicalSpace Γ] (c c' : PD Φ.ι Γ R) : Prop :=
  Good4 Φ a c ∧ Relation.ReflTransGen (fun x y => Good4 Φ a y ∧ Φ.Linked a x y) c c'

end

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

structure QuadOn (T : Tower D) (K' : IntermediateField ℚ Ω) [NumberField K'] : Prop where
  deg : Module.finrank ℚ K' = 2
  imag : IsTotallyComplex K'
  disc : ¬ (l : ℤ) ∣ discr K'
  split : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup
  splS : ∀ p ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ K'.fixingSubgroup
  on : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup → T.rb wAl g = 1
  off : ∀ g : G T.F Ω, resQ T.F g ∉ K'.fixingSubgroup → T.rb wAl g = -1

structure Four (T : Tower D) : Prop where
  five : 5 ≤ l
  sb : D.Sb = ∅
  psi : ∃ m : ℕ, l.Coprime m ∧ D.ψ ^ m = 1
  quad : ∃ (K' : IntermediateField ℚ Ω) (_ : NumberField K'), QuadOn T K'

end

def HFit : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), Ctx3 D → T.Ok → Four T → T.Fit

def RankFourTensorFactorization : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ : Tower D),
    Ctx3 D → T₀.Ok → Four T₀ → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l),
    ∃ (w : ℕ) (s : PD T₀.ι (G T₀.F Ω) 𝔞.k), w.Prime ∧ T₀.Splits w ∧ (T₀.fr {w}).IsRes (𝔞.red c) s ∧ Supp nM s.r ∧
      ∀ (T : Tower D) (hT : T₀.Le T), T.Ok → Dies l w T.F →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧ T₀.OverT hT s (Q.map (𝔞.red c₁)) ∧
          InA (Q.map (𝔞.red c₁)) ∧ Ent (Q.map (𝔞.red c₁)).r (-wBe) ∧ Ent (Q.map (𝔞.red c₁)).r (-wTh)

def ExistsTensorFactorTower : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D → ∀ pr, LabOk D pr → ∃ T : Tower D, T.pr = pr ∧ T.Ok ∧ Four T ∧ TameL l T.F

def RedTanA : Prop :=
  ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (a : O →+* k), Φ.Ok a → ∀ d C : ℕ, Φ.Bounds a d C → ∀ c : PD Φ.ι Γ k, Φ.IsRes a c → InA c →
    ∀ S ∈ redTypes, (-wPs ∈ S ∨ (-wBe ∈ S ∧ -wTh ∈ S ∧ S ≠ yY)) → Supp S c.r →
      Module.rank k (Submodule.span k (Φ.Tan S c)) ≤ d + 20 * C

def RedA : Prop :=
  ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ d C : ℕ, Φ.Bounds ((residue Λ).comp a) d C → ∀ c : PD Φ.ι Γ (ResidueField Λ),
    Φ.IsRes ((residue Λ).comp a) c → InA c → (Ent c.r (-wPs) ∨ (Ent c.r (-wBe) ∧ Ent c.r (-wTh))) →
    ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ S ∈ redTypes, S ≠ yY →
      ringKrullDim (R ⧸ redIdeal S P.r) ≤ (d + 20 * C + 1 : ℕ)

def YCoin : Prop :=
  ∀ {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {K : Type} [Field K] (a : O →+* K) (P : PD Φ.ι Γ K), Φ.IsPair a P →
    Supp yY P.r → ∀ v, P.n v 1 0 ≠ 0 →
      (∀ s ∈ Φ.Gv v, P.ψ v 0 s = P.ψ v 1 s) ∨ ∀ s ∈ Φ.Gv v, P.ψ v 1 s = P.ψ v 3 s

def TorusY : Prop :=
  ∀ {Γ K : Type} [Group Γ] [Field K] (r : Γ →* M4 K) (g0 : Γ), (r g0).IsDiag → (∀ i j, i ≠ j → r g0 i i ≠ r g0 j j) →
    Supp yY r → Ent r wBe → Ent r (-wBe) → Ent r wTh → Ent r (-wTh) →
    ∃ s t : K, ∀ E : Subfield K, s ∈ E → t ∈ E → (∀ g, (r g).trace ∈ E) → (∀ i, r g0 i i ∈ E) → ∀ g i j, r g i j ∈ E

def FibY : Prop :=
  ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ (X : Space Φ a) (c : PD Φ.ι Γ (ResidueField Λ)), Φ.IsRes ((residue Λ).comp a) c →
    ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (f : X.A →ₐ[Λ] R), Φ.IsDef a c (X.P.map (f : X.A →+* R)) →
    ∀ (q : Ideal R) [q.IsPrime] (r : Γ →* M4 (FractionRing (R ⧸ q))),
      r = mapRep ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp ((Ideal.Quotient.mk q).comp (f : X.A →+* R))) X.P.r →
      Supp yY r → Ent r wBe → Ent r (-wBe) → Ent r wTh → Ent r (-wTh) →
      ringKrullDim (R ⧸ q) ≤ ringKrullDim (X.B ⧸ q.comap ((f : X.A →+* R).comp (algebraMap X.B X.A))) + (2 + 4 * Nat.card Φ.ι : ℕ)

def Ch4 : Prop :=
  CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (ι : PadicAlgCl l ≃+* ℂ) (c' : Coef l) (h : c.O ≤ c'.O)
    (X : Space (T.fr ∅) (inc h)) (J : Ideal X.B), T.PM ι X J → ∀ C : ℕ, (T.fr ∅).Bounds ((residue c'.O).comp (inc h)) T.d C →
    30 * (C + 1) * (C + 1) ≤ T.d → ∀ x : X.A →ₐ[c'.O] ResidueField c'.O,
      (T.fr ∅).IsRes ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      Good4 (T.fr ∅) ((residue c'.O).comp (inc h)) (X.P.map (x : X.A →+* _)) →
      X.SomeIn J (RingHom.ker x) → X.AllIn J (RingHom.ker x)

def ChainDesc4 : Prop :=
  ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (c : Coef l) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (Φ : Fr c.O Γ)
    (s t : PD Φ.ι Γ 𝔞.k), Φ.IsRes (𝔞.red c) s → Chain4 Φ (𝔞.red c) s t → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O →
      ∃ s' t' : PD Φ.ι Γ (ResidueField c'.O), s'.map (𝔞.j c') = s ∧ t'.map (𝔞.j c') = t ∧
        Φ.IsRes ((residue c'.O).comp (inc h)) s' ∧ Chain4 Φ ((residue c'.O).comp (inc h)) s' t'

def ChainIV : Prop :=
  CohomologyHyp → HFit → RankFourTensorFactorization → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T₀ : Tower D), Ctx3 D → T₀.Ok → Four T₀ → TameL l T₀.F →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (c₀ : PD Unit (G ℚ Ω) 𝔞.k), LatShape D T₀.pr (resQ T₀.F T₀.g0) (𝔞.red c) c₀ →
      ∃ T₁ : Tower D, T₀.Le T₁ ∧ TameL l T₁.F ∧ ∀ T : Tower D, T₁.Le T → T.Deep →
        ∃ (c₁ : Coef l) (h : c.O ≤ c₁.O) (Q : PD T.ι (G T.F Ω) c₁.O), T.SeedPair ι h Q ∧
          ∀ c₀' : PD T.ι (G T.F Ω) 𝔞.k, T.OverQ c₀ c₀' → (T.fr ∅).IsRes (𝔞.red c) c₀' →
            Chain4 (T.fr ∅) (𝔞.red c) c₀' (Q.map (𝔞.red c₁))

def PromodularityCaseThree : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → RankFourTensorFactorization → PMEx → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
    ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) r u, KPair D 𝔞 r u → Star (mapRep 𝔞.toK r) → ProMod D ι 𝔞 r

def AutomorphyRankFourMain : Prop :=
  CohomologyHyp → UpperTheory.V.Published.FerreroWashington → HFit → SeedII → RankFourTensorFactorization → PMEx → UpperTheory.V.Aut.Sp4In

end UpperTheory.V.Cu

end
