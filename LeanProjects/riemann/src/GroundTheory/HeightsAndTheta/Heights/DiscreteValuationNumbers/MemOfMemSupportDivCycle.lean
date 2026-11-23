import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import GroundTheory.ArithmeticGeometry.IwasawaModules.SpanFinrankMaximalIdealLeTwo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR

open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section Lengths

def colonMod {A : Type*} [CommRing A] (a b : A) : Submodule A (A ⧸ Ideal.span {a}) :=
  Submodule.map (Ideal.span {a}).mkQ ((Ideal.span {a}).colon (Ideal.span {b}) : Submodule A A)

def NumbersBirationalInvariance.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A)
          (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
            p.asIdeal ≠ IsLocalRing.maximalIdeal A),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))

def NumbersBirationalInvariance.LocalRingStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))

def NumbersSymmetry.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 → length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    length A (A ⧸ Ideal.span {a, b}) = length A (colonMod a b) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
          length (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal ⧸
                Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) ∧
      Nonempty (colonMod a b ≃ₗ[A] colonMod b a)

end Lengths

section Models

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)

def genMap : MRingOver O ι →+* MRingOver (FractionRing O) ι :=
  MvPolynomial.map (algebraMap O (FractionRing O))

def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)

def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z

def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)

def genFib (P : Ideal (MRingOver O ι)) : Ideal (MRingOver (FractionRing O) ι) :=
  P.map genMap

def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)

def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)

def IsVerticalDiv (ϖ : O) (P : Ideal (MRingOver O ι)) (b : K → ℤ) (f g : MRingOver O ι) : Prop :=
  (∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ ∀ k, (α k : ℤ) - β k = b k) ∧
    g ∉ P ∧ ∀ W ∈ (divO P f g).support, C ϖ ∈ W

def IsRegSection (P : Ideal (MRingOver O ι)) (c : K → ℕ) (s : MRingOver O ι) : Prop :=
  IsMultiHomog s c ∧ s ∉ P

end Models

def NumbersMultilinearity.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d : ℕ) (a : Fin d → K → ℤ)
      (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (IK : IFamily (FractionRing O) ι),
      IsModelOver P d → IsFieldIntersection Iκ → IsFieldIntersection IK →
      redEval (fun W => Iκ W d a) (intCyc (specCyc ϖ P)) = IK (genFib P) d a

open Classical in

def NumbersProjectionFormula.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b : K → ℤ) (f g : MRingOver O ι) (c : K → ℕ)
      (s : MRingOver O ι) (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsRegSection P c s →
      IsFieldIntersection Iκ →
      (∀ H ∈ (divCycle P s).support, C ϖ ∉ H → IsVerticalDiv ϖ H b f g) →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L (fun k => (c k : ℤ))))
          (divO P f g) =
        (divCycle P s).sum fun H m =>
          if C ϖ ∈ H then (m : ℤ) * Iκ (H.map redMap) (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)
          else (m : ℤ) * redEval (fun G => Iκ G n L) (divO H f g)

def VerticalDivisorsCommuting.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRingOver O ι)
      (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsVerticalDiv ϖ P b' f' g' →
      IsFieldIntersection Iκ →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b')) (divO P f g) =
        redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (divO P f' g')

section Inhabitants

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem mem_of_mem_support_divCycle {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι} (h : W ∈ (divCycle P s).support) :
    W.IsPrime ∧ s ∈ W := by
  classical
  have hW : W ∈ divSupp P s := by
    by_contra hn
    apply Finsupp.mem_support_iff.mp h
    simp only [divCycle]
    rw [Finsupp.ofSupportFinite_coe, if_neg hn]
  exact ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))⟩

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem mem_of_mem_support_divO {P W : Ideal (MRingOver O ι)} {f g : MRingOver O ι}
    (h : W ∈ (divO P f g).support) :
    W ∈ (divCycle P f).support ∨ W ∈ (divCycle P g).support := by
  classical
  rcases Finset.mem_union.mp (Finsupp.support_sub h) with h1 | h1
  · exact Or.inl (Finsupp.support_mapRange h1)
  · exact Or.inr (Finsupp.support_mapRange h1)

omit [Fintype K] [IsDomain O] [IsDiscreteValuationRing O] in

theorem isMultiHomog_C (a : O) : IsMultiHomog (C a : MRingOver O ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
  split_ifs at hm with h0
  · subst h0; simp
  · exact absurd rfl hm

theorem isVerticalDiv_unif (ϖ : O) {P : Ideal (MRingOver O ι)} (hP : P.IsPrime) :
    IsVerticalDiv ϖ P 0 (C ϖ) 1 := by
  refine ⟨⟨0, 0, isMultiHomog_C ϖ, by simpa using isMultiHomog_C (ι := ι) (1 : O), by simp⟩,
    hP.one_notMem, fun W hW => ?_⟩
  rcases mem_of_mem_support_divO hW with h | h
  · exact (mem_of_mem_support_divCycle h).2
  · exact absurd (mem_of_mem_support_divCycle h).2 (mem_of_mem_support_divCycle h).1.one_notMem

variable (O) in

theorem isModelOver_line : IsModelOver (⊥ : Ideal (MRingOver O (fun _ : Unit => Fin 2))) 1 := by
  refine ⟨⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun k => ⟨0, by simp [X_ne_zero]⟩⟩, ?_, ?_⟩
  · exact Ideal.comap_bot_of_injective _ (MvPolynomial.C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
    rfl

end Inhabitants

section LengthInhabitants

open IsLocalRing

end LengthInhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
