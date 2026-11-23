import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.PlaneGramData

def geZ (x : WithTop ℤ) (t : ℝ) : Prop := ∀ k : ℤ, x = (k : WithTop ℤ) → t ≤ (k : ℝ)

def geQ (x : WithTop ℚ) (t : ℝ) : Prop := ∀ q : ℚ, x = (q : WithTop ℚ) → t ≤ (q : ℝ)

def leQ (x : WithTop ℚ) (t : ℝ) : Prop := ∃ q : ℚ, x = (q : WithTop ℚ) ∧ (q : ℝ) ≤ t

def HidaSetting (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  Nonempty (UniformizedDVR p O) ∧ ∃ n' : ℕ, AdmissibleDVR p n' O

def atLetter {ι : Type*} {r : ℕ} (i : ι) (be : Fin r → ℕ) : ι × Fin r →₀ ℕ := ∑ a, Finsupp.single (i, a) (be a)

def glE (K : Type*) [Field K] {ι : Type*} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι) :
    GLOps r K (MvPolynomial (ι × Fin r) K) := fun a b => glAct K LL S a b

def IsotypicValuationAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (r : ℕ) [NeZero r] (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    (∀ F G : MvPolynomial (ι × Fin r) (KK O),
      valS LL S (F * G) = valS LL S F + valS LL S G ∧
      min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G)) ∧
    ∀ (d : ι → ℕ) (th : ℤ),
      ((Pol (KK O) r d : Set (MvPolynomial (ι × Fin r) (KK O))) ∩ ASet LL S th) =
        (((⨆ (ν : Fin r → ℤ) (_ : th ≤ ν (lastIdx r)), isoSub (glE (KK O) LL S) ν :
          Submodule (KK O) (MvPolynomial (ι × Fin r) (KK O)))) : Set (MvPolynomial (ι × Fin r) (KK O))) ∩
          (Pol (KK O) r d : Set (MvPolynomial (ι × Fin r) (KK O)))

def CoordinateMultiplicationAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (r : ℕ) [NeZero r] (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    (∀ (i : ι) (a : Fin r),
      (LL.vec i = true → geZ (valS LL S (X (i, a) : MvPolynomial (ι × Fin r) (KK O))) 0) ∧
      (LL.vec i = false → geZ (valS LL S (X (i, a) : MvPolynomial (ι × Fin r) (KK O))) (-1))) ∧
    (∀ (i : ι) (be : Fin r → ℕ) (F : MvPolynomial (ι × Fin r) (KK O)),
      (LL.vec i = true →
        valS LL S F ≤ valS LL S (divDer (atLetter i be) F) + (((∑ a, be a : ℕ) : ℤ) : WithTop ℤ)) ∧
      (LL.vec i = false → valS LL S F ≤ valS LL S (divDer (atLetter i be) F)))

def EnlargingLettersAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (r : ℕ) [NeZero r] (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    (∀ V : Set ι, (∀ i ∈ V, LL.vec i = true) →
      ∀ F : MvPolynomial (ι × Fin r) (KK O), valS LL S F ≤ valS LL (S ∪ V) F) ∧
    (∀ (V : Finset ι) (d : ι → ℕ), (↑V : Set ι) ⊆ S → (∀ i ∈ V, LL.vec i = true) →
      ∀ F ∈ Pol (KK O) r d,
        valS LL S F ≤ valS LL (S \ (↑V : Set ι)) F + (((∑ i ∈ V, d i : ℕ) : ℤ) : WithTop ℤ))

def ValuationStabilityAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop := CoordinateMultiplicationAtRing O ∧ EnlargingLettersAtRing O

def PathColumnBasisAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (N r : ℕ) [NeZero r] (LL : Letters (Fin N)) (d : Fin N → ℕ),
    LinearIndependent O (fun x : {x : PPath r N LL d × (ℤ → Finset (Fin r)) // IsSt x.1.mu x.2} =>
      Psi O x.1.1.mu x.1.2) ∧
    Submodule.span O {G | ∃ P : PPath r N LL d, ∃ I : ℤ → Finset (Fin r), IsSt P.mu I ∧ G = Psi O P.mu I} =
      Pol O r d

def PathSpanAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (N r : ℕ) [NeZero r] (LL : Letters (Fin N)) (d : Fin N → ℕ),
    (∀ th M : Fin N → ℤ, Formalism.MainNotions.CovariantDegrees.A3at O N r LL d th M) ∧
    ∀ (P : PPath r N LL d) (I : ℤ → Finset (Fin r)), IsSt P.mu I → ∀ i : Fin N,
      ((P.mu i.succ (lastIdx r) : ℤ) : WithTop ℤ) ≤ valS LL {j | j ≤ i} (Psi O P.mu I)

def ColumnDegreeBoundAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (N r : ℕ) [NeZero r] (LL : Letters (Fin N)) (d : Fin N → ℕ) (P : PPath r N LL d),
    (∀ (c : ℤ) (Jc : Finset (Fin r)) (i : Fin N), ∀ m ∈ (Kcol O P.mu c N Jc).support,
      multideg m i = if IsUsed P.mu c i then 1 else 0) ∧
    (∀ i : Fin N, ((colRange P.mu).filter fun c => IsUsed P.mu c i).card = d i) ∧
    (∀ (c : ℤ) (i : Fin N), IsUsed P.mu c i → c ∈ colRange P.mu) ∧
    (∀ c : ℤ, 1 ≤ c → ∀ i : Fin (N + 1),
      P.h i c ≤ (Finset.univ.filter fun j : Fin N => j.val < i.val ∧ LL.vec j = true ∧ IsUsed P.mu c j).card) ∧
    (∀ c : ℤ, c ≤ 0 → (∀ i, IsUsed P.mu c i → LL.vec i = true) →
      ∀ I : ℤ → Finset (Fin r), IsSt P.mu I → Kcol O P.mu c N (I c) = 1)

def PolynomialSpanAtRing (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop := PathColumnBasisAtRing O ∧ PathSpanAtRing O ∧ ColumnDegreeBoundAtRing O

def IsFockProj {K : Type*} [Field K] {ι : Type*} {r : ℕ} (d : ι → ℕ) (U : Set (MvPolynomial (ι × Fin r) K))
    (π : MvPolynomial (ι × Fin r) K →ₗ[K] MvPolynomial (ι × Fin r) K) : Prop :=
  (∀ F ∈ Pol K r d, π F ∈ Pol K r d ∧ π F ∈ U) ∧ (∀ F ∈ Pol K r d, F ∈ U → π F = F) ∧
  ∀ F ∈ Pol K r d, ∀ G ∈ Pol K r d, fock (π F) G = fock F (π G)

def AK {K : Type*} [Field K] {ι : Type*} {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι) (d : ι → ℕ) (th : ℤ) :
    Set (MvPolynomial (ι × Fin r) K) :=
  (Pol K r d : Set (MvPolynomial (ι × Fin r) K)) ∩ ASet LL S th

def FockProjectorAtRing (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (r : ℕ) [NeZero r] (ι : Type) [Fintype ι] (LL : Letters ι) (d : ι → ℕ) (S : Set ι) (th : ℤ),
    (∃ π, IsFockProj d (AK (K := KK O) (r := r) LL S d th) π) ∧
    ∀ π, IsFockProj d (AK (K := KK O) (r := r) LL S d th) π →
      (∀ S' : Set ι, (S ⊆ S' ∨ Disjoint S S') →
        (∀ (a b : Fin r), ∀ F ∈ Pol (KK O) r d,
          π (glAct (KK O) LL S' a b F) = glAct (KK O) LL S' a b (π F)) ∧
        (∀ (th' : ℤ) π', IsFockProj d (AK (K := KK O) (r := r) LL S' d th') π' →
          ∀ F ∈ Pol (KK O) r d, π (π' F) = π' (π F))) ∧
      ∀ F ∈ Pol (KK O) r d, InBB (O := O) p F →
        geQ (vBB (O := O) p (π F))
          (-(((r.choose 2 : ℕ) : ℝ) * Real.logb p (2 * ((degIn d S : ℕ) : ℝ) + r)))

def gamDig {r : ℕ} (P : ℕ) (rho be : Fin r → ℕ) : ℚ := ∏ a, cUnit P (be a) * dUnit P (be a) (rho a)

def binomComb {O K : Type*} [CommRing O] [Field K] [Algebra O K] {σ : Type*} [Fintype σ]
    (lam : (σ → ℕ) →₀ O) (be : σ → ℕ) : K :=
  ∑ m ∈ lam.support, algebraMap O K (lam m) * ∏ a, (((be a).choose (m a) : ℕ) : K)

def FactorialDigitSplitAtRing (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (g r : ℕ) (rho : Fin r → ℕ), (∀ a, rho a < p ^ g) →
    (∀ be : Fin r → ℕ, (∏ a, ((rho a + p ^ g * be a).factorial : ℚ)) =
        (∏ a, ((rho a).factorial : ℚ)) * ((p ^ g).factorial : ℚ) ^ (∑ a, be a) *
          (∏ a, ((be a).factorial : ℚ)) * gamDig (p ^ g) rho be) ∧
    (∀ be : Fin r → ℕ, gamDig (p ^ g) rho be ≠ 0 ∧ padicValRat p (gamDig (p ^ g) rho be) = 0) ∧
    ∀ c : ℕ, 1 ≤ c → ∀ ε : Bool, ∃ lam : (Fin r → ℕ) →₀ O, (∀ m ∈ lam.support, ∑ a, m a ≤ 4 * c) ∧
      ∀ be : Fin r → ℕ,
        geQ (vK p ((if ε then ((gamDig (p ^ g) rho be : ℚ) : KK O) else ((gamDig (p ^ g) rho be : ℚ) : KK O)⁻¹) -
          binomComb (K := KK O) lam be)) (c : ℝ)

def monoL {K : Type*} [Field K] {r : ℕ} (e : Fin r → ℕ) : MvPolynomial (Unit × Fin r) K :=
  ∏ a, X ((), a) ^ e a

def DerivativeCongruenceAtRing (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (g r : ℕ) (M rho : Fin r → ℕ), (∀ a, rho a < p ^ g) → ∀ c : ℕ, 1 ≤ c →
    ∃ (T : Finset ((Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ)))
      (coef : (Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ) → O),
      (∀ t ∈ T, (∀ a, t.1 a < p ^ g) ∧
        ((∑ a, t.2.2 a : ℕ) : ℝ) ≤ ((∑ a, M a : ℕ) : ℝ) / ((p ^ g : ℕ) : ℝ) + c) ∧
      ∀ (be : Fin r → ℕ) (mo : Unit × Fin r →₀ ℕ),
        geQ (vK p ((divDer (atLetter () M) (monoL (K := KK O) fun a => rho a + p ^ g * be a) -
            ∑ t ∈ T, C (algebraMap O (KK O) (coef t) * ∏ a, (((be a).choose (t.2.2 a) : ℕ) : KK O)) *
              monoL (K := KK O) t.1 * monoL (K := KK O) (fun a => p ^ g * (be a - t.2.2 a + t.2.1 a))).coeff mo)) (c : ℝ)

def AdmAt (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  IsotypicValuationAtRing O ∧ ValuationStabilityAtRing O ∧ PolynomialSpanAtRing O ∧ FockProjectorAtRing p O ∧ FactorialDigitSplitAtRing p O ∧ DerivativeCongruenceAtRing p O

def adm1 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → IsotypicValuationAtRing O

def WittOrbitTheorem (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → CoordinateMultiplicationAtRing O

def adm2b (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → EnlargingLettersAtRing O

def adm2 (D : Formalism.BasicNotions.D7) : Prop := WittOrbitTheorem D ∧ adm2b D

def adm3a (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → PathColumnBasisAtRing O

def adm3b (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → PathSpanAtRing O

def IntegralityRemainder (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → ColumnDegreeBoundAtRing O

def adm3 (D : Formalism.BasicNotions.D7) : Prop := adm3a D ∧ adm3b D ∧ IntegralityRemainder D

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → FockProjectorAtRing p O

def adm5 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → FactorialDigitSplitAtRing p O

def adm6 (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → DerivativeCongruenceAtRing p O

abbrev TL (J : ℕ) (nL : ZMod J → ℕ) (r : ℕ) := Σ j : ZMod J, Fin (nL j) ⊕ Fin r

inductive ML (J : ℕ) (nL : ZMod J → ℕ) (r : ℕ) : Type
  | ll (j : ZMod J) (l : Fin (nL j))
  | lab (j : ZMod J) (m : Fin r)
  | wc (j : ZMod J) (m : Fin r)
  | tp (j : ZMod J) (m : Fin r) (h : 1 ≤ m.val)

def binomCombF {O K : Type*} [CommRing O] [Field K] [Algebra O K] {σ : Type*}
    (lam : (σ →₀ ℕ) →₀ O) (al : σ →₀ ℕ) : K :=
  ∑ m ∈ lam.support, algebraMap O K (lam m) * ∏ v ∈ m.support, (((al v).choose (m v) : ℕ) : K)

structure SignedChainData (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (r J : ℕ) where
  nL : ZMod J → ℕ
  sgn : ∀ j, Fin (nL j) → Bool
  d : TL J nL r → ℕ
  gP : ZMod J → Fin r → ℕ
  nch : ZMod J → ℕ
  chain : ∀ j, Fin (nch j) → Set (Fin (nL j) ⊕ Fin r)
  chain_mono : ∀ j, StrictMono (chain j)
  chain_w : ∀ j i (m : Fin r), Sum.inr m ∈ chain j i
  th : ∀ j, Fin (nch j) → ℝ
  sl : ∀ j, Fin (nch j) → ℝ
  thL : ZMod J → Fin r → ℝ
  thL_pos : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m
  ga : (TL J nL r × Fin r →₀ ℕ) → O
  ga_unit : ∀ al, IsUnit (ga al)
  ga_dig : ∀ k : ℕ, 1 ≤ k → ∀ ε : Bool, ∃ lam : (TL J nL r × Fin r →₀ ℕ) →₀ O,
    (∀ m ∈ lam.support, (m.sum fun _ e => e) ≤ 6 * k) ∧
    ∀ al : TL J nL r × Fin r →₀ ℕ,
      geQ (vK p ((if ε then algebraMap O (KK O) (ga al) else (algebraMap O (KK O) (ga al))⁻¹) -
        binomCombF (K := KK O) lam al)) (k : ℝ)
  c : ℝ
  one_le_c : 1 ≤ c

namespace SignedChainData

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}
variable (Dt : SignedChainData p O r J)

def trueLet : Letters (TL J Dt.nL r) where
  vec x := match x with
    | ⟨j, Sum.inl l⟩ => Dt.sgn j l
    | ⟨_, Sum.inr _⟩ => true

def modelLet : Letters (ML J Dt.nL r) where
  vec x := match x with
    | ML.ll j l => Dt.sgn j l
    | _ => true

def P (j : ZMod J) (m : Fin r) : ℕ := p ^ Dt.gP j m

def ph : MvPolynomial (ML J Dt.nL r × Fin r) (KK O) →ₐ[KK O] MvPolynomial (TL J Dt.nL r × Fin r) (KK O) :=
  aeval fun v => match v with
    | (ML.ll j l, a) => X (⟨j, Sum.inl l⟩, a)
    | (ML.lab j m, a) => X (⟨j, Sum.inr m⟩, a)
    | (ML.wc j m, a) => X (⟨j, Sum.inr m⟩, a) ^ Dt.P j m
    | (ML.tp j m _, a) => X (⟨j, Sum.inr m⟩, a)

def digOK (rho : (ZMod J × Fin r) × Fin r → ℕ) (mo : TL J Dt.nL r × Fin r →₀ ℕ) : Prop :=
  ∀ (j : ZMod J) (m : Fin r) (a : Fin r), mo (⟨j, Sum.inr m⟩, a) % Dt.P j m = rho ((j, m), a)

def liftVar : TL J Dt.nL r × Fin r → ML J Dt.nL r × Fin r
  | (⟨j, Sum.inl l⟩, a) => (ML.ll j l, a)
  | (⟨j, Sum.inr m⟩, a) => (ML.wc j m, a)

def liftExp (mo : TL J Dt.nL r × Fin r →₀ ℕ) : TL J Dt.nL r × Fin r → ℕ
  | (⟨j, Sum.inl l⟩, a) => mo (⟨j, Sum.inl l⟩, a)
  | (⟨j, Sum.inr m⟩, a) => mo (⟨j, Sum.inr m⟩, a) / Dt.P j m

def Fdig (rho : (ZMod J × Fin r) × Fin r → ℕ) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) :
    MvPolynomial (ML J Dt.nL r × Fin r) (KK O) :=
  ∑ mo ∈ F.support.filter (Dt.digOK rho),
    C (F.coeff mo) * ∏ v ∈ mo.support, MvPolynomial.X (Dt.liftVar v) ^ Dt.liftExp mo v

def levToML (j : ZMod J) : Fin (Dt.nL j) ⊕ Fin r → ML J Dt.nL r
  | Sum.inl l => ML.ll j l
  | Sum.inr m => ML.wc (j - 1) m

def chainML (j : ZMod J) (i : Fin (Dt.nch j)) : Set (ML J Dt.nL r) := Dt.levToML j '' Dt.chain j i

def TSet (j : ZMod J) (m : Fin r) : Set (TL J Dt.nL r) :=
  {x | ∃ l, x = ⟨j, Sum.inl l⟩} ∪ {x | ∃ m' : Fin r, m < m' ∧ x = ⟨j, Sum.inr m'⟩}

def linkML (j : ZMod J) (m : Fin r) : Set (ML J Dt.nL r) :=
  {x | ∃ m'' : Fin r, x = ML.wc (j - 1) m''} ∪ {x | ∃ l, x = ML.ll j l} ∪
    {x | ∃ (m' : Fin r) (h : 1 ≤ m'.val), m < m' ∧ x = ML.tp j m' h}

def dLL (j : ZMod J) : ℕ := ∑ l : Fin (Dt.nL j), Dt.d ⟨j, Sum.inl l⟩

def Bform (F G : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) : KK O :=
  fock F (∑ mo ∈ G.support, monomial mo (algebraMap O (KK O) (Dt.ga mo) * G.coeff mo))

variable [NeZero J]

def eP : ℝ := (r : ℝ) ^ 2 * lg p r (2 * ∑ x, Dt.d x)

def Dm : ℝ := ((∑ j, Dt.nch j : ℕ) : ℝ) * Dt.eP

def Dl : ℝ := (J : ℝ) * ((r : ℝ) - 1) * Dt.eP

def kp : ℝ := kap p r Dt.d

def EE (CE : ℝ) : ℝ := Dt.Dm + Dt.Dl + CE * Dt.kp

def n0 : ℝ := (padicValNat p (∏ x, (Dt.d x).factorial) : ℝ) / 2

def Hyp (CH : ℝ) : Prop :=
  ∀ (j : ZMod J) (m : Fin r) (i : Fin (Dt.nch (j + 1))),
    (r : ℝ) * (Dt.dLL j : ℝ) / (Dt.P j m : ℝ) + CH * (r : ℝ) * Dt.c ≤ Dt.sl (j + 1) i

variable [NeZero r]

def XX (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) : Prop :=
  F ∈ Pol (KK O) r Dt.d ∧
  (∀ (rho : (ZMod J × Fin r) × Fin r → ℕ) (j : ZMod J) (i : Fin (Dt.nch j)),
    geZ (valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho F)) (Dt.th j i)) ∧
  ∀ (j : ZMod J) (m : Fin r), m.val + 2 ≤ r → geZ (valS Dt.trueLet (Dt.TSet j m) F) (Dt.thL j m)

def YY (C6 C18 : ℝ) (G : MvPolynomial (ML J Dt.nL r × Fin r) (KK O)) : Prop :=
  (∀ (j : ZMod J) (i : Fin (Dt.nch j)),
    geZ (valS Dt.modelLet (Dt.chainML j i) G) (Dt.th j i - Dt.sl j i - C6 * Dt.c)) ∧
  ∀ (j : ZMod J) (m : Fin r), m.val + 2 ≤ r →
    geZ (valS Dt.modelLet (Dt.linkML j m) G) (Dt.thL j m - C18 * Dt.c)

end SignedChainData

open SignedChainData in

def ProjectionDerivativeEstimate (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (CH CE C6 C18 : ℝ) : Prop :=
  ∀ (r : ℕ) [NeZero r] (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J),
    Dt.Hyp CH → 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c →
    ∀ F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O), Dt.XX F → vBB (O := O) p F = 0 →
      ∃ G R : MvPolynomial (ML J Dt.nL r × Fin r) (KK O),
        (∀ mo, geQ (vK p (G.coeff mo)) 0) ∧ Dt.YY C6 C18 G ∧
        (∀ mo, geQ (vK p (R.coeff mo)) (Dt.c - Dt.EE CE)) ∧
        (∀ mo ∈ G.support ∪ R.support, Dt.ph (monomial mo 1) ∈ Pol (KK O) r Dt.d) ∧
        geQ (vBB (O := O) p (Dt.ph (G + R))) (Dt.n0 - Dt.kp) ∧
        leQ (vK p (Dt.Bform F (Dt.ph (G + R)))) (Dt.EE CE + 2 * Dt.kp + Dt.n0 - Dt.kp)

def aux₃ (_D : Formalism.BasicNotions.D7) (CH CE C6 C18 : ℝ) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O → ProjectionDerivativeEstimate p O CH CE C6 C18

def admitted (D : Formalism.BasicNotions.D7) : Prop := adm1 D ∧ adm2 D ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D

def Stmt (_D : Formalism.BasicNotions.D7) (CH CE C6 C18 : ℝ) : Prop :=
  ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O], HidaSetting p O →
    AdmAt p O → ProjectionDerivativeEstimate p O CH CE C6 C18

def ClosedFormOfAdmitted (D : Formalism.BasicNotions.D7) : Prop :=
  ∃ FormalChartAtZero CE C6 C18 : ℝ, 0 < FormalChartAtZero ∧ 0 < CE ∧ 0 < C6 ∧ 0 < C18 ∧ ∀ CH : ℝ, FormalChartAtZero ≤ CH → Stmt D CH CE C6 C18

def admF1 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)
def admF2 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i)
def admF3 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  admF1 Fm ∧ admF2 Fm ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm

def OrbitValuationBound {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CH CE C6 C18 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, aux₃ (Fm.D x i) CH CE C6 C18

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CH CE C6 C18 : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, Stmt (Fm.D x i) CH CE C6 C18

def DerivativeStatementDesign (Fm : Formalism.MainNotions.DFamP) (CH CE C6 C18 : ℝ) : Prop :=
  ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52), KudlaFamilyStatement (Fm ε h0 h1) CH CE C6 C18

def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ FormalChartAtZero CE C6 C18 : ℝ, 0 < FormalChartAtZero ∧ 0 < CE ∧ 0 < C6 ∧ 0 < C18 ∧
    ∃ x0 : ℝ, ∀ CH : ℝ, FormalChartAtZero ≤ CH → ∀ x, x0 ≤ x → ∀ i : Fm.Ix x, Stmt (Fm.D x i) CH CE C6 C18

def DerivativeStatementClosedDesign (Fm : Formalism.MainNotions.DFamP) : Prop :=
  ∃ FormalChartAtZero CE C6 C18 : ℝ, 0 < FormalChartAtZero ∧ 0 < CE ∧ 0 < C6 ∧ 0 < C18 ∧
    ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 52),
      ∃ x0 : ℝ, ∀ CH : ℝ, FormalChartAtZero ≤ CH → ∀ x, x0 ≤ x → ∀ i : (Fm ε h0 h1).Ix x, Stmt ((Fm ε h0 h1).D x i) CH CE C6 C18

end Formalism.MainNotions.PlaneGramData
