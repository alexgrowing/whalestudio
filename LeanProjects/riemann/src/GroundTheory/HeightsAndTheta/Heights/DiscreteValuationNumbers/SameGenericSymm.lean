import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u

section Statements

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (Ω : Type*) [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def NumbersCommuteVertical.Statement : Prop :=
  ∀ I : IFamily (kap O) ι, IsFieldIntersection I →
    ∀ (P : Ideal (MRingOver O ι)) (n : ℕ) (L : Fin n → K → ℤ) (b b' : K → ℤ)
      (f g f' g' : MRingOver O ι),
      IsModelOver O P (n + 1) → IsVertDiv O P b f g → IsVertDiv O P b' f' g' →
      vEval O (fun G => I G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b')) (ratCyc O P f g) =
        vEval O (fun G => I G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (ratCyc O P f' g')

def TwoExpansionsAgree.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (φ₁ φ₂ : FlagPair O x E E') (I : IFamily (kap O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRingOver O ι),
      (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      pairNum O I (mcIdeal O x) d (Fin.append φ₁.deg y) (Fin.append φ₁.deg' y')
          (Fin.append φ₁.f f) (Fin.append φ₁.g g) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) =
        pairNum O I (mcIdeal O x) d (Fin.append φ₂.deg y) (Fin.append φ₂.deg' y')
          (Fin.append φ₂.f f) (Fin.append φ₂.g g) (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

def B0.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F₁ F₂ : FlagModel O x d N E E') (I₁ : IFamily (kap O) (Sum.elim ι F₁.ι'))
      (I₂ : IFamily (kap O) (Sum.elim ι F₂.ι')), IsFieldIntersection I₁ → IsFieldIntersection I₂ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRingOver O ι),
      (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
    ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
      Q.IsHomogeneous (d + 1 - c) →
      F₁.value O I₁ G y y' f g Q = F₂.value O I₂ G y y' f g Q

def Ba.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E' E'' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E'' k L Q = ck O x d N E E' k L Q + ck O x d N E' E'' k L Q ∧
        ck O x d N E' E k L Q = -ck O x d N E E' k L Q

def Bb.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ N₂ : ℕ) (V V₁ V₂ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsSubQuot O x E i p E₁ E₂ →
    IsSubQuot O x E' i p E₁' E₂' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def Bc.Statement : Prop :=
  (∀ (x : (Σ k, ι k) → Ω) (d N N₁ : ℕ) (V V₁ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → LatLE O x E' E →
    SameGeneric O x E₁ E₁' → LatLE O x E₁' E₁ → QuotIso O x E E' E₁ E₁' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q) ∧
  (∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E E'' →
    LatLE O x E' E'' → LatLE O x E'' E →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N E E'' k L Q + ck O x d N E'' E' k L Q) ∧
  (∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (Ω₁ : Type u) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type)
      [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁),
      IsModelOver O (mcIdeal O (bcCoord x z)) d →
    ∀ (V₁ : Type u) [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁] [IsScalarTower Ω Ω₁ V₁]
      (bc : V →ₗ[Ω] V₁), IsBaseChange Ω₁ bc →
    ∀ (E₁ E₁' : ChartBundle O (mseg (bcCoord x z)) N V₁),
      IsPullBC O x z bc E E₁ → IsPullBC O x z bc E' E₁' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O (bcCoord x z) d N E₁ E₁' k (fun j => pullDeg (K' := K') (L j)) Q =
        (modelDeg O x z : ℤ) * ck O x d N E E' k L Q)

def Bd.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (g : O), g ≠ 0 →
    IsModelOver O (mcIdeal O x) d →
    (∀ s, mseg x s ≠ 0 → ∀ v, v ∈ E'.lat s ↔ ∃ e ∈ E.lat s, v = algebraMap O Ω g • e) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g ∧
        ∀ (m n : ℕ) (h w : O), IsUnit w → 1 ≤ m → g ^ m = w * h ^ n →
          (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g =
            (n : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q h

def BlowUpLemma.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ : ℕ) (V V₁ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (p : ℕ), p.Prime →
    ∀ (g w : O), IsUnit w → g ^ p = w * (p : O) →
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → LatLE O x E' E →
    (∀ s, mseg x s ≠ 0 → ∀ v ∈ E.lat s, algebraMap O Ω g • v ∈ E'.lat s) →
    SameGeneric O x E₁ E₁' → LatLE O x E₁' E₁ →
    ∀ ψ : (∀ k, ι k) → V → V₁, IsFrobPres O p x E E' E₁ E₁' ψ →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N₁ E₁ E₁' k L Q = (p : ℤ) ^ k * ck O x d N E E' k L Q

end Statements

section FieldStatements

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def Segre.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type u) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (mseg x) N E) (fl : FullFlag F x B) (bas : Module.Basis (Fin N) Ω E)
      (tw : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsDualGen F x B tw φ →
    ∀ (I₀ : IFamily F ι) (I₁ : IFamily F (Sum.elim ι fun _ : Unit => Fin M)),
      IsFieldIntersection I₀ → IsFieldIntersection I₁ →
    ∀ (m n : ℕ) (h : m + n = N - 1 + e) (Y : Fin n → K → ℤ),
      I₁ (mcIdeal F (peCoord x bas φ)) (N - 1 + e)
          (fun j => Fin.append (fun _ : Fin m => zetaDeg tw)
            (fun j => pullDeg (K' := Unit) (Y j)) (Fin.cast h.symm j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl.deg Y) (segrePoly N m n)

def ProjectiveBundleNumbers.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type u) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (mseg x) N E) (fl : FullFlag F x B) (bas : Module.Basis (Fin N) Ω E)
      (tw : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsDualGen F x B tw φ →
    ∀ (I₀ : IFamily F ι) (I₁ : IFamily F (Sum.elim ι fun _ : Unit => Fin M)),
      IsFieldIntersection I₀ → IsFieldIntersection I₁ →
    ∀ (a : ℤ) (n : ℕ), -((N : ℤ) - 1) ≤ a → (n : ℤ) = e - a → ∀ (Y : Fin n → K → ℤ)
      (h : (N - 1 + a).toNat + n = N - 1 + e),
      I₁ (mcIdeal F (peCoord x bas φ)) (N - 1 + e)
          (fun j => Fin.append (fun _ : Fin (N - 1 + a).toNat => zetaDeg tw)
            (fun j => pullDeg (K' := Unit) (Y j)) (Fin.cast h.symm j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl.deg Y) (segrePoly N (N - 1 + a).toNat n)

def SegreFlagIndep.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric → ∀ (c n : ℕ) (Y : Fin n → K → ℤ),
      G.IsHomogeneous c → c + n = e →
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j))

end FieldStatements

section Inhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem sameGeneric_symm {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') : SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

theorem NumbersCommuteVertical.hyp :
    IsModelOver O (⊥ : Ideal (MRingOver O fun _ : Unit => Fin 2)) (0 + 1) ∧
      IsVertDiv O (⊥ : Ideal (MRingOver O fun _ : Unit => Fin 2)) 0 (C (unif O)) 1 ∧
      IsVertDiv O (⊥ : Ideal (MRingOver O fun _ : Unit => Fin 2)) 0 (C (unif O * unif O)) 1 :=
  ⟨line_isModelOver O, line_vert O,
    isVertDiv_const O _ (mul_ne_zero (unif_ne_zero O) (unif_ne_zero O))⟩

theorem Segre.hyp (F : Type*) [Field F] :
    IsProjVarF (mcIdeal F (ptCoord (Ω := F))) 0 ∧
      Nonempty (FullFlag F (ptCoord (Ω := F)) (frameBundle F (mseg ptCoord) (Pi.basisFun F (Fin 2)))) ∧
      IsDualGen F (ptCoord (Ω := F)) (frameBundle F (mseg ptCoord) (Pi.basisFun F (Fin 2))) 0
        (fun j : Fin 2 => (LinearMap.proj j : (Fin 2 → F) →ₗ[F] F)) :=
  ⟨pt_projVar F, ⟨stdFlag F ptCoord⟩, proj_isDualGen F ptCoord⟩

theorem B0.hyp :
    IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      Nonempty (FlagModel O (ptCoord (Ω := FractionRing O)) 0 2 (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O))) ∧
      IsVertDiv O (mcIdeal O (ptCoord (Ω := FractionRing O))) ((0 : Unit → ℤ) - 0) (C (unif O)) 1 :=
  ⟨pt_model O, sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O), ⟨ptFlagModel O⟩,
    by
      rw [mcIdeal_of_one (frac_inj O) pt_sub ptCoord_eq, sub_self]
      exact isVertDiv_const O _ (unif_ne_zero O)⟩

theorem TwoExpansionsAgree.hyp :
    IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      Nonempty (FlagPair O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O))) :=
  ⟨pt_model O, sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O),
    ⟨stdFlagPair O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O)
      (mcIdeal_of_one (frac_inj O) pt_sub ptCoord_eq)⟩⟩

theorem Ba.hyp :
    IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) (stdE O (ptCoord (Ω := FractionRing O))) :=
  ⟨pt_model O, sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O),
    sameGeneric_symm O (sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O))⟩

theorem Bb.hyp :
    IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      IsSubQuot O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) iSub qSub (std1 O (ptCoord (Ω := FractionRing O))) (std1 O (ptCoord (Ω := FractionRing O))) ∧
      IsSubQuot O (ptCoord (Ω := FractionRing O)) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) iSub qSub (std1 O (ptCoord (Ω := FractionRing O)))
        (sc1 O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) :=
  ⟨pt_model O, sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O),
    subQuot_std O (ptCoord (Ω := FractionRing O)), subQuot_c O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)⟩

theorem unif_sq_frac_ne : algebraMap O (FractionRing O) (unif O * unif O) ≠ 0 :=
  (map_ne_zero_iff _ (frac_inj O)).mpr (mul_ne_zero (unif_ne_zero O) (unif_ne_zero O))

theorem Bc.hyp₁₂ :
    (IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (std1 O (ptCoord (Ω := FractionRing O))) (sc1 O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      LatLE O (ptCoord (Ω := FractionRing O)) (sc1 O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) (std1 O (ptCoord (Ω := FractionRing O))) ∧
      QuotIso O (ptCoord (Ω := FractionRing O)) (std1 O (ptCoord (Ω := FractionRing O))) (sc1 O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) (std1 O (ptCoord (Ω := FractionRing O)))
        (sc1 O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O))) ∧
    (SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) _ (unif_sq_frac_ne O)) ∧
      SameGeneric O (ptCoord (Ω := FractionRing O)) (stdE O (ptCoord (Ω := FractionRing O))) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      LatLE O (ptCoord (Ω := FractionRing O)) (cE O (ptCoord (Ω := FractionRing O)) _ (unif_sq_frac_ne O)) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) ∧
      LatLE O (ptCoord (Ω := FractionRing O)) (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)) (stdE O (ptCoord (Ω := FractionRing O)))) :=
  ⟨⟨pt_model O, sameGeneric_scaledRankOne O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O),
      scaledRankOne_le_standardRankOne O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O), quotIso_c O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)⟩,
    ⟨sameGeneric_cE O (ptCoord (Ω := FractionRing O)) _ (mul_ne_zero (unif_ne_zero O) (unif_ne_zero O)) (unif_sq_frac_ne O),
      sameGeneric_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_ne_zero O) (unif_frac_ne O),
      cE_le_cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif O) (unif_frac_ne O) (unif_sq_frac_ne O),
      cE_le_stdE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)⟩⟩

theorem Bc.hyp₃ :
    IsModelOver O (mcIdeal O (bcCoord (Ω₁ := FractionRing O) (ptCoord (Ω := FractionRing O))
        (noCoord (Ω := FractionRing O)))) 0 ∧
      IsBaseChange (FractionRing O) (LinearEquiv.refl (FractionRing O) (Fin 2 → FractionRing O)).toLinearMap ∧
      IsPullBC O (Ω₁ := FractionRing O) (ptCoord (Ω := FractionRing O)) (noCoord (Ω := FractionRing O))
        (LinearEquiv.refl (FractionRing O) (Fin 2 → FractionRing O)).toLinearMap (stdE O (ptCoord (Ω := FractionRing O)))
        (frameBundle O (mseg (bcCoord (Ω₁ := FractionRing O) (ptCoord (Ω := FractionRing O)) (noCoord (Ω := FractionRing O)))) (Pi.basisFun (FractionRing O) (Fin 2))) ∧
      IsPullBC O (Ω₁ := FractionRing O) (ptCoord (Ω := FractionRing O)) (noCoord (Ω := FractionRing O))
        (LinearEquiv.refl (FractionRing O) (Fin 2 → FractionRing O)).toLinearMap
        (cE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O))
        (frameBundle O (mseg (bcCoord (Ω₁ := FractionRing O) (ptCoord (Ω := FractionRing O)) (noCoord (Ω := FractionRing O)))) (bPi _ (unif_frac_ne O))) := by
  refine ⟨?_, IsBaseChange.ofEquiv _, isPullBC_frame_self O ptCoord_eq bc_pt_eq _,
    isPullBC_frame_self O ptCoord_eq bc_pt_eq _⟩
  rw [mcIdeal_of_one (frac_inj O) join_sub bc_pt_eq]
  exact isModelOver_bot O join_ne 0 (by rw [card_sigma_of_point join_sub join_ne]; simp)

theorem Bd.hyp :
    IsModelOver O (mcIdeal O (ptCoord (Ω := FractionRing O))) 0 ∧
      ∀ s, mseg (ptCoord (Ω := FractionRing O)) s ≠ 0 → ∀ v,
        v ∈ (gE O (ptCoord (Ω := FractionRing O)) (unif O) (unif_frac_ne O)).lat s ↔
          ∃ e ∈ (stdE O (ptCoord (Ω := FractionRing O))).lat s, v = algebraMap O (FractionRing O) (unif O) • e :=
  ⟨pt_model O, fun _ _ _ => mem_gE O⟩

theorem BlowUpLemma.hyp :
    Nat.Prime 2 ∧ IsUnit uG ∧ gG ^ 2 = uG * ((2 : ℕ) : GO) ∧
      IsModelOver GO (mcIdeal GO (ptCoord (Ω := FractionRing GaussianInt))) 0 ∧
      SameGeneric GO (ptCoord (Ω := FractionRing GaussianInt)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt))) (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) gG (GO_frac_ne gG gG_ne_zero)) ∧
      LatLE GO (ptCoord (Ω := FractionRing GaussianInt)) (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) gG (GO_frac_ne gG gG_ne_zero)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt))) ∧
      (∀ s, mseg (ptCoord (Ω := FractionRing GaussianInt)) s ≠ 0 → ∀ v ∈ (std1 GO (ptCoord (Ω := FractionRing GaussianInt))).lat s,
        algebraMap GO (FractionRing GaussianInt) gG • v ∈
          (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) gG (GO_frac_ne gG gG_ne_zero)).lat s) ∧
      SameGeneric GO (ptCoord (Ω := FractionRing GaussianInt)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt))) (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) 2 (GO_frac_ne 2 two_ne_zero)) ∧
      LatLE GO (ptCoord (Ω := FractionRing GaussianInt)) (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) 2 (GO_frac_ne 2 two_ne_zero)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt))) ∧
      IsFrobPres GO 2 (ptCoord (Ω := FractionRing GaussianInt)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt)))
        (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) gG (GO_frac_ne gG gG_ne_zero)) (std1 GO (ptCoord (Ω := FractionRing GaussianInt)))
        (sc1 GO (ptCoord (Ω := FractionRing GaussianInt)) 2 (GO_frac_ne 2 two_ne_zero)) frobSq := by
  refine ⟨Nat.prime_two, uG_isUnit, gG_sq, ?_, sameGeneric_scaledRankOne GO (ptCoord (Ω := FractionRing GaussianInt)) gG gG_ne_zero _,
    scaledRankOne_le_standardRankOne GO (ptCoord (Ω := FractionRing GaussianInt)) gG _, fun s _ v hv => smul_mem_scaledRankOne GO (ptCoord (Ω := FractionRing GaussianInt)) gG _ s v hv,
    sameGeneric_scaledRankOne GO (ptCoord (Ω := FractionRing GaussianInt)) 2 two_ne_zero _, scaledRankOne_le_standardRankOne GO (ptCoord (Ω := FractionRing GaussianInt)) 2 _, frobSq_isFrobPres⟩
  rw [mcIdeal_of_one (IsFractionRing.injective GO (FractionRing GaussianInt)) pt_sub ptCoord_eq]
  exact isModelOver_bot GO pt_ne 0 (by rw [card_sigma_of_point pt_sub pt_ne]; simp)

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
