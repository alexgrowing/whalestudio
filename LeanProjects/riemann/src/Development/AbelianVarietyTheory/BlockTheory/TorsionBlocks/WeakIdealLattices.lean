import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem exists_pow_ge (l : ℕ) [Fact l.Prime] (H₀ : ℕ) : ∃ n : ℕ, H₀ ≤ l ^ n * (l - 1) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  refine ⟨H₀, (Nat.lt_pow_self hl).le.trans (Nat.le_mul_of_pos_right _ (by omega))⟩

def nZero (l : ℕ) [Fact l.Prime] (H₀ : ℕ) : ℕ := Nat.find (exists_pow_ge l H₀)

def levelM (l : ℕ) [Fact l.Prime] (s M₀ h₀ : ℕ) : ℕ := 2 * s + nZero l (M₀ + h₀) + 1

def cZero (l : ℕ) (m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt l u)

theorem finiteDimensional_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := by
    refine Set.Finite.to_subtype ((Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet.subset ?_)
    intro x hx
    simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

def KsFin (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finiteDimensional_Ks K s⟩

def InGKs (K : FinExt l) (s : ℕ) (g : ↥(GK K)) : Prop := (g : GQ l) ∈ GK (KsFin K s)

def InH (K : FinExt l) (g : ↥(GK K)) : Prop :=
  ∀ (j : ℕ) (x : Om l), x ^ (l ^ j) = 1 → (g : GQ l) x = x

section Ring

variable {P : LocPrime l} (AI : LocAinf l P)

def piS (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1

def polyW (K : FinExt l) (s : ℕ) : Subalgebra ℤ_[l] (Ainf l) :=
  Algebra.adjoin ℤ_[l] (insert (piS AI s)
    {a | ∃ x : OCb l, x ^ (l ^ Module.finrank ℚ_[l] ↥(K0 K)) = x ∧ a = WittVector.teichmuller l x})

def weakIdeal (s : ℕ) : Ideal (Ainf l) := Ideal.span {((l : ℕ) : Ainf l), piS AI s}

def ringAs (K : FinExt l) (s : ℕ) : Subalgebra ℤ_[l] (Ainf l) where
  carrier := {a | ∀ r : ℕ, ∃ b ∈ polyW AI K s, a - b ∈ weakIdeal AI s ^ r}
  mul_mem' := by
    intro a a' ha ha' r
    obtain ⟨b, hb, h⟩ := ha r
    obtain ⟨b', hb', h'⟩ := ha' r
    refine ⟨b * b', (polyW AI K s).mul_mem hb hb', ?_⟩
    have : a * a' - b * b' = a * (a' - b') + (a - b) * b' := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h') (Ideal.mul_mem_right _ _ h)
  add_mem' := by
    intro a a' ha ha' r
    obtain ⟨b, hb, h⟩ := ha r
    obtain ⟨b', hb', h'⟩ := ha' r
    refine ⟨b + b', (polyW AI K s).add_mem hb hb', ?_⟩
    have : a + a' - (b + b') = (a - b) + (a' - b') := by ring
    rw [this]
    exact Ideal.add_mem _ h h'
  algebraMap_mem' := fun c _ =>
    ⟨algebraMap _ _ c, (polyW AI K s).algebraMap_mem c, by rw [sub_self]; exact Ideal.zero_mem _⟩

def InAs (K : FinExt l) (s : ℕ) (w : WCb l) : Prop := ∃ a ∈ ringAs AI K s, inclW l a = w

end Ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R : Type} [CommRing R] [Algebra O R]

def rsmul (T : LocLat G Qp LL O) (a : R) (x : TW R T) : TW R T := a • x

def osmul (T : LocLat G Qp LL O) (o : O) (x : TW R T) : TW R T :=
  TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearMap.lsmul O ↥T.L.T o) x

end Generic

theorem inf_inf_eq_of_inf_eq {α : Type} [SemilatticeInf α] {a b c d : α} (h : a ⊓ c = a ⊓ d) :
    a ⊓ b ⊓ c = a ⊓ b ⊓ d := by
  rw [inf_right_comm, h, inf_right_comm]

section Hyp

variable {K LL : FinExt l}

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev TWC (T : Lat K LL) : Type := TW (RW LL) T

def wsmul (T : Lat K LL) (w : WCb l) (x : TWC T) : TWC T :=
  rsmul T ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) x

def comb (T : Lat K LL) {r : ℕ} (n : Fin r → TWC T) (c : Fin r → WCb l) : TWC T :=
  ∑ i, wsmul T (c i) (n i)

variable {P : LocPrime l} (AI : LocAinf l P)

def actTWC (T : Lat K LL) (g : ↥(GK K)) : TWC T →ₗ[↥(OL LL)] TWC T :=
  TWact (AI.gRW LL (g : GQ l)) T g

def spanAs (s : ℕ) (T : Lat K LL) {r : ℕ} (n : Fin r → TWC T) : Set (TWC T) :=
  {x | ∃ c : Fin r → WCb l, (∀ i, InAs AI K s (c i)) ∧ x = comb T n c}

def IsWachBasis (s M₀ h₀ : ℕ) (T : Lat K LL) {r : ℕ} (n : Fin r → TWC T) : Prop :=
  Function.Bijective (comb T n) ∧
  (∀ g : ↥(GK K), InH K g → ∀ x ∈ spanAs AI s T n, actTWC AI T g x = x) ∧
  (∃ A A' : Matrix (Fin r) (Fin r) (WCb l), A * A' = 1 ∧ A' * A = 1 ∧
    (∀ i, TWmap (φRW LL) T (n i) = comb T n (A i)) ∧
    (∀ i j, InAs AI K s (inclW l AI.ξ ^ M₀ * A i j)) ∧
    (∀ i j, InAs AI K s (inclW l AI.ξ ^ h₀ * A' i j))) ∧
  (∀ g : ↥(GK K), InGKs K s g → ∀ x ∈ spanAs AI s T n, actTWC AI T g x ∈ spanAs AI s T n) ∧
  (∀ g : ↥(GK K), InGKs K s g → ∀ x ∈ spanAs AI s T n, ∃ y ∈ spanAs AI s T n,
    actTWC AI T g x - x = wsmul T (inclW l (piS AI s)) y) ∧
  (∀ (o : ↥(OL LL)), ∀ x ∈ spanAs AI s T n, osmul T o x ∈ spanAs AI s T n)

def IsJumpAll (P : LocPrime l) (T : Lat K LL) (u : ℤ) : Prop :=
  DdR (P.PD K) T.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) (u + 1) ≠
    DdR (P.PD K) T.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) u

def HypW (s : ℕ) (hK : K.1 ≤ Ks K s) (M₀ h₀ : ℕ) (T : Lat K LL) : Prop :=
  IsCrys (P.PD (KsFin K s))
    (T.ρ.comp (Subgroup.inclusion (GK_le (K := K) (K' := KsFin K s) hK))) ∧
  (∀ u : ℤ, IsJumpAll P T u → -(M₀ : ℤ) ≤ u ∧ u ≤ (h₀ : ℤ)) ∧
  ∃ (r : ℕ) (n : Fin r → TWC T), IsWachBasis AI s M₀ h₀ T n

open Classical in

def jumpsAt (P : LocPrime l) (T : Lat K LL) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (M₀ h₀ : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M₀ : ℤ)) (h₀ : ℤ)).filter fun u => IsJumpV (P.PD K) T.ρ τ u

theorem isJumpAll_of_isJumpV (P : LocPrime l) (T : Lat K LL) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (u : ℤ)
    (h : IsJumpV (P.PD K) T.ρ τ u) : IsJumpAll P T u := by
  intro h'
  apply h
  exact inf_inf_eq_of_inf_eq h'

theorem mem_jumpsAt {s : ℕ} {hK : K.1 ≤ Ks K s} {M₀ h₀ : ℕ} {T : Lat K LL}
    (hW : HypW AI s hK M₀ h₀ T) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (u : ℤ) :
    u ∈ jumpsAt P T τ M₀ h₀ ↔ IsJumpV (P.PD K) T.ρ τ u := by
  classical
  unfold jumpsAt
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨hW.2.1 u (isJumpAll_of_isJumpV P T τ u h), h⟩⟩

end Hyp

def InvariantsKilledAt {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (hK : K.1 ≤ Ks K s) : Prop :=
  ∀ (T : Lat K LL) (M₀ h₀ : ℕ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1),
    Nontrivial ↥T.L.T → HypW AI s hK M₀ h₀ T → ¬ IsJumpV (P.PD K) T.ρ τ 0 →
    ∀ x : T.V ⧸ T.L.T, (∀ g : ↥(GK K), actD T.L g x = x) →
      (l ^ cZero l (levelM l s M₀ h₀) (jumpsAt P T τ M₀ h₀) : ℕ) • x = 0

def InvariantsKilled (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    InvariantsKilledAt (D.locA l) K s LL h.2.2.1

def InvariantsKilledAllCoeff (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l), 1 ≤ s → (l = 2 → 2 ≤ s) →
    ∀ hK : K.1 ≤ Ks K s, InvariantsKilledAt (D.locA l) K s LL hK

theorem InvariantsKilledAllCoeff.good {D : D7} (h : InvariantsKilledAllCoeff D) :
    InvariantsKilled D :=
  fun l _ K s LL hg => h l K s LL hg.1 hg.2.1 hg.2.2.1

theorem nZero_eq_zero (l : ℕ) [Fact l.Prime] (H₀ : ℕ) (h : H₀ ≤ l - 1) : nZero l H₀ = 0 := by
  unfold nZero
  rw [Nat.find_eq_zero]
  simpa using h

theorem piS_mem {P : LocPrime l} (AI : LocAinf l P) (K : FinExt l) (s : ℕ) :
    piS AI s ∈ ringAs AI K s := fun _ =>
  ⟨piS AI s, Algebra.subset_adjoin (Set.mem_insert _ _), by rw [sub_self]; exact Ideal.zero_mem _⟩

example : cZero 3 4 {-1} = 6 := by simp [cZero, padicValInt]

end GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants
