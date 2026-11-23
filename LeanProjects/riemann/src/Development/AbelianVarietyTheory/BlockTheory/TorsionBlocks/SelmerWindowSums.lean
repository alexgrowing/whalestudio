import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.StatementTor
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.finKs (K : _root_.Formalism.BasicNotions.Loc.FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.Ks K s) := by
  classical
  have hl : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hK : FiniteDimensional ℚ_[l] ↥(K.1) := K.2
  have hK0 : FiniteDimensional ℚ_[l] ↥(_root_.Formalism.BasicNotions.Loc.K0 K) := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : (K.1 : IntermediateField ℚ_[l] (_root_.Formalism.BasicNotions.Loc.Om l)) ⊓
        _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l ≤ K.1)).toLinearMap (RingHom.injective _)
  have hfin : {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}.Finite := by
    refine (Polynomial.nthRoots (l ^ s) (1 : _root_.Formalism.BasicNotions.Loc.Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hl] using hx
  have : Finite {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1} := hfin.to_subtype
  have hA : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] {x : _root_.Formalism.BasicNotions.Loc.Om l | x ^ l ^ s = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x hx =>
      IsIntegral.of_pow hl (by rw [show x ^ l ^ s = 1 from hx]; exact isIntegral_one)
  unfold _root_.Formalism.BasicNotions.Loc.Ks
  infer_instance

def levelField (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finKs K s⟩

section Generic

variable {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]

def charLat (hO : Function.Injective (algebraMap O LL)) (ψ : G →* LLˣ)
    (hψ : ∀ g, ∃ a : O, algebraMap O LL a = ((ψ g : LLˣ) : LL)) :
    Lattice (O := O) (charRep ψ) where
  T := LinearMap.range (Algebra.linearMap O LL)
  stable := by
    rintro g x ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hψ g
    refine ⟨b * a, ?_⟩
    change algebraMap O LL (b * a) = ((ψ g : LLˣ) : LL) * algebraMap O LL a
    rw [map_mul, hb]
  fg := by
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) hO)
  span := by
    rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

def mulR {R M : Type} [CommRing R] [Algebra O R] [AddCommGroup M] [Module O M] (a : R)
    (x : R ⊗[O] M) : R ⊗[O] M := a • x

variable [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) [Algebra Qp LL] [TopologicalSpace LL]
    [ContinuousAdd LL] [ContinuousConstSMul LL LL]
    {ψ : G →* LLˣ} (L : Lattice (O := O) (charRep ψ))

def PushInHf (p k : ℕ) (Y : LocLat G Qp LL O) (c : G → ↥Y.L.T) : Prop :=
  ∀ f : ↥Y.L.T →ₗ[O] (LL ⧸ L.T), (∀ g y, f (Y.actT g y) = actD L g (f y)) →
    ((p : O) ^ k) • (fun g => f (c g)) ∈ HfD PD L

def HfZero : Prop := divisibleFiniteCohomology PD L = ⊥

def HfUnram (I : Subgroup G) : Prop :=
  ∀ z : ↥(divisibleCocycles L), (Submodule.Quotient.mk z : DivisibleCohomology L) ∈ divisibleFiniteCohomology PD L ↔
    ∃ a : LL ⧸ L.T, ∀ g ∈ I, (z : G → LL ⧸ L.T) g = actD L g a - a

def TorsLenLe (p n b : ℕ) : Prop :=
  Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) ((p : O) ^ n)) ≤
    (b : ℕ∞) * Module.length O (O ⧸ Ideal.span {(p : O)})

end Generic

open TensorProduct in
variable {l : ℕ} [Fact l.Prime] in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem (P : _root_.Formalism.BasicNotions.LocPrime l) (K LL : _root_.Formalism.BasicNotions.Loc.FinExt l) (g : ↥(_root_.Formalism.BasicNotions.Loc.GK K)) :
    ((_root_.Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  obtain ⟨a, ha, -⟩ := P.χQ_cyc (g : _root_.Formalism.BasicNotions.Loc.GQ l) 0 1 (by simp)
  have hnorm : ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have ha' : ‖(a : ℚ_[l])‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one ℚ_[l] a
    calc ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l])‖
        = ‖(((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a) + a‖ := by ring_nf
      _ ≤ max ‖((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) - a‖ ‖(a : ℚ_[l])‖ := Padic.nonarchimedean _ _
      _ ≤ 1 := max_le (by simpa using ha) ha'
  unfold _root_.Formalism.MainNotions.N.cycLL
  show algebraMap ℚ_[l] LL (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∈ _
  rw [P.PD_χ K g]
  have hmap : algebraMap ℚ_[l] LL ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) =
      algebraMap ℤ_[l] LL ⟨_, hnorm⟩ := rfl
  rw [hmap]
  unfold _root_.Formalism.BasicNotions.Loc.OL
  exact (integralClosure ℤ_[l] LL).algebraMap_mem _

def negTwist (P : LocPrime l) (K LL : FinExt l) (e : ℕ) : ↥(GK K) →* (↥LL.1)ˣ :=
  ((cycLL (P.PD K) ↥LL.1)⁻¹) ^ e

theorem negTwist_mem (P : LocPrime l) (K LL : FinExt l) (e : ℕ) (g : ↥(GK K)) :
    ((negTwist P K LL e g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  have : negTwist P K LL e g = (cycLL (P.PD K) ↥LL.1 g⁻¹) ^ e := by
    simp [negTwist]
  rw [this, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (cyc_mem P K LL _) e

def tateLat (P : LocPrime l) (K LL : FinExt l) (e : ℕ) :
    Lattice (O := ↥(OL LL)) (charRep (negTwist P K LL e)) :=
  charLat Subtype.val_injective _ fun g => ⟨⟨_, negTwist_mem P K LL e g⟩, rfl⟩

def unitLat (K LL : FinExt l) :
    Lattice (O := ↥(OL LL)) (charRep (1 : ↥(GK K) →* (↥LL.1)ˣ)) :=
  charLat Subtype.val_injective 1 fun _ => ⟨1, rfl⟩

def wittFixedFrobeniusPow (K : FinExt l) : Set (Ainf l) :=
  {a | (WittVector.frobenius : Ainf l →+* Ainf l)^[Module.finrank ℚ_[l] ↥(K0 K)] a = a}

variable {P : LocPrime l} (AI : LocAinf l P)

def piS (s : ℕ) : Ainf l := WittVector.teichmuller l (AI.εroot s) - 1

def ringAs (K : FinExt l) (s : ℕ) : Subring (Ainf l) :=
  ⨅ m : ℕ, ((Subring.closure (insert (piS AI s) (wittFixedFrobeniusPow K))).map
      (Ideal.Quotient.mk (Ideal.span {piS AI s ^ m}))).comap
    (Ideal.Quotient.mk (Ideal.span {piS AI s ^ m}))

def ringAsW (K : FinExt l) (s : ℕ) : Subring (WCb l) := (ringAs AI K s).map (inclW l)

example (K : FinExt l) (s : ℕ) : piS AI s ∈ ringAs AI K s := by
  simp only [ringAs, Subring.mem_iInf, Subring.mem_comap]
  exact fun m => ⟨_, Subring.subset_closure (Set.mem_insert _ _), rfl⟩

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

def resKs {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) :
    Representation ↥LL.1 ↥(GK (levelField K s)) Y.V :=
  Y.ρ.comp (Subgroup.inclusion (GK_le (K := K) (K' := levelField K s) h.2.2.1))

def IsJump (P : LocPrime l) {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) (u : ℤ) :
    Prop :=
  DdR (P.PD (levelField K s)) (resKs h Y) ⊓
      FilV (P.PD (levelField K s)) (LL := ↥LL.1) (V := Y.V) (u + 1) ≠
    DdR (P.PD (levelField K s)) (resKs h Y) ⊓
      FilV (P.PD (levelField K s)) (LL := ↥LL.1) (V := Y.V) u

abbrev WY {K LL : FinExt l} (Y : Lat K LL) : Type := TW (RW LL) Y

def comb {K LL : FinExt l} {Y : Lat K LL} {r : ℕ} (n : Fin r → WY Y) (a : Fin r → WCb l) : WY Y :=
  ∑ i, mulR ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] a i : RW LL) (n i)

def actWY {K LL : FinExt l} (Y : Lat K LL) (g : ↥(GK K)) : WY Y →ₗ[↥(OL LL)] WY Y :=
  TWact (AI.gRW LL (g : GQ l)) Y g

def spanAs {K LL : FinExt l} (s : ℕ) {Y : Lat K LL} {r : ℕ} (n : Fin r → WY Y) : Set (WY Y) :=
  {x | ∃ a : Fin r → WCb l, (∀ i, a i ∈ ringAsW AI K s) ∧ x = comb n a}

def WachHyp {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (Y : Lat K LL) (M₀ h₀ : ℕ) : Prop :=
  IsCrys (P.PD (levelField K s)) (resKs h Y) ∧
  (∀ u : ℤ, IsJump P h Y u → -(M₀ : ℤ) ≤ u ∧ u ≤ (h₀ : ℤ)) ∧
  ∃ (r : ℕ) (n : Fin r → WY Y),
    Function.Bijective (comb n) ∧
    (∀ g : ↥(GK K), (∀ j : ℕ, (g : GQ l) (P.ζQ j) = P.ζQ j) → ∀ i, actWY AI Y g (n i) = n i) ∧
    (∃ Pm Pi : Matrix (Fin r) (Fin r) (WCb l), Pm * Pi = 1 ∧ Pi * Pm = 1 ∧
      (∀ i, TWmap (φRW LL) Y (n i) = comb n (Pm i)) ∧
      (∀ i j, inclW l AI.ξ ^ M₀ * Pm i j ∈ ringAsW AI K s) ∧
      (∀ i j, inclW l AI.ξ ^ h₀ * Pi i j ∈ ringAsW AI K s)) ∧
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK (levelField K s) →
      ∀ x ∈ spanAs AI s n, actWY AI Y g x ∈ spanAs AI s n) ∧
    (∀ g : ↥(GK K), (g : GQ l) ∈ GK (levelField K s) →
      ∀ x ∈ spanAs AI s n, ∃ x' ∈ spanAs AI s n, actWY AI Y g x - x =
        mulR ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (piS AI s) : RW LL) x')

theorem exists_pow_mul_pred_ge (l : ℕ) [Fact l.Prime] (H : ℕ) : ∃ k : ℕ, H ≤ l ^ k * (l - 1) := by
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  refine ⟨H, ?_⟩
  have h1 : H < l ^ H := Nat.lt_pow_self (by omega)
  calc H ≤ l ^ H * 1 := by omega
    _ ≤ l ^ H * (l - 1) := Nat.mul_le_mul_left _ (by omega)

def n0 (l : ℕ) [Fact l.Prime] (H : ℕ) : ℕ := Nat.find (exists_pow_mul_pred_ge l H)

def mLevel (l : ℕ) [Fact l.Prime] (s H : ℕ) : ℕ := 2 * s + n0 l H + 1

def rSum (l m : ℕ) (U : Finset ℤ) (i : ℤ) : ℕ :=
  ∑ u ∈ U.erase i, (m + padicValInt l (u - i))

def cWindow (l : ℕ) [Fact l.Prime] (s H : ℕ) (U : Finset ℤ) (e : ℕ) : ℕ :=
  (mLevel l s H - s) + ∑ i ∈ Finset.range (e + 1), (2 + max 1 (rSum l (mLevel l s H) U (i : ℤ)))

def gK (K : FinExt l) (s : ℕ) : ℕ := padicValNat l (IntermediateField.relfinrank K.1 (Ks K s))

def cTor (K : FinExt l) (s H : ℕ) (U : Finset ℤ) (e : ℕ) : ℕ :=
  cWindow l s H U e + ((e + 2) * s + padicValNat l e + e / (l - 1) + 1) +
    (s + padicValNat l (e + 1)) + gK K s

example : padicValNat l 0 = 0 := padicValNat.zero

def TorsionBound {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (e : ℕ) : Prop :=
  ∀ (Y Yt : Lat K LL) (ι : LatHom Y.L Yt.L) (π : LatHom Yt.L (unitLat K LL)),
    IsSESLat (Qp := ℚ_[l]) ι π →
    IsCrys (P.PD (levelField K s)) (resKs h Yt) →
  ∀ M₀ h₀ : ℕ, WachHyp AI h Y M₀ h₀ →
  ∀ U : Finset ℤ, (∀ u, u ∈ U ↔ IsJump P h Y u) →
  ∀ x ∈ Yt.L.T, π.f x = 1 →
  ∀ c : ↥(GK K) → ↥Y.L.T, (∀ g, ι.f (c g : Y.V) = Yt.ρ g x - x) →
    PushInHf (P.PD K) (tateLat P K LL e) l (cTor K s (M₀ + h₀) U e) Y c

def FiniteClasses (P : LocPrime l) (K LL : FinExt l) (e : ℕ) : Prop :=
  (0 < e → HfZero (P.PD K) (tateLat P K LL e)) ∧
    (e = 0 → HfUnram (P.PD K) (tateLat P K LL e) (IK K))

def LengthBound (P : LocPrime l) (K LL : FinExt l) (e : ℕ) : Prop :=
  ∀ n : ℕ, TorsLenLe (P.PD K) (tateLat P K LL e) l n ((Module.finrank ℚ_[l] ↥K.1 + 1) * n)

def TorsionTheorem (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (e : ℕ),
    TorsionBound (D.locA l) h e ∧ FiniteClasses (D.loc l) K LL e ∧ LengthBound (D.loc l) K LL e

end GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified
