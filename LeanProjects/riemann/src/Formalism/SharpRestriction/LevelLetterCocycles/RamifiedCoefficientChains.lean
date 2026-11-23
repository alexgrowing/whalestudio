import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def lam (l H : ℕ) : ℝ := Real.logb (l : ℝ) (2 * (H : ℝ)) + 1

def aR (l H : ℕ) : ℝ := (H : ℝ) * (2 * (l : ℝ) - 1) / ((l : ℝ) - 1) ^ 2 + 3 + lam l H

def cD (l H : ℕ) : ℝ := ((H : ℝ) + 1) / ((l : ℝ) - 1) + 1

def hpar (n : ℕ) [NeZero n] (b : ZMod n → ℕ) (S : ℕ) : ℕ := Finset.univ.sup b + S

def JumpWinS {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : Set ℤ :=
  (if (i.val + d) % 2 = 0 then Set.Icc (-((b i + S : ℕ) : ℤ)) (-((b i : ℕ) : ℤ))
    else Set.Icc ((b i : ℕ) : ℤ) ((b i + S : ℕ) : ℤ)) ∪ Set.Icc (-(η : ℤ)) (η : ℤ)

def JumpWin {n : ℕ} (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : Set ℤ := JumpWinS 0 b S η i

def MiW {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then b i + S else η

def hiW {n : ℕ} (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) (i : ZMod n) : ℕ :=
  if (i.val + d) % 2 = 0 then η else b i + S

def eBd (k₁ k₂ k₃ C : ℝ) (l H S η : ℕ) : ℝ :=
  k₁ * (H : ℝ) / (l : ℝ) ^ 2 + k₂ * (S : ℝ) + k₃ * (η : ℝ) / ((l : ℝ) - 1) + C * lam l H

def colBd (k₄ k₅ : ℝ) (l n r m S H e e' : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (r : ℝ) * (e : ℝ) + k₄ * (n : ℝ) * (m : ℝ) * (e' : ℝ) +
    k₅ * (n : ℝ) * ((r : ℝ) * (S : ℝ) + 2 * (m : ℝ) * cD l H)

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ColLeR (PD : PeriodData G Qp K₀ K B BdR) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ℝ) : Prop :=
  ∃ mm k : ℕ, F.col PD = mm ∧ lenOl PD (O := O) = k ∧ (mm : ℝ) ≤ c * k

def ePC (W : LocWach PD LL O v n) (T₁ : LocLat G Qp LL O) (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) : ℕ :=
  Formalism.MainNotions.LiftingTheory.ePA PD.p (Formalism.MainNotions.LiftingTheory.Mmax n (MiW d b S η)) (Formalism.MainNotions.LiftingTheory.Hmax n (MiW d b S η) (hiW d b S η))
    (Formalism.MainNotions.LiftingTheory.jumpSet W T₁ (Formalism.MainNotions.LiftingTheory.Mmax n (MiW d b S η)) (Formalism.MainNotions.LiftingTheory.Mmax n (hiW d b S η)))

def SetCS [NeZero n] (W : LocWach PD LL O v n) (d : ℕ) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W ∧ 11 ≤ PD.p ∧ Even n ∧
    (∃ _ : IsDomain O, IsDiscreteValuationRing O ∧ IsFractionRing O LL) ∧
    (∃ ζ : LL, IsPrimitiveRoot ζ PD.p) ∧
    Formalism.MainNotions.LiftingTheory.Sur W F ∧
    (∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      JumpsInV PD T₁.ρ τ (JumpWinS d b S η i)) ∧
    (∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∑ a ∈ Finset.Icc (-(η : ℤ)) (η : ℤ), multV PD T₂.ρ τ a ≤ (m : ℤ)) ∧
    (∀ i, 2 * aR PD.p (hpar n b S + η) + (η : ℝ) + 1 ≤ (b i : ℝ)) ∧
    (∀ i, ((hpar n b S : ℕ) : ℝ) / 2 ≤ (b i : ℝ))

def SetC [NeZero n] (W : LocWach PD LL O v n) (T₁ T₂ : LocLat G Qp LL O)
    (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ) : Prop := SetCS W 0 T₁ T₂ F b S η m

def ConclC [NeZero n] (W : LocWach PD LL O v n) (d : ℕ) (k₁ k₂ k₃ k₄ k₅ C : ℝ)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ) : Prop :=
  ∃ e : ℕ, (e : ℝ) ≤ eBd k₁ k₂ k₃ C PD.p (hpar n b S + η) S η ∧
    ColLeR PD F (colBd k₄ k₅ PD.p n (finrank LL T₂.V) m S (hpar n b S + η) e (ePC W T₁ d b S η)) ∧
    (m = 0 → F.LiftF PD (e + 3 * S))

def ThmCKR [NeZero n] (W : LocWach PD LL O v n) (R : ℕ → Prop) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → R m → ConclC W d k₁ k₂ k₃ k₄ k₅ C F b S η m

def ThmCK [NeZero n] (W : LocWach PD LL O v n) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  ThmCKR W (fun _ => True) k₁ k₂ k₃ k₄ k₅ C

def ThmC [NeZero n] (W : LocWach PD LL O v n) (C : ℝ) : Prop := ThmCK W 32 4 10 4 (3 / 2) C

def LocalBoundDegreeZero [NeZero n] (W : LocWach PD LL O v n) (C : ℝ) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → m = 0 →
      ∃ e : ℕ, (e : ℝ) ≤ eBd 32 4 10 C PD.p (hpar n b S + η) S η ∧ F.LiftF PD (e + 3 * S)

theorem jumpsLet_win [NeZero n] (W : LocWach PD LL O v n) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m) :
    Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ (MiW d b S η) (hiW d b S η) := by
  obtain ⟨-, hl, -, -, -, -, hJ, -, hbig, -⟩ := hS
  intro i τ hτ a ha
  have hwin := hJ i τ hτ a ha
  have hl1 : (1 : ℝ) < (PD.p : ℝ) := by exact_mod_cast (show 1 < PD.p by omega)
  have hlam : 0 ≤ lam PD.p (hpar n b S + η) := by
    unfold lam
    rcases Nat.eq_zero_or_pos (hpar n b S + η) with h0 | h0
    · rw [h0]; simp
    · have : (1 : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h0
        linarith
      have := Real.logb_nonneg hl1 this
      linarith
  have haR : 0 ≤ aR PD.p (hpar n b S + η) := by
    unfold aR
    have h1 : (0 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 := by
      apply div_nonneg _ (sq_nonneg _)
      exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hη : η ≤ b i := by
    have := hbig i
    have : (η : ℝ) ≤ (b i : ℝ) := by linarith
    exact_mod_cast this
  unfold JumpWinS at hwin
  unfold MiW hiW
  split_ifs at hwin ⊢ with h
  · simp only [Set.mem_union, Set.mem_Icc] at hwin ⊢
    push_cast at hwin ⊢
    omega
  · simp only [Set.mem_union, Set.mem_Icc] at hwin ⊢
    push_cast at hwin ⊢
    omega

end Core

def LocalBoundRange (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (R : ℕ → Prop) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))],
    ThmCKR ((HW l).W K 1 LL hg) R k₁ k₂ k₃ k₄ k₅ C

def ConclusionL (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop := LocalBoundRange LT A HW F (fun _ => True) 32 4 10 4 (3 / 2) C

def CorollaryALocal (LT : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l)) (HW : HWOf LT) (F : FonOf LT A HW) (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l) (hg : Loc.Good K 1 LL)
    [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))], LocalBoundDegreeZero ((HW l).W K 1 LL hg) C

section Lit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL]

def mapVB {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  TensorProduct.AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

def DcrisExactStrict : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂),
    (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.ker π = LinearMap.range ι →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    (∀ x ∈ Dcris PD ρ₀, mapVB (B := B) LL ι x = 0 → x = 0) ∧
    (Dcris PD ρ₀).map (mapVB (B := B) LL ι) = Dcris PD ρ₁ ⊓ LinearMap.ker (mapVB (B := B) LL π) ∧
    (Dcris PD ρ₁).map (mapVB (B := B) LL π) = Dcris PD ρ₂ ∧
    ∀ a : ℤ, (FilCris PD ρ₁ a).map (mapVB (B := B) LL π) = FilCris PD ρ₂ a ∧
      FilCris PD ρ₀ a = Dcris PD ρ₀ ⊓ (FilCris PD ρ₁ a).comap (mapVB (B := B) LL ι)

def CrysSubQuot : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂),
    (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) →
    Function.Injective ι → Function.Surjective π → LinearMap.ker π = LinearMap.range ι →
    IsCrys PD ρ₁ → IsCrys PD ρ₀ ∧ IsCrys PD ρ₂

def DdREqDcris : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ ∧
    ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
      finrank LL ↥(DdRE PD ρ τ) = finrank LL V ∧
      ∀ a : ℤ, FildR PD ρ τ a =
        (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
          (ιV PD (LL := LL) (V := V))

def BKDim : Prop := ∀ [Fintype (K →ₐ[Qp] LL)], BlochKatoDim PD LL

def Gen (O : Type) [CommRing O] [Algebra O LL] : Prop :=
  ∀ [Fintype (K →ₐ[Qp] LL)] (T : LocLat G Qp LL O) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound PD T.L

def ExtCrys (O : Type) [CommRing O] [Algebra O LL] : Prop :=
  ∀ (T Tp To : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L To.L),
    IsSESLat (Qp := Qp) ι π → (∀ g, To.ρ g = LinearMap.id) → finrank LL To.V = 1 →
    IsCrys PD T.ρ →
    ∀ x ∈ Tp.L.T, π.f x ≠ 0 → ∀ c : G → T.V, (∀ g, ι.f (c g) = Tp.ρ g x - x) →
      (c ∈ finiteCocycles PD T.ρ ↔ IsCrys PD Tp.ρ)

end Lit

section GenN

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {Bc BdR : Type} [CommRing Bc] [CommRing BdR] [Algebra Qp Bc] [Algebra K₀ Bc]
    [IsScalarTower Qp K₀ Bc] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]

def H1fGeneratorBound (PD : PeriodData G Qp K₀ K Bc BdR) (LL O : Type) [Field LL] [Algebra Qp LL]
    [TopologicalSpace LL] [CommRing O] [Algebra O LL] : Prop :=
  Function.Bijective (algebraMap K₀ K) →
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∃ s : Finset (LatticeCohomology T.L), Submodule.span O (s : Set (LatticeCohomology T.L)) = latticeFiniteCohomology PD T.L ∧
      s.card ≤ (finrank Qp K₀ + 1) * finrank LL T.V

end GenN

def BlochKatoExtensionCriterion (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), ExtCrys ((LT l).PD K) ↥LL.1 ↥(Loc.OL LL)

def DcrisExactStrictAll (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), DcrisExactStrict ((LT l).PD K) ↥LL.1 ∧
    CrysSubQuot ((LT l).PD K) ↥LL.1 ∧ DdREqDcris ((LT l).PD K) ↥LL.1

def admBK (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), BKDim ((LT l).PD K) ↥LL.1

def H1fGeneratorCount (LT : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), Gen ((LT l).PD K) ↥LL.1 ↥(Loc.OL LL)

def H1fGeneratorBoundAll (Th : LocTheory) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l), H1fGeneratorBound ((Th l).PD K) ↥LL.1 ↥(Loc.OL LL)

section Ties

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

def UnitGen (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  e ∈ W.N W.one ∧ W.N W.one = Submodule.span (LetA O n) {e} ∧
    Submodule.span W.EE {e} = (⊤ : Submodule W.EE (W.DD W.one)) ∧
    W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧ W.one.L.T = Submodule.span O {e₀}

def clsK (T : LocLat G Qp LL O) (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L) : LatticeCohomology T.L :=
  Submodule.Quotient.mk (⟨κ, hκ⟩ : ↥(latticeCocycles T.L))

def IsCocOf {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (e₀ : W.one.V) (κ : G → T.V) : Prop :=
  IsSESLat (Qp := Qp) ι π ∧ ∃ t ∈ Tp.L.T, π.f t = e₀ ∧ ∀ g, ι.f (κ g) = Tp.ρ g t - t

def ExtKs (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e →
    ∀ w : ↥(W.divisibleCocycles T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γ Tp x - x →
      W.cl T w = c • Formalism.MainNotions.DeltaInvariantLattices.res W.GKs T (clsK T κ hκ)

def ExtK (e : W.DD W.one) (e₀ : W.one.V) : Prop :=
  W.s = 1 → PD.p ≠ 2 →
  ∀ (T Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L)
    (κ : G → T.V) (hκ : κ ∈ latticeCocycles T.L), IsCocOf W ι π e₀ κ →
    ∀ (x : W.DD Tp) (c : O), W.map π x = c • e → (∀ δ ∈ W.DelF, W.γD Tp δ x = x) →
    ∀ w : ↥(W.wachCocyclesDelta T), W.map ι (w : W.DD T × W.DD T).1 = W.φD Tp x - x →
      W.map ι (w : W.DD T × W.DD T).2 = W.γD Tp W.gamK x - x →
      W.clK T w = c • clsK T κ hκ

def HerrExt : Prop :=
  ∃ (e : W.DD W.one) (e₀ : W.one.V), UnitGen W e e₀ ∧ ExtKs W e e₀ ∧ ExtK W e e₀

def jumpSetL (T : LocLat G Qp LL O) (i : ZMod n) (M h : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(M : ℤ)) h).filter fun a =>
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ IsJumpV PD T.ρ τ a

def xListL (T : LocLat G Qp LL O) (i : ZMod n) (M h y' Y : ℕ) : List ℤ :=
  (((jumpSetL W T i M h) ×ˢ Finset.Icc ((y' : ℤ) + 1) Y).image
    (fun p : ℤ × ℤ => p.1 + p.2)).sort (· ≤ ·)

def DssLet : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (i : ZMod n) (y' Y : ℕ) (y₀ : W.DD T), y' ≤ Y → Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.Nl T i →
      (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∃ seq : ℕ → W.DD T, seq 0 = y₀ ∧
        (∀ k : ℕ, k < (xListL W T i (Mi i) (hi i) y' Y).length →
          W.π₀ • (seq (k + 1) + cO ((xListL W T i (Mi i) (hi i) y' Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) ∧
        Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq (xListL W T i (Mi i) (hi i) y' Y).length ∈ W.Nl T i

end Ties

open Formalism.BasicNotions in

def TheoremCConstantsRange (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (R : ℕ → Prop) (k₁ k₂ k₃ k₄ k₅ C : ℝ) : Prop := LocalBoundRange D.loc D.locA HW F R k₁ k₂ k₃ k₄ k₅ C

open Formalism.BasicNotions in

def aux₃ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := ConclusionL D.loc D.locA HW F C

open Formalism.BasicNotions in

def Conclusion2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := CorollaryALocal D.loc D.locA HW F C

open Formalism.BasicNotions in

def adm1 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Prop := Formalism.MainNotions.DeltaInvariantLattices.deltaInvariantLatticeGlobal D HW F Cm

open Formalism.BasicNotions in

def adm2 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.gammaSemisimpleQuotientGlobal D HW F

open Formalism.BasicNotions in

def adm3 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.prop2 D HW F

open Formalism.BasicNotions in

def ArchimedeanSignatureMatching (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.lem3 D HW F

def adm5 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionL D HW F

def adm6 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionW D HW F

def adm7 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.WachAnnihilatorAll D HW F ∧ Formalism.MainNotions.LiftingTheory.WachExponentRecursionAll D HW F ∧ Formalism.MainNotions.LiftingTheory.WachResultConstant D HW F C

def adm8 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ConclusionH D HW F

def adm9 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F

def adm10 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (CA CB CK : ℝ) : Prop := Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK

open Formalism.BasicNotions in

def adm11 (D : D7) : Prop := DcrisExactStrictAll D.loc

open Formalism.BasicNotions in

def adm12 (D : D7) : Prop := admBK D.loc

open Formalism.BasicNotions in

def adm13 (D : D7) : Prop := H1fGeneratorCount D.loc

open Formalism.BasicNotions in

def adm14 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.DeltaInvariantLattices.adm2 D HW F

open Formalism.BasicNotions in

def adm15 (D : D7) : Prop := BlochKatoExtensionCriterion D.loc

def adm16 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ) (LL : Loc.FinExt l) (h : Loc.Good K s LL),
    HerrExt ((HW l).W K s LL h)

def adm17 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ) (LL : Loc.FinExt l) (h : Loc.Good K s LL),
    ((HW l).W K s LL h).ClNat ∧ Formalism.MainNotions.DeltaInvariantLattices.ClKNatG ((HW l).W K s LL h)

def adm18 (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (s : ℕ) (LL : Loc.FinExt l) (h : Loc.Good K s LL),
    DssLet ((HW l).W K s LL h)

open Formalism.BasicNotions in

def adm19 (D : D7) : Prop := H1fGeneratorBoundAll D.loc

def admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) : Prop :=
  adm1 D HW F Cm ∧ adm2 D HW F ∧ adm3 D HW F ∧ ArchimedeanSignatureMatching D HW F ∧ adm5 D HW F ∧ adm6 D HW F ∧ adm7 D HW F CR ∧ adm8 D HW F ∧ adm9 D HW F ∧
    adm10 D HW F CA CB CK ∧ adm11 D ∧ adm12 D ∧ adm13 D ∧ adm14 D HW F ∧ adm15 D ∧ adm16 D HW F ∧ adm17 D HW F ∧
    adm18 D HW F ∧ adm19 D

def Stmt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (C CR CA CB CK : ℝ) : Prop := admitted D HW F Cm CR CA CB CK → aux₃ D HW F C

def RealisationStatementAll : Prop := ∀ CR CA CB CK : ℝ, ∃ C : ℝ, ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW,
    ∀ Cm : CmpOf D.loc D.locA HW F, Stmt D HW F Cm C CR CA CB CK

def RealisationConstantSixteen : Prop := ∀ CR CA CB CK : ℝ, ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW,
    ∀ Cm : CmpOf D.loc D.locA HW F, Stmt D HW F Cm 16 CR CA CB CK

theorem realisation_all_of_constant_sixteen (h : RealisationConstantSixteen) : RealisationStatementAll := fun CR CA CB CK => ⟨16, h CR CA CB CK⟩

def LiftingBoundSomeConstants : Prop :=
  ∀ CR CA CB CK : ℝ, ∃ k₁ k₂ k₃ k₄ k₅ C : ℝ, ∀ D : D7, ∀ HW : HWOf D.loc, ∀ F : FonOf D.loc D.locA HW, ∀ Cm : CmpOf D.loc D.locA HW F,
    admitted D HW F Cm CR CA CB CK → TheoremCConstantsRange D HW F (fun _ => True) k₁ k₂ k₃ k₄ k₅ C

theorem first_hypothesis_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : adm1 D HW F Cm := Formalism.MainNotions.DeltaInvariantLattices.thm1used_of h.1

theorem second_hypothesis_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : adm2 D HW F := Formalism.MainNotions.DeltaInvariantLattices.gamma_semisimple_local_of_consequences h.2.1

theorem integrality_of_commutation (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : adm3 D HW F := h.2.2.1

theorem fourth_hypothesis_of_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : Formalism.MainNotions.DeltaInvariantLattices.aux₃ D HW F Cm) : ArchimedeanSignatureMatching D HW F := h.2.2.2

theorem sizes_bound_of_log_estimates (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) : adm5 D HW F := h.1

theorem restriction_dimension_of_division (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) : adm6 D HW F := h.2.1

theorem level_tools_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) : adm7 D HW F C :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem lemma_M_prime_hypothesis (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) : adm8 D HW F :=
  h.2.2.2.2.2.1

theorem crystalline_lift_of_theorem_c (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) : adm9 D HW F :=
  h.2.2.2.2.2.2.1

theorem lifting_bounds_of_theorem_c (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C CA CB CK : ℝ} (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    adm10 D HW F CA CB CK := h.2.2.2.2.2.2.2

theorem crystalline_image_of_prop_two_a (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : adm3 D HW F) : adm14 D HW F :=
  fun l _ K s LL hg T hT _ => (h l K s LL hg).1 T hT

theorem stmtAllK_of (h : RealisationStatementAll) : LiftingBoundSomeConstants := fun CR CA CB CK =>
  (h CR CA CB CK).elim fun C hC => ⟨32, 4, 10, 4, 3 / 2, C, fun D HW F Cm hA => hC D HW F Cm hA⟩

theorem theorem_c_last_of_theorem_c (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : ℝ) (h : aux₃ D HW F C) : Conclusion2 D HW F C := by
  intro l _ K LL hg _ d T₁ T₂ F b S η m hS hm
  obtain ⟨e, he, _, h0⟩ := h l K LL hg d T₁ T₂ F b S η m hS trivial
  exact ⟨e, he, h0 hm⟩

end Formalism.MainNotions.RamifiedCoefficientChains
