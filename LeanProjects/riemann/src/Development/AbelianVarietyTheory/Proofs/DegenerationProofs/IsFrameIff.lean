import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsBasisB
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.OneBasis
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex

section Geo
variable {S S' : Scheme.{0}}

def RigPull (G' : Over S') [GrpObj G'] (G : Over S) [GrpObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) {L' : LB G'.left}
    {L : LB G.left} (w : LB.Iso L' (L.pull φ)) (ρ' : LB.Gen (L'.pull (eSec G'))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  IsGrpPullback G' G f φ ∧ w.IsGen ∧ ρ'.IsGen ∧
    PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) ρ' ρ f

def Thru {G' : Over S'} {G : Over S} {φ : G'.left ⟶ G.left} {L' : LB G'.left} {L : LB G.left} (w : LB.Iso L' (L.pull φ))
    (k : ℕ) {T' : Over S'} {T : Over S} (h : T'.left ⟶ T.left) (s : LB.Sec (LPow G L (k : ℤ) T))
    (s' : LB.Sec (LPow G' L' (k : ℤ) T')) : Prop :=
  ∀ (Z : Scheme.{0}) (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left),
    r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h → r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ →
    ∀ (z : Z) (J) (J'), Good L z J → Good L' z J' →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) s r z J =
        (GlobalTheory.ConstFam.wVal w z J J' (r' ≫ (snd T' G').left)).val ^ k *
          sval (L := L') (φ := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ)) s' r' z J'

abbrev fnR {R : Type} [CommRing R] (x : R) : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x

def FrameAt (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∃ b' : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b' ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) (fun _ : Fin 1 => b i) (fun _ => 1) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b' i) (fun _ => 1) s
theorem isFrame_iff (G : Over S) (L : LB G.left) (N : ℕ) {R₁ : Type} [CommRing R₁] [IsDomain R₁]
    (x : Sp (FractionRing R₁) ⟶ S) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) :
    IsFrame G L N x b ↔ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W →
      ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W),
      (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ),
      FrameAt G L N x gam χ h b := Iff.rfl

def BasisBy (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {W : Type} [CommRing W] [IsDomain W]
    (gam : K →+* FractionRing W) (χ : Sp W ⟶ S) (h : spMap gam ≫ x = jK W ≫ χ) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) (B : Matrix (Fin n) (Fin n) (FractionRing W)) : Prop :=
  ∃ b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk χ)), BasisAlong G L N (𝟙 _) b ∧
    ∀ i, ∃ s : LB.Sec (LPow G L (N : ℤ) (Over.mk (jK W ≫ χ))),
      Lin G L N (Over.homMk (spMap gam) h : Over.mk (jK W ≫ χ) ⟶ Over.mk x) τ (fun j => fnR (B i j)) s ∧
      Lin G L N (Over.homMk (jK W) rfl : Over.mk (jK W ≫ χ) ⟶ Over.mk χ) (fun _ : Fin 1 => b i) (fun _ => 1) s

def AllBasis (G : Over S) (L : LB G.left) (N : ℕ) {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ}
    (τ : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [Field K'] (ga : K →+* K') (x' : Sp K' ⟶ S) (h : spMap ga ≫ x = x'),
    BasisAlong G L N (Over.homMk (spMap ga) h : Over.mk x' ⟶ Over.mk x) τ
end Geo

section Tables

structure Tab (K : Type) (r : ℕ) where

  Pt : Type
  [grp : CommGroup Pt]

  E : Pt → (Fin r → K) → Prop

  C : ℕ → Pt → K → Prop

  Λ : ℕ → Pt → (Fin r → K) → Prop
attribute [instance] Tab.grp
variable {K K' : Type} [Field K] [Field K'] {r : ℕ}

def Tab.Full (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x, x ^ N = 1 → ∃ a, T.E x a) ∧ (∀ j x, x ^ ((n ^ j) ^ 2) = 1 → ∃ c, T.C (n ^ j) x c) ∧
    ∀ j h, h ^ (n ^ j) = 1 → ∃ l, T.Λ (n ^ j) h l

def Tab.Uniq (T : Tab K r) (N n : ℕ) : Prop :=
  (∀ x a, T.E x a → x ^ N = 1 ∧ ∀ a', T.E x a' → a' = a) ∧
    ∀ j x c, T.C (n ^ j) x c → x ^ ((n ^ j) ^ 2) = 1 ∧ ∀ c', T.C (n ^ j) x c' → c' = c

def Tab.Map (σ : K →+* K') (T : Tab K r) (T' : Tab K' r) : Prop :=
  ∃ β : T.Pt →* T'.Pt, (∀ k y, 1 ≤ k → y ^ k = 1 → ∃ x, x ^ k = 1 ∧ β x = y) ∧
    (∀ x a, T.E x a → T'.E (β x) (σ ∘ a)) ∧ (∀ k x c, T.C k x c → T'.C k (β x) (σ c)) ∧
    ∀ k h l, T.Λ k h l → T'.Λ k (β h) (σ ∘ l)

def Tab.Hs (T : Tab K r) (O : ValuationSubring K) (k : ℕ) : Subgroup T.Pt :=
  Subgroup.closure {y | ∃ x c, T.C k x c ∧ O.valuation c = 1 ∧ y = x ^ k}

def Tab.Loc (T : Tab K r) (O : ValuationSubring K) (B : Matrix (Fin r) (Fin r) K) (n d : ℕ) (κ : K) : Prop :=
  B.det ≠ 0 ∧ (∀ j x c, T.C (n ^ j) x c → c ∈ O) ∧
  (∀ j h l, h ∈ T.Hs O (n ^ j) → T.Λ (n ^ j) h l → ∀ i, B.mulVec l i ∈ O) ∧
  (∀ a : Fin r → K, (∀ i, a i ∈ O) → (∃ i, O.valuation (a i) = 1) →
    ∃ j h, h ∈ T.Hs O (n ^ j) ∧ ∀ l, T.Λ (n ^ j) h l → O.valuation (a ⬝ᵥ B.mulVec l) = 1) ∧
  ∃ π : Fin r → K, (∀ i, π i ≠ 0) ∧ O.valuation ((∏ i, π i) ^ d) = O.valuation κ ∧
    ∀ a : Fin r → K, (∀ i, a i / π i ∈ O) ↔ Matrix.vecMul a B ∈ Submodule.span O {e | ∃ x, T.E x e}

def Tab.Near (T : Tab K r) (N n d : ℕ) (κ : K) (σ : K →+* K') (O : ValuationSubring K') (T' : Tab K' r)
    (B : Matrix (Fin r) (Fin r) K') : Prop :=
  Tab.Map σ T T' ∧ T'.Uniq N n ∧ T'.Loc O B n d (σ κ)
end Tables

section Av
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

def Cmb {k n : ℕ} (b : Fin n → SecA A F k) (a : Fin n → F) (t : SecA A F k) : Prop :=
  ∀ j, t.f j = ∑ i, liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a i)) * (b i).f j

def ValAt {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A)
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : F) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J =
    @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

def tab (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (θ : SecA A F 1) {r : ℕ} (τ : Fin r → SecA A F (m ^ 2)) : Tab F r where
  Pt := TFK (R := R) F ⟶ A.A
  grp := Hom.commGroup
  E x a := x ^ (m ^ 2) = 1 ∧ ∃ t c, ThC A ρ m θ x t c ∧ Cmb τ a t
  C k x c := x ^ (k ^ 2) = 1 ∧ ∃ t, ThC A ρ k θ x t c
  Λ k h l := ∃ e, IsTorsFrame A ρ k h e ∧ ∀ j, ValAt (τ j) h e (l j)

def unitGrp (v : AddValuation F (WithTop ℚ)) (ρ : LB.Gen (A.L.pull (eSec A.A))) (θ : SecA A F 1) (k : ℕ) :
    Subgroup (TFK (R := R) F ⟶ A.A) :=
  Subgroup.closure {y | ∃ x t c, x ^ (k ^ 2) = 1 ∧ ThC A ρ k θ x t c ∧ v c = 0 ∧ y = x ^ k}

def FromGt {I : Ideal R} {D : DegData R I} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (k : ℕ) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  ∃ p : QkPt D.toPre F k, p.y = 0 ∧ QkToAkU U F k p x

def IsBasisH {G : Over (Spec (CommRingCat.of R))} {L : LB G.left} {k n : ℕ} (σ : Fin n → H0 L k) : Prop :=
  ∀ s : H0 L k, ∃! c : Fin n → R, ∀ j, s.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j
end Av

def Adapted {X : Type} [AddCommGroup X] (k : ℕ) (Q : X → ℤ) {r : ℕ} (cls : Fin r → X) (mu : ℕ) : Prop :=
  (∀ i z, Q (cls i) ≤ Q (cls i + k • z)) ∧ (∀ i i', (∃ z, cls i = cls i' + k • z) → cls i = cls i') ∧
    (∀ α, ∃ i z, α = cls i + k • z) ∧ ∀ i₀, Nat.card {i // cls i = cls i₀} = mu

section Dvr
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))
  (Q : D.toPre.X → ℤ)
open Classical in

def AdFam (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (mu : ℕ) (f : Fin r → ∀ α, D.toPre.SecB k α) : Prop :=
  Adapted k Q cls mu ∧ (∀ i, ∃ s : Fam D.toPre (FractionRing V) k, GlobalTheory.ZH.FamOf D.toPre _ (f i) s) ∧
    (∀ i α, (∀ z, α ≠ cls i + k • z) → ∀ j, (f i α).f j = 0) ∧
    ∀ i₀, GlobalTheory.ZH.IsBasisB D.toPre (fun i : {i // cls i = cls i₀} => f i (cls i₀))
variable {F : Type} [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ))

def IntGe {k : ℕ} (s : Fam D.toPre F k) (q : ℚ) : Prop := ∀ α, VGe D F v k α (s.s α) q

def Norms (k : ℕ) {r : ℕ} (cls : Fin r → D.toPre.X) (s : Fin r → Fam D.toPre F k) : Prop :=
  (∀ s' : Fam D.toPre F k, ∃! a : Fin r → F, s' = ∑ i, a i • s i) ∧ ∀ (a : Fin r → F) (q : ℚ),
    (NuGe D Q F v k (∑ i, a i • s i) q ↔ ∀ i, ((q + (Q (cls i) : ℚ) / k : ℚ) : WithTop ℚ) ≤ v (a i)) ∧
    (IntGe D v (∑ i, a i • s i) q ↔ ∀ i, (q : WithTop ℚ) ≤ v (a i)) ∧
    ∀ i, VGe D F v k (cls i) ((∑ i, a i • s i).s (cls i)) q → (q : WithTop ℚ) ≤ v (a i)
end Dvr

theorem exists_valuationSubring {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    ∃ O : ValuationSubring F, ∀ x, x ∈ O ↔ 0 ≤ v x :=
  ⟨(AddValuation.toValuation v).valuationSubring, fun _ => Iff.rfl⟩

theorem valuation_eq_one_iff {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {O : ValuationSubring F}
    (h : ∀ x, x ∈ O ↔ 0 ≤ v x) (x : F) : O.valuation x = 1 ↔ v x = 0 := by
  have e : O = (AddValuation.toValuation v).valuationSubring := ValuationSubring.ext _ _ h
  subst e
  exact (Valuation.isEquiv_valuation_valuationSubring (AddValuation.toValuation v)).eq_one_iff_eq_one.symm

end GlobalTheory.OneBasis
end
