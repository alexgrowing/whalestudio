import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwFam

variable {R : Type} [CommRing R] [IsDomain R]

def tφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (β : D.X) : Fin 5 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left, (toUnit D.P.A ≫ D.c β).left,
    (toUnit D.P.A ≫ η[D.P.A]).left, a.left]

def tε (n j : ℤ) : Fin 5 → ℤ := ![n - 1, 1, -1, 1, j]

abbrev SecT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : Type :=
  LB.Sec (LB.LinComb D.P.L (tφ D a β) (tε n j))

def Van (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
    sval s (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J = 0

def Small (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) : Prop :=
  ∀ e : ℕ, {i | ¬ Van I (s i) e}.Finite

def dφ (D : DegPre R) (a : D.P.A ⟶ D.P.A) (mu β β' : D.X) :
    Fin 5 ⊕ Fin 5 → ((DegPre.BF D (FractionRing R)).left ⟶ D.P.A.left) :=
  Sum.elim (fun k => (DegPre.prB D (FractionRing R)).left ≫ tφ D a β' k)
    (fun k => (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left ≫ tφ D a β k)

def dε (n j : ℤ) : Fin 5 ⊕ Fin 5 → ℤ := Sum.elim (tε n j) (fun k => - tε n j k)

def IsFac (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h : D.X →+ D.X) (n j : ℤ) (mu β β' : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (dφ D a mu β β') (dε n j))) : Prop :=
  u.IsGen ∧ ∀ (z : (TF (R := R) (FractionRing R)).left) (J), Good D.P.L z J →
    val u (DegPre.zF D (FractionRing R)).left z J =
      val (D.psi mu) (jFK (R := R) (FractionRing R)) z J ^ n * val (D.psi (h mu)) (jFK (R := R) (FractionRing R)) z J ^ j *
        val (D.tau mu β) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J ^ (n + j)

def TRel {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h : D.X →+ D.X) {n j : ℤ} (mu : D.X) {β β' : D.X}
    (s : SecT D a n j β) (s' : SecT D a n j β') : Prop :=
  ∀ u, IsFac D a h n j mu β β' u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J),
    Good D.P.L z J → sval s' (x ≫ (DegPre.prB D (FractionRing R)).left) z J =
      sval s (x ≫ (DegPre.trF D (FractionRing R) mu).left ≫ (DegPre.prB D (FractionRing R)).left) z J * (val u x z J).val

def shift {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (mu : X) : X := n • mu + j • h' (h mu)

def TFE {D : DegPre R} {a : D.P.A ⟶ D.P.A} (h h' : D.X →+ D.X) {n j : ℤ} (f : ∀ β, SecT D a n j β) : Prop :=
  ∀ mu β, TRel h mu (f β) (f (β + shift h h' n j mu))

open Classical in

def IsSum (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (F : ∀ δ, SecT D a n j δ) : Prop :=
  ∀ (e : ℕ) (S : Finset Ix), (∀ i ∉ S, Van I (s i) e) → ∀ (δ : D.X) (Z : Scheme.{0})
    (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval (F δ) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J =
        ∑ i ∈ S.filter (fun i => w i = δ), sval (s i) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J

def HasAdicSum (I : Ideal R) {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    (s : ∀ i, SecT D a n j (w i)) (F : ∀ δ, SecT D a n j δ) : Prop :=
  Small I s ∧ IsSum I s F

def IsProdT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j n' j' n'' j'' : ℤ} {β β' : D.X} (f : SecT D a n j β)
    (g : SecT D a n' j' β') (p : SecT D a n'' j'' (β + β')) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval p x z J = sval f x z J * sval g x z J *
      (val D.cub.t (x ≫ (lift (toUnit _ ≫ D.c β) (lift (toUnit _ ≫ D.c β') (𝟙 D.P.A)) : D.P.A ⟶ G3 D.P.A).left) z J).val

abbrev IotaLB (D : DegPre R) (a : D.P.A ⟶ D.P.A) (α δ : D.X) : LB D.P.A.left :=
  LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)) (Sum.elim Oε Oinvε)

def IsIota {D : DegPre R} {a : D.P.A ⟶ D.P.A} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) : Prop :=
  u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good D.P.L z J → val u (r ≫ eSec D.P.A) z J = 1

def IsPullT {D : DegPre R} {a : D.P.A ⟶ D.P.A} {k : ℕ} {α δ : D.X} (u : LB.Gen (IotaLB D a α δ)) (f : D.SecB k α)
    (s : SecT D a 0 k δ) : Prop :=
  ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
    sval s x z J = sval f (x ≫ a.left) z J * (val u x z J).val

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev SecE (U : UnifPre I D A G) {e : ℕ} (b : thickObj R I e G ⟶ thickObj R I e G) (n j : ℤ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 2) ![(fstG I e G).left, b.left ≫ (fstG I e G).left] ![n, j])

def evalE (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {n j : ℤ} (τ : SecE U b n j)
    {Z : Scheme.{0}} (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ G.left) → U.LG.L.ι) : Z.presheaf.stalk z :=
  (DVR.wv U e x z (J (x ≫ (U.gt e).pG.left)) (J' (x ≫ (fstG I e G).left)) ^ n *
    DVR.wv U e (x ≫ b.left) z (J (x ≫ b.left ≫ (U.gt e).pG.left)) (J' (x ≫ b.left ≫ (fstG I e G).left)) ^ j).val *
    sval τ x z J'

def TExp (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {a : D.toPre.P.A ⟶ D.toPre.P.A}
    {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) : Prop :=
  ∀ S : Finset Ix, (∀ i ∉ S, Van I (s i) e) → ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
    Good D.toPre.P.L z J → Good U.LG.L z J' → evalE U τ x z J J' =
      ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val

def ExpandsIn (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G} {a : D.toPre.P.A ⟶ D.toPre.P.A}
    {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X} (s : ∀ i, SecT D.toPre a n j (w i)) : Prop :=
  {i | ¬ Van I (s i) e}.Finite ∧ TExp U τ s

def zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) : SecT D a n j β := ⟨fun _ => 0, fun _ _ => by simp⟩

theorem sval_zeroT (D : DegPre R) (a : D.P.A ⟶ D.P.A) (n j : ℤ) (β : D.X) {Z : Scheme.{0}} (x : Z ⟶ D.P.A.left) (z : Z) (J)
    (hJ : Good D.P.L z J) : sval (zeroT D a n j β) x z J = 0 := DVR.gs_zero x z _ (hJ.mem _ x)

theorem zero_small_tfe (I : Ideal R) (D : DegPre R) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) (n j : ℤ) :
    Small I (w := id) (zeroT D a n j) ∧ TFE h h' (zeroT D a n j) :=
  ⟨fun e => Set.finite_empty.subset fun i hi => hi fun _ _ z J hJ => sval_zeroT D a n j i _ z J hJ,
    fun _ _ _ _ _ _ z J hJ => by rw [sval_zeroT _ _ _ _ _ _ z J hJ, sval_zeroT _ _ _ _ _ _ z J hJ, zero_mul]⟩

theorem Small.hasAdicSum_iff {I : Ideal R} {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    {s : ∀ i, SecT D a n j (w i)} (hs : Small I s) (F : ∀ δ, SecT D a n j δ) : HasAdicSum I s F ↔ IsSum I s F :=
  and_iff_right hs

theorem Small.expandsIn_iff (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X}
    {s : ∀ i, SecT D.toPre a n j (w i)} (hs : Small I s) : ExpandsIn U τ s ↔ TExp U τ s :=
  and_iff_right (hs e)

theorem HasAdicSum.small {I : Ideal R} {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    {s : ∀ i, SecT D a n j (w i)} {F : ∀ δ, SecT D a n j δ} (H : HasAdicSum I s F) : Small I (w := id) F := by
  classical
  intro e
  refine ((H.1 e).image w).subset fun δ hδ => by_contra fun hn => hδ fun Z x z J hJ => ?_
  refine (H.2 e (H.1 e).toFinset (fun i hi => by_contra fun h => hi ((H.1 e).mem_toFinset.2 h)) δ Z x z J hJ).trans
    (Finset.sum_eq_zero fun i hi => absurd ?_ hn)
  obtain ⟨h₁, h₂⟩ := Finset.mem_filter.1 hi
  exact ⟨i, (H.1 e).mem_toFinset.1 h₁, h₂⟩

theorem HasAdicSum.unique {I : Ideal R} {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {Ix : Type} {w : Ix → D.X}
    {s : ∀ i, SecT D a n j (w i)} {F F' : ∀ δ, SecT D a n j δ} (H : HasAdicSum I s F) (H' : HasAdicSum I s F') (e : ℕ) (δ : D.X)
    (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    sval (F δ) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J = sval (F' δ) (x ≫ pullback.fst D.P.A.hom (thick R I e)) z J :=
  have h₀ : ∀ i ∉ (H.1 e).toFinset, Van I (s i) e := fun _ hi => by_contra fun h => hi ((H.1 e).mem_toFinset.2 h)
  (H.2 e _ h₀ δ Z x z J hJ).trans (H'.2 e _ h₀ δ Z x z J hJ).symm

theorem Small.hasAdicSum_self {I : Ideal R} {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {f : ∀ β, SecT D a n j β}
    (hf : Small I (w := id) f) : HasAdicSum I (w := id) f f := by
  classical
  refine ⟨hf, fun e S hS δ Z x z J hJ => ?_⟩
  by_cases h : δ ∈ S
  · symm
    refine Finset.sum_eq_single_of_mem δ ?_ ?_
    · simpa using h
    · intro b hb hne
      exact absurd (by simpa using hb : b ∈ S ∧ b = δ).2 hne
  · rw [hS δ h Z x z J hJ]
    symm
    refine Finset.sum_eq_zero fun b hb => ?_
    obtain ⟨hb', rfl⟩ : b ∈ S ∧ b = δ := by simpa using hb
    exact absurd hb' h

theorem HasAdicSum.not_const {I : Ideal R} {D : DegPre R} {a : D.P.A ⟶ D.P.A} {n j : ℤ} {β : D.X} {s : SecT D a n j β} {e : ℕ}
    (hs : ¬ Van I s e) (F : ∀ δ, SecT D a n j δ) : ¬ HasAdicSum I (w := fun _ : ℕ => β) (fun _ => s) F :=
  fun H => Set.infinite_univ ((H.1 e).subset fun _ _ => hs)

theorem ExpandsIn.not_const (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {n j : ℤ} (τ : SecE U b n j) {β : D.toPre.X} {s : SecT D.toPre a n j β}
    (hs : ¬ Van I s e) : ¬ ExpandsIn U τ (w := fun _ : ℕ => β) (fun _ => s) :=
  fun H => Set.infinite_univ (H.1.subset fun _ _ => hs)

theorem Van.iff_chart (I : Ideal R) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.P.L φ ε)) (e : ℕ) :
    Van I s e ↔ ∀ j : K → D.P.L.ι, ((pullback.fst D.P.A.hom (thick R I e)).app _).hom (s.f j) = 0 := by
  constructor
  · intro H j
    refine fn_ext fun y hy => ?_
    choose J hJ using fun ψ : (thickObj R I e D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ y)
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
    exact (sec_trans s _ y hy (Good.mem hJ _ _)).trans ((congrArg _ (H _ (𝟙 _) y J hJ)).trans (mul_zero _))
  · intro H Z x z J hJ
    have m := hJ.mem φ (x ≫ pullback.fst D.P.A.hom (thick R I e))
    exact (gs_pull x _ z _ m _).symm.trans ((congrArg (gs x z _) (H _)).trans (DVR.gs_zero x z _ m))

theorem Van.iff_pull (U : UnifPre I D A G) {K : Type} [Fintype K] {φ : K → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb D.toPre.P.L φ ε)) (e : ℕ) :
    Van I s e ↔ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      sval s (x ≫ (U.gt e).pG.left) z J = 0 := by
  have e' : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e) := rfl
  constructor
  · intro H Z x z J hJ
    have := H Z (x ≫ (U.gt e).q.left) z J hJ
    rwa [Category.assoc] at this
  · intro H
    refine (Van.iff_chart I s e).2 fun j => ?_
    have := (U.gt e).q_flat
    have := (U.gt e).q_surj
    apply DVR.TG.app_injective_of_flat_surj (U.gt e).q.left
    rw [map_zero]
    have h' : ((U.gt e).pG.left.app _).hom (s.f j) = 0 := by
      refine fn_ext fun y hy => ?_
      choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
      refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
      exact (sec_trans s _ y hy (Good.mem hJ _ _)).trans ((congrArg _ (H _ (𝟙 _) y J hJ)).trans (mul_zero _))
    rw [e', Scheme.Hom.comp_app] at h'
    exact h'

theorem ExpandsIn.iff_exists (U : UnifPre I D A G) {e : ℕ} {b : thickObj R I e G ⟶ thickObj R I e G}
    {a : D.toPre.P.A ⟶ D.toPre.P.A} {n j : ℤ} (τ : SecE U b n j) {Ix : Type} {w : Ix → D.toPre.X}
    (s : ∀ i, SecT D.toPre a n j (w i)) : ExpandsIn U τ s ↔ ∃ S : Finset Ix, ∀ (Z : Scheme.{0})
      (x : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
        (∀ i ∉ S, sval (s i) (x ≫ (U.gt e).pG.left) z J = 0) ∧ ∀ J', Good U.LG.L z J' → evalE U τ x z J J' =
          ∑ i ∈ S, sval (s i) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (w i)) x z J).val := by
  classical
  constructor
  · rintro ⟨hf, H⟩
    have h₀ : ∀ i ∉ hf.toFinset, Van I (s i) e := fun _ hi => by_contra fun h => hi (hf.mem_toFinset.2 h)
    exact ⟨_, fun Z x z J hJ => ⟨fun i hi => (Van.iff_pull U _ e).1 (h₀ i hi) Z x z J hJ,
      fun J' hJ' => H _ h₀ Z x z J J' hJ hJ'⟩⟩
  · rintro ⟨S₀, h₀⟩
    refine ⟨S₀.finite_toSet.subset fun i hi => by_contra fun h => hi ((Van.iff_pull U _ e).2 fun Z x z J hJ =>
      (h₀ Z x z J hJ).1 i h), fun S hS Z x z J J' hJ hJ' => ((h₀ Z x z J hJ).2 J' hJ').trans ?_⟩
    refine (Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun i _ hi => by
      rw [(h₀ Z x z J hJ).1 i hi, zero_mul]).trans ?_
    exact (Finset.sum_subset (Finset.subset_union_right (s₁ := S₀)) fun i _ hi => by
      rw [(Van.iff_pull U _ e).1 (hS i hi) Z x z J hJ, zero_mul]).symm

theorem ExpandsIn.iff_expandsAt (U : UnifPre I D A G) (e k : ℕ) (b : thickObj R I e G ⟶ thickObj R I e G)
    (a : D.toPre.P.A ⟶ D.toPre.P.A) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α)
    (τ : SecE U b k 0) (hτ : ∀ (Z : Scheme.{0}) (x : Z ⟶ _) z J', Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (fstG I e G).left) z J')
    (s : ∀ α, SecT D.toPre a k 0 α) (hs : ∀ α (Z : Scheme.{0}) (x : Z ⟶ _) z J, Good D.toPre.P.L z J →
      sval (s α) x z J = sval (f α) x z J) : ExpandsIn U τ (w := id) s ↔ U.ExpandsAt e k σ f := by
  have l : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) z J J', Good U.LG.L z J' → evalE U τ x z J J' =
      (DVR.wv U e x z (J (x ≫ DVR.pGl U e)) (J' (x ≫ (fstG I e G).left)) ^ k).val *
        DVR.sv U k σ (x ≫ DVR.fGl I G e) z (J' (x ≫ (fstG I e G).left)) := fun Z x z J J' hJ' => by
    rw [evalE, hτ Z x z J' hJ', zpow_zero, _root_.mul_one, zpow_natCast,
      sval_of σ _ z J' (fun _ => J' (x ≫ (fstG I e G).left)) (fun _ => by rw [Category.comp_id])]
    rfl
  rw [ExpandsIn.iff_exists]
  constructor
  · rintro ⟨S, H⟩
    refine DVR.expandsAt_of_val U e k σ f S fun y J hJ => ⟨fun α hα => ?_, fun jL hL => ?_⟩
    · have := (H _ (𝟙 _) y J hJ).1 α hα
      rw [Category.id_comp] at this
      exact (hs α _ _ y J hJ).symm.trans this
    · obtain ⟨J', hJ', eJ⟩ := exists_good U.LG.L U.LG.isLB y (fun _ : Unit => (fstG I e G).left) (fun _ => jL)
        (fun _ _ _ => rfl) (fun _ => hL)
      have := (l _ (𝟙 _) y J J' hJ').symm.trans ((H _ (𝟙 _) y J hJ).2 J' hJ')
      simp only [Category.id_comp] at this
      rw [eJ ()] at this
      exact this.trans (Finset.sum_congr rfl fun α _ => congrArg (· * _) (hs α _ _ y J hJ))
  · intro H
    obtain ⟨S, h₀⟩ := DVR.expandsAt_val U e k σ f H
    refine ⟨S, fun Z x z J hJ => ⟨fun α hα => (hs α _ _ z J hJ).trans ((h₀ Z x z J hJ).1 α hα), fun J' hJ' => ?_⟩⟩
    exact (l Z x z J J' hJ').trans (((h₀ Z x z J hJ).2 _ (hJ' (x ≫ (fstG I e G).left))).trans
      (Finset.sum_congr rfl fun α _ => congrArg (· * _) (hs α _ _ z J hJ).symm))

namespace Witness

theorem formEq_delta {D : DegPre R} (a : D.P.A ⟶ D.P.A) (k : ℕ) (mu β : D.X) :
    FormEq (dφ D a mu β (β + k • mu)) (dε k 0) (DegPre.deltaφ D (FractionRing R) k β mu) (DegPre.deltaε k) := by
  intro U _ h
  have c : ∀ α (i : Fin 4), (DegPre.prB D (FractionRing R)).left ≫ tφ D a α i.castSucc = DegPre.famφ D (FractionRing R) α i := by
    intro α i
    fin_cases i
    · exact Category.comp_id _
    · show (DegPre.prB D (FractionRing R) ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left =
        (padd D.P.A (DegPre.prB D (FractionRing R)) (toUnit _ ≫ D.c α)).left
      congr 1
      simp only [padd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    · show (DegPre.prB D (FractionRing R) ≫ toUnit _ ≫ D.c α).left = (toUnit _ ≫ D.c α).left
      rw [← Category.assoc, comp_toUnit]
    · show (DegPre.prB D (FractionRing R) ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
      rw [← Category.assoc, comp_toUnit]
  have e : ∀ i : Fin 4, tε k 0 i.castSucc = DegPre.famε k i := by intro i; fin_cases i <;> rfl
  have e' : tε k 0 (Fin.last 4) = 0 := rfl
  simp only [Fintype.prod_sum_type, dφ, dε, DegPre.deltaφ, DegPre.deltaε, Sum.elim_inl, Sum.elim_inr]
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc (n := 4)]
  simp only [c, e, e', neg_zero, zpow_zero, _root_.mul_one]

theorem of_integral {I : Ideal R} {D : DegPre R} {k : ℕ} (F : Mum.IntFam I D k) (a : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) :
    ∃ f : ∀ β, SecT D a k 0 β, (∀ β (Z : Scheme.{0}) (r : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval (f β) r z J = sval (F.f β) r z J) ∧ (∀ β e, Van I (f β) e ↔ Mum.VanMod I (F.f β) e) ∧
      Small I (w := id) f ∧ TFE h h' f := by
  choose f hf using fun β => exists_sec D.P.isLB (φ' := tφ D a β) (ε' := tε k 0) (fun U _ h => by
    rw [Fin.prod_univ_four, Fin.prod_univ_five]
    simp [tφ, tε, DegPre.famφB, DegPre.famε]) (F.f β)
  have hv : ∀ β e, Van I (f β) e ↔ Mum.VanMod I (F.f β) e := fun β e => by
    refine Iff.trans ?_ (Van.iff_chart I (F.f β) e)
    exact forall_congr' fun Z => forall_congr' fun x => forall_congr' fun z => forall_congr' fun J =>
      forall_congr' fun hJ => by rw [hf β Z _ z J hJ]
  refine ⟨f, hf, hv, fun e => (F.small e).subset fun β hβ => (hv β e).not.1 hβ, fun mu β => ?_⟩
  have key : ∀ β', β' = β + k • mu → TRel h mu (f β) (f β') := by
    rintro _ rfl u ⟨hu, u₀⟩ Z x z J hJ
    obtain ⟨u', hu', vu⟩ := exists_gen D.P.isLB (formEq_delta a k mu β) u hu
    have h1 : Out.scal (DegPre.BF D (FractionRing R)).hom (1 : R) = 1 := by unfold Out.scal; rw [map_one, map_one]
    have ex : ∀ α (x : Z ⟶ _), sval (F.f α) (x ≫ (DegPre.prB D (FractionRing R)).left) z J = sval (F.F.s α) x z J :=
      fun α x => DVR.SectionScalarValuation.secScal_sval (h1 ▸ F.ext α) x z hJ
    have fe := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u').1 (F.F.fe mu β u' hu' (corr_of_val D.P.isLB fun y J' hJ' => by
      rw [val_pull hJ', Category.id_comp, vu _ _ y J' hJ', u₀ y J' hJ']
      refine Eq.trans ?_ (val_pull hJ' _ _ _).symm
      rw [Category.id_comp, val_mul hJ', val_mul hJ']
      have p₁ : val (GeneratorPullback.powGen D.P.L _ _ (D.psi mu) k) (jFK (R := R) (FractionRing R)) y J' =
        val (D.psi mu) (jFK (R := R) (FractionRing R)) y J' ^ k := map_pow _ _ _
      have p₂ : val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) (jFK (R := R) (FractionRing R)) y J' =
        val D.rigK (jFK (R := R) (FractionRing R)) y J' ^ k := map_pow _ _ _
      rw [p₁, p₂]
      simp)) Z x z J hJ
    rw [hf _ _ _ z J hJ, hf _ _ _ z J hJ, ex, ← Category.assoc, ex, fe, vu _ _ z J hJ]
  exact key _ (by simp [shift])

theorem exists_secE (U : UnifPre I D A G) {e k : ℕ} (b : thickObj R I e G ⟶ thickObj R I e G) (σ : H0 U.LG.L k) :
    ∃ τ : SecE U b k 0, ∀ (Z : Scheme.{0}) (x : Z ⟶ _) z J', Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (fstG I e G).left) z J' := by
  obtain ⟨τ, hτ⟩ := exists_sec U.LG.isLB (φ' := ![(fstG I e G).left, b.left ≫ (fstG I e G).left])
    (ε' := ![(k : ℤ), 0]) (fun U _ h => by
      simp [Fintype.prod_sum_type])
    (pullMulSec σ (fstG I e G).left (LB.oneGen U.LG.L) (fun _ _ =>
      (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
  refine ⟨τ, fun Z r z J hJ => ?_⟩
  exact (hτ Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ _ _ hJ).trans
    ((congrArg (fun u : (Z.presheaf.stalk z)ˣ => _ * u.val) (val_one _)).trans (_root_.mul_one _)))

theorem finite_of_expandsAt (U : UnifPre I D A G) {e k : ℕ} {σ : H0 U.LG.L k} {g : ∀ α, D.toPre.SecB k α}
    (x : U.ExpandsAt e k σ g) : {α | ¬ Mum.VanMod I (g α) e}.Finite := by
  obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ g x
  exact S.finite_toSet.subset fun α hα => by_contra fun h => hα ((Van.iff_chart _ _ e).1
    ((Van.iff_pull U _ e).2 fun Z r z J hJ => (hS Z r z J hJ).1 α h))

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG in

theorem exists_of_unif {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) :
    ∃ f : ∀ β, SecT D.toPre a (1 : ℕ) 0 β, HasAdicSum (maximalIdeal V) (w := id) f f ∧ TFE h h' f ∧
      ¬ Van (maximalIdeal V) (f 0) 0 ∧ ∀ (e : ℕ) (b : thickObj V (maximalIdeal V) e G ⟶ thickObj V (maximalIdeal V) e G),
        ∃ τ : SecE U.toUnifPre b (1 : ℕ) 0, ExpandsIn U.toUnifPre τ (w := id) f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨ϑ, hϑ, -⟩ := GlobalTheory.ThetaSectionTest.exists_isTheta_of_dvr GlobalTheory.allSixLaws.1 V D A G U
  obtain ⟨F, g, -, x, f⟩ := integral_exp rfl U ϑ
  have hv := terms_vanish hϖ rfl F g f
  have h1 : Out.scal (DegPre.BF D.toPre (FractionRing V)).hom (1 : V) = 1 := by unfold Out.scal; rw [map_one, map_one]
  let Φ : Mum.IntFam (maximalIdeal V) D.toPre 1 := ⟨F, g, fun α => h1 ▸ f α, fun e => finite_of_expandsAt U.toUnifPre (x e)⟩
  obtain ⟨s, hs, hw, hsm, hfe⟩ := of_integral Φ a h h'
  have hn : ¬ Mum.VanMod (maximalIdeal V) (g 0) 0 := leading_expansion_term_ne_zero rfl U ϑ (nonzero_of_isTheta rfl U hϑ) g (x 0) hv
  refine ⟨s, hsm.hasAdicSum_self, hfe, fun H => hn ((hw 0 0).1 H), fun e b => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_secE U.toUnifPre b ϑ
  exact ⟨τ, (ExpandsIn.iff_expandsAt U.toUnifPre e 1 b a ϑ g τ hτ s hs).2 (x e)⟩

theorem exists_toric_rank_one : ∃ (A : PolAV (Sp (FractionRing (PowerSeries ℚ)))) (G : Over (Sp (PowerSeries ℚ))) (_ : GrpObj G)
    (_ : IsCommMonObj G) (D : DegData (PowerSeries ℚ) (maximalIdeal (PowerSeries ℚ))) (U : Unif (maximalIdeal _) D A G),
    Module.finrank ℤ D.toPre.X = 1 ∧ ∃ f : ∀ β, SecT D.toPre (𝟙 _) (1 : ℕ) 0 β, HasAdicSum (maximalIdeal _) (w := id) f f ∧
      TFE (AddMonoidHom.id _) (AddMonoidHom.id _) f ∧ ¬ Van (maximalIdeal _) (f 0) 0 ∧
      ∀ e : ℕ, ∃ τ : SecE U.toUnifPre (𝟙 (thickObj _ (maximalIdeal _) e G)) (1 : ℕ) 0, ExpandsIn U.toUnifPre τ (w := id) f := by
  obtain ⟨A, G, _, _, D, U, -, -, hr, -⟩ := GlobalTheory.TateUnif.exists_unif_rank_one
  obtain ⟨f, h₁, h₂, h₃, h₄⟩ := exists_of_unif U (𝟙 _) (AddMonoidHom.id _) (AddMonoidHom.id _)
  exact ⟨A, G, _, _, D, U, hr, f, h₁, h₂, h₃, fun e => h₄ e _⟩

end Witness

example {X : Type} [AddCommGroup X] (h h' : X →+ X) (κ : ℤ) (mu : X) : shift h h' κ (-1) mu = κ • mu - h' (h mu) := by
  simp [shift, sub_eq_add_neg]

end GlobalTheory.TwFam
