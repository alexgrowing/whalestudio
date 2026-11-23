import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.LogAbsVpOfNormalised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.Serre

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayEv

section Alg

variable {S : Type} [CommRing S] {ρ V : Type}

def apolar (P : MvPolynomial V S) (f : MvPowerSeries V S) : S :=
  ∑ m ∈ P.support, P.coeff m * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f)

theorem apolar_monomial (m : V →₀ ℕ) (c : S) (f : MvPowerSeries V S) :
    apolar (MvPolynomial.monomial m c) f = c * ((m.prod fun _ n => (n.factorial : S)) * MvPowerSeries.coeff m f) := by
  classical
  rw [apolar, Finset.sum_subset (MvPolynomial.support_monomial_subset) fun x _ hx => by
    rw [MvPolynomial.notMem_support_iff.1 hx, zero_mul], Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

example : apolar (MvPolynomial.monomial (Finsupp.single () 2) (1 : ℚ))
    (MvPowerSeries.monomial (Finsupp.single () 2) 1) = 2 := by
  rw [apolar_monomial, MvPowerSeries.coeff_monomial_same, Finsupp.prod_single_index (by simp)]
  norm_num [Nat.factorial]

def jetAt (c : ρ → V) (m : ℕ) : Jet S ρ m →ₐ[S] Jet S V m :=
  jetMap (fun r => MvPolynomial.X (c r)) fun r => X_mem_orig (c r)

def serAt (c : ρ → V) (g : MvPowerSeries ρ S) : MvPowerSeries V S :=
  MvPowerSeries.subst (fun r => (MvPowerSeries.X (c r) : MvPowerSeries V S)) g

end Alg

section Exp

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {O : Type} [CommRing O] (a : OAct O G)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

structure IsExp (u : ρ → (Sp (DualNumber S) ⟶ G.left)) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Prop where
  zero : ∀ m, homAt x0 (jetAug : Jet S ρ m →ₐ[S] S) ≫ x m = 1
  trunc : ∀ m, homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m) ≫ x (m + 1) = x m
  law : ∀ m, homAt x0 (jetSum (Finset.univ : Finset (Fin 2))) ≫ x m =
    (homAt x0 (jetIn (0 : Fin 2)) ≫ x m) * (homAt x0 (jetIn (1 : Fin 2)) ≫ x m)
  act : ∀ m (c : O), x m ≫ a.act c = homAt x0 (jetScale fun r => ch r c) ≫ x m
  tan : ∀ r, (homAt x0 (jetTan r : Jet S ρ (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left = u r

variable (bar : O → O) (L : LB G.left) (rig : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => eSec G) fun _ => 1))

abbrev Fr (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) : Type :=
  ∀ m, LB.Gen (LB.LinComb L (K := PUnit) (fun _ => (x m).left) fun _ => 1)

structure IsHoriz (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) : Prop where
  gen : ∀ m, (e m).IsGen
  trunc : ∀ m y J, Good L y J →
    val (e (m + 1)) (homAt x0 (jetTrunc : Jet S ρ (m + 1) →ₐ[S] Jet S ρ m)).left y J = val (e m) (𝟙 _) y J
  zero : ∀ y J, Good L y J → val (e 0) (homAt x0 (jetAug : Jet S ρ 0 →ₐ[S] S)).left y J = val rig x0 y J
  coc : ∀ c : O, ∃ β : LB.Gen (LB.LinComb L (K := Fin 4)
      ![(a.act (1 + c * bar c)).left, (a.act c).left, 𝟙 _, (a.act (c * bar c)).left] ![1, -2, -1, -1]), β.IsGen ∧
    (∀ y J, Good L y J → val β (eSec G) y J = (val rig (𝟙 _) y J ^ 3)⁻¹) ∧
    ∀ m y J, Good L y J → val (e m) (homAt x0 (jetScale fun r => ch r (1 + c * bar c))).left y J =
      val β (x m).left y J * val (e m) (homAt x0 (jetScale fun r => ch r c)).left y J ^ 2 * val (e m) (𝟙 _) y J *
        val (e m) (homAt x0 (jetScale fun r => ch r (c * bar c))).left y J

variable (G) in

abbrev Pw (n : ℕ) : Over X := Over.mk x0 ⊗ powObj G n

variable (G) in

abbrev pr {n : ℕ} (b : Fin n) : (Pw G x0 n).left ⟶ G.left := (snd _ _ ≫ powPr G b).left

abbrev SecPw (n k : ℕ) : Type := LB.Sec (LB.LinComb L (pr G x0 (n := n)) fun _ => (k : ℤ))

def pwPt {n : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (m : ℕ) :
    overAt x0 (Jet S V m) ⟶ Pw G x0 n :=
  lift (Over.homMk (spMap (algebraMap S (Jet S V m))) rfl)
    ((powIsLimit G n).lift (Fan.mk _ fun b => homAt x0 (jetAt (col b) m) ≫ x m))

def IsGermPw {n k : ℕ} (col : Fin n → ρ → V) (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x)
    (s : SecPw x0 L n k) (f : MvPowerSeries V S) : Prop :=
  ∀ m y J, Good L y J → sval s (pwPt x0 col x m).left y J =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m f)) * ∏ b, (val (e m) (homAt x0 (jetAt (col b) m)).left y J ^ k).val

def IsVal (u : ρ → (Sp (DualNumber S) ⟶ G.left)) {n k : ℕ} (col : Fin n → ρ → V) (P : MvPolynomial V S)
    (s : SecPw x0 L n k) (v : S) : Prop :=
  ∃ (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ G) (e : Fr x0 L x) (f : MvPowerSeries V S),
    IsExp a x0 ch u x ∧ IsHoriz a x0 ch bar L rig x e ∧ IsGermPw x0 L col x e s f ∧ v = apolar P f

def IsBoxSum {n k N : ℕ} (s : SecPw x0 L n k) (c : Fin N → S) (σ : Fin N → Fin n → H0 L k) : Prop :=
  ∀ y J, Good L y J → sval s (𝟙 _) y J =
    ∑ i, gs (fst (Over.mk x0) (powObj G n)).left y ⊤ (toΓ S (c i)) * ∏ b, sval (σ i b) (pr G x0 b) y J

end Exp

section Gt

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X] {oa : D.toPre.OAct O} (Y : Ray oa)
  {S : Type} [CommRing S] (x0 : Sp S ⟶ Sp R) {ρ V : Type} [Fintype ρ] [DecidableEq ρ] [Fintype V] [DecidableEq V]
  (ch : ρ → O →+* S)

def IsTermGerm {k : ℕ} (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    {α : D.toPre.X} (σ : D.toPre.SecB k α) (g : MvPowerSeries ρ S) : Prop :=
  ∀ m y J, Good D.toPre.P.L y J → sval σ (x m ≫ Y.q).left y J * (val ((Y.Φ _ (x m)).s α) (𝟙 _) y J).val =
    gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (e m) (𝟙 _) y J ^ k).val

def IsValGt [TopologicalSpace S] (u : ρ → (Sp (DualNumber S) ⟶ Y.H.left)) {n k : ℕ} (col : Fin n → ρ → V)
    (P : MvPolynomial V S) (s : SecPw x0 U.LG.L n k) (v : S) : Prop :=
  ∃ (N : ℕ) (c : Fin N → S) (σ : Fin N → Fin n → H0 U.LG.L k) (F : Fin N → Fin n → ∀ α, D.toPre.SecB k α)
    (x : ∀ m, overAt x0 (Jet S ρ m) ⟶ Y.H) (e : Fr x0 D.toPre.P.L fun m => x m ≫ Y.q)
    (g : Fin N → Fin n → D.toPre.X → MvPowerSeries ρ S),
    IsBoxSum x0 U.LG.L s c σ ∧ (∀ i b l, U.ExpandsAt l k (σ i b) (F i b)) ∧ IsExp Y.act x0 ch u x ∧
    IsHoriz (Ray.actB oa) x0 ch star D.toPre.P.L D.toPre.rig (fun m => x m ≫ Y.q) e ∧
    (∀ i b α, IsTermGerm Y x0 x e (F i b α) (g i b α)) ∧
    HasSum (fun χ : Fin n → D.toPre.X =>
      apolar P (∑ i, MvPowerSeries.C (c i) * ∏ b, serAt (col b) (g i b (χ b)))) v

end Gt

end GlobalTheory.RayEv
