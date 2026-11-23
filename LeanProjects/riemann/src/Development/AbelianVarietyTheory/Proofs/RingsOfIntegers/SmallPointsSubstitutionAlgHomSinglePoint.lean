import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RegularSectionIntegralGermUniqueScale
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPref
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.TransUnit

section Alg
variable {Γ Γ' U U' : Type*} [CommGroup Γ] [CommGroup Γ'] [CommGroup U] [CommGroup U']

def c3 (q : Γ → U) (x y z : Γ) : U := q (x * y * z) * q x * q y * q z / (q (x * y) * q (x * z) * q (y * z))

def quadT (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x y : Γ) : U :=
  p₁ x y (w (x * y)) * p₂ x (w x) (w y) * p₂ y (w x) (w y)

def quadQ (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x y z : Γ) : U :=
  quadT p₁ p₂ w (x * y) z / (quadT p₁ p₂ w x z * quadT p₁ p₂ w y z) * p₁ x y (w z) * p₂ z (w x) (w y)

def quadN (p₁ p₂ : Γ → Γ → Γ → U) (w : Γ → Γ) (x : Γ) : U := p₂ x⁻¹ (w x) (w x)⁻¹ / p₁ x x⁻¹ (w x)

def LiftLaws (θ : Γ → Γ → Γ → U) (ρ φ : Γ → U) (w : Γ → Γ) (a : Γ) (k : ℕ) : Prop :=
  (∀ x, ∏ j ∈ Finset.range k, φ (a ^ j * x) = 1) ∧
  φ 1 * φ a⁻¹ * (ρ a / ρ a⁻¹ * quadN θ θ w a) ^ k = 1 ∧
  ∀ x y, φ (x * y) * φ 1 * (c3 ρ x y a / ρ 1 * quadQ θ θ w x y a) ^ k = φ x * φ y

theorem quadQ_of_diff {p₁ p₂ q₁ q₂ : Γ → Γ → Γ → U} {e : Γ → Γ → U} (w : Γ →* Γ)
    (h₁ : ∀ x y z, p₁ x y z = q₁ x y z * (e (x * y) z / (e x z * e y z)))
    (h₂ : ∀ x y z, p₂ x y z = q₂ x y z * (e x (y * z) / (e x y * e x z))) (x y z : Γ) :
    quadQ p₁ p₂ w x y z = quadQ q₁ q₂ w x y z * c3 (fun x => e x (w x)) x y z := by
  apply Additive.ofMul.injective
  simp only [quadQ, quadT, c3, h₁, h₂, map_mul, ofMul_mul, ofMul_div]
  abel

theorem quadN_of_diff {p₁ p₂ q₁ q₂ : Γ → Γ → Γ → U} {e : Γ → Γ → U} (w : Γ →* Γ)
    (h₁ : ∀ x y z, p₁ x y z = q₁ x y z * (e (x * y) z / (e x z * e y z)))
    (h₂ : ∀ x y z, p₂ x y z = q₂ x y z * (e x (y * z) / (e x y * e x z)))
    (e₁ : ∀ z, e 1 z = 1) (e₂ : ∀ x, e x 1 = 1) (x : Γ) :
    quadN p₁ p₂ w x = quadN q₁ q₂ w x * (e x (w x) / e x⁻¹ (w x⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [quadN, h₁, h₂, map_inv, mul_inv_cancel, e₁, e₂, ofMul_mul, ofMul_div, ofMul_one]
  abel

theorem quadQ_one (w : Γ → Γ) (x y z : Γ) : quadQ (fun _ _ _ => (1 : U)) (fun _ _ _ => 1) w x y z = 1 := by simp [quadQ, quadT]

theorem quadN_one (w : Γ → Γ) (x : Γ) : quadN (fun _ _ _ => (1 : U)) (fun _ _ _ => 1) w x = 1 := by simp [quadN]

theorem map_lineCoeffCubic (P : Γ →* Γ') (g : U →* U') {q : Γ → U} {q' : Γ' → U'} (h : ∀ x, q' (P x) = g (q x)) (x y z : Γ) :
    c3 q' (P x) (P y) (P z) = g (c3 q x y z) := by
  have hP : ∀ a b, P a * P b = P (a * b) := fun a b => (map_mul P a b).symm
  simp only [c3, hP, h, map_mul g, map_div g]

theorem quadQ_map (P : Γ →* Γ') (g : U →* U') {p₁ p₂ : Γ → Γ → Γ → U} {p₁' p₂' : Γ' → Γ' → Γ' → U'} {w : Γ → Γ}
    {w' : Γ' → Γ'} (hw : ∀ x, w' (P x) = P (w x)) (h₁ : ∀ x y z, p₁' (P x) (P y) (P z) = g (p₁ x y z))
    (h₂ : ∀ x y z, p₂' (P x) (P y) (P z) = g (p₂ x y z)) (x y z : Γ) :
    quadQ p₁' p₂' w' (P x) (P y) (P z) = g (quadQ p₁ p₂ w x y z) := by
  have hP : ∀ a b, P a * P b = P (a * b) := fun a b => (map_mul P a b).symm
  simp only [quadQ, quadT, hP, hw, h₁, h₂, map_mul g, map_div g]

theorem quadN_map (P : Γ →* Γ') (g : U →* U') {p₁ p₂ : Γ → Γ → Γ → U} {p₁' p₂' : Γ' → Γ' → Γ' → U'} {w : Γ → Γ}
    {w' : Γ' → Γ'} (hw : ∀ x, w' (P x) = P (w x)) (h₁ : ∀ x y z, p₁' (P x) (P y) (P z) = g (p₁ x y z))
    (h₂ : ∀ x y z, p₂' (P x) (P y) (P z) = g (p₂ x y z)) (x : Γ) :
    quadN p₁' p₂' w' (P x) = g (quadN p₁ p₂ w x) := by
  have hP : ∀ a, (P a)⁻¹ = P a⁻¹ := fun a => (map_inv P a).symm
  simp only [quadN, hw, hP, h₁, h₂, map_div g]

end Alg

section Jet
variable {V : Type} [CommRing V]

def jetA (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ) : MvPowerSeries κ V →ₐ[V] Jet V κ m where
  toFun := psJet m
  map_one' := FBIdJet.psJet_one m
  map_mul' := FBIdJet.psJet_mul m
  map_zero' := FrameBiextId.psJet_zero m
  map_add' f g := by simp only [psJet, FBIdJet.psTrunc_eq, map_add]
  commutes' c := by
    have := RegularGerm.psJet_smul (κ := κ) m c 1
    rw [FBIdJet.psJet_one, _root_.mul_one] at this
    rw [Algebra.algebraMap_eq_smul_one, this]

theorem jetA_apply (κ : Type) [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ V) :
    jetA κ m f = psJet m f := rfl

variable (V) in

abbrev limO (d n : ℕ) : Over (Sp V) := overAt (𝟙 (Sp V)) (PS V n d)

def IsLimit {G : Over (Sp V)} {d : ℕ} (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G) : Prop :=
  ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m) ≫ X = x m

end Jet

section Small
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Sm (_B : FB V d O) (n : ℕ) : Type := {x : Pt V n d // SmallPt x}

variable {B : FB V d O} {l m n : ℕ}

instance : CommGroup (Sm B n) :=
  { mul := fun x y => ⟨addV B.G.F x.1 y.1, fun i => small_evV _ (small_two x.2 y.2) _ (B.G.const i)⟩
    one := ⟨0, fun i => by simp⟩
    inv := fun x => ⟨compV (B.A.act (-1)) x.1, fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)⟩
    mul_assoc := fun x y z => Subtype.ext (addV_assoc B.G x.2 y.2 z.2)
    one_mul := fun x => Subtype.ext (zero_addV B.G x.2)
    mul_one := fun x => Subtype.ext (addV_zero B.G x.2)
    mul_comm := fun x y => Subtype.ext (addV_comm B.G x.2 y.2)
    inv_mul_cancel := fun x => Subtype.ext ((addV_comm B.G
      (fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)) x.2).trans (addV_neg_actV B.A x.2)) }

theorem Sm.mul_val (x y : Sm B n) : (x * y).1 = addV B.G.F x.1 y.1 := rfl
theorem Sm.one_val : (1 : Sm B n).1 = 0 := rfl
theorem Sm.inv_val (x : Sm B n) : (x⁻¹).1 = compV (B.A.act (-1)) x.1 := rfl

variable (B) in

def Sm.act (o : O) : Sm B n →* Sm B n :=
  MonoidHom.mk' (fun x => ⟨compV (B.A.act o) x.1, fun i => small_evV _ (small_one x.2) _ (B.A.const _ i)⟩)
    fun x y => Subtype.ext (act_addV B.A o x.2 y.2)

theorem Sm.act_val (o : O) (x : Sm B n) : (Sm.act B o x).1 = compV (B.A.act o) x.1 := rfl

variable (B) in

def Sm.gen (j : Fin n) : Sm B n := ⟨pt V d j, fun i => by simp [pt]⟩

variable (B) in

def Sm.const (α : Fin d → V) (hα : Small α) : Sm B n := ⟨cpt α, fun i => by simpa [cpt] using hα i⟩

def evA (a : Fin m → Sm B n) : PS V m d →ₐ[V] PS V n d :=
  (exists_algHom_evC (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).choose

theorem evA_X (a : Fin m → Sm B n) (p : Fin m × Fin d) : evA a (MvPowerSeries.X p) = (a p.1).1 p.2 := (exists_algHom_evC (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).choose_spec p

theorem evA_apply (a : Fin m → Sm B n) (f : PS V m d) : evA a f = evV (fun j => (a j).1) f := (evC_eq_algHom (fun p : Fin m × Fin d => (a p.1).1 p.2) (fun p => (a p.1).2 p.2) (evA a) (evA_X a) f).symm

theorem smallPointsSubstitutionAlgHom_single_point (x : Sm B n) (f : PS V 1 d) : evA ![x] f = evV ![x.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

theorem smallPointsSubstitutionAlgHom_two_points (x y : Sm B n) (f : PS V 2 d) : evA ![x, y] f = evV ![x.1, y.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

theorem smallPointsSubstitutionAlgHom_three_points (x y z : Sm B n) (f : PS V 3 d) : evA ![x, y, z] f = evV ![x.1, y.1, z.1] f := by
  rw [evA_apply]
  exact congrArg (evV · f) (funext fun j => by fin_cases j <;> rfl)

def Sm.subFun (b : Fin m → Sm B n) (x : Sm B m) : Sm B n :=
  ⟨fun i => evA b (x.1 i), fun i =>
    (congrArg (fun q => MvPowerSeries.constantCoeff q ∈ maximalIdeal V) (evA_apply b (x.1 i))).mpr
      (constantCoeff_evC_mem (fun p : Fin m × Fin d => (b p.1).1 p.2) (fun p => (b p.1).2 p.2) _ (x.2 i))⟩

theorem evA_evA' (b : Fin m → Sm B n) (a : Fin l → Sm B m) (f : PS V l d) :
    evA b (evA a f) = evA (fun j => Sm.subFun b (a j)) f := by
  rw [evA_apply (fun j => Sm.subFun b (a j))]
  exact (evC_eq_algHom (fun p : Fin l × Fin d => (Sm.subFun b (a p.1)).1 p.2) (fun p => (Sm.subFun b (a p.1)).2 p.2)
    ((evA b).comp (evA a)) (fun p => by rw [AlgHom.comp_apply, evA_X]; rfl) f).symm

def Sm.sub (b : Fin m → Sm B n) : Sm B m →* Sm B n :=
  MonoidHom.mk' (Sm.subFun b) fun x y => Subtype.ext (funext fun i => by
    show evA b (evV ![x.1, y.1] (B.G.F i)) = evV ![(Sm.subFun b x).1, (Sm.subFun b y).1] (B.G.F i)
    rw [← smallPointsSubstitutionAlgHom_two_points, ← smallPointsSubstitutionAlgHom_two_points, evA_evA']
    exact congrArg (evA · (B.G.F i)) (funext fun j => by fin_cases j <;> rfl))

theorem evA_evA (b : Fin m → Sm B n) (a : Fin l → Sm B m) (f : PS V l d) :
    evA b (evA a f) = evA (fun j => Sm.sub b (a j)) f := evA_evA' b a f

theorem Sm.sub_gen (b : Fin m → Sm B n) (j : Fin m) : Sm.sub b (Sm.gen B j) = b j := Subtype.ext (funext fun i => evA_X b (j, i))

theorem Sm.sub_const (b : Fin m → Sm B n) (α : Fin d → V) (hα : Small α) :
    Sm.sub b (Sm.const B α hα) = Sm.const B α hα := Subtype.ext (funext fun i => (evA b).commutes (α i))

theorem Sm.sub_act (b : Fin m → Sm B n) (o : O) (x : Sm B m) : Sm.sub b (Sm.act B o x) = Sm.act B o (Sm.sub b x) := Subtype.ext (funext fun i => by
    show evA b (evV ![x.1] (B.A.act o i)) = evV ![(Sm.sub b x).1] (B.A.act o i)
    rw [← smallPointsSubstitutionAlgHom_single_point, ← smallPointsSubstitutionAlgHom_single_point, evA_evA]
    exact congrArg (evA · (B.A.act o i)) (funext fun j => by fin_cases j; rfl))

theorem evA_gen (f : PS V n d) : evA (Sm.gen B) f = f := by
  rw [evA_apply]
  exact evC_eq_algHom _ (fun p => (Sm.gen B p.1).2 p.2) (AlgHom.id V _) (fun p => rfl) f

theorem evA_eq_ev (a : Fin m → Sm B n) (ha : ∀ j i, MvPowerSeries.constantCoeff ((a j).1 i) = 0) (f : PS V m d) :
    evA a f = ev (fun j => (a j).1) f := by
  rw [evA_apply]
  exact (evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => (a p.1).1 p.2) (fun p => (a p.1).2 p.2)).2.2.1
    (fun p => ha p.1 p.2) f

def evU (a : Fin m → Sm B n) : (PS V m d)ˣ →* (PS V n d)ˣ := Units.map (evA a : PS V m d →* PS V n d)

theorem evU_val (a : Fin m → Sm B n) (f : (PS V m d)ˣ) : (evU a f).val = evA a f.val := rfl

def u1 (f : (PS V 1 d)ˣ) (x : Sm B n) : (PS V n d)ˣ := evU ![x] f

def u2 (f : (PS V 2 d)ˣ) (x y : Sm B n) : (PS V n d)ˣ := evU ![x, y] f

def u3 (f : (PS V 3 d)ˣ) (x y z : Sm B n) : (PS V n d)ˣ := evU ![x, y, z] f

theorem besselUnipotentSubgroup_zero_subsingleton (b : Fin m → Sm B n) (f : (PS V 1 d)ˣ) (x : Sm B m) : u1 f (Sm.sub b x) = evU b (u1 f x) := Units.ext (by
    show evA ![Sm.sub b x] f.val = evA b (evA ![x] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

theorem unitSeriesValueTwoPoints_substitution (b : Fin m → Sm B n) (f : (PS V 2 d)ˣ) (x y : Sm B m) :
    u2 f (Sm.sub b x) (Sm.sub b y) = evU b (u2 f x y) := Units.ext (by
    show evA ![Sm.sub b x, Sm.sub b y] f.val = evA b (evA ![x, y] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

theorem unitSeriesValueThreePoints_substitution (b : Fin m → Sm B n) (f : (PS V 3 d)ˣ) (x y z : Sm B m) :
    u3 f (Sm.sub b x) (Sm.sub b y) (Sm.sub b z) = evU b (u3 f x y z) := Units.ext (by
    show evA ![Sm.sub b x, Sm.sub b y, Sm.sub b z] f.val = evA b (evA ![x, y, z] f.val)
    rw [evA_evA]
    exact congrArg (evA · f.val) (funext fun j => by fin_cases j <;> rfl))

def ptOf {G : Over (Sp V)} (X : limO V d 1 ⟶ G) (a : Sm B n) : limO V d n ⟶ G :=
  Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA ![a]) ≫ X

theorem ptOf_sub {G : Over (Sp V)} (X : limO V d 1 ⟶ G) (b : Fin m → Sm B n) (a : Sm B m) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) (evA b) ≫ ptOf X a = ptOf X (Sm.sub b a) := by
  have hc : (evA b).comp (evA ![a]) = evA ![Sm.sub b a] :=
    AlgHom.ext fun f => by
      rw [AlgHom.comp_apply, evA_evA]
      exact congrArg (evA · f) (funext fun j => by fin_cases j <;> rfl)
  simp only [ptOf]
  rw [← Category.assoc]
  congr 1
  ext1
  simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left]
  rw [← hc]
  unfold spMap
  rw [← Spec.map_comp]
  rfl

end Small

end GlobalTheory.TransUnit
