import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.BoxSec

section Rep
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)

def Rep (P : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ X) → L.ι), T.left.presheaf.stalk z) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)),
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = P U h) ∧
    ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → sval s r.left z J = v T r z J

variable {L Y}

theorem Rep.mul {P P' v v'} (h : Rep L Y P v) (h' : Rep L Y P' v') :
    Rep L Y (fun U _ h => P U h * P' U h) (fun T r z J => v T r z J * v' T r z J) := by
  obtain ⟨K, _, φ, ε, s, hP, hv⟩ := h
  obtain ⟨K', _, φ', ε', s', hP', hv'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, H1.SectionArithmetic.mulSec s s', fun U _ h => ?_, fun T r z J hJ => ?_⟩
  · exact DVR.prod_sum₂ _ (hP U h) (hP' U h)
  · rw [H1.SectionArithmetic.sval_mulSec _ _ _ _ hJ, hv T r z J hJ, hv' T r z J hJ]

theorem Rep.out (hL : L.IsLB) {P v} (h : Rep L Y P v) {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = ∏ k, h (φ k) ^ ε k) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J →
      sval s r.left z J = v T r z J := by
  obtain ⟨K', _, φ', ε', s', hP', hv'⟩ := h
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ h => (hP' U h).trans (hP U h)) s'
  exact ⟨s, fun T r z J hJ => (hs _ _ z J hJ).trans (hv' T r z J hJ)⟩

theorem rep_sec {Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (q : Y.left ⟶ Y') :
    Rep L Y (fun _ _ h => ∏ k, h (q ≫ φ k) ^ ε k) (fun _ r z J => sval s (r.left ≫ q) z J) :=
  ⟨K, inferInstance, _, _, H1.SectionArithmetic.pullSec s q, fun _ _ _ => rfl,
    fun _ _ z _ hJ => H1.SectionArithmetic.sval_pullSec _ _ _ z hJ⟩

theorem rep_gen {Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (q : Y.left ⟶ Y') :
    Rep L Y (fun _ _ h => ∏ k, h (q ≫ φ k) ^ ε k) (fun _ r z J => (val t (r.left ≫ q) z J).val) :=
  ⟨K, inferInstance, _, _, H1.SectionArithmetic.pullSec (genSec t ht) q, fun _ _ _ => rfl,
    fun _ _ z _ hJ => (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans (sval_genSec t ht _ z hJ)⟩

theorem rep_inv {Y' : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y' ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (q : Y.left ⟶ Y') :
    Rep L Y (fun _ _ h => (∏ k, h (q ≫ φ k) ^ ε k)⁻¹) (fun _ r z J => ((val t (r.left ≫ q) z J)⁻¹).val) :=
  ⟨K, inferInstance, _, _, H1.SectionArithmetic.pullSec (genSec (LB.invGen L φ ε t) (DVR.invGen_isGen _ _ _ _ ht)) q,
    fun _ _ _ => DVR.prod_neg _ _ rfl,
    fun _ _ z _ hJ => (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ).trans ((sval_genSec _ _ _ z hJ).trans
      (congrArg Units.val (val_inv _ _)))⟩

theorem Rep.congr {P P' v v'} (h : Rep L Y P v)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = P' U h)
    (hv : ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J → v T r z J = v' T r z J) : Rep L Y P' v' := by
  obtain ⟨K', _, φ', ε', s', hP', hv'⟩ := h
  exact ⟨K', inferInstance, φ', ε', s', fun U _ h => (hP' U h).trans (hP U h),
    fun T r z J hJ => (hv' T r z J hJ).trans (hv T r z J hJ)⟩

theorem exists_sum {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ ε)) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J →
      sval d r z J = ∑ i, sval (s i) r z J := by
  induction n with
  | zero =>
    refine ⟨DVR.SecOps.secZero, fun Z r z J hJ => ?_⟩
    rw [Fin.sum_univ_zero]
    exact (gs_eq r z _ (hJ.mem φ r) 0).trans (by rw [map_zero, map_zero])
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih (fun i => s i.succ)
    refine ⟨DVR.SecOps.secAdd (s 0) d, fun Z r z J hJ => ?_⟩
    rw [Fin.sum_univ_succ, ← hd Z r z J hJ]
    exact gs_add r z _ (hJ.mem φ r) _ _

end Rep

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}

theorem comp_cT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T) (a : D.X) : ρ ≫ cT D T a = cT D T' a :=
  DVR.comp_cP D ρ a

theorem prod_famB {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (x.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h x.left ^ ((k : ℤ) - 1) * h (x * cT D T α).left * (h (cT D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : x.left ≫ D.famφB α 0 = x.left := Category.comp_id _
  have e₁ : x.left ≫ D.famφB α 1 = (x * cT D T α).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul x (𝟙 _) (cT D _ α)).trans (by rw [comp_cT, Category.comp_id]))
  have e₂ : x.left ≫ D.famφB α 2 = (cT D T α).left := congrArg (fun q => q.left) (comp_cT D x α)
  have e₃ : x.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) x)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem prod_famT {T T₀ : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ T₀) (x : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h ((lift ρ x).left ≫ famφT D T₀ α i) ^ DegPre.famε k i =
      h x.left ^ ((k : ℤ) - 1) * h (x * cT D T α).left * (h (cT D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : (lift ρ x).left ≫ famφT D T₀ α 0 = x.left := congrArg (fun q => q.left) (lift_snd ρ x)
  have e₁ : (lift ρ x).left ≫ famφT D T₀ α 1 = (x * cT D T α).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul (lift ρ x) (snd T₀ D.P.A) (cT D _ α)).trans
      (by rw [comp_cT, lift_snd]))
  have e₂ : (lift ρ x).left ≫ famφT D T₀ α 2 = (cT D T α).left := congrArg (fun q => q.left) (comp_cT D (lift ρ x) α)
  have e₃ : (lift ρ x).left ≫ famφT D T₀ α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (lift ρ x))
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem rep_fam {T₀ : Over (Spec (CommRingCat.of R))} (ρ : Y ⟶ T₀) (x : Y ⟶ D.P.A) {α : D.X} {k : ℕ}
    (f : SecBT D T₀ k α) :
    Rep D.P.L Y (fun _ _ h => h x.left ^ ((k : ℤ) - 1) * h (x * cT D Y α).left * (h (cT D Y α).left)⁻¹ *
      h (1 : Y ⟶ D.P.A).left) (fun _ r z J => sval f (lift (r ≫ ρ) (r ≫ x)).left z J) :=
  (rep_sec f (lift ρ x).left).congr (fun _ _ h => prod_famT D ρ x α k h)
    (fun _ r z J _ => by rw [← Over.comp_left, comp_lift])

def cubP {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) (x x' y : Y ⟶ D.P.A) : U :=
  h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : Y ⟶ D.P.A).left)⁻¹

theorem rep_cub (x x' y : Y ⟶ D.P.A) :
    Rep D.P.L Y (fun _ _ h => cubP D h x x' y) (fun _ r z J => (cubV D.cub z J (r ≫ x) (r ≫ x') (r ≫ y)).val) :=
  (rep_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t D.cub.isGen (lift x (lift x' y)).left).congr
    (fun _ _ h => prod_cub x x' y h)
    (fun _ r z J _ => by rw [← Over.comp_left, comp_lift, comp_lift]; rfl)

theorem rep_cub_inv (x x' y : Y ⟶ D.P.A) :
    Rep D.P.L Y (fun _ _ h => (cubP D h x x' y)⁻¹)
      (fun _ r z J => ((cubV D.cub z J (r ≫ x) (r ≫ x') (r ≫ y))⁻¹).val) :=
  (rep_inv (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t D.cub.isGen (lift x (lift x' y)).left).congr
    (fun _ _ h => congrArg (·⁻¹) (prod_cub x x' y h))
    (fun _ r z J _ => by rw [← Over.comp_left, comp_lift, comp_lift]; rfl)

theorem rep_sym_inv (y : Y ⟶ D.P.A) :
    Rep D.P.L Y (fun _ _ h => (h (y⁻¹).left)⁻¹ * h y.left) (fun _ r z J => ((val D.sym (r ≫ y).left z J)⁻¹).val) :=
  (rep_inv D.sym D.sym_gen y.left).congr
    (fun _ _ h => by
      rw [Fin.prod_univ_two]
      show (h (y⁻¹).left ^ (1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (-1 : ℤ))⁻¹ = _
      rw [Category.comp_id, zpow_one, zpow_neg_one, mul_inv, inv_inv])
    (fun _ _ _ _ _ => rfl)

theorem rep_rig :
    Rep D.P.L Y (fun _ _ h => h (1 : Y ⟶ D.P.A).left) (fun _ _ z J => (rigV D z J).val) := by
  refine (rep_gen (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig D.rig_gen Y.hom).congr
    (fun _ _ h => ?_) (fun T r z J _ => ?_)
  · rw [Fintype.prod_unique, zpow_one]; rfl
  · rw [Over.w r]; rfl

theorem cT_add (T : Over (Spec (CommRingCat.of R))) (a b : D.X) : cT D T (a + b) = cT D T a * cT D T b :=
  DVR.cPoint_add D T a b

theorem box_form (α β : D.X) {U : Type} [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4 ⊕ Fin 4, h (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) k) ^ Sum.elim (DegPre.famε 2) (DegPre.famε 2) k =
    (h (fst D.P.A D.P.A).left ^ (((2 : ℕ) : ℤ) - 1) * h (fst D.P.A D.P.A * cT D _ α).left * (h (cT D _ α).left)⁻¹ *
      h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left) *
    (h (snd D.P.A D.P.A).left ^ (((2 : ℕ) : ℤ) - 1) * h (snd D.P.A D.P.A * cT D _ β).left * (h (cT D _ β).left)⁻¹ *
      h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left) :=
  DVR.prod_sum₂ _ (prod_famB D _ α 2 h) (prod_famB D _ β 2 h)

theorem form_add {U : Type} [CommGroup U] (h : (Y.left ⟶ D.P.A.left) → U) (x y a b c : Y ⟶ D.P.A) (hc : c * b = a) :
    cubP D h x y y⁻¹ * ((h (y⁻¹).left)⁻¹ * h y.left) * (h (1 : Y ⟶ D.P.A).left * h (1 : Y ⟶ D.P.A).left) *
      cubP D h a b x * cubP D h b y y⁻¹ * ((cubP D h a x y)⁻¹ * (cubP D h b x y⁻¹)⁻¹ * (cubP D h c b y)⁻¹) *
      ((h (x * y).left ^ (((1 : ℕ) : ℤ) - 1) * h (x * y * a).left * (h a.left)⁻¹ * h (1 : Y ⟶ D.P.A).left) *
        (h (x * y⁻¹).left ^ (((1 : ℕ) : ℤ) - 1) * h (x * y⁻¹ * b).left * (h b.left)⁻¹ * h (1 : Y ⟶ D.P.A).left)) =
    (h x.left ^ (((2 : ℕ) : ℤ) - 1) * h (x * (a * b)).left * (h (a * b).left)⁻¹ * h (1 : Y ⟶ D.P.A).left) *
    (h y.left ^ (((2 : ℕ) : ℤ) - 1) * h (y * c).left * (h c.left)⁻¹ * h (1 : Y ⟶ D.P.A).left) := by
  simp only [cubP, hc, mul_inv_cancel_right, mul_inv_cancel]
  rw [mul_comm x (a * b), mul_comm (x * y) a, ← _root_.mul_assoc a x y, mul_comm (x * y⁻¹) b,
    ← _root_.mul_assoc b x y⁻¹, mul_comm y c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, Nat.cast_one, Nat.cast_ofNat]
  module

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T₀ : Over (Spec (CommRingCat.of R))) (ρ₀ : D.P.A ⊗ D.P.A ⟶ T₀) (α β : D.X), (∀ (n : ℕ) (f : Fin n → SecBT D T₀ 2 α) (f' : Fin n → SecBT D T₀ 2 β), ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))), ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval d (lift x y).left z J = ∑ i, sval (f i) (lift (lift x y ≫ ρ₀) x).left z J * sval (f' i) (lift (lift x y ≫ ρ₀) y).left z J) ∧ ∀ (a b : D.X) (g : SecBT D T₀ 1 a) (g' : SecBT D T₀ 1 b), α = a + b → β = a - b → ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))), ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J → sval d (lift x y).left z J = (kapV D a b z J x y).val * (sval g (lift (lift x y ≫ ρ₀) (x * y)).left z J * sval g' (lift (lift x y ≫ ρ₀) (x * y⁻¹)).left z J) := by
  intro R _ _ D T₀ ρ₀ α β
  refine ⟨fun n f f' => ?_, fun a b g g' hα hβ => ?_⟩
  · choose s hs using fun i => ((rep_fam D ρ₀ (fst D.P.A D.P.A) (f i)).mul
      (rep_fam D ρ₀ (snd D.P.A D.P.A) (f' i))).out D.P.isLB _ _ (fun _ _ h => (box_form D α β h).symm)
    obtain ⟨d, hd⟩ := exists_sum _ _ s
    refine ⟨d, fun T x y z J hJ => (hd _ _ z J hJ).trans (Finset.sum_congr rfl fun i _ => ?_)⟩
    rw [hs i T (lift x y) z J hJ, lift_fst, lift_snd]
  · subst hα hβ
    let x := fst D.P.A D.P.A
    let y := snd D.P.A D.P.A
    have hc : cT D (D.P.A ⊗ D.P.A) (a - b) * cT D _ b = cT D _ a := by rw [← cT_add, sub_add_cancel]
    obtain ⟨d, hd⟩ := (((((((rep_cub D x y y⁻¹).mul (rep_sym_inv D y)).mul ((rep_rig D).mul (rep_rig D))).mul
      (rep_cub D (cT D _ a) (cT D _ b) x)).mul (rep_cub D (cT D _ b) y y⁻¹)).mul
      (((rep_cub_inv D (cT D _ a) x y).mul (rep_cub_inv D (cT D _ b) x y⁻¹)).mul
        (rep_cub_inv D (cT D _ (a - b)) (cT D _ b) y))).mul
      ((rep_fam D ρ₀ (x * y) g).mul (rep_fam D ρ₀ (x * y⁻¹) g'))).out D.P.isLB _ _ (fun _ _ h =>
        (form_add D h x y _ _ _ hc).trans (by rw [← cT_add]; exact (box_form D (a + b) (a - b) h).symm))
    refine ⟨d, fun T p q z J hJ => (hd T (lift p q) z J hJ).trans ?_⟩
    have e₁ : lift p q ≫ x = p := lift_fst _ _
    have e₂ : lift p q ≫ y = q := lift_snd _ _
    have e₃ : lift p q ≫ y⁻¹ = q⁻¹ := by rw [GrpObj.comp_inv, e₂]
    have e₄ : lift p q ≫ (x * y) = p * q := by rw [MonObj.comp_mul, e₁, e₂]
    have e₅ : lift p q ≫ (x * y⁻¹) = p * q⁻¹ := by rw [MonObj.comp_mul, e₁, e₃]
    simp only [e₁, e₂, e₃, e₄, e₅, comp_cT]
    congr 1
    simp only [kapV, kap0, rigV, mul_inv, sq, Units.val_mul]

end GlobalTheory.UU.BoxSec
