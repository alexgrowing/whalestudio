import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RaynaudAxis

theorem cubN_mul_pow {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (n : ℕ) :
    cubN θ n 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ n = t (a ^ n * b) * t 1 * (t (a ^ n))⁻¹ * (t b)⁻¹ := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have e := h (a ^ n) a b
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [pow_succ, pow_succ]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    have ih' := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ih' ⊢
    linear_combination (norm := abel) e' + ih'

theorem cubN_of_torsion {A U : Type} [CommGroup A] [CommGroup U] (t : A → U) (θ : A → A → A → U)
    (h : ∀ p q w, θ p q w * t (p * q) * t (p * w) * t (q * w) * t 1 = t (p * q * w) * t p * t q * t w)
    (a b : A) (N : ℕ) (ha : a ^ N = 1) :
    cubN θ N 1 a b * (t (a * b) * t 1 * (t a)⁻¹ * (t b)⁻¹) ^ N = 1 := by
  rw [cubN_mul_pow t θ h, ha, _root_.one_mul, mul_inv_cancel_right, mul_inv_cancel]

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

def tV {L : RigLB G} (i : H ⟶ G) (τ : LB.Gen (L.L.pull i.left)) {T : Over S} (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (x : T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := fun _ : PUnit => i.left) (ε := fun _ => 1) τ x.left z J

theorem prod_tt (i : H ⟶ G) {Y : Over S} (p : Y ⟶ H) {U : Type} [CommGroup U] (h : (Y.left ⟶ G.left) → U) :
    ∏ k : PUnit, h ((fun _ : PUnit => p.left ≫ i.left) k) ^ ((fun _ : PUnit => (1 : ℤ)) k) = h (p ≫ i).left := by
  rw [Fintype.prod_unique, zpow_one]; rfl

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H]

theorem cub_tV (hG : GlobalFnsSt) (hA : IsAbelianScheme H) (i : H ⟶ G) [IsMonHom i] {L : RigLB G}
    (c : CubicalStr G L) (τ : LB.Gen (L.L.pull i.left)) (hτ : τ.IsGen) (T : Over S) (x y u : T ⟶ H) (z : T.left)
    (J : (T.left ⟶ G.left) → L.L.ι) (hJ : Good L.L z J) :
    cubV c z J (x ≫ i) (y ≫ i) (u ≫ i) * tV i τ z J (x * y) * tV i τ z J (x * u) * tV i τ z J (y * u) *
        tV i τ z J 1 = tV i τ z J (x * y * u) * tV i τ z J x * tV i τ z J y * tV i τ z J u := by
  haveI := hA.comm
  have h3 := surjective_cube hG hA
  let a := x3 H 0
  let b := x3 H 1
  let d := x3 H 2
  let tt := fun p : G3 H ⟶ H => LB.pullGen L.L (fun _ : PUnit => i.left) (fun _ => 1) τ p.left
  let cu := LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (a ≫ i) (lift (b ≫ i) (d ≫ i))).left
  have gt : ∀ p, (tt p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ hτ _
  have gc : cu.IsGen := DVR.pullGen_isGen _ _ _ _ c.isGen _
  have vt : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J → ∀ p,
      val (tt p) σ.left z J = tV i τ z J (σ ≫ p) := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ cu
    (tt (a * b))) (tt (a * d))) (tt (b * d))) (tt 1)
  let t₂ := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (tt (a * b * d)) (tt a)) (tt b))
    (tt d)
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 H) {z : T'.left} {J}, Good L.L z J →
      val t₁ σ.left z J = cubV c z J (σ ≫ a ≫ i) (σ ≫ b ≫ i) (σ ≫ d ≫ i) * tV i τ z J (σ ≫ (a * b)) *
        tV i τ z J (σ ≫ (a * d)) * tV i τ z J (σ ≫ (b * d)) * tV i τ z J (σ ≫ 1) ∧
      val t₂ σ.left z J = tV i τ z J (σ ≫ (a * b * d)) * tV i τ z J (σ ≫ a) * tV i τ z J (σ ≫ b) *
        tV i τ z J (σ ≫ d) := fun σ z J hJ => by
    constructor
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
          (val_cub c σ hJ _ _ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
    · exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vt σ hJ _) (vt σ hJ _))) (vt σ hJ _))) (vt σ hJ _))
  let e : 𝟙_ (Over S) ⟶ G3 H := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  have e₂ : e ≫ d = 1 := by simp [e, d, x3]
  let ρ : T ⟶ G3 H := lift x (lift y u)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have r₂ : ρ ≫ d = u := by simp [ρ, d, x3]
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' L.isLB (fun V _ k => ?_) (G3 H).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
        (DVR.mulGen_isGen _ _ _ _ _ _ _ gc (gt _)) (gt _)) (gt _)) (gt _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gt _)
        (gt _)) (gt _)) (gt _)) (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
        (prod_tt i (a * b * d) k) (prod_tt i a k)) (prod_tt i b k)) (prod_tt i d k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _ (DVR.prod_sum₂ (U := V) _
          (prod_cub (a ≫ i) (b ≫ i) (d ≫ i) k) (prod_tt i (a * b) k)) (prod_tt i (a * d) k))
          (prod_tt i (b * d) k)) (prod_tt i 1 k)).symm)
      simp only [MonObj.mul_comp, MonObj.one_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      have C := isCub_cubV c (T := 𝟙_ (Over S)) hI
      simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, e₀, e₁, e₂, MonObj.one_comp, _root_.mul_one]
      rw [C.face, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  simp only [← Category.assoc, MonObj.comp_mul, MonObj.comp_one, r₀, r₁, r₂] at this
  exact this

end GlobalTheory.RaynaudAxis

namespace GlobalTheory.RaynaudAxis

theorem cubWeil_one_of_triv_pull : ∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H]
    (i : H ⟶ G), IsAbelianScheme H → IsMonHom i → ∀ (L : RigLB G) (c : CubicalStr G L), Triv (L.L.pull i.left) →
    ∀ (N : ℕ) (T : Over S) (a b : T ⟶ H), a ^ N = 1 → b ^ N = 1 → CubWeil c N (a ≫ i) (b ≫ i) 1 := by
  intro S G H _ _ _ i hA hi L c ⟨τ, hτ⟩ N T a b ha hb
  haveI := hA.comm
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine ⟨by rw [← MonObj.pow_comp, ha, MonObj.one_comp], by rw [← MonObj.pow_comp, hb, MonObj.one_comp],
    fun z J hJ => ?_⟩
  let θ : (T ⟶ H) → (T ⟶ H) → (T ⟶ H) → (T.left.presheaf.stalk z)ˣ :=
    fun p q w => cubV c z J (p ≫ i) (q ≫ i) (w ≫ i)
  have h := cub_tV hG hA i c τ hτ T (z := z) (J := J) (hJ := hJ)
  have tr : ∀ p q : T ⟶ H, cubN (cubV c z J) N 1 (p ≫ i) (q ≫ i) = cubN θ N 1 p q := fun p q =>
    Finset.prod_congr rfl fun k _ => by
      simp only [θ, _root_.one_mul, MonObj.pow_comp]
  have e₁ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) a b N ha
  have e₂ := cubN_of_torsion (tV i τ z J) θ (fun p q w => h p q w) b a N hb
  rw [mul_comm b a, mul_right_comm _ (tV i τ z J b)⁻¹] at e₂
  rw [map_one, _root_.one_mul, tr, tr]
  exact mul_right_cancel (e₁.trans e₂.symm)

end GlobalTheory.RaynaudAxis
