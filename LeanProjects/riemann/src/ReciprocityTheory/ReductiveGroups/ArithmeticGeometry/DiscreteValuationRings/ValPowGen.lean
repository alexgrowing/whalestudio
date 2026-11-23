import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.CubicNormMulIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

section Values

variable {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
  {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
include hJ

theorem tau_nsmul (hB : D.TauBimult) (ρ mu nu : D.X) (k : ℕ) :
    val (D.tau (ρ + k • mu) nu) (σ.left ≫ jFK (R := R) F) z J * cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      val (D.tau ρ nu) (σ.left ≫ jFK (R := R) F) z J * val (D.tau mu nu) (σ.left ≫ jFK (R := R) F) z J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero]; simp [cubN]
  | succ k ih =>
    have e := tau_mul σ hJ hB (ρ + k • mu) mu nu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, pow_succ]
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e
    have a2 := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_pow, cubN] at a1 a2 ⊢
    linear_combination (norm := abel) a1 + a2

theorem psi_add (a b : D.X) : val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J =
    val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J * val (D.psi a) (σ.left ≫ jFK (R := R) F) z J *
      val (D.psi b) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have e : val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ :=
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  rw [e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Values

theorem val_powGen' {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n :=
  map_pow _ _ _

theorem fe_cocycle (hB : D.TauBimult) {T : Over (Spec (CommRingCat.of R))} (ρ' : T ⟶ DegPre.BF D F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (k : ℕ) (ρ mu nu : D.X) :
    (uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J *
        val (DegPre.famMult D F k mu ρ) (ρ' ≫ fst _ _).left z J) *
      (uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J * val (DegPre.famMult D F k nu (ρ + k • mu)) (ρ' ≫ fst _ _).left z J) =
    uVal D F k ρ (cP D _ (mu + nu)) ρ' z J * val (DegPre.famMult D F k (mu + nu) ρ) (ρ' ≫ fst _ _).left z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have hf : (ρ' ≫ DegPre.trF D F nu) ≫ fst (TF (R := R) F) D.P.A = ρ' ≫ fst _ _ := by
    rw [Category.assoc, trF_eq, tr_fst]
  have hp : (ρ' ≫ DegPre.trF D F nu) ≫ DegPre.prB D F = (ρ' ≫ DegPre.prB D F) * cP D T nu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ← Category.assoc, comp_cP]
  have hc : ∀ χ, ρ' ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ χ = cP D T χ := fun χ => by
    rw [← Category.assoc, comp_cP]
  have u1 : uVal D F k ρ (cP D _ mu) (ρ' ≫ DegPre.trF D F nu) z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu) ((ρ' ≫ DegPre.prB D F) * cP D T nu) := by
    rw [uVal, hp, ← Category.assoc (ρ' ≫ DegPre.trF D F nu), hf, Category.assoc, hc]; rfl
  have u2 : uVal D F k (ρ + k • mu) (cP D _ nu) ρ' z J =
      hv (th D z J) k (cP D T ρ * cP D T mu ^ k) (cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add, cPoint_nsmul]; rfl
  have u3 : uVal D F k ρ (cP D _ (mu + nu)) ρ' z J =
      hv (th D z J) k (cP D T ρ) (cP D T mu * cP D T nu) (ρ' ≫ DegPre.prB D F) := by
    rw [uVal, hc, cPoint_add]; rfl
  have hvc := hv_comp C k (cP D T ρ) (cP D T mu) (cP D T nu) (ρ' ≫ DegPre.prB D F)
  have σσ := ρ' ≫ fst (TF (R := R) F) D.P.A
  have fM : ∀ ν α, val (DegPre.famMult D F k ν α) (ρ' ≫ fst _ _).left z J =
      val (D.tau ν α) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J *
        (val (D.psi ν) ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k *
          val D.rigK ((ρ' ≫ fst _ _).left ≫ jFK (R := R) F) z J ^ k) := fun ν α => by
    rw [val_famMult (ρ' ≫ fst _ _) hJ k ν α, val_powGen', val_powGen']
  have t1 := tau_mul (ρ' ≫ fst _ _) hJ hB mu nu ρ
  have t2 := tau_nsmul (ρ' ≫ fst _ _) hJ hB ρ mu nu k
  have t3 := tau_symm (ρ' ≫ fst _ _) hJ nu (ρ + k • mu)
  have t4 := tau_symm (ρ' ≫ fst _ _) hJ ρ nu
  have p1 := psi_add (ρ' ≫ fst _ _) hJ mu nu
  have sy : th D z J (cP D T ρ) (cP D T nu) (cP D T mu) = th D z J (cP D T mu) (cP D T nu) (cP D T ρ) := by
    rw [C.s01, C.s12, C.s01]
  have h8 : hv (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) =
      cubN (th D z J) k (cP D T ρ) (cP D T mu) (cP D T nu) * (th D z J (cP D T ρ) (cP D T nu) (cP D T mu))⁻¹ := rfl
  rw [u1, u2, u3, fM, fM, fM]
  apply Additive.ofMul.injective
  have a1 := congrArg Additive.ofMul hvc
  have a2 := congrArg (fun q => (k : ℕ) • Additive.ofMul q) p1
  have a3 := congrArg Additive.ofMul t1
  have a4 := congrArg Additive.ofMul t2
  have a5 := congrArg Additive.ofMul t3
  have a6 := congrArg Additive.ofMul t4
  have a7 := congrArg Additive.ofMul sy
  have a8 := congrArg Additive.ofMul h8
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, smul_add] at a1 a2 a3 a4 a5 a6 a7 a8 ⊢
  linear_combination (norm := abel) a1 - a2 - a3 + a4 + a5 + a6 - a7 + a8

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
