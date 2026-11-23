import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationValuesIntOfAdmissibleBaseStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumOfAdicSumUnitBallExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQTStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumGradedOfMulDegreeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymmetricLiftOddOrderActsAsExpansionOperator
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsActValue

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.Ex.CoordSeries
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.UT.CoefBasic GlobalTheory.UT.SymFrame GlobalTheory.Ex.GtValues

section Alg
variable {A A' U U' : Type} [CommGroup A] [CommGroup A'] [CommGroup U] [CommGroup U'] {θ : A → A → A → U}
  {θ' : A' → A' → A' → U'} {σ : A → U} {σ' : A' → U'}

theorem cubN_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u)) (k : ℕ) (b x : A) :
    cubN θ' k 1 (e b) (e x) = f (cubN θ k 1 b x) := by
  simp only [cubN, map_prod, _root_.one_mul, ← map_pow, h]

theorem dbl_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u))
    (h' : ∀ x, σ' (e x) = f (σ x)) (x : A) : dbl θ' σ' (e x) = f (dbl θ σ x) := by
  simp only [dbl, map_div, ← map_inv e, h, h']

theorem mulq_map (e : A →* A') (f : U →* U') (h : ∀ x y u, θ' (e x) (e y) (e u) = f (θ x y u))
    (h' : ∀ x, σ' (e x) = f (σ x)) (k : ℕ) (x : A) : mulq θ' σ' k (e x) = f (mulq θ σ k x) := by
  simp only [mulq, map_prod, map_div, map_pow f, cubN_map e f h, dbl_map e f h h']

theorem phi_term {O : Type} [CommRing O] (N : NumD O) (m : ℕ) (q : N.QT (m ^ 2)) (h : N.Gt) (f : N.X → N.A → O) (c : O)
    (χ : N.X) (H : f (m • χ) (h * q.1.2).b * (h * q.1.2).s (m • χ) =
      c * N.vt ((h * q.1.2) ^ m) χ * ((mulq N.θ N.σ m (h * q.1.2).b)⁻¹ : Oˣ)) :
    N.phi q (N.wQ q) f (m • χ + q.1.1.toAdd) h.b * h.s (m • χ + q.1.1.toAdd) = c * N.evT m q h χ := by
  have e : N.uV (m ^ 2) (N.c (m • χ)) q.1.2.b h.b * q.1.2.s (m • χ) * N.wQ q * h.s (m • χ + q.1.1.toAdd) =
      h.s q.1.1.toAdd * cubN N.θ (m ^ 2) 1 q.1.2.b h.b * N.wQ q * (h * q.1.2).s (m • χ) := by
    have a := congrArg Additive.ofMul (h.mult (m • χ) q.1.1.toAdd)
    rw [NumB.uV, N.cub.N_split, N.QT_pow_b, NumD.Gt.mul_s]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) a
  have e' := congrArg Units.val e
  rw [NumD.phi, NumD.evT, add_sub_cancel_right, div_eq_mul_inv]
  rw [NumD.Gt.mul_b] at H
  simp only [Units.val_mul] at e' ⊢
  linear_combination f (m • χ) (h.b * q.1.2.b) * e' +
    (h.s q.1.1.toAdd : O) * (cubN N.θ (m ^ 2) 1 q.1.2.b h.b : Oˣ) * (N.wQ q : Oˣ) * H

end Alg

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}

theorem comp_inv_eq {T : Over (Spec (CommRingCat.of R))} (r : T ⟶ Y) (x : Y ⟶ D.P.A) : r ≫ x⁻¹ = (r ≫ x)⁻¹ :=
  map_inv (preHom (G := D.P.A) r) x

theorem grep_dbl (x : Y ⟶ D.P.A) :
    GRep D.P.L Y (fun _ _ h => h x.left ^ 4 * (h (x * x).left)⁻¹ * (h (1 : Y ⟶ D.P.A).left ^ 3)⁻¹)
      (fun _ r z J => dbl (cubV D.cub z J) (fun a => val D.sym a.left z J) (r ≫ x)) :=
  ((grep_cub x x⁻¹ x).mul (grep_sym x).inv).congr (fun U _ h => by
      simp only [mul_inv_cancel, inv_mul_cancel, _root_.one_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module) (fun T r z J _ => by rw [dbl, comp_inv_eq, div_eq_mul_inv])

theorem grep_mulq (x : Y ⟶ D.P.A) (n : ℕ) :
    GRep D.P.L Y (fun _ _ h => h (x ^ n).left * (h x.left ^ (n ^ 2))⁻¹ * h (1 : Y ⟶ D.P.A).left ^ (n ^ 2) *
        (h (1 : Y ⟶ D.P.A).left)⁻¹)
      (fun _ r z J => mulq (cubV D.cub z J) (fun a => val D.sym a.left z J) n (r ≫ x)) := by
  induction n with
  | zero => exact ((grep_sym x).pow 0).congr (fun U _ h => by simp) (fun _ _ _ _ _ => by simp [mulq])
  | succ n ih =>
    refine (ih.mul ((grep_cubN x x n).mul ((grep_dbl x).pow n).inv)).congr (fun U _ h => ?_) (fun _ _ _ _ _ => ?_)
    · rw [pow_succ x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module
    · simp only [mulq, Finset.prod_range_succ, div_eq_mul_inv]

theorem dbl_one {z : Y.left} {J} (hJ : Good D.P.L z J) :
    dbl (cubV D.cub z J) (fun a : Y ⟶ D.P.A => val D.sym a.left z J) 1 = 1 := by
  rw [dbl, (isCub_cubV D.cub hJ).face, normd_one (u := D.sym) ⟨D.sym_gen, D.sym_rig⟩ hJ, div_one]

theorem val_kap (hG : GlobalFnsSt) {n : ℕ} {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)} (hκ : Normd κ)
    (b : Y ⟶ D.P.A) {z : Y.left} {J} (hJ : Good D.P.L z J) :
    val κ b.left z J = (mulq (cubV D.cub z J) (fun a => val D.sym a.left z J) n b)⁻¹ := by
  have key := ((grep_kap κ hκ.1 (𝟙 _)).mul (grep_mulq (𝟙 _) n)).triv hG (fun U _ h => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hκ hJ, _root_.one_mul, mulq]
      exact Finset.prod_eq_one fun i _ => by rw [(isCub_cubV D.cub hJ).N_one, dbl_one hJ, one_pow, div_one]) Y b z J hJ
  beta_reduce at key
  rw [Category.comp_id] at key
  exact eq_inv_of_mul_eq_one_left key

theorem val_nu (hG : GlobalFnsSt) {n : ℕ} {ν : LB.Gen (nuLB D n)} (hν : Normd ν)
    (b : Y ⟶ D.P.A) {z : Y.left} {J} (hJ : Good D.P.L z J) :
    val ν b.left z J = cubN (cubV D.cub z J) n 1 b b / dbl (cubV D.cub z J) (fun a => val D.sym a.left z J) b ^ n := by
  have key := (((grep_nu ν hν.1 (𝟙 _)).mul ((grep_dbl (𝟙 _)).pow n)).mul (grep_cubN (𝟙 _) (𝟙 _) n).inv).triv hG
    (fun U _ h => by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
      module)
    (fun y J hJ => by
      beta_reduce
      rw [Category.comp_id, normd_one hν hJ, (isCub_cubV D.cub hJ).N_one, dbl_one hJ]
      simp) Y b z J hJ
  beta_reduce at key
  rw [Category.comp_id] at key
  exact eq_div_iff_mul_eq'.2 (mul_inv_eq_one.1 key)

end Gen

section Val
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

theorem toStk_sF' {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    toStk z (sF s r J) = sval s r z J := FamVal.toStk_sF hJ s r

theorem sym_eq (y : Sp F) (a : N.A) : val D.sym (ν.eA a).left y ν.J = toStkU y (N.σ a) :=
  ((eq_vF_iff _ _ (good ν y) _).1 (ν.σ_eq a)).symm

theorem kap_eq (hG : GlobalFnsSt) {n : ℕ} {κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)} (hκ : Normd κ) (y : Sp F)
    (a : N.A) : val κ (ν.eA a).left y ν.J = toStkU y (mulq N.θ N.σ n a)⁻¹ :=
  (val_kap (Y := TF (R := R) F) hG hκ _ (good ν y)).trans ((congrArg (·⁻¹) (mulq_map
    (θ' := cubV D.cub (T := TF (R := R) F) y ν.J) (σ' := fun x => val D.sym x.left y ν.J) ν.eA.toMonoidHom (toStkU y)
    (fun a b c => (theta_eq ν y a b c).symm) (sym_eq ν y) n a)).trans (map_inv _ _).symm)

theorem nu_eq (hG : GlobalFnsSt) {n : ℕ} {u : LB.Gen (nuLB D n)} (hu : Normd u) (y : Sp F)
    (a : N.A) : val u (ν.eA a).left y ν.J = toStkU y (cubN N.θ n 1 a a / dbl N.θ N.σ a ^ n) :=
  (val_nu (Y := TF (R := R) F) hG hu _ (good ν y)).trans ((congrArg₂ (fun p q => p / q ^ n) (cubN_map
    (θ' := cubV D.cub (T := TF (R := R) F) y ν.J) ν.eA.toMonoidHom (toStkU y)
    (fun a b c => (theta_eq ν y a b c).symm) n a a) (dbl_map
    (θ' := cubV D.cub (T := TF (R := R) F) y ν.J) (σ' := fun x => val D.sym x.left y ν.J) ν.eA.toMonoidHom (toStkU y)
    (fun a b c => (theta_eq ν y a b c).symm) (sym_eq ν y) a)).trans (by rw [map_div, map_pow]))

theorem txFrame_val [IsNoetherianRing R] (hL : Laws) {k : ℕ} (hk : Odd k) {p : QkPt D F k} {q : N.QT k} (hq : ν.QPt p q)
    {w : Frm D F k p.g.b} (hw : TXFrame k p w) : (N.wQ q : F) = vF w (𝟙 (Sp F)) ν.J := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν y
  obtain ⟨u, hu⟩ := exists_nu (D := D) hL.mulPull k
  obtain ⟨κ, hκ⟩ := exists_kap (D := D) hL.mulPull k
  obtain ⟨b₁, b₂⟩ := (pt_iff ν y _ _).1 hq.2
  obtain ⟨v, hv⟩ := (toStkU_bijective y).2 (val w (𝟙 (Sp F)) y ν.J)
  have e₁ : val u p.g.b.left y ν.J = _ := b₁ ▸ nu_eq ν hL.globalFns hu y q.1.2.b
  have e₂ : val κ p.g.b.left y ν.J = _ := b₁ ▸ kap_eq ν hL.globalFns hκ y q.1.2.b
  have e₃ : val (p.g.s p.y) (𝟙 _) y ν.J = toStkU y (q.1.2.s q.1.1.toAdd) := hq.1 ▸ (b₂ _).symm
  have e₄ : toStkU y (N.ψ q.1.1.toAdd) = @id ((TF (R := R) F).left.presheaf.stalk y)ˣ
      (val (D.psi p.y) (jFK (R := R) F) y ν.J) * rigV D (TF (R := R) F).hom y ν.J :=
    Units.ext ((congrArg (toStk y) (ν.ψ_eq _)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (hq.1 ▸ toStk_vF (D.psi (ν.eX q.1.1.toAdd)) (jFK (R := R) F) hJ) (toStk_vF _ _ hJ))))
  have a₁ : v ^ 2 = q.1.2.s q.1.1.toAdd * (cubN N.θ k 1 q.1.2.b q.1.2.b / dbl N.θ N.σ q.1.2.b ^ k) :=
    (toStkU_bijective y).1 (((map_pow _ _ _).trans (congrArg (· ^ 2) hv)).trans ((hw.2.1 u hu y ν.J hJ).trans
      ((congrArg₂ (· * ·) e₃ e₁).trans (map_mul _ _ _).symm)))
  have a₂ : v ^ k * (mulq N.θ N.σ k q.1.2.b)⁻¹ = N.ψ q.1.1.toAdd :=
    (toStkU_bijective y).1 (((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ k) hv))
      e₂.symm)).trans ((hw.2.2 κ hκ y ν.J hJ).trans e₄.symm))
  refine (eq_vF_iff _ _ hJ _).2 (Eq.trans (congrArg _ ?_) hv)
  obtain ⟨l, rfl⟩ := hk
  rw [NumD.wQ, NumB.wS, ← a₂, mul_div_assoc (q.1.2.s _), ← a₁, Nat.add_sub_cancel, Nat.mul_div_cancel_left l two_pos,
    inv_mul_cancel_right, ← pow_mul, pow_succ, mul_div_cancel_left]

theorem rg_ne : ν.rg ≠ 0 := fun h => by
  let y : Sp F := IsLocalRing.closedPoint F
  exact Units.ne_zero _ ((toStk_vF _ _ (good ν y)).symm.trans ((congrArg (toStk y) h).trans (map_zero _)))

theorem coef_val {k : ℕ} {s : Fam D F k} {f : N.X → N.A → F} (hs : ν.FamV s f) {g : GtPtF D F} {c : N.Gt} (hg : ν.Pt g c)
    {w : Frm D F k g.b} (hw : w.IsGen) (χ : N.X) :
    coef s g w (ν.eX χ) = f χ c.b * c.s χ * vF w (𝟙 (Sp F)) ν.J := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν y
  have a := isCoef_coef g hw (ν.eX χ) s y ν.J hJ
  have e₁ : sval (s.s (ν.eX χ)) (lift (𝟙 (TF (R := R) F)) g.b).left y ν.J = toStk y (f χ c.b * ν.rg ^ k) := by
    rw [hs χ c.b, hg.1]
    exact (toStk_sF' _ _ hJ).symm
  have e₂ : (val (g.s (ν.eX χ)) (𝟙 _) y ν.J).val = toStk y (c.s χ) := by
    rw [hg.2 χ]
    exact (toStk_vF _ _ hJ).symm
  have e : toStk y (coef s g w (ν.eX χ)) * toStk y ν.rg ^ k =
      toStk y (f χ c.b * ν.rg ^ k) * toStk y (c.s χ) * toStk y (vF w (𝟙 (Sp F)) ν.J) :=
    (congrArg₂ (fun a b => a * b ^ k) (gs_eq (𝟙 (Sp F)) y ⊤ trivial _).symm (toStk_vF _ _ hJ)).trans (a.trans
      (congrArg₂ (· * ·) (congrArg₂ (· * ·) e₁ e₂) (toStk_vF _ _ hJ).symm))
  rw [← map_pow, ← map_mul, ← map_mul, ← map_mul] at e
  refine mul_right_cancel₀ (pow_ne_zero k (rg_ne ν)) (((toStk y).injective e).trans ?_)
  ring

theorem vF_ne {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) : vF w (𝟙 (Sp F)) ν.J ≠ 0 := fun h => by
  let y : Sp F := IsLocalRing.closedPoint F
  exact Units.ne_zero _ ((toStk_vF _ _ (good ν y)).symm.trans ((congrArg (toStk y) h).trans (map_zero _)))

theorem famV_lin {k : ℕ} {s s' : Fam D F k} {f f' : N.X → N.A → F} (h : ν.FamV s f) (h' : ν.FamV s' f') (c : F) :
    ν.FamV (c • s + s') (c • f + f') := fun α x => by
  let y : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν y
  refine (toStk y).injective (Eq.trans ?_ ((toStk_sF' _ _ hJ).trans (sval_lin (ν.eA x) s s' c (ν.eX α) hJ)).symm)
  refine Eq.trans ?_ (congrArg₂ (· + ·) (congrArg₂ (· * ·) (gs_eq (𝟙 (Sp F)) y ⊤ trivial _).symm
    ((congrArg (toStk y) (h α x)).trans (toStk_sF' _ _ hJ))) ((congrArg (toStk y) (h' α x)).trans (toStk_sF' _ _ hJ)))
  refine Eq.trans (congrArg (toStk y) (?_ : _ = c * (f α x * ν.rg ^ k) + f' α x * ν.rg ^ k)) ?_
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  · rw [map_add, map_mul]; rfl

theorem coef_theta {ϑ : Fam D F 1} {c₀ : F} (h : ν.FamV ϑ (c₀ • N.vth)) {g : GtPtF D F} {c : N.Gt} (hg : ν.Pt g c)
    {w : Frm D F 1 g.b} (hw : w.IsGen) (χ : N.X) :
    coef ϑ g w (ν.eX χ) = c₀ * vF w (𝟙 (Sp F)) ν.J * N.vt c χ := by
  rw [coef_val ν h hg hw, NumD.vt, mul_comm (N.c χ), Units.val_mul]
  simp only [Pi.smul_apply, smul_eq_mul, NumD.vth]
  ring

end Val

theorem exists_gen_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L)
    (σ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hσ : σ.IsGen) (m : ℕ) (a : G ⟶ G)
    (ha : a = 𝟙 G ^ m) :
    ∃ β : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 _, a.left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), β.IsGen := by
  subst ha
  have hL := L.isLB
  have hcube : MulPull.HasGen L.L (thφ G (x3 G)) thε := ⟨c.t, c.isGen⟩
  have hrig : MulPull.HasGen L.L (K := PUnit) (fun _ => eSec G) (fun _ => 1) := ⟨L.rig, L.rigGen⟩
  have hsym : MulPull.HasGen L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1] := ⟨σ, hσ⟩
  have h := MulPull.hasGen_pow hL hcube (𝟙 G) ((hrig.pull G.hom).of_formEq hL (fun U _ h => by
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl))
    (hsym.inv.of_formEq hL (fun U _ h => by
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Hom.inv_def, Category.id_comp, mul_comm]
      rfl)) m
  refine h.of_formEq hL fun U _ h => ?_
  rw [Fin.prod_univ_two, Fin.prod_univ_two, Nat.cast_pow]
  rfl

section Frames
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frm_pow {b : TF (R := R) F ⟶ D.P.A} (ω : Frm D F 1 b) (hω : ω.IsGen) (k : ℕ) :
    ∃ w : Frm D F k b, w.IsGen ∧ ∀ z J, Good D.P.L z J → val w (𝟙 _) z J = val ω (𝟙 _) z J ^ k := by
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε k) (fun U _ h => by
      rw [prod_line, Fin.prod_univ_two]
      show h (1 : TF (R := R) F ⟶ D.P.A).left ^ ((k : ℤ) * ((1 : ℕ) : ℤ)) * h b.left ^ ((k : ℤ) * -((1 : ℕ) : ℤ)) = _
      simp)
    (GeneratorPullback.powGen D.P.L _ _ ω k) (powGen_isGen _ _ _ ω hω k)
  exact ⟨w, hw, fun z J hJ => (hv _ _ z J hJ).trans (map_pow _ _ _)⟩

theorem exists_frm_kap {k' k : ℕ} {b b' : TF (R := R) F ⟶ D.P.A} {a : D.P.A ⟶ D.P.A} (hb : b' = b ≫ a)
    (W : Frm D F k' b) (hW : W.IsGen) (κ : LB.Gen (kapLB D a k' k)) (hκ : κ.IsGen) :
    ∃ w : Frm D F k b', w.IsGen ∧ ∀ z J, Good D.P.L z J →
      val W (𝟙 _) z J * val κ b.left z J = val w (𝟙 _) z J := by
  have a₁ : b.left ≫ a.left = b'.left := by rw [hb, Over.comp_left]
  have a₂ : b.left ≫ (1 : D.P.A ⟶ D.P.A).left = (1 : TF (R := R) F ⟶ D.P.A).left := by
    rw [← Over.comp_left, MonObj.comp_one]
  obtain ⟨w, hw, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b') (ε' := DegPre.lineε k) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      refine (congrArg₂ (· * ·) (prod_line k' b h) (Fin.prod_univ_three _)).trans ?_
      rw [prod_line]
      show _ * (h (b.left ≫ 𝟙 _) ^ (k' : ℤ) * h (b.left ≫ a.left) ^ (-(k : ℤ)) *
        h (b.left ≫ (1 : D.P.A ⟶ D.P.A).left) ^ ((k : ℤ) - k')) = _
      rw [Category.comp_id, a₁, a₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen D.P.L _ _ _ _ W (LB.pullGen D.P.L _ _ κ b.left))
    (mulGen_isGen _ _ _ _ _ _ _ hW (pullGen_isGen _ _ _ _ hκ _))
  refine ⟨w, hw, fun z J hJ => Eq.symm ((hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_)))⟩
  exact (val_pull hJ _ _ _).trans (by rw [Category.id_comp])

theorem exists_secA_mul {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k k' : ℕ} (t : SecA A F k)
    (t' : SecA A F k') : ∃ t'' : SecA A F (k + k'), ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J),
      Good A.L z J → sA t'' r z J = sA t r z J * sA t' r z J := by
  obtain ⟨t'', h⟩ := exists_sec A.isLB (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (ε' := fun _ => ((k + k' : ℕ) : ℤ)) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Nat.cast_add, zpow_add])
    (H1.SectionArithmetic.mulSec (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (k : ℤ))
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (k' : ℤ)) t t')
  exact ⟨t'', fun Z r z J hJ => (h Z r z J hJ).trans (H1.SectionArithmetic.sval_mulSec _ _ r z hJ)⟩

theorem exists_scale {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Sp F ⟶ X)} {ε : K → ℤ}
    (ω : LB.Gen (LB.LinComb L φ ε)) (hω : ω.IsGen) {c : F} (hc : c ≠ 0) :
    ∃ w : LB.Gen (LB.LinComb L φ ε), w.IsGen ∧ ∀ z J, Good L z J →
      (val w (𝟙 _) z J).val = toStk z c * (val ω (𝟙 _) z J).val := by
  let u : Γ(Sp F, ⊤)ˣ := ((Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  refine ⟨DVR.scaleGen u ω, DVR.scaleGen_isGen u ω hω, fun z J hJ => ?_⟩
  have e : val (DVR.scaleGen u ω) (𝟙 _) z J = gm (𝟙 _) z ⊤ u * val ω (𝟙 _) z J :=
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) z le_top (hJ.mem _ (𝟙 _)) u) rfl)
  rw [e, Units.val_mul, ← gs_unit (𝟙 _) z ⊤ trivial u]
  exact congrArg (· * _) (gs_eq _ z ⊤ trivial _)

end Frames

theorem isCoordPt_of_eq {S : Scheme.{0}} (P : PolAV S) (m : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A)) (z : T ⟶ P.A)
    (w : I → Γ(T.left, ⊤)) (hm : Odd m) (hu : IsUnit (m : Γ(T.left, ⊤))) {k : ℤ} (hk : k = (m : ℤ) ^ 2)
    (th : LB.Sec (LPow P.A P.L 1 T)) (s₁ : LB.Sec (LPow P.A P.L k T))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![k, -1]))
    (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => k)))
    (U : I → ThetaGrp P.A P.L k T) (s₂ : I → LB.Sec (LPow P.A P.L k T))
    (h₁ : IsGenSec P.A P.L 1 th) (h₂ : α.IsGen) (h₃ : τ.IsGen)
    (h₄ : IsTwistPull P.A P.L (mulT P.A T m) (snd T P.A ^ m) (lift_snd _ _) k 1 α th s₁)
    (h₅ : ∀ i, SymLift P.A P.L k (m ^ 2) (x i) (U i)) (h₆ : ∀ i, IsActOf P.A P.L k (U i) s₁ (s₂ i))
    (h₇ : ∀ i, IsValueAt P.A P.L k (s₂ i) z τ (w i)) : IsCoordPt P m x z w := by
  subst hk
  exact ⟨hm, hu, th, s₁, α, τ, U, s₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩

section Unif
variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C]

abbrev ValIs {k : ℕ} (t : SecA A C k) (x : TFK (R := R) C ⟶ A.A)
    (e : LB.Gen (LB.LinComb A.L (Y := (TFK (R := R) C).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) (c : C) : Prop :=
  ∀ z J, Good A.L z J → sA t (ptSecT A.A x).left z J = @id ((TFK (R := R) C).left.presheaf.stalk z)
    (cst (R := R) C z c) * (val (powFrame A.A A.L x e k) (𝟙 _) z J).val

omit [CompleteSpace C] in

theorem value_at_level (hL : LL) (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) (hC : CExt R I C)
    {w₀ ρ} (hN : NormW U.toUnifPre w₀ ρ) {N : ℕ} (hN1 : 1 ≤ N) (q : QkPt D.toPre C N) (x : TFK (R := R) C ⟶ A.A)
    (hx : QkToAkU U.toUnifPre C N q x) (e) (he : e.IsGen) (w : Frm D.toPre C N q.g.b) (hw : w.IsGen) :
    ∃ κ : C, κ ≠ 0 ∧ ∀ (t : SecA A C N) s (c : C), U.ExpandsF C N w₀ t s → ValIs t x e c →
      HasSum (coef s q.g w) (κ * c) := by
  haveI : IsNoetherianRing R := hB.1
  haveI : Subsingleton (TFK (R := R) C).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of C)))
  haveI : Nonempty (TFK (R := R) C).left := inferInstanceAs (Nonempty (Spec (CommRingCat.of C)))
  obtain ⟨hxN, hθ⟩ := hx w₀ hN.1
  obtain ⟨θ, rfl⟩ := GlobalTheory.BoxTheta.exists_theta hL.1.kerPow A hN1 (T := TFK (R := R) C) x hxN
  obtain ⟨w', hw', hΦ⟩ := hθ θ rfl
  obtain ⟨u, hu, hval⟩ := EvalLevel.exists_act_value hN.2.1 N θ e he
  obtain ⟨o, ho⟩ := exists_zero_gt (D := D.toPre) (F := C)
  obtain ⟨w₁, hw₁⟩ := (coef_basic R D.toPre C N o).2.1 ho.1
  have hadd : o.IsAdd q.g q.g := by
    rw [GlobalTheory.TorusExt.isZero_unique ho GlobalTheory.TorusExt.isZero_gtZero]
    have := GlobalTheory.TorusExt.isAdd_gtAdd (GlobalTheory.TorusExt.gtZero D.toPre C) q.g
    rwa [GlobalTheory.TorusExt.gtZero_add] at this
  obtain ⟨ω, hω, -, hc⟩ := GlobalTheory.UT.CoefPhi.coef_phi hL R _ hB D C N hN1 q w' hw' o q.g hadd w₁ hw₁.1
  obtain ⟨d, hd, -, hdc⟩ := ((coef_basic R D.toPre C N q.g).2.2 ω hω).2.2.1 w hw
  refine ⟨d * u, mul_ne_zero hd hu, fun t s c hts hc' => ?_⟩
  obtain ⟨t', ht'⟩ := GlobalTheory.VVRank.exists_isTwistPull A.A (ψ := translT A.A θ.pt) (m := translPt A.A θ.pt)
    (hm := lift_snd _ _) (a := N) (b := N) (α := θ.φ) A.isLB θ.isGen t
  obtain ⟨s', hs', -⟩ := ((GlobalTheory.UT.expBijF_and_expandsF_lin hL R _ hB D A G hG U).1 C N hN1 w₀ hN.1).1 t'
  have h₁ := (GlobalTheory.UT.EvalZero.value_at_origin hL R _ hB D A G hG U C).2.2 w₀ ρ hN N t' s' hs' o w₁ ho hw₁ (u * c)
    (hval t t' c ht' hc')
  have h₂ := (Equiv.addRight q.y).hasSum_iff.2 (GlobalTheory.T.hasSum_of_adicSum_unitBallExtension R I C hC _ _ _ h₁)
  have h₃ := hc 1 N le_rfl (Nat.mul_one N).symm q (one_nsmul _).symm rfl w' w₁ ω ⟨hw', fun _ _ _ => (pow_one _).symm⟩
    ⟨hw₁.1, fun _ _ _ => (pow_one _).symm⟩ ⟨hω, fun _ _ _ => (pow_one _).symm⟩ s s' (hΦ t t' s s' hts hs' ht')
  have h₄ := h₂.mul_left d
  simp only [Function.comp_apply, Equiv.coe_addRight, h₃, ← hdc] at h₄
  rw [_root_.mul_assoc]
  exact h₄

attribute [local instance] TorusExt.gtGroup in

theorem value_at_torsion (hL : LL) (hB : AdmBase R I) (hG : IsSemiAbelian G) (U : Unif I D A G) (hC : CExt R I C)
    {w₀ ρ} (hN : NormW U.toUnifPre w₀ ρ) {n : ℕ} (hn : 1 ≤ n) (p : QkPt D.toPre C n) (x : TFK (R := R) C ⟶ A.A)
    (hx : QkToAkU U.toUnifPre C n p x) (e) (he : e.IsGen) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (w : Frm D.toPre C k p.g.b) (u : C), w.IsGen ∧ u ≠ 0 ∧ ∀ (t : SecA A C k) s (c : C), U.ExpandsF C k w₀ t s →
      ValIs t x e c → Summable (coef s p.g w) → HasSum (coef s p.g w) (u * c) := by
  haveI : IsNoetherianRing R := hB.1
  have hbij := (expBijF_and_expandsF_lin hL R _ hB D A G hG U).1 C
  obtain ⟨ω, hω⟩ := (coef_basic R D.toPre C 1 p.g).1
  choose Ω hΩ hΩv using exists_frm_pow ω hω
  have pf : ∀ (k : ℤ) z J, val (powFrame A.A A.L x e k) (𝟙 _) z J = val e (𝟙 _) z J ^ k := fun k z J => map_zpow _ _ _
  obtain ⟨u, hu, H⟩ := GlobalTheory.T.hasSum_graded_of_mul_degree' C D.toPre.X (fun k a c => ∃ (t : SecA A C k) (s : Fam D.toPre C k),
      U.ExpandsF C k w₀ t s ∧ ValIs t x e c ∧ a = coef s p.g (Ω k)) n k hn hk
    (by
      rintro k k' _ _ c c' hk hk' ⟨t, s, hs, ht, rfl⟩ ⟨t', s', hs', ht', rfl⟩
      obtain ⟨t'', h''⟩ := exists_secA_mul t t'
      obtain ⟨s'', hs'', -⟩ := (hbij (k + k') (by omega) w₀ hN.1).1 t''
      refine ⟨_, ⟨t'', s'', hs'', fun z J hJ => ?_, rfl⟩, fun α => GlobalTheory.T.hasSum_of_adicSum_unitBallExtension R I C hC _ _ _
        (ProdConv.main hL R _ hB D A G hG U C w₀ hN.1 k k' _ hk hk' rfl t t' t'' s s' s'' hs hs' hs''
          (fun z J hJ => h'' _ _ z J hJ) p.g _ _ _ (hΩ k) (hΩ k') (hΩ _)
          (fun z J hJ => by rw [hΩv _ z J hJ, hΩv _ z J hJ, hΩv _ z J hJ, pow_add]) α)⟩
      have cm : @id ((TFK (R := R) C).left.presheaf.stalk z) (cst (R := R) C z (c * c')) =
          @id ((TFK (R := R) C).left.presheaf.stalk z) (cst (R := R) C z c) *
            @id ((TFK (R := R) C).left.presheaf.stalk z) (cst (R := R) C z c') :=
        (cst_eq (R := R) z _).trans ((map_mul _ _ _).trans
          (congrArg₂ (· * ·) (cst_eq (R := R) z _).symm (cst_eq (R := R) z _).symm))
      rw [h'' _ _ z J hJ, ht z J hJ, ht' z J hJ, pf, pf, pf, cm, Nat.cast_add, zpow_add, Units.val_mul]
      ring)
    (by
      let q : QkPt D.toPre C (n * k) := TorusExt.qkMk D.tau_bimult (k • p.y) p.g (by
        rw [mul_nsmul, TorusExt.qk_nsmul D.tau_bimult p, map_nsmul])
      have hq : QkToAkU U.toUnifPre C (n * k) q x :=
        ((GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL R _ hB D A G hG U C n k _ hn hk rfl p q x).1 rfl rfl).1 hx
      obtain ⟨κ, hκ, Hκ⟩ := value_at_level hL hB hG U hC hN (Nat.mul_pos hn hk) q x hq e he (Ω _) (hΩ _)
      refine ⟨κ, hκ, ?_⟩
      rintro _ c ⟨t, s, hs, ht, rfl⟩
      exact Hκ t s c hs ht)
  exact ⟨Ω k, u, hΩ k, hu, fun t s c hs ht => H _ c ⟨t, s, hs, ht, rfl⟩⟩

theorem summable_vt [IsLocalRing R] (hL : LL) (hgt : BrGtSt) (hfam : BrFamSt) (hB : AdmBase R I) (hC : CExt R I C)
    {N : NumD C} (ν : NumOf D.toPre C N) {ϑ : Fam D.toPre C 1} {c₀ : C} (hc₀ : c₀ ≠ 0) (hϑ : ν.FamV ϑ (c₀ • N.vth))
    {k : ℕ} (hk : k ≠ 0) (q : N.QT k) : Summable (N.vt q.1.2) := by
  haveI : IsNoetherianRing R := hB.1
  have mem : ∀ x : C, x ∈ (NormedField.valuation (K := C)).valuationSubring ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  obtain ⟨N', ν', hν'⟩ := GlobalTheory.ValuesExist.exists_integral_values hL.1 R D.toPre D.psi_even D.tau_bimult C _
    (fun r => (mem _).2 (hC.1 r))
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase R I hB D C hC N' ν' ⟨_, mem, hν'⟩
  obtain ⟨p, hp⟩ := ((hgt R D.toPre D.psi_even D.tau_bimult C N ν).2.2.2.2 k).2.1 q
  obtain ⟨q', hq', -⟩ := ((hgt R D.toPre D.psi_even D.tau_bimult C N' ν').2.2.2.2 k).1 p
  obtain ⟨h₁, -, -, -, h₂, -⟩ := hfam R D.toPre D.psi_even D.tau_bimult C N' ν' 1 le_rfl
  obtain ⟨f, hf, -⟩ := h₁ ϑ
  obtain ⟨c', rfl⟩ := h₂ ϑ f hf
  obtain ⟨w, hw⟩ := (coef_basic R D.toPre C 1 p.g).1
  have a₁ : Summable (coef ϑ p.g w ∘ ν'.eX.toEquiv) :=
    ((GlobalTheory.T.summable_vt_of_int C N' Q hQ k hk q').mul_left _).congr fun χ => (coef_theta ν' hf hq'.2 hw χ).symm
  have a₂ := ν.eX.toEquiv.summable_iff.2 (ν'.eX.toEquiv.summable_iff.1 a₁)
  exact (summable_mul_left_iff (mul_ne_zero hc₀ (vF_ne ν w))).1 (a₂.congr fun χ => coef_theta ν hϑ hp.2 hw χ)

omit [CharZero R] [IsUltrametricDist C] [CompleteSpace C] in

theorem exists_theta (hL : LL) (hfam : BrFamSt) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw : w₀.IsGen)
    {N : NumD C} (ν : NumOf D.toPre C N) : ∃ (th : SecA A C 1) (ϑ : Fam D.toPre C 1) (c₀ : C), c₀ ≠ 0 ∧
      U.ExpandsF C 1 w₀ th ϑ ∧ ν.FamV ϑ (c₀ • N.vth) ∧ IsGenSec A.A A.L 1 th := by
  obtain ⟨h₁, h₂, -, ⟨ϑ, f, hf, hf0⟩, h₃, -⟩ := hfam R D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨c₀, rfl⟩ := h₃ ϑ f hf
  have hc₀ : c₀ ≠ 0 := fun h => hf0 (by rw [h, zero_smul])
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hL.1.globalFns U C (k := 1) le_rfl w₀ hw
  refine ⟨e.symm ϑ, ϑ, c₀, hc₀, (he _ _).2 (e.apply_symm_apply ϑ), hf, fun t => ?_⟩
  obtain ⟨f', hf', -⟩ := h₁ (e t)
  obtain ⟨c, rfl⟩ := h₃ _ f' hf'
  have a₁ := famV_lin ν hf hf (c / c₀ - 1)
  rw [smul_smul, ← add_smul, sub_mul, div_mul_cancel₀ _ hc₀, _root_.one_mul, sub_add_cancel] at a₁
  have a₂ := h₂ _ _ _ hf' a₁
  rw [sub_smul, one_smul, sub_add_cancel] at a₂
  have ht : t = ((c / c₀) • e.symm ϑ : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A C) _) :=
    e.injective (a₂.trans (by rw [map_smul, e.apply_symm_apply]))
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c / c₀), fun j => ?_⟩
  rw [ht]
  rfl

end Unif

theorem coord_eq_series : HV → BrGtSt → BrFamSt → EVSt := by
  rintro ⟨hL, -⟩ hgt hfam R _ _ _ _ ⟨hdvr, hcpl, hch⟩ rfl D A G _ _ hG U C _ _ _ _ _ _ hC N ν m hm Ix p q x hx hq j hj
    p₀ q₀ z hz hq₀
  have hB : AdmBase R (IsLocalRing.maximalIdeal R) := ⟨inferInstance, inferInstance, inferInstance, hcpl⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm.pos
  have hLB := A.isLB
  let y : Sp C := IsLocalRing.closedPoint C
  obtain ⟨⟨ρ, hρ⟩, hw₀, -⟩ := EvalZero.value_at_origin hL R _ hB D A G hG U C
  obtain ⟨w₀, hN⟩ := hw₀ ρ hρ
  obtain ⟨th, ϑ, c₀, hc₀, hth, hϑ, hgen⟩ := exists_theta hL hfam U hN.1 ν
  obtain ⟨⟨_, _⟩, ⟨α, s₁, -, hα, hαn, hs₁, -⟩, -⟩ :=
    GlobalTheory.existsUnique_thetaConst hL R A C ρ hρ m hm th 1 (one_pow _)
  have hbij := (expBijF_and_expandsF_lin hL R _ hB D A G hG U).1 C (m ^ 2) hm2 w₀ hN.1
  obtain ⟨σ₁, hσ₁, -⟩ := hbij.1 s₁
  obtain ⟨hv₁, -, -, -, -, hv₂⟩ := hfam R D.toPre D.psi_even D.tau_bimult C N ν (m ^ 2) hm2
  obtain ⟨f₁, hf₁, -⟩ := hv₁ σ₁
  obtain ⟨E, hEG, hEA, hEB, hEh, hEact⟩ := (IntEnd.exists_nsmul_and_neg hL R _ hB D A G hG U).1 m
  have hsm : ∀ {X : Type} [AddCommGroup X] [Module.Free ℤ X], Function.Injective fun χ : X => m • χ := by
    intro X _ _ a b h
    have h' : (m : ℤ) • a = (m : ℤ) • b := by simpa only [natCast_zsmul] using h
    exact smul_right_injective _ (Int.natCast_ne_zero.2 hm0) h'
  have hinj : Function.Injective E.h := fun a b h => hsm (by simpa only [hEh] using h)
  have hpull := (PullExp.main hL R _ hB D A G hG U C E hinj (m ^ 2) 1 le_rfl hm2
    (exists_gen_pow U.LG U.cubG U.symG U.symG_gen m E.aG hEG)).2 w₀ ρ hN (mulT A.A _ m) (snd _ A.A ^ m) (lift_snd _ _)
    (lift_fst _ _) (by rw [hEA, MonObj.comp_pow, Category.comp_id]) α hα hαn th s₁ ϑ σ₁ hth hσ₁ hs₁
  rw [hEB] at hpull
  obtain ⟨κ, hκ⟩ := exists_kap (D := D.toPre) hL.1.mulPull m
  have pull : ∀ h : N.Gt, (∀ χ, f₁ (m • χ) h.b * h.s (m • χ) =
      c₀ * N.vt (h ^ m) χ * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ)) ∧ ∀ β, (∀ χ, β ≠ m • χ) → f₁ β h.b = 0 := fun h => by
    obtain ⟨g, hg⟩ := GtValues.exists_pt ν h
    obtain ⟨g', hg'⟩ := GtValues.exists_pt ν (h ^ m)
    have act := (hEact C g g').2 ((isNsmul_val ν m hg hg').2 rfl)
    obtain ⟨W, hW⟩ := (coef_basic R D.toPre C (m ^ 2) g).1
    obtain ⟨w, hw, hwv⟩ := exists_frm_kap (act.1.trans (congrArg _ hEB)) W hW κ hκ.1
    obtain ⟨r₁, r₂⟩ := hpull κ hκ g g' act W w hW hw hwv
    have hJ := good ν y
    have e₁ : val κ g.b.left y ν.J = _ := hg.1 ▸ kap_eq ν hL.1.globalFns hκ y h.b
    have e₂ : vF w (𝟙 (Sp C)) ν.J = vF W (𝟙 (Sp C)) ν.J * ((mulq N.θ N.σ m h.b)⁻¹ : Cˣ) :=
      (toStk y).injective ((GtValues.toStk_vF _ _ hJ).trans ((congrArg Units.val (hwv y ν.J hJ)).symm.trans
        (((Units.val_mul _ _).trans (congrArg₂ (· * ·) (GtValues.toStk_vF _ _ hJ).symm (congrArg Units.val e₁))).trans
          (map_mul (toStk y) _ _).symm)))
    refine ⟨fun χ => mul_right_cancel₀ (vF_ne ν W) ?_, fun β hβ => ?_⟩
    · have a := r₁ (ν.eX χ)
      rw [hEh, ← map_nsmul, coef_val ν hf₁ hg hW, coef_theta ν hϑ hg' hw, e₂] at a
      rw [a]; ring
    · have a := r₂ (ν.eX β) (by
        rintro ⟨χ, e⟩
        exact hβ (ν.eX.symm χ) (ν.eX.injective (by rw [map_nsmul, ν.eX.apply_symm_apply, ← hEh, e])))
      rw [coef_val ν hf₁ hg hW] at a
      exact (mul_eq_zero.1 ((mul_eq_zero.1 a).resolve_right (vF_ne ν W))).resolve_right (Units.ne_zero _)
  obtain ⟨e, he⟩ := exists_gen_pt hLB (Y := (TFK (R := R) C).left) y (fun y' => pt_eq (R := R) y' y)
    (fun _ : Fin 1 => z.left) (fun _ => 1)
  obtain ⟨Ω, u, hΩ, hu, H⟩ := value_at_torsion hL hB hG U hC hN (by omega) p₀ z hz e he hm2
  have hd : c₀ * vF Ω (𝟙 (Sp C)) ν.J ≠ 0 := mul_ne_zero hc₀ (vF_ne ν Ω)
  have he' := EvalLevel.powFrame_isGen z e he ((m ^ 2 : ℕ) : ℤ)
  obtain ⟨τ, hτ, hτv⟩ := exists_scale (F := C) _ he' (div_ne_zero hd hu)
  have key : ∀ i, ∃ (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) C)) (t : SecA A C (m ^ 2)),
      SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) (x i) θ ∧ IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
      IsValueAt A.A A.L ((m ^ 2 : ℕ) : ℤ) t z τ (fnOf (N.ev m (q i) q₀.1.2)) := fun i => by
    obtain ⟨⟨_, _⟩, ⟨_, _, θ, -, -, -, hθ, -⟩, -⟩ :=
      GlobalTheory.existsUnique_thetaConst hL R A C ρ hρ m hm th (x i) (hx i w₀ hN.1).1
    obtain ⟨t, ht⟩ := ThetaPtExist.exists_isTwistPull hLB (translT A.A θ.pt) (translPt A.A θ.pt) (lift_snd _ _)
      ((m ^ 2 : ℕ) : ℤ) ((m ^ 2 : ℕ) : ℤ) θ.φ θ.isGen s₁
    obtain ⟨σ, hσ, -⟩ := hbij.1 t
    obtain ⟨f, hf, -⟩ := hv₁ σ
    obtain ⟨w, hw⟩ := (SymFrame.main hL R _ hB D C (m ^ 2) hm.pow (p i)).1
    have hΦ := symLift_acts_as_phi hL R _ hB D A G hG U C (m ^ 2) hm.pow (p i) (x i) (hx i) θ hθ w₀ hN.1 w hw s₁ t σ₁ σ
      hσ₁ hσ ht
    obtain rfl := (hv₂ (p i) (q i) w _ σ₁ σ f₁ f (hq i) hw.1 (txFrame_val ν hL.1 hm.pow (hq i) hw) hf₁ hf).1 hΦ
    obtain ⟨v, hv⟩ := ThetaPtExist.exists_isValueAt hLB t z _ he'
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).2 v
    have hc : ValIs t z e c := fun z' J hJ => ThetaCompare.sval_valueAt hv hJ
    let l : N.X → D.toPre.X := fun χ => ν.eX (m • χ + (q i).1.1.toAdd)
    have hl : Function.Injective l := fun a b h => hsm (add_right_cancel (ν.eX.injective h))
    have on : coef σ p₀.g Ω ∘ l = fun χ => c₀ * vF Ω (𝟙 (Sp C)) ν.J * N.evT m (q i) q₀.1.2 χ := funext fun χ => by
      refine (coef_val ν hf hq₀.2 hΩ _).trans ?_
      rw [phi_term N m (q i) q₀.1.2 f₁ c₀ χ ((pull _).1 χ), mul_right_comm]
    have off : ∀ β, β ∉ Set.range l → coef σ p₀.g Ω β = 0 := fun β hβ => by
      obtain ⟨β, rfl⟩ := ν.eX.surjective β
      have a := (pull (q₀.1.2 * (q i).1.2)).2 (β - (q i).1.1.toAdd) fun χ e =>
        hβ ⟨χ, congrArg ν.eX (sub_eq_iff_eq_add.1 e).symm⟩
      rw [NumD.Gt.mul_b] at a
      rw [coef_val ν hf hq₀.2 hΩ, NumD.phi, a]
      simp
    let Q : N.QT (j * m) := ⟨(q₀.1.1 ^ (m ^ 2) * (q i).1.1 ^ j, (q₀.1.2 * (q i).1.2) ^ m), by
      rw [NumD.mem_QT, ← pow_mul, mul_pow, toAdd_mul, toAdd_pow, toAdd_pow, N.io_add, N.io_nsmul, N.io_nsmul,
        ← N.mem_QT.1 q₀.2, ← N.mem_QT.1 (q i).2, ← pow_mul, ← pow_mul]
      congr 2 <;> ring⟩
    have sm : Summable (N.evT m (q i) q₀.1.2) :=
      (summable_vt hL hgt hfam hB hC ν hc₀ hϑ (Nat.mul_ne_zero (by omega) hm0) Q).mul_left _
    have a₁ : HasSum (coef σ p₀.g Ω) (c₀ * vF Ω (𝟙 (Sp C)) ν.J * N.ev m (q i) q₀.1.2) :=
      (hl.hasSum_iff off).1 (on ▸ sm.hasSum.mul_left _)
    have a₂ := (H t σ c hσ hc a₁.summable).unique a₁
    have a₃ : c = N.ev m (q i) q₀.1.2 * (c₀ * vF Ω (𝟙 (Sp C)) ν.J / u) := by
      field_simp
      linear_combination a₂
    refine ⟨θ, t, hθ, ht, ThetaCoord.isValueAt_of_sv hLB hτ fun z' J hJ => (hc z' J hJ).trans ?_⟩
    have alg : ∀ {S : Type} [CommRing S] (a b c d e f : S), a = b * c → e = c * d → f = b → a * d = f * e := by
      rintro S _ _ b c d _ _ rfl rfl rfl
      exact _root_.mul_assoc _ _ _
    exact alg (S := (Sp C).presheaf.stalk z') _ _ _ _ _ _ ((gs_eq (𝟙 (Sp C)) z' ⊤ trivial _).trans
      ((congrArg (toStk z') a₃).trans (map_mul _ _ _))) (hτv z' J hJ) (gs_eq (𝟙 (Sp C)) z' ⊤ trivial _)
  choose θ t hθ ht hv using key
  refine isCoordPt_of_eq A m x z _ hm ?_ (Nat.cast_pow m 2) th s₁ α τ θ t hgen hα hτ hs₁ hθ ht hv
  have := (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hm0 : (m : C) ≠ 0)).map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
  rwa [map_natCast] at this

end GlobalTheory.Ex.CoordSeries
end
