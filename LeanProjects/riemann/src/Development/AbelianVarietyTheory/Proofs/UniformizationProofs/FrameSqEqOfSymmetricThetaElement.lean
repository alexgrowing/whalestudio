import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FamEqOfCoefEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalOfIsTwistPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijFAndExpandsFLin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNsmulAndNeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.SymFrame

theorem exists_sval_ne_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] {K : Type} [Fintype K] {φ : K → ((DegPre.BF D F).left ⟶ D.P.A.left)} {ε : K → ℤ}
    (σ : LB.Sec (LB.LinComb D.P.L φ ε)) (hσ : ¬ ∀ j, σ.f j = 0) (z : (TF (R := R) F).left) {J}
    (hJ : Good D.P.L z J) : ∃ x : TF (R := R) F ⟶ D.P.A, sval σ (lift (𝟙 (TF (R := R) F)) x).left z J ≠ 0 := by
  by_contra H
  push_neg at H
  have hsm := D.P.isAb.smooth
  let p : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsReduced (DegPre.BF D F).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  refine hσ fun j => CoefDet.fn_ext_of_points p fun r hr z' hz => ?_
  obtain rfl : z' = z := CoefBasic.pt_eq (R := R) z' z
  let r' : TF (R := R) F ⟶ DegPre.BF D F := Over.homMk r (by
    rw [← Over.w (fst (TF (R := R) F) D.P.A), ← Category.assoc]
    exact (congrArg (· ≫ (TF (R := R) F).hom) hr).trans (Category.id_comp _))
  have er : lift (𝟙 (TF (R := R) F)) (r' ≫ snd _ _) = r' := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
    rw [lift_fst]
    exact Over.OverMorphism.ext hr.symm
  have a := H (r' ≫ snd _ _)
  rw [er] at a
  refine (sec_trans σ r z' hz (hJ.mem _ r)).trans (((congrArg _ a).trans (mul_zero _)).trans ?_)
  rw [gs_eq r z' _ hz, map_zero, map_zero]

theorem exists_normW {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : UnifPre I D A G) (w₀ : W0 U) (hw : w₀.IsGen) : ∃ ρ, NormW U w₀ ρ := by
  have := U.gen_hom
  let e : Spec (CommRingCat.of (FractionRing R)) ⟶ ((Over.pullback (jK R)).obj G).left :=
    eSec ((Over.pullback (jK R)).obj G)
  let eA : Spec (CommRingCat.of (FractionRing R)) ⟶ A.A.left := eSec A.A
  have e₁ : e ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G := by
    simp [e, eSec]
    erw [pullback.lift_fst]
    rw [← Category.assoc, ← pullback.condition, Category.comp_id]
  have e₂ : e ≫ U.gen.hom.left = eA :=
    congrArg (fun q => q.left) (IsMonHom.one_hom U.gen.hom)
  have pt : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) z z'
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  obtain ⟨i, hi⟩ := exists_chart U.LG.isLB ((jK R ≫ eSec G) z₀)
  have hi' : ∀ z, (jK R ≫ eSec G) z ∈ U.LG.L.U i := fun z => pt z₀ z ▸ hi
  have m₁ : ∀ z i, (jK R ≫ eSec G) z ∈ U.LG.L.U i → pullback.fst G.hom (jK R) (e z) ∈ U.LG.L.U i := fun z i h =>
    (congrArg (fun q => q z ∈ U.LG.L.U i) e₁).mpr h
  have m₂ : ∀ z (j : PUnit → A.L.ι), eA z ∈ A.L.U (j PUnit.unit) → e z ∈ (A.L.pull U.gen.hom.left).U j :=
    fun z j h => mem_pull.2 ((congrArg (fun q => q z ∈ A.L.U (j PUnit.unit)) e₂).mpr h)
  have l₁ : ∀ j : PUnit → A.L.ι, (A.L.pull eA).U j ≤
      e ⁻¹ᵁ ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => i) ⊓ (A.L.pull U.gen.hom.left).U j) :=
    fun j z hz => ⟨mem_pull.2 (m₁ z i (hi' z)), m₂ z j (mem_pull.1 hz)⟩
  have l₂ : ∀ j : PUnit → A.L.ι, (A.L.pull eA).U j ≤ jK R ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => i) :=
    fun j z _ => mem_pull.2 (hi' z)
  let ρ : LB.Gen (A.L.pull eA) := ⟨fun j => (res (l₁ j) (pullU e _ (w₀.s (fun _ => i, j))))⁻¹ *
    res (l₂ j) (pullU (jK R) _ (U.LG.rig.s fun _ => i))⟩
  have v : ∀ z j, z ∈ (A.L.pull eA).U j → gm (𝟙 _) z _ (ρ.s j) = (gw w₀ e z i j)⁻¹ *
      gm (jK R) z ((U.LG.L.pull (eSec G)).U (fun _ => i)) (U.LG.rig.s fun _ => i) := fun z j hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res _ z _ hz _).trans
      (gm_pull (𝟙 _) e z ((U.LG.L.pull (pullback.fst G.hom (jK R))).U (fun _ => i) ⊓ (A.L.pull U.gen.hom.left).U j)
        (l₁ j hz) _)))) ((gm_res _ z _ hz _).trans
      (gm_pull (𝟙 _) (jK R) z ((U.LG.L.pull (eSec G)).U (fun _ => i)) (l₂ j hz) _)))
  have P := (isGen_iff w₀).1 hw
  refine ⟨ρ, hw, fun j j' => unit_ext fun z hz => ?_, fun z JA JG hA hG => ?_⟩
  · refine ((gm_res _ z _ hz _).trans (v z j hz.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_pull_g A.L eA (𝟙 _) z j j' hz.1 hz.2) ((gm_res _ z _ hz _).trans (v z j' hz.2)))).symm)
    have a := P _ e z i i j j' (m₁ z i (hi' z)) (m₁ z i (hi' z)) (m₂ z j (mem_pull.1 hz.1)) (m₂ z j' (mem_pull.1 hz.2))
    rw [gm_self U.LG.isLB (e ≫ _) z (m₁ z i (hi' z)),
      gm_pull_g A.L _ e z j j' (m₂ z j (mem_pull.1 hz.1)) (m₂ z j' (mem_pull.1 hz.2)), e₂] at a
    rw [a, Category.id_comp, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]
  · have h₁ := m₂ z (fun _ => JA (eSec A.A)) (hA _)
    have a := P _ e z (JG (jK R ≫ eSec G)) i _ _ (m₁ z _ (hG _)) (m₁ z i (hi' z)) h₁ h₁
    rw [gm_pull_g A.L _ e z _ _ h₁ h₁,
      gm_self A.isLB (e ≫ U.gen.hom.left) z (i := JA (eSec A.A)) (mem_pull.1 h₁ :), e₁] at a
    have b := gen_trans (L := U.LG.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.LG.rigGen (jK R) z
      (hG.mem _ _) (j' := fun _ => i) (mem_pull.2 (hi' z))
    rw [trF, Fintype.prod_unique, zpow_one] at b
    rw [val_of (L := A.L) (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (𝟙 _) z JA (fun _ => JA (eSec A.A))
      (fun _ => by rw [Category.id_comp])]
    refine (congrArg₂ (· * ·) a (v z _ (mem_pull.2 (hA _)))).trans (Eq.trans ?_ b.symm)
    rw [inv_one, _root_.mul_one, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

section Canon

variable {S : Scheme.{0}} {B : Over S} (L : LB B.left) (Y : Over S)

def HasGen (fm : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ B.left) → U) → U)
    (f : ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ B.left) → L.ι), (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ B.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ B.left) → U), ∏ k, h (φ k) ^ ε k = fm U h) ∧
    ∀ T ρ z J, Good L z J → val t ρ.left z J = f T ρ z J

variable {L Y}

theorem HasGen.mul {fm fm' f f'} (a : HasGen L Y fm f) (b : HasGen L Y fm' f') :
    HasGen L Y (fun U _ h => fm U h * fm' U h) (fun T ρ z J => f T ρ z J * f' T ρ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', p', v'⟩ := b
  exact ⟨_, _, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ h => prod_sum₂ (K := K) (K' := K') (U := U) _ (p U h) (p' U h),
    fun T ρ z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v T ρ z J hJ) (v' T ρ z J hJ))⟩

theorem HasGen.inv {fm f} (a : HasGen L Y fm f) :
    HasGen L Y (fun U _ h => (fm U h)⁻¹) (fun T ρ z J => (f T ρ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  exact ⟨_, _, _, _, LB.invGen L _ _ t, invGen_isGen _ _ _ _ ht, fun U _ h => prod_neg _ _ (p U h),
    fun T ρ z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (v T ρ z J hJ))⟩

theorem hasGen_pull {K : Type} [Fintype K] {φ : K → (B.left ⟶ B.left)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (x : Y ⟶ B) :
    HasGen L Y (fun _ _ h => ∏ k, h (x.left ≫ φ k) ^ ε k) (fun _ ρ z J => val t (ρ ≫ x).left z J) :=
  ⟨_, _, _, _, LB.pullGen L _ _ t x.left, pullGen_isGen _ _ _ _ ht _, fun _ _ _ => rfl,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem HasGen.unique (hL : L.IsLB) {fm fm' f f'} (a : HasGen L Y fm f) (b : HasGen L Y fm' f')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ B.left) → U), fm U h = fm' U h)
    (hY : Function.Surjective Y.hom.appTop.hom) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → f _ e z J = f' _ e z J) (T : Over S) (ρ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    f T ρ z J = f' T ρ z J := by
  obtain ⟨K, _, φ, ε, t, ht, p, v⟩ := a
  obtain ⟨K', _, φ', ε', t', ht', p', v'⟩ := b
  exact (v T ρ z J hJ).symm.trans ((gen_unique' hL (fun U _ h => (p' U h).trans ((hF U h).symm.trans (p U h).symm))
    Y.hom e.left (Over.w e) hY ht ht' (fun y I hI => (v _ e y I hI).trans ((he y I hI).trans (v' _ e y I hI).symm))
    _ ρ.left z J hJ).trans (v' T ρ z J hJ))

variable [GrpObj B] [IsCommMonObj B] {M : RigLB B} (c : CubicalStr B M)

theorem hasGen_cub (x x' y : Y ⟶ B) :
    HasGen M.L Y (fun _ _ h => h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ *
      h x.left * h x'.left * h y.left * (h (1 : Y ⟶ B).left)⁻¹)
      (fun _ ρ z J => cubV c z J (ρ ≫ x) (ρ ≫ x') (ρ ≫ y)) :=
  ⟨_, _, _, _, LB.pullGen M.L (thφ B (x3 B)) thε c.t (lift x (lift x' y)).left, pullGen_isGen _ _ _ _ c.isGen _,
    fun _ _ h => prod_cub x x' y h, fun _ ρ _ _ hJ => val_cub c ρ hJ _ _ _⟩

theorem hasGen_cubN (a m x : Y ⟶ B) (k : ℕ) :
    HasGen M.L Y (fun _ _ h => h (a * m ^ k * x).left * (h (a * m ^ k).left)⁻¹ * (h (a * x).left)⁻¹ * h a.left *
      (h (m * x).left ^ k)⁻¹ * h m.left ^ k * h x.left ^ k * (h (1 : Y ⟶ B).left ^ k)⁻¹)
      (fun _ ρ z J => cubN (cubV c z J) k (ρ ≫ a) (ρ ≫ m) (ρ ≫ x)) := by
  obtain ⟨t, ht, v⟩ := exists_cubN c a m x k
  refine ⟨_, _, _, _, t, ht, fun U _ h => ?_, v⟩
  simp [Fin.prod_univ_succ, _root_.mul_assoc]

end Canon

theorem canon_identity {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hG : GlobalFnsSt) (N : ℕ)
    (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 4)
      ![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left]
      ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1])) (hν : Normd ν)
    {a : D.P.A ⟶ D.P.A} (ha : a = (𝟙 D.P.A)⁻¹) (κ : LB.Gen (kapLB D a N N)) (hκ : Normd κ) {T : Over (Spec (CommRingCat.of R))} (b x : T ⟶ D.P.A)
    (z : T.left) {J} (hJ : Good D.P.L z J) :
    val ν b.left z J * val κ (x * b).left z J * cubN (th D z J) N 1 b x * cubN (th D z J) N (b ^ N)⁻¹ b (x * b)⁻¹ *
        (th D z J (b ^ N)⁻¹ (x * b)⁻¹ b)⁻¹ * th D z J (b ^ N) (b ^ N)⁻¹ b =
      val κ x.left z J * th D z J (b ^ N)⁻¹ x x⁻¹ * (th D z J (b ^ N) (b ^ N)⁻¹ x)⁻¹ := by
  subst ha
  let β : D.P.A ⊗ D.P.A ⟶ D.P.A := fst _ _
  let ξ : D.P.A ⊗ D.P.A ⟶ D.P.A := snd _ _
  have nv : ∀ {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)} {ε : K → ℤ}
      (u : LB.Gen (LB.LinComb D.P.L φ ε)), Normd u → ∀ y I, Good D.P.L y I →
      val u (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left y I = 1 := by
    intro K _ φ ε u hu y I hI
    have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = η[D.P.A] := by simp [Hom.one_def]
    have := (val_pull hI u _ _).symm.trans ((val_corr hI hu.2 (𝟙 _)).trans (val_one _))
    rw [Category.id_comp] at this
    rw [o]; exact this
  have fκ : ∀ (q : D.P.A ⊗ D.P.A ⟶ D.P.A) (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U),
      ∏ k, h (q.left ≫ (![𝟙 _, ((𝟙 D.P.A)⁻¹ : D.P.A ⟶ D.P.A).left, (1 : D.P.A ⟶ D.P.A).left] : Fin 3 → _) k) ^
        (![(N : ℤ), -(N : ℤ), (N : ℤ) - N] : Fin 3 → ℤ) k = h q.left ^ N * (h q⁻¹.left ^ N)⁻¹ := by
    intro q U _ h
    have e : q ≫ (𝟙 D.P.A)⁻¹ = q⁻¹ := by rw [GrpObj.comp_inv, Category.comp_id]
    rw [← e]
    simp [Fin.prod_univ_succ]
  have fν : ∀ (U : Type) [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U),
      ∏ k, h (β.left ≫ (![(𝟙 D.P.A ^ (N + 1)).left, (𝟙 D.P.A ^ N).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] : Fin 4 → _) k) ^
        (![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1] : Fin 4 → ℤ) k =
      h (β ^ N * β).left * (h (β ^ N).left)⁻¹ * h β.left ^ (-(2 * (N : ℤ) + 1)) *
        h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left ^ (2 * (N : ℤ) + 1) := by
    intro U _ h
    have e : ∀ n : ℕ, β ≫ (𝟙 D.P.A ^ n) = β ^ n := fun n => by rw [MonObj.comp_pow, Category.comp_id]
    rw [← pow_succ, ← e, ← e, ← MonObj.comp_one (M := D.P.A) β, Fin.prod_univ_four]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Over.comp_left, Category.comp_id, zpow_one,
      zpow_neg_one]
  have H := (((((((hasGen_pull (L := D.P.L) hν.1 β).mul (hasGen_pull hκ.1 (ξ * β))).mul (hasGen_cubN D.cub 1 β ξ N)).mul
    (hasGen_cubN D.cub (β ^ N)⁻¹ β (ξ * β)⁻¹ N)).mul (hasGen_cub D.cub (β ^ N)⁻¹ (ξ * β)⁻¹ β).inv).mul
    (hasGen_cub D.cub (β ^ N) (β ^ N)⁻¹ β)).unique D.P.isLB
    (((hasGen_pull (L := D.P.L) hκ.1 ξ).mul (hasGen_cub D.cub (β ^ N)⁻¹ ξ ξ⁻¹)).mul (hasGen_cub D.cub (β ^ N) (β ^ N)⁻¹ ξ).inv)
    (fun U _ h => by
      have a₁ : β * (ξ * β)⁻¹ = ξ⁻¹ := by rw [mul_inv, mul_comm ξ⁻¹, mul_inv_cancel_left]
      have a₂ : (ξ * β)⁻¹ * β = ξ⁻¹ := by rw [mul_comm, a₁]
      have a₃ : (β ^ N)⁻¹ * (ξ * β)⁻¹ * β = (β ^ N)⁻¹ * ξ⁻¹ := by rw [_root_.mul_assoc, a₂]
      rw [fκ, fκ, fν]
      simp only [_root_.one_mul, inv_mul_cancel, mul_inv_cancel, mul_inv_cancel_right, a₁, a₂, a₃, mul_comm β ξ]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (by
      rw [← Over.w (snd D.P.A D.P.A)]
      exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) (lift 1 1) (fun y I hI => by
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      simp only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, MonObj.comp_one, lift_fst, lift_snd,
        _root_.mul_one, inv_one, one_pow, C.face, C.N_one, nv ν hν y I hI, nv κ hκ y I hI]) T (lift b x) z J hJ)
  simpa only [β, ξ, MonObj.comp_mul, MonObj.comp_pow, GrpObj.comp_inv, MonObj.comp_one, lift_fst, lift_snd] using H

theorem exists_twist {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    (s : LB.Sec (LPow A L b T)) : ∃ s' : LB.Sec (LPow A L a T), IsTwistPull A L ψ m hm a b α s s' := by
  have e : ψ.left ≫ (snd T A).left = m.left := by rw [← Over.comp_left, hm]
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => a)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fin.prod_univ_one,
        e, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, mul_inv_cancel_comm_assoc])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s ψ.left α hα)
  exact ⟨s', ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ =>
    (hs' _ _ y J hJ).trans ((sval_pullMulSec _ _ α hα _ y hJ).trans (mul_comm _ _))⟩

section Sym

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

theorem val_symGen (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z}
    {J} (hJ : Good L z J) : val (symGen A L k θ nu) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu r z J *
      (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) rfl))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

theorem exists_norm_sym (hL : L.IsLB) (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) (hnu : nu.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k θ nu) (LB.oneGen L)) :
    ∃ α : LB.Gen (negLB A L k T), α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (symGen A L k θ α) (LB.oneGen L) ∧
      ∀ z J, Good L z J → val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) α
        (ptSecT A (1 : T ⟶ A)).left z J = 1 := by
  let o : T ⊗ A ⟶ T ⊗ A := fst T A ≫ ptSecT A 1
  have o₁ : o.left ≫ (snd T A).left = (1 : T ⊗ A ⟶ A).left := by
    rw [← Over.comp_left, Category.assoc, ptSecT, lift_snd, MonObj.comp_one]
  have o₂ : o.left ≫ (snd T A ≫ ι[A]).left = (1 : T ⊗ A ⟶ A).left := by
    rw [← Over.comp_left, ← Category.assoc, Category.assoc (fst T A), ptSecT, lift_snd, MonObj.comp_one,
      ← Hom.inv_def, inv_one]
  obtain ⟨α, hα, v⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε' := ![k, -k])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, o₁, o₂, neg_neg, zpow_neg, inv_inv, inv_mul_cancel, _root_.mul_one])
    (LB.mulGen L _ _ _ _ nu (LB.invGen L _ _ (LB.pullGen L _ _ nu o.left)))
    (mulGen_isGen _ _ _ _ _ _ _ hnu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hnu _)))
  have v' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) z J, Good L z J → val α r z J =
      val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu r z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ ι[A]).left]) (ε := ![k, -k]) nu (r ≫ o.left) z J)⁻¹ :=
    fun Z r z J hJ => (v Z r z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ ((val_inv _ _).trans
      (congrArg (·⁻¹) (val_pull hJ _ _ _)))))
  refine ⟨α, hα, corr_of_val hL fun y J hJ => ?_, fun z J hJ => ?_⟩
  · have e := val_corr hJ h (𝟙 _)
    have t : (translT A θ.pt⁻¹).left ≫ o.left = o.left := by
      rw [← Over.comp_left, ← Category.assoc, translT, lift_fst]
    refine ((val_symGen A θ α _ hJ).trans ?_).trans ((val_symGen A θ nu _ hJ).symm.trans e)
    rw [v' _ _ y J hJ, v' _ _ y J hJ, Category.assoc, t]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    try abel
  · have t : (ptSecT A (1 : T ⟶ A)).left ≫ o.left = (ptSecT A (1 : T ⟶ A)).left := by
      rw [← Over.comp_left, ← Category.assoc, ptSecT, lift_fst, Category.id_comp]
    rw [v' _ _ z J hJ, t, mul_inv_cancel]

theorem isTwistPull_of_sym [IsCommMonObj A] (hL : L.IsLB) (θ : ThetaGrp A L k T) (α : LB.Gen (negLB A L k T)) (hα : α.IsGen)
    (h : LB.Gen.Corr L _ _ _ _ (symGen A L k θ α) (LB.oneGen L)) {t t₁ t₂ t₃ : LB.Sec (LPow A L k T)}
    (h₁ : IsActOf A L k θ t t₁) (h₂ : IsTwistPull A L (negT A T) (snd T A ≫ ι[A]) (lift_snd _ _) k k α t₁ t₂)
    (h₃ : IsActOf A L k θ t₂ t₃) : IsTwistPull A L (negT A T) (snd T A ≫ ι[A]) (lift_snd _ _) k k α t t₃ := by
  refine ThetaLin.isTwistPull_of_sval A hL hα fun y J hJ => ?_
  have e := (val_symGen A θ α (translT A θ.pt).left hJ).symm.trans ((val_corr hJ h (translT A θ.pt).left).trans (val_one _))
  have t₁ : (translT A θ.pt).left ≫ (translT A θ.pt⁻¹).left = 𝟙 _ := by
    rw [← Over.comp_left, ThetaLin.translT_comp _ _ _ (inv_mul_cancel _), Over.id_left]
  have t₂ : ((translT A θ.pt).left ≫ (negT A T).left) ≫ (translT A θ.pt).left = (negT A T).left := by
    have e : translPt A θ.pt = (fst T A ≫ θ.pt) * snd T A := rfl
    have n : translT A θ.pt ≫ negT A T = lift (fst T A) ((fst T A ≫ θ.pt) * snd T A)⁻¹ := by
      rw [negT, comp_lift, ← Category.assoc, translT, lift_fst, lift_snd, e, Hom.inv_def]
    rw [← Over.comp_left, ← Over.comp_left, n, ThetaLin.lift_translT, mul_inv, mul_inv_cancel_left, Hom.inv_def, negT]
  rw [t₁] at e
  rw [ThetaLin.sval_of_isTwistPull A h₃ _ y hJ, ThetaLin.sval_of_isTwistPull A h₂ _ y hJ,
    ThetaLin.sval_of_isTwistPull A h₁ _ y hJ, Category.id_comp, Category.id_comp, t₂, ← _root_.mul_assoc,
    ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
  rw [← _root_.mul_assoc, mul_inv_eq_one] at e
  exact congrArg₂ (· * ·) (congrArg Units.val e) rfl

end Sym

section Main

variable {R : Type} [CommRing R] [IsDomain R]

theorem phi_at {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] (hG : GlobalFnsSt) {k : ℕ}
    (p : QkPt D F k) (w : Frm D F k p.g.b) (hw : w.IsGen) {s t : Fam D F k} (h : PhiRel D F k p w s t) (α β : D.X)
    (e : α + p.y = β) (x : TF (R := R) F ⟶ D.P.A) (z : (TF (R := R) F).left) {J} (hJ : Good D.P.L z J) :
    sval (t.s β) (lift (𝟙 _) x).left z J = sval (s.s α) (lift (𝟙 _) (x * p.g.b)).left z J *
      (cubN (th D z J) k (cP D _ α) p.g.b x * (th D z J (cP D _ α) x p.g.b)⁻¹ *
        (val (p.g.s α) (𝟙 _) z J * val w (𝟙 _) z J)).val := by
  have H := (phiRel_iff hG p w hw s t).1 h α β e _ (lift (𝟙 _) x) z J hJ
  have a : lift (𝟙 (TF (R := R) F)) x ≫ DegPre.trPt D F p.g.b = lift (𝟙 _) (x * p.g.b) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tr_fst, lift_fst, lift_fst]
    · rw [Category.assoc, lift_snd]
      refine (congrArg _ (tr_pr D F p.g.b)).trans ?_
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.id_comp]
  rw [a, uVal, lift_fst_assoc, lift_snd, lift_fst, Category.id_comp, val_mul hJ] at H
  exact H

theorem val_rigT_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left)
    (ρ : LB.Gen (L.pull (eSec A))) (T : Over S) (k : ℤ) (hk : k = 0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (rigT A L ρ T k) r z J = 1 := by
  subst hk
  exact (congrArg _ (zpow_zero _)).trans (map_one _)

theorem sq_frame_of_symmetric : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)) (w₀ : W0 U.toUnifPre) (w : Frm D.toPre F N p.g.b), w₀.IsGen → w.IsGen → (∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' → PhiRel D.toPre F N p w s s') → (∃ nu : LB.Gen (negLB A.A A.L N (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L N θ nu) (LB.oneGen A.L)) → ∀ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 4) ![(𝟙 D.toPre.P.A ^ (N + 1)).left, (𝟙 D.toPre.P.A ^ N).left, 𝟙 _, (1 : D.toPre.P.A ⟶ D.toPre.P.A).left] ![1, -1, -(2 * (N : ℤ) + 1), 2 * (N : ℤ) + 1]), Normd ν → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ 2 = val (p.g.s p.y) (𝟙 _) z J * val ν p.g.b.left z J := by
  intro hL R _ _ _ I hA D A G _ _ hS U F _ _ _ N hN p θ w₀ w hw₀ hw hΦ ⟨nu, hnu, hsym⟩ ν hν z J hJ
  have hG := hL.1.globalFns
  have C : IsCub (th D.toPre (T := TF (R := R) F) z J) := isCub_cubV D.toPre.cub hJ
  obtain ⟨ρ, hρ⟩ := exists_normW U.toUnifPre w₀ hw₀
  obtain ⟨-, E, eG, eA, eB, eh, eAct⟩ := IntEnd.exists_nsmul_and_neg hL R I hA D A G hS U
  obtain ⟨α, hα, hαs, hα₁⟩ := exists_norm_sym A.A A.isLB θ nu hnu hsym
  obtain ⟨β, hβ, -⟩ := exists_gen U.LG.isLB (φ' := ![𝟙 _, E.aG.left]) (ε' := ![(N : ℤ), -(N : ℤ)]) (fun V _ h => by
      rw [eG, Hom.inv_def, Category.id_comp]
      simp [Fin.prod_univ_two, mul_comm])
    (GeneratorPullback.powGen U.LG.L _ _ (LB.invGen U.LG.L _ _ U.symG) N) (powGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ U.symG_gen) N)
  obtain ⟨⟨κ, hκ⟩, hP⟩ := GlobalTheory.T.expansion_pullback_section_endomorphism hL R I hA D A G hS U F E
    (fun a b e => neg_injective ((eh a).symm.trans (e.trans (eh b)))) N N hN hN ⟨β, hβ⟩
  have hP' := hP w₀ ρ hρ (negT A.A _) (snd _ _ ≫ ι[A.A]) (lift_snd _ _) (lift_fst _ _)
    (by rw [eA, Hom.inv_def, Category.id_comp]) α hα (corr_of_val A.isLB fun y J' hJ' => by
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_rigT_zero _ _ _ _ _ (sub_self _) _ _ _).symm)
      rw [Category.id_comp]
      exact hα₁ y J' hJ')

  have neg : ∀ (t t' : SecA A F N) s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' →
      IsTwistPull A.A A.L (negT A.A _) (snd _ _ ≫ ι[A.A]) (lift_snd _ _) N N α t t' → ∀ χ χ', χ + χ' = 0 →
      ∀ x : TF (R := R) F ⟶ D.toPre.P.A, sval (s'.s χ') (lift (𝟙 _) x).left z J =
        sval (s.s χ) (lift (𝟙 _) x⁻¹).left z J * (val κ x.left z J * th D.toPre z J (cP _ _ χ) x x⁻¹ *
          (th D.toPre z J (cP _ _ χ) (cP _ _ χ') x)⁻¹).val := by
    intro t t' s s' hs hs' ht χ χ' hχ x
    obtain ⟨g, rfl⟩ := (gt_onto_divisible_kernel hL R I hA D F).1 x
    obtain ⟨b', v'⟩ : (TorusExt.gtNeg g).b = g.b⁻¹ ∧ ∀ χ y J, Good D.toPre.P.L y J →
      TorusExt.charVal (TorusExt.gtNeg g) χ y J = (TorusExt.charVal g χ y J)⁻¹ *
        th D.toPre y J (cP D.toPre _ χ) g.b g.b⁻¹ := (TorusExt.exists_neg g).choose_spec
    have act : E.Act g (TorusExt.gtNeg g) := (eAct F _ _).2
      ⟨_, TorusExt.isZero_gtZero, TorusExt.gtAdd_neg g ▸ TorusExt.isAdd_gtAdd g _⟩
    obtain ⟨ω, hω⟩ := (CoefBasic.coef_basic R D.toPre F N g).1
    obtain ⟨ω', hω', vω⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F (TorusExt.gtNeg g).b)
      (ε' := DegPre.lineε N) (fun V _ h => by
        refine (prod_sum₂ (K := Fin 2) (K' := Fin 3) (U := V) _ (CoefBasic.prod_line N g.b h) rfl).trans ?_
        rw [CoefBasic.prod_line, act.1]
        simp [Fin.prod_univ_succ, _root_.mul_assoc])
      (LB.mulGen D.toPre.P.L _ _ _ _ ω (LB.pullGen D.toPre.P.L _ _ κ g.b.left))
      (mulGen_isGen _ _ _ _ _ _ _ hω (pullGen_isGen _ _ _ _ hκ.1 _))
    have vω' : ∀ z J, Good D.toPre.P.L z J → val ω (𝟙 _) z J * val κ g.b.left z J = val ω' (𝟙 _) z J := fun z J hJ => by
      rw [vω _ _ z J hJ, val_mul hJ, val_pull hJ, Category.id_comp]
    have c := (hP' t t' s s' hs hs' ht κ hκ g _ act ω ω' hω hω' vω').1 χ
    rw [eh, neg_eq_of_add_eq_zero_right hχ] at c
    have a := CoefBasic.isCoef_coef g hω χ' s' z J hJ
    have a' := CoefBasic.isCoef_coef _ hω' χ s z J hJ
    have m := TorusExt.charVal_add g hJ χ χ'
    have l : lift (𝟙 (TF (R := R) F)) (TorusExt.gtNeg g).b = lift (𝟙 _) g.b⁻¹ := by rw [b']
    rw [hχ, TorusExt.charVal_zero g hJ, _root_.one_mul] at m
    rw [c, a', l, ← vω' z J hJ, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul] at a
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 a.symm, _root_.mul_assoc, ← Units.val_mul, m]
    congr 2
    have v := congrArg Additive.ofMul (v' χ z J hJ)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, TorusExt.charVal] at v ⊢
    linear_combination (norm := abel) v
  obtain ⟨bij, -⟩ := expBijF_and_expandsF_lin hL R I hA D A G hS U
  obtain ⟨ts, st⟩ := bij F N hN w₀ hw₀
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hN (-p.y)
  obtain ⟨s, rfl, -⟩ := FamFree.exists_fam_single hG D.tau_bimult hN (-p.y) σ
  obtain ⟨x', hx⟩ := exists_sval_ne_zero _ hσ z hJ
  obtain ⟨x, rfl⟩ : ∃ x, x⁻¹ = x' := ⟨x'⁻¹, inv_inv _⟩
  obtain ⟨t, ht, -⟩ := st s
  obtain ⟨t₁, h₁⟩ := exists_twist A.A A.isLB (ψ := translT A.A θ.pt) (hm := lift_snd _ _) θ.isGen t
  obtain ⟨t₂, h₂⟩ := exists_twist A.A A.isLB (ψ := negT A.A _) (hm := lift_snd _ _) hα t₁
  obtain ⟨t₃, h₃⟩ := exists_twist A.A A.isLB (ψ := translT A.A θ.pt) (hm := lift_snd _ _) θ.isGen t₂
  obtain ⟨s₁, hs₁, -⟩ := ts t₁
  obtain ⟨s₂, hs₂, -⟩ := ts t₂
  obtain ⟨s₃, hs₃, -⟩ := ts t₃
  have e₁ := phi_at hG p w hw (hΦ _ _ _ _ ht hs₁ h₁) (-p.y) 0 (neg_add_cancel _) (x * p.g.b)⁻¹ z hJ
  have e₂ := neg _ _ _ _ hs₁ hs₂ h₂ 0 0 (add_zero _) (x * p.g.b)
  have e₃ := phi_at hG p w hw (hΦ _ _ _ _ hs₂ hs₃ h₃) 0 p.y (zero_add _) x z hJ
  have e₄ := neg _ _ _ _ ht hs₃ (isTwistPull_of_sym A.A A.isLB θ α hα hαs h₁ h₂ h₃) (-p.y) p.y (neg_add_cancel _) x
  have cn : cP D.toPre (TF (R := R) F) (-p.y) = (p.g.b ^ N)⁻¹ := by
    rw [← cPoint_y, eq_inv_iff_mul_eq_one, ← cPoint_add, neg_add_cancel, cPoint_zero]
  have m := TorusExt.charVal_add p.g hJ p.y (-p.y)
  rw [add_neg_cancel, TorusExt.charVal_zero p.g hJ, _root_.one_mul, cn, cPoint_y] at m
  have z₀ := TorusExt.charVal_zero p.g hJ
  have key := canon_identity hG N ν hν eB κ hκ p.g.b x z hJ
  have hu : IsUnit (sval (s.s (-p.y)) (lift (𝟙 (TF (R := R) F)) x⁻¹).left z J) := by
    obtain ⟨a, ha⟩ := CoefBasic.cstH_surj z (sval (s.s (-p.y)) (lift (𝟙 (TF (R := R) F)) x⁻¹).left z J)
    rw [← ha] at hx ⊢
    exact (IsUnit.mk0 a fun h => hx (by rw [h, map_zero])).map _
  rw [mul_inv x, inv_mul_cancel_right, ← mul_inv x, cn] at e₁
  rw [cPoint_zero, C.face, C.face] at e₂
  rw [cPoint_zero, C.face] at e₃
  rw [cn, cPoint_y, C.s01 _ (p.g.b ^ N), e₃, e₂, e₁, _root_.mul_assoc, _root_.mul_assoc, hu.mul_right_inj, ← Units.val_mul,
    ← Units.val_mul, Units.val_inj, ← key] at e₄
  have a₁ := congrArg Additive.ofMul e₄
  have a₂ := congrArg Additive.ofMul m
  have a₃ := congrArg Additive.ofMul z₀
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one, TorusExt.charVal] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ + a₂ - a₃

end Main

end GlobalTheory.SymFrame
