import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdditivePointsDescendFieldExtension
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldTorsionPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp

noncomputable section

namespace GlobalTheory.NormDescent

section Algebra

variable {X G : Type} [AddCommGroup X] [CommGroup G]

def polar (q : X → G) (a b : X) : G := q (a + b) * (q a)⁻¹ * (q b)⁻¹

theorem polar_comm (q : X → G) (a b : X) : polar q a b = polar q b a := by
  rw [polar, polar, add_comm, mul_right_comm]

variable {q : X → G} (hB : ∀ a a' b, polar q (a + a') b = polar q a b * polar q a' b)
include hB

def polarHom (b : X) : X →+ Additive G :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (polar q a b)) fun a a' => congrArg Additive.ofMul (hB a a' b)

theorem apply_zero : q 0 = 1 := by
  have e : polar q 0 0 = 1 := congrArg Additive.toMul (map_zero (polarHom hB 0))
  simpa [polar] using e

theorem polar_nsmul (n : ℕ) (a b : X) : polar q (n • a) b = polar q a b ^ n :=
  congrArg Additive.toMul (map_nsmul (polarHom hB b) n a)

theorem pow_eq_one (hE : ∀ x, q (-x) = q x) {n : ℕ} (hK : ∀ a b, polar q (n • a) (n • b) = 1) (x : X) :
    q x ^ (2 * (n * n)) = 1 := by
  have e := hK x (-x)
  rw [polar_nsmul hB, polar_comm, polar_nsmul hB, polar, neg_add_cancel, apply_zero hB, hE, one_mul, ← mul_inv, ← sq,
    ← pow_mul, inv_pow, inv_eq_one, ← pow_mul] at e
  exact e

theorem eq_one {I : Type} (b : I → X) (hb : AddSubgroup.closure (Set.range b) = ⊤) (h₁ : ∀ i, q (b i) = 1)
    (h₂ : ∀ i j, q (b i + b j) = 1) (x : X) : q x = 1 := by
  have z : ∀ f : X →+ Additive G, (∀ i, f (b i) = 0) → ∀ x, f x = 0 := fun f hf x =>
    AddMonoidHom.eq_of_eqOn_dense hb (g := 0) (by rintro _ ⟨i, rfl⟩; exact hf i) ▸ rfl
  have p₁ : ∀ j x, polar q x (b j) = 1 := fun j x => congrArg Additive.toMul (z (polarHom hB (b j)) (fun i => by
    show Additive.ofMul (polar q (b i) (b j)) = 0
    simp [polar, h₁, h₂]) x)
  have p₂ : ∀ y x, polar q x y = 1 := fun y x => congrArg Additive.toMul (z (polarHom hB y) (fun i => by
    show Additive.ofMul (polar q (b i) y) = 0
    rw [polar_comm, p₁]; rfl) x)
  exact congrArg Additive.toMul (z (AddMonoidHom.mk' (fun a => Additive.ofMul (q a)) fun a a' => by
    have := p₂ a' a
    rw [polar, mul_assoc, ← mul_inv, mul_inv_eq_one] at this
    exact congrArg Additive.ofMul this) (fun i => congrArg Additive.ofMul (h₁ i)) x)

end Algebra

def unitsIn (k : IntermediateField ℚ ℂ) : Subgroup ℂˣ where
  carrier := {x | (x : ℂ) ∈ k}
  mul_mem' ha hb := k.mul_mem ha hb
  one_mem' := one_mem k
  inv_mem' {x} hx := by
    show ((x⁻¹ : ℂˣ) : ℂ) ∈ k
    rw [Units.val_inv_eq_inv_val]
    exact inv_mem hx

theorem exists_field {X : Type} [AddCommGroup X] [Module.Finite ℤ X] (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    (u : X → ℂˣ) {n : ℕ} (hn : 0 < n) (hE : ∀ x, u (-x) * (u x)⁻¹ ∈ unitsIn k)
    (hB : ∀ a a' b, polar u (a + a') b * (polar u a b * polar u a' b)⁻¹ ∈ unitsIn k)
    (hK : ∀ a b, polar u (n • a) (n • b) ∈ unitsIn k) :
    ∃ k₂ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₂ ∧ k ≤ k₂ ∧ ∀ x, (u x : ℂ) ∈ k₂ := by
  have pm : ∀ (S : Subgroup ℂˣ) a b, polar (fun x => QuotientGroup.mk' S (u x)) a b = QuotientGroup.mk' S (polar u a b) :=
    fun S a b => by simp only [polar, map_mul, map_inv]
  have one : ∀ (S : Subgroup ℂˣ) x, QuotientGroup.mk' S x = 1 ↔ x ∈ S := fun S x => QuotientGroup.eq_one_iff x
  have hB' : ∀ S : Subgroup ℂˣ, unitsIn k ≤ S → ∀ a a' b, polar (fun x => QuotientGroup.mk' S (u x)) (a + a') b =
      polar (fun x => QuotientGroup.mk' S (u x)) a b * polar (fun x => QuotientGroup.mk' S (u x)) a' b :=
    fun S hS a a' b => by
      rw [pm, pm, pm, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, one]
      exact hS (hB a a' b)
  have hint : ∀ x, IsIntegral k (u x : ℂ) := fun x => by
    have e := pow_eq_one (hB' _ le_rfl) (fun x => by
      rw [← mul_inv_eq_one, ← map_inv, ← map_mul, one]; exact hE x) (fun a b => by rw [pm, one]; exact hK a b) x
    rw [← map_pow, one] at e
    refine IsIntegral.of_pow (n := 2 * (n * n)) (by positivity) ?_
    have e' : (u x : ℂ) ^ (2 * (n * n)) ∈ k := by rw [← Units.val_pow_eq_pow_val]; exact e
    exact isIntegral_algebraMap (R := k) (x := ⟨_, e'⟩)
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := X)
  have hb' : AddSubgroup.closure (Set.range b) = ⊤ := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, hb]; rfl
  let S : Set ℂ := Set.range (fun i => (u (b i) : ℂ)) ∪ Set.range fun p : Fin m × Fin m => (u (b p.1 + b p.2) : ℂ)
  have : Finite S := (Set.finite_range _).union (Set.finite_range _)
  have hfd : FiniteDimensional k (IntermediateField.adjoin k S) := IntermediateField.finiteDimensional_adjoin (by
    rintro _ (⟨i, rfl⟩ | ⟨p, rfl⟩) <;> exact hint _)
  have hfd' : FiniteDimensional ℚ (IntermediateField.adjoin k S) := Module.Finite.trans k _
  have le : k ≤ (IntermediateField.adjoin k S).restrictScalars ℚ := fun x hx =>
    (IntermediateField.adjoin k S).algebraMap_mem ⟨x, hx⟩
  refine ⟨(IntermediateField.adjoin k S).restrictScalars ℚ, hfd', le, fun x => ?_⟩
  exact (one (unitsIn _) _).1 (eq_one (hB' (unitsIn ((IntermediateField.adjoin k S).restrictScalars ℚ))
    fun y hy => le hy) b hb'
    (fun i => (one _ _).2 (IntermediateField.subset_adjoin k S (Or.inl ⟨i, rfl⟩)))
    (fun i j => (one _ _).2 (IntermediateField.subset_adjoin k S (Or.inr ⟨(i, j), rfl⟩))) x)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.ArcPull GlobalTheory.TauTwist GlobalTheory.TorusExt
open GlobalTheory.PsiEvenPull (proj)

section Defect

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem exists_ratio_genMap (hφ : Function.Injective φ) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {ψ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ}
    (hF : FormEq ψ ε ψ' ε') {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')} (ht : t.IsGen)
    (ht' : t'.IsGen) : ∃ r : (FractionRing R)ˣ, ∀ (z : (TK R').left) J, Good L z J →
      val t (genMap hφ) z J = unitAt (A := FractionRing R) (genMap hφ) z r * val t' (genMap hφ) z J := by
  obtain ⟨r, hr⟩ := exists_ratio (F := FractionRing R) hL hF ht ht'
  have c : LB.Gen.Corr L _ _ _ _ t (scaleGen (unitOn r) t') :=
    corr_of_val hL fun y J hJ => (hr y J hJ).trans (val_scale r t' _ hJ).symm
  exact ⟨r, fun z J hJ => (val_corr hJ c _).trans (val_scale r t' _ hJ)⟩

theorem xK_neg (D : DegPre R) (x : D.X) : D.xK (-x) = D.xK x ≫ (ι[D.P.A]).left := by
  show (toUnit _ ≫ D.c (-x)).left = _
  rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]

theorem even_defect (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (x : D'.X) :
    ∃ r : (FractionRing R)ˣ, ∀ (z : (TK R').left) J', Good D'.P.L z J' →
      val (D'.psi (-x)) (𝟙 _) z J' * val D'.sym (𝟙 _ ≫ D'.xK x) z J' =
        unitAt (A := FractionRing R) (genMap hφ) z r * val (D'.psi x) (𝟙 _) z J' := by
  obtain ⟨r, hr⟩ := exists_ratio_genMap hφ D.P.isLB (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two]
      show h (D.xK (-hD.xe x)) ^ (-1 : ℤ) * (h (D.xK (hD.xe x) ≫ (ι[D.P.A]).left) ^ (1 : ℤ) *
        h (D.xK (hD.xe x) ≫ 𝟙 _) ^ (-1 : ℤ)) = h (D.xK (hD.xe x)) ^ (-1 : ℤ)
      rw [xK_neg, Category.comp_id]
      simp)
    (mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen (-hD.xe x)) (pullGen_isGen _ _ _ _ D.sym_gen (D.xK (hD.xe x))))
    (D.psi_gen (hD.xe x))
  refine ⟨r, fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := (TK R').left) z
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have cW : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hφ ≫ D.xK (hD.xe x) := by
    rw [Category.id_comp]; exact cPoint_proj hD _ hh x
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [xK_neg, Category.assoc]
  have a₁ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' (-x)
  have a₂ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' x
  have a₃ : val D.sym (genMap hφ ≫ D.xK (hD.xe x)) z J =
      om hD.w z J J' ((𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left) * (om hD.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ *
        val D'.sym (𝟙 _ ≫ D'.xK x) z J' :=
    (congrArg (fun q => val D.sym q z J) cW.symm).trans (PsiEvenPull.sym_pull hG hD _ z hJ hJ')
  rw [c', map_neg] at a₁
  have e := (congrArg₂ (· * ·) a₁ ((val_pull hJ _ _ _).trans a₃)).symm.trans
    ((val_mul hJ _ _ _).symm.trans ((hr z J hJ).trans (congrArg₂ (· * ·) rfl a₂)))
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem prod_tau (D : DegPre R) (a b : D.X) {U : Type} [CommGroup U] (h : ((TK R).left ⟶ D.P.A.left) → U) :
    (h (D.xK (a + b)))⁻¹ * h (D.xK a) * h (D.xK b) * (h ((toUnit (TK R)).left ≫ eSec D.P.A))⁻¹ =
      (h (cP D (TK R) a * cP D (TK R) b).left)⁻¹ * h (cP D (TK R) a).left * h (cP D (TK R) b).left *
        (h (1 : TK R ⟶ D.P.A).left)⁻¹ := by
  rw [← cPoint_add]; rfl

theorem tau_defect (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (a b : D'.X) (ha : cP D' (TK R') a = 1)
    (hb : cP D' (TK R') b = 1) (ha₀ : cP D (TK R) (hD.xe a) = 1) (hb₀ : cP D (TK R) (hD.xe b) = 1) :
    ∃ r : (FractionRing R)ˣ, ∀ (z : (TK R').left) J', Good D'.P.L z J' →
      val (D'.tau a b) (𝟙 _) z J' = unitAt (A := FractionRing R) (genMap hφ) z r := by
  obtain ⟨r, hr⟩ := exists_ratio_genMap hφ D.P.isLB (ψ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      have p := prod_tau D (hD.xe a) (hD.xe b) h
      rw [ha₀, hb₀, _root_.mul_one] at p
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one,
        Fintype.prod_empty]
      exact p.trans (by simp)) (tau_isGen D (hD.xe a) (hD.xe b)) oneGen_isGen
  refine ⟨r, fun z J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := (TK R').left) z
  have e := tau_val hD (Z := (TK R').left) _ _ (fracMap_sq hφ) hJ hJ' a b
  have c : ∀ x, cP D' (TK R') x = 1 → D'.xK x = (1 : TK R' ⟶ D'.P.A).left := fun x hx => congrArg (fun q => q.left) hx
  rw [c a ha, c b hb, c (a + b) (by rw [cPoint_add, ha, hb, _root_.mul_one]), hr z J hJ, val_one] at e
  simpa using e.symm

set_option maxHeartbeats 1000000 in

theorem bimult_defect (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (a a' b : D'.X) :
    ∃ r : (FractionRing R)ˣ, ∀ (y : (TK R').left) J', Good D'.P.L y J' →
      val (D'.tau (a + a') b) (𝟙 _) y J' * th D' (T := TK R') y J' (cP D' _ a) (cP D' _ a') (cP D' _ b) =
        unitAt (A := FractionRing R) (genMap hφ) y r * (val (D'.tau a b) (𝟙 _) y J' * val (D'.tau a' b) (𝟙 _) y J') := by
  obtain ⟨r, hr⟩ := exists_ratio_genMap hφ D.P.isLB (fun U _ h => by
      have p₁ := prod_tau D (hD.xe a + hD.xe a') (hD.xe b) h
      have p₂ := prod_tau D (hD.xe a) (hD.xe b) h
      have p₃ := prod_tau D (hD.xe a') (hD.xe b) h
      have p₄ := prod_cub (cP D (TK R) (hD.xe a)) (cP D (TK R) (hD.xe a')) (cP D (TK R) (hD.xe b)) h
      rw [cPoint_add] at p₁
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, neg_neg, zpow_neg, zpow_one]
      refine (congrArg₂ (· * ·) p₁ p₄).trans (Eq.trans ?_ (congrArg₂ (· * ·) p₂ p₃).symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen D (hD.xe a + hD.xe a') (hD.xe b))
      (pullGen_isGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen (D.pt3 (hD.xe a) (hD.xe a') (hD.xe b))))
    (mulGen_isGen _ _ _ _ _ _ _ (tau_isGen D (hD.xe a) (hD.xe b)) (tau_isGen D (hD.xe a') (hD.xe b)))
  refine ⟨r, fun y J' hJ' => ?_⟩
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := (TK R').left) y
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have gp := pull_grp hD
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk (genMap hφ) hh.symm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ proj hD = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => om hD.w (Z := (TK R').left) y J J' x.left
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' (T := TK R') y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => om hD.w (Z := (TK R').left) y J J' q)) rfl)
  let τ : D.X → D.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D.tau a b) (genMap hφ) y J
  let τ' : D'.X → D'.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D'.tau a b) (𝟙 (TK R').left) y J'
  have vτ : ∀ a b, τ (hD.xe a) (hD.xe b) =
      (Ω (cP D' _ a * cP D' _ b))⁻¹ * Ω (cP D' _ a) * Ω (cP D' _ b) * (Ω 1)⁻¹ * τ' a b := fun a b => by
    have e := tau_val hD (Z := (TK R').left) _ _ sq hJ hJ' a b
    simp only [Category.id_comp] at e
    rw [← cPoint_add]
    exact e
  have key : τ (hD.xe a + hD.xe a') (hD.xe b) * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      unitAt (A := FractionRing R) (genMap hφ) y r * (τ (hD.xe a) (hD.xe b) * τ (hD.xe a') (hD.xe b)) := by
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_)
      ((val_mul hJ _ _ _).symm.trans ((hr y J hJ).trans (congrArg₂ (· * ·) rfl (val_mul hJ _ _ _))))
    refine Eq.trans ?_ (val_cub D.cub κ hJ (cP D _ (hD.xe a)) (cP D _ (hD.xe a')) (cP D _ (hD.xe b))).symm
    rw [comp_cP, comp_cP, comp_cP]
  rw [← βc, ← βc, ← βc, cub, ← map_add, vτ, vτ, vτ, cPoint_add] at key
  show τ' (a + a') b * _ = _ * (τ' a b * τ' a' b)
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end Defect

section Ratio

variable {k K : Type} [Field k] [Field K] (β : k →+* K) (D : DegPre K) (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen)
  (u : D.X → (FractionRing K)ˣ) (hu : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (u χ) * val (ψ χ) (𝟙 _) z J)
include hu

theorem val_tau_ratio (a b : D.X) {z : (TK K).left} {J} (hJ : Good D.P.L z J) : val (D.tau a b) (𝟙 _) z J =
    unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (polar u a b) *
      val ((withPsi D ψ hψ).tau a b) (𝟙 _) z J := by
  have e := val_tau (withPsi D ψ hψ) a b (𝟙 _) hJ
  have e₅ : val (withPsi D ψ hψ).rigK (𝟙 _) z J = val D.rigK (𝟙 _) z J := rfl
  rw [e₅] at e
  rw [e, val_tau D a b _ hJ, hu _ z J hJ, hu _ z J hJ, hu _ z J hJ, polar, map_mul, map_mul, map_inv, map_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem ratio_defects (hG : GlobalFnsSt) (D₀ : DegPre k) (h : IsPullDeg β D₀ (withPsi D ψ hψ)) (hE : D.PsiEven)
    (hB : D.TauBimult) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (hκ : ∀ y y', kappa hc y y' = 1)
    (hc₀ : ∀ y, D₀.c y ^ n = 1) :
    (∀ x, ∃ r, u (-x) * (u x)⁻¹ = Units.map (fracMap β.injective).toMonoidHom r) ∧
    (∀ a a' b, ∃ r, polar u (a + a') b * (polar u a b * polar u a' b)⁻¹ = Units.map (fracMap β.injective).toMonoidHom r) ∧
    ∀ a b, ∃ r, polar u (n • a) (n • b) = Units.map (fracMap β.injective).toMonoidHom r := by
  let z : (TK K).left := IsLocalRing.closedPoint (FractionRing K)
  obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB (Z := (TK K).left) z
  let υ := unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z
  have inj : Function.Injective υ := unitAt_injective z
  refine ⟨fun x => ?_, fun a a' b => ?_, fun a b => ?_⟩
  · obtain ⟨r, hr⟩ := even_defect hG β.injective h x
    have e₁ : val (ψ (-x)) (𝟙 _) z J * val D.sym (𝟙 _ ≫ D.xK x) z J =
      υ (Units.map (fracMap β.injective).toMonoidHom r) * val (ψ x) (𝟙 _) z J :=
      (hr z J hJ).trans (congrArg₂ (· * ·) (FieldPull.unitAt_genMap β z r) rfl)
    have e₂ : υ (u (-x)) * val (ψ (-x)) (𝟙 _) z J * val D.sym (𝟙 _ ≫ D.xK x) z J = υ (u x) * val (ψ x) (𝟙 _) z J :=
      (congrArg₂ (· * ·) (hu _ z J hJ) (val_pull hJ _ _ _)).symm.trans ((val_mul hJ _ _ _).symm.trans
        ((val_corr hJ (hE x) (𝟙 _)).trans (hu _ z J hJ)))
    refine ⟨r⁻¹, inj ?_⟩
    rw [map_inv, map_inv, map_mul, map_inv]
    apply Additive.ofMul.injective
    have e₁' := congrArg Additive.ofMul e₁
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
    linear_combination (norm := abel) e₂' - e₁'
  · obtain ⟨r, hr⟩ := bimult_defect hG β.injective h a a' b
    let τ := fun a b => val ((withPsi D ψ hψ).tau a b) (𝟙 _) z J
    let θ := th D (T := TK K) z J (cP D _ a) (cP D _ a') (cP D _ b)
    have e₁ : τ (a + a') b * θ = υ (Units.map (fracMap β.injective).toMonoidHom r) * (τ a b * τ a' b) :=
      (hr z J hJ).trans (congrArg₂ (· * ·) (FieldPull.unitAt_genMap β z r) rfl)
    have e₂ : υ (polar u (a + a') b) * τ (a + a') b * θ = (υ (polar u a b) * τ a b) * (υ (polar u a' b) * τ a' b) :=
      (congrArg₂ (· * ·) (val_tau_ratio D ψ hψ u hu _ _ hJ) rfl).symm.trans
        ((val_tau_add (𝟙 (TK K)) hJ hB a a' b).trans
          (congrArg₂ (· * ·) (val_tau_ratio D ψ hψ u hu _ _ hJ) (val_tau_ratio D ψ hψ u hu _ _ hJ)))
    refine ⟨r⁻¹, inj ?_⟩
    rw [map_inv, map_inv, map_mul, map_inv, map_mul]
    apply Additive.ofMul.injective
    have e₁' := congrArg Additive.ofMul e₁
    have e₂' := congrArg Additive.ofMul e₂
    simp only [ofMul_mul, ofMul_inv] at e₁' e₂' ⊢
    linear_combination (norm := abel) e₂' - e₁'
  · obtain ⟨r, hr⟩ := tau_defect β.injective h (n • a) (n • b) (cPoint_nsmul_eq_one hc _ a) (cPoint_nsmul_eq_one hc _ b)
      (by rw [map_nsmul]; exact cPoint_nsmul_eq_one hc₀ _ _) (by rw [map_nsmul]; exact cPoint_nsmul_eq_one hc₀ _ _)
    have e := (unitAt_kappa hc a b hJ).trans ((val_tau_ratio D ψ hψ u hu _ _ hJ).trans
      (congrArg₂ (· * ·) rfl ((hr z J hJ).trans (FieldPull.unitAt_genMap β z r))))
    rw [hκ] at e
    refine ⟨r⁻¹, inj ?_⟩
    rw [map_inv, map_inv, eq_inv_iff_mul_eq_one]
    exact e.symm.trans (map_one _)

end Ratio

theorem torsion_below {k K : Type} [Field k] [Field K] {β : k →+* K} {D₀ : DegPre k} {D : DegPre K}
    (h : IsPullDeg β D₀ D) {n : ℕ} (hc : ∀ y, D.c y ^ n = 1) (y : D₀.X) : D₀.c y ^ n = 1 := by
  obtain ⟨x, rfl⟩ := h.xe.surjective y
  have := FieldBaseChange.flat_spMap β
  have := FieldBaseChange.surjective_spMap β
  have : Epi (spMap β) := Flat.epi_of_flat_of_surjective _
  let ρ : Over.mk ((𝟙_ (Over (Sp K))).hom ≫ spMap β) ⟶ 𝟙_ (Over (Sp k)) :=
    Over.homMk (spMap β) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e : pushHom (pull_grp h) (𝟙_ _) (D.c x) = ρ ≫ D₀.c (h.xe x) := Over.OverMorphism.ext (h.c_pr x)
  have e' : ρ ≫ D₀.c (h.xe x) ^ n = ρ ≫ 1 := by
    rw [MonObj.comp_pow, ← e, ← map_pow, MonObj.comp_one]
    exact (congrArg _ (hc x)).trans (map_one _)
  exact Over.OverMorphism.ext ((cancel_epi (spMap β)).1 (congrArg (fun q => q.left) e'))

theorem exists_of_ratio (hL : Laws) {k k₂ K : Type} [Field k] [Field k₂] [Field K] (i : k →+* k₂) (β₂ : k₂ →+* K)
    {β : k →+* K} (hi : β₂.comp i = β) (D : DegPre K) (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (D₀ : DegPre k)
    (h : IsPullDeg β D₀ (withPsi D ψ hψ)) (u : D.X → (FractionRing K)ˣ)
    (hu : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (u χ) * val (ψ χ) (𝟙 _) z J)
    (a : D.X → k₂) (ha : ∀ χ, β₂ (a χ) = FractionRing.algEquiv K K (u χ).val) :
    ∃ (D₂ : DegPre k₂) (p : IsPullDeg β₂ D₂ D) (χ : D₂.P.A.left ⟶ D₀.P.A.left),
      IsPolFibre i D₀.P D₂.P χ ∧ proj p ≫ χ = proj h := by
  subst hi
  obtain ⟨D', h₁, -, hg⟩ := DegPull.exists_isPullDeg hL.polBaseChange k k₂ i D₀ ⊤ (FieldPull.nonempty_psiOn_field D₀)
    trivial
  obtain ⟨h₂, e₂⟩ := FieldPull.exists_isPullDeg_cancel k k₂ K i β₂ D₀ D' _ h₁ h
  have key : ∀ χ, fracMap β₂.injective (algebraMap k₂ (FractionRing k₂) (a χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap k₂ (FractionRing k₂) (a χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D'.X → (FractionRing k₂)ˣ,
      ∀ χ, Units.map (fracMap β₂.injective).toMonoidHom (q (h₂.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h₂.xe.symm y)), fun χ => Units.ext (by
      show fracMap β₂.injective (algebraMap k₂ (FractionRing k₂) (a (h₂.xe.symm (h₂.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := FieldPull.exists_isPullDeg_rescale β₂ D' D ψ hψ h₂ q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  have f : IsPolFibre i D₀.P D'.P (proj h₁) := ⟨hg, pull_grp h₁, LBIso.symm ⟨h₁.w, h₁.w_gen⟩⟩
  refine ⟨rescale D' q, hD, proj (D := D₀) (D' := D') h₁, f, ?_⟩
  rw [hp]
  exact e₂

def toC : (FractionRing ℂ)ˣ →* ℂˣ := Units.map (FractionRing.algEquiv ℂ ℂ).toRingHom.toMonoidHom

theorem toC_mem (k : IntermediateField ℚ ℂ) (r : (FractionRing k)ˣ) :
    toC (Units.map (fracMap (algebraMap k ℂ).injective).toMonoidHom r) ∈ unitsIn k := by
  obtain ⟨a, ha⟩ := (FractionRing.algEquiv k k).symm.surjective r.val
  have ha' : algebraMap k (FractionRing k) a = r.val := ((FractionRing.algEquiv k k).symm.commutes a).symm.trans ha
  show FractionRing.algEquiv ℂ ℂ (fracMap (algebraMap k ℂ).injective r.val) ∈ k
  rw [← ha', fracMap_algebraMap, AlgEquiv.commutes]
  exact a.2

theorem exists_of_pre (hL : Laws) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (D : DegPre ℂ) (ψ : PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (D₀ : DegPre k) (h : IsPullDeg (algebraMap k ℂ) D₀ (withPsi D ψ hψ)) (hE : D.PsiEven)
    (hB : D.TauBimult) {n : ℕ} (hn : 0 < n) (hc : ∀ y, D.c y ^ n = 1) (hκ : ∀ y y', kappa hc y y' = 1) :
    ∃ (k₂ : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k₂) (i : k →+* k₂) (D₂ : DegPre k₂)
      (p : IsPullDeg (algebraMap k₂ ℂ) D₂ D) (χ : D₂.P.A.left ⟶ D₀.P.A.left),
      (algebraMap k₂ ℂ).comp i = algebraMap k ℂ ∧ IsPolFibre i D₀.P D₂.P χ ∧ proj p ≫ χ = proj h := by
  choose u hu using FieldPull.exists_psi_ratio D ψ hψ
  obtain ⟨d₁, d₂, d₃⟩ := ratio_defects _ D ψ hψ u hu hL.globalFns D₀ h hE hB hc hκ (torsion_below h hc)
  have pm : ∀ a b, polar (fun x => toC (u x)) a b = toC (polar u a b) := fun a b => by
    simp only [polar, map_mul, map_inv]
  obtain ⟨k₂, fd, le, hk⟩ := exists_field k (fun x => toC (u x)) hn
    (fun x => by
      obtain ⟨r, hr⟩ := d₁ x
      rw [← map_inv, ← map_mul, hr]; exact toC_mem k r)
    (fun a a' b => by
      obtain ⟨r, hr⟩ := d₂ a a' b
      rw [pm, pm, pm, ← map_mul, ← map_inv, ← map_mul, hr]; exact toC_mem k r)
    (fun a b => by
      obtain ⟨r, hr⟩ := d₃ a b
      rw [pm, hr]; exact toC_mem k r)
  have hi : (algebraMap k₂ ℂ).comp (IntermediateField.inclusion le).toRingHom = algebraMap k ℂ :=
    RingHom.ext fun _ => rfl
  obtain ⟨D₂, p, χ, h₁, h₂⟩ := exists_of_ratio hL _ _ hi D ψ hψ D₀ h u hu (fun χ => ⟨_, hk χ⟩) fun _ => rfl
  exact ⟨k₂, fd, _, D₂, p, χ, hi, h₁, h₂⟩

theorem exists_points (hL : Laws) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P : PolAV (Sp K))
    (Q : PolAV (Sp ℂ)) (φ : Q.A.left ⟶ P.A.left) {n : ℕ} (hn : 0 < n) (h : IsPolFibre σ P Q φ) :
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (i : K →+* k) (P₁ : PolAV (Sp k))
      (φ₁ : P₁.A.left ⟶ P.A.left) (Φ : Q.A.left ⟶ P₁.A.left), (algebraMap k ℂ).comp i = σ ∧ IsPolFibre i P P₁ φ₁ ∧
      IsPolFibre (algebraMap k ℂ) P₁ Q Φ ∧ Φ ≫ φ₁ = φ ∧ ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, x ^ n = 1 →
        ∃ x₁ : 𝟙_ (Over (Sp k)) ⟶ P₁.A, x.left ≫ Φ = spMap (algebraMap k ℂ) ≫ x₁.left := by
  let k₀ : IntermediateField ℚ ℂ := σ.toRatAlgHom.fieldRange
  have : FiniteDimensional ℚ k₀ := (AlgEquiv.ofInjectiveField σ.toRatAlgHom).toLinearEquiv.finiteDimensional
  let i₀ : K →+* k₀ := σ.codRestrict k₀ fun x => ⟨x, rfl⟩
  obtain ⟨P₀, φ₀, h₀⟩ := exists_isPolFibre hL.polBaseChange i₀ P
  obtain ⟨Φ₀, e₀, H₀⟩ := CM.EllComp.exists_isPolFibre_lift (g := algebraMap k₀ ℂ) h₀ h
  obtain ⟨k, fd, le, hk⟩ := exists_numberField_torsion_points hL k₀ P₀ n hn
  let j : k₀ →+* k := (IntermediateField.inclusion le).toRingHom
  obtain ⟨P₁, φ₁, h₁⟩ := exists_isPolFibre hL.polBaseChange j P₀
  obtain ⟨Φ, e₁, H₁⟩ := CM.EllComp.exists_isPolFibre_lift (g := algebraMap k ℂ) h₁ H₀
  refine ⟨k, fd, j.comp i₀, P₁, φ₁ ≫ φ₀, Φ, rfl, CM.EllComp.isPolFibre_comp h₀ h₁, H₁,
    by rw [← Category.assoc, e₁, e₀], fun x hx => ?_⟩
  let ρ : Over.mk (spMap (algebraMap k₀ ℂ)) ⟶ Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ spMap (algebraMap k₀ ℂ)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans (Category.id_comp _))
  obtain ⟨y, hy, -⟩ := hk k le le_rfl (ρ ≫ pushHom H₀.2.1 (𝟙_ _) x) (by
    rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one])
  have hy' : spMap (algebraMap k ℂ) ≫ y.left = x.left ≫ Φ₀ := hy.trans (Category.id_comp _)
  have w : y.left ≫ P₀.A.hom = 𝟙 (Sp k) ≫ spMap j := (Over.w y).trans (Category.id_comp _).symm
  refine ⟨Over.homMk (h₁.2.1.1.lift _ _ w) (h₁.2.1.1.lift_snd _ _ w), h₁.2.1.1.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans (hy'.symm.trans
      ((congrArg (_ ≫ ·) (h₁.2.1.1.lift_fst _ _ w).symm).trans (Category.assoc _ _ _).symm)))
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) H₁.2.1.1.w).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (Over.w x)).trans (Eq.trans ?_ ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (h₁.2.1.1.lift_snd _ _ w))).symm))))
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.NormDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem GlobalTheory.NormDescent.exists_numberField_pre : Known → ∀ (K : Type) [Field K] [NumberField K] (σ₁ : K →+* ℂ) (P : Out.PolAV (Sp K)) (DC : Out.DegPre ℂ) (φ : DC.P.A.left ⟶ P.A.left) (n : ℕ), 0 < n → IsPolFibre σ₁ P DC.P φ → DC.PsiEven → DC.TauBimult → TauCan DC n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (i : K →+* K₂) (σ₂ : K₂ →+* ℂ) (D₂ : Out.DegPre K₂) (p : Out.IsPullDeg σ₂ D₂ DC) (ψ : D₂.P.A.left ⟶ P.A.left), σ₂.comp i = σ₁ ∧ IsPolFibre i P D₂.P ψ ∧ prj p ≫ ψ = φ := by
  intro hK K _ _ σ₁ P DC φ n hn h hE hB ⟨hc, hκ⟩
  obtain ⟨k, fd, i, P₁, φ₁, Φ, hi, h₁, H, e, hx⟩ := NormDescent.exists_points hK.laws K σ₁ P DC.P φ hn h
  choose x₀ hx₀ using fun y => hx (DC.c y) (hc y)
  obtain ⟨c₀, hc₀, hc₁⟩ := PointDescent.additive_points_descend k ℂ _ P₁ DC.P Φ H.2.1 DC.X DC.X id (by simp) DC.c
    DC.c_add x₀ hx₀
  obtain ⟨D₀, ψ, hψ, h₀, rfl, e₀⟩ := FieldPull.exists_pre_below hK.laws k ℂ _ DC P₁ Φ H.2.1 H.2.2.symm c₀ hc₀ hc₁
  obtain rfl := eq_of_heq e₀
  obtain ⟨k₂, fd₂, j, D₂, p, χ, hj, h₂, e₂⟩ := NormDescent.exists_of_pre hK.laws k DC ψ hψ D₀ h₀ hE hB hn hc hκ
  refine ⟨k₂, inferInstance, ⟨⟩, j.comp i, algebraMap k₂ ℂ, D₂, p, χ ≫ φ₁, ?_, CM.EllComp.isPolFibre_comp h₁ h₂, ?_⟩
  · rw [← RingHom.comp_assoc, hj, hi]
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ₁) e₂).trans e)
