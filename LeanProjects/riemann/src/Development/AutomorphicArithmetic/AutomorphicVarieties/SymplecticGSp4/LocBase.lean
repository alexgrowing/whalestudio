import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartL
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LiftGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Series

open MvPowerSeries

variable {O E σ τ : Type} [CommRing O] [CommRing E] [Algebra O E]

private theorem lb_ext [Finite σ] [Finite τ] (f g : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E)
    (h0 : ∀ s, constantCoeff (f (X s)) = 0) (h : ∀ s, f (X s) = g (X s)) : f = g := by
  refine AlgHom.ext fun p => MvPowerSeries.ext fun d => ?_
  have := GlobalTheory.algHom_sub_mem_pow f g (J := GlobalTheory.germIdeal τ E) h0 (fun s => h s ▸ h0 s)
    (n := d.degree + 1) (fun s => by simp [h s]) p
  have h2 := GlobalTheory.mem_germIdeal_pow_iff.1 this d (Nat.lt_succ_self _)
  rwa [map_sub, sub_eq_zero] at h2

private theorem lb_graded [Finite σ] [Finite τ] {G : Type} [AddCommGroup G] (w : σ → G) (w' : τ → G)
    (F : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E) (h0 : ∀ s, constantCoeff (F (X s)) = 0)
    (hw : ∀ s, F (X s) ∈ wtPart E w' (w s)) (j : G) (f : MvPowerSeries σ O) (hf : f ∈ wtPart O w j) :
    F f ∈ wtPart E w' j := by
  classical
  have ha : HasSubst fun s => F (X s) := hasSubst_of_constantCoeff_zero h0
  rw [lb_ext F (substAlgHom ha) h0 fun s => (substAlgHom_X ha s).symm]
  intro n hn
  rw [coe_substAlgHom, coeff_subst ha]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : Finsupp.weight w d = j
  · have : (d.prod fun s k => F (X s) ^ k) ∈ wtPart E w' j := by
      rw [← hd, Finsupp.weight_apply, Finsupp.sum]
      exact SetLike.prod_pow_mem_graded (wtPart E w') w (fun s => F (X s)) d (fun s _ => hw s)
    rw [this n hn, smul_zero]
  · rw [hf d hd, zero_smul]

private theorem lb_const [Finite σ] (x : MvPowerSeries σ O →ₐ[O] O) (h0 : ∀ s, x (X s) = 0) (f : MvPowerSeries σ O) :
    x f = constantCoeff f := by
  let k : MvPowerSeries σ O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries σ O →+* O) with commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  have := GlobalTheory.algHom_sub_mem_pow x k (J := (⊥ : Ideal O)) (fun s => h0 s) (fun s => by simp [k])
    (n := 1) (fun s => by simp [h0, k]) f
  rw [pow_one, Ideal.mem_bot, sub_eq_zero] at this
  exact this

private theorem lb_max {K : Type} [Field K] : maximalIdeal (MvPowerSeries τ K) = GlobalTheory.germIdeal τ K := by
  ext f
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  rfl

private theorem lb_chart [IsDomain O] [Finite τ] {R Y : Type} [CommRing R] [Algebra O R] [AddCommGroup Y]
    (W : WPres O Y R) (x : R →ₐ[O] O) (hz : ∀ s, x (W.z s) = 0) (P : Ideal R) (u : τ → Y)
    (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)) (hφ : Loc.IsCompl P x φ) (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0)
    (hw : ∀ s, φ (W.z s) ∈ wtPart (FractionRing O) u (W.wt s)) :
    ∃ h : W.HasOrigin, W.origin h = x ∧ IsChart W.part x u φ := by
  classical
  have hc : ∀ f, x (W.π f) = constantCoeff f := lb_const (x.comp W.π) hz
  have h : W.HasOrigin := fun f hf => by rw [← hc, hf, map_zero]
  refine ⟨h, AlgHom.ext fun a => ?_, ?_, hφ.const, fun i => ?_, fun f hf hl => ?_⟩
  · obtain ⟨f, rfl⟩ := W.surj a
    rw [W.origin_π, hc]
  · rintro j _ ⟨f, hf, rfl⟩
    exact lb_graded W.wt u (φ.comp W.π) (fun s => (hφ.const (W.z s)).trans (by rw [hz, map_zero])) hw j f hf
  · obtain ⟨a, c, hc0, ha⟩ := hφ.dense 2 (X i)
    rw [lb_max] at ha
    have key : ∀ i', coeff (Finsupp.single i' 1) (φ a) = c • (if i' = i then 1 else 0 : FractionRing O) := fun i' => by
      have := GlobalTheory.mem_germIdeal_pow_iff.1 ha (Finsupp.single i' 1) (by simp)
      rw [map_sub, sub_eq_zero] at this
      rw [← this, ← IsScalarTower.algebraMap_smul (FractionRing O) c, map_smul, IsScalarTower.algebraMap_smul, coeff_X]
      simp [Finsupp.single_left_inj]
    refine ⟨a, ?_, fun i' hi => ?_⟩
    · rw [key, if_pos rfl, Algebra.smul_def, mul_one]
      exact fun e => hc0 (IsFractionRing.injective O (FractionRing O) (by rw [e, map_zero]))
    · rw [key, if_neg hi, smul_zero]
  · have h2 : φ f ∈ maximalIdeal (MvPowerSeries τ (FractionRing O)) ^ 2 := by
      rw [lb_max]
      refine GlobalTheory.mem_germIdeal_pow_iff.2 fun d hd => ?_
      obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
      · rw [(Finsupp.degree_eq_zero_iff d).1 h0, coeff_zero_eq_constantCoeff_apply, hφ.const, hf, map_zero]
      · obtain ⟨i, rfl⟩ : ∃ i, d = Finsupp.single i 1 := by
          have : d ∈ Set.range fun i : τ => Finsupp.single i 1 := by
            rw [Finsupp.range_single_one]; exact h1
          obtain ⟨i, hi⟩ := this
          exact ⟨i, hi.symm⟩
        exact hl i
    obtain ⟨c, hc0, hcf⟩ := hφ.inj 2 f h2
    obtain ⟨a, ha, p, hp, e⟩ := Submodule.mem_sup.1 hcf
    obtain ⟨y, hy0, hy⟩ := hy
    have hxp : x p = 0 := by
      apply IsFractionRing.injective O (FractionRing O)
      have : φ p = 0 := by rw [← hφ.ker] at hp; exact hp
      rw [← hφ.const, this, map_zero, map_zero]
    refine ⟨x y * c, mul_ne_zero hy0 hc0, ?_⟩
    rw [mul_smul, ← e, smul_add]
    refine add_mem (Submodule.smul_of_tower_mem _ _ ha) ?_
    have : x y • p = (algebraMap O R (x y) - y) * p := by rw [sub_mul, hy p hp, sub_zero, Algebra.smul_def]
    rw [this, sq]
    exact Ideal.mul_mem_mul (by simp [RingHom.mem_ker]) hxp

end Series

section Abstract

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

private structure Pk {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)} (P : Cond O rbar)
    (ρ₀ : Γ →* M4 O) (n : ℤ × ℤ → ℕ) where
  B : Type
  [cB : CommRing B]
  [aB : Algebra O B]
  [coB : IsCO O B]
  W : WPres O (ℤ × ℤ) B
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  z_mem : ∀ i, W.z i ∈ maximalIdeal B
  ρ : Lift O rbar B
  rep : Represents P ρ
  hom : ∀ g i j, ρ.hom g i j ∈ W.part (wt i j)
  at0 : ∀ g i j, W.origin org (ρ.hom g i j) = ρ₀ g i j
  τ : Type
  [fτ : Fintype τ]
  u : τ → ℤ × ℤ
  φ : B →ₐ[O] MvPowerSeries τ (FractionRing O)
  chart : IsChart W.part (W.origin org) u φ
  card : ∀ j, Nat.card {i // u i = j} = n j

attribute [local instance] Pk.cB Pk.aB Pk.coB Pk.fτ

private theorem pk_of {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)} (P : Cond O rbar)
    (ρ₀ : Γ →* M4 O) (h0 : ∀ g a b, a ≠ b → ρ₀ g a b = 0) (n : ℤ × ℤ → ℕ)
    (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (hrep : Represents P ρ) (hst : ρ.TStable w4)
    (x : R →ₐ[O] O) (Q : Ideal R) {m : ℕ} (u : Fin m → ℤ × ℤ) (φ : R →ₐ[O] MvPowerSeries (Fin m) (FractionRing O))
    (hx : (ρ.map x).hom = ρ₀) (hφ : Loc.IsCompl Q x φ) (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ Q, y * a = 0)
    (hu : ∀ j, Nat.card {i // u i = j} = n j) (hw : ∀ g a b, φ (ρ.hom g a b) ∈ wtPart (FractionRing O) u (wt a b)) :
    Nonempty (Pk P ρ₀ n) := by
  have hx' : ∀ g a b, x (ρ.hom g a b) = ρ₀ g a b := fun g a b => by rw [← hx]; rfl
  have hres : ∀ g a b, residue O (ρ₀ g a b) = rbar g a b := fun g a b => by
    rw [← (ρ.map x).red g a b, hx]
    exact ((res O O).commutes _).symm
  obtain ⟨W, hW1, hW2⟩ := lift_grading O (ℤ × ℤ) Γ (Fin 4) rbar w4 R ρ (fun g a b => ρ₀ g a b) hres
    (fun g a b h => h0 g a b fun e => h (congrArg w4 e))
    (fun R' _ _ _ f f' e => ((hrep R').2 _ ((hrep R').1 f')).unique e rfl) hst
  have hz : ∀ s, x (W.z s) = 0 := fun s => by
    obtain ⟨g, a, b, e, -⟩ := hW2 s
    rw [e, map_sub, hx', AlgHom.commutes]
    exact sub_self _
  obtain ⟨h, ho, hc⟩ := lb_chart W x hz Q u φ hφ hy fun s => by
    obtain ⟨g, a, b, e, e'⟩ := hW2 s
    rw [e, e', w4_sub_w4_eq_wt, map_sub]
    refine sub_mem (hw g a b) ?_
    by_cases hab : a = b
    · rw [(wt_eq_zero a b).2 hab, AlgHom.commutes, IsScalarTower.algebraMap_apply O (FractionRing O),
        Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart _ _)
    · rw [h0 g a b hab, map_zero, map_zero]
      exact zero_mem _
  refine ⟨{ B := R, W := W, wt_mem := fun s => ?_, org := h, z_mem := fun s => ?_, ρ := ρ, rep := hrep, hom := hW1
            at0 := fun g a b => by rw [ho, hx'], τ := Fin m, u := u, φ := φ, chart := ho ▸ hc, card := hu }⟩
  · obtain ⟨g, a, b, -, e'⟩ := hW2 s
    rw [e', w4_sub_w4_eq_wt]
    exact wt_mem a b
  · rw [← res_eq_zero_iff O, ← res_map x, hz, map_zero]

private theorem card_sigma {T Y : Type} [Fintype T] (τ : T → Type) [∀ v, Fintype (τ v)] (u : ∀ v, τ v → Y) (j : Y) :
    Nat.card {p : Σ v, τ v // u p.1 p.2 = j} = ∑ v, Nat.card {i // u v i = j} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem pk_sum {T : Type} [Fintype T] {Γ : T → Type} [∀ v, Group (Γ v)] [∀ v, TopologicalSpace (Γ v)]
    {rbar : ∀ v, Γ v →* M4 (ResidueField O)} {P : ∀ v, Cond O (rbar v)} {ρ₀ : ∀ v, Γ v →* M4 O} {n : T → ℤ × ℤ → ℕ}
    (K : ∀ v, Pk (P v) (ρ₀ v) (n v)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (W : WPres O (ℤ × ℤ) B) (org : W.HasOrigin)
      (ρ : ∀ v, Lift O (rbar v) B), (∀ i, W.wt i ∈ wts) ∧ (∀ v, P v B (ρ v)) ∧
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ' : ∀ v, Lift O (rbar v) R), (∀ v, P v R (ρ' v)) →
        ∃! f : B →ₐ[O] R, ∀ v, (ρ v).map f = ρ' v) ∧
      (∀ v g i j, (ρ v).hom g i j ∈ W.part (wt i j)) ∧ (∀ v g i j, W.origin org ((ρ v).hom g i j) = ρ₀ v g i j) ∧
      SmoothPt W.gr ((W.origin org).comp W.A.val) fun j => ∑ v, n v j := by
  obtain ⟨B, i1, i2, i3, ι, W, e, hu, hz, hp, hk⟩ :=
    coprod O (ℤ × ℤ) T (fun v => (K v).B) (fun v => (K v).W) fun v => (K v).z_mem
  obtain ⟨org, ψ, hψ, -⟩ := chart_sum O (ℤ × ℤ) T (fun v => (K v).B) (fun v => (K v).W) (fun v => (K v).org)
    (fun v => (K v).τ) (fun v => (K v).u) (fun v => (K v).φ) (fun v => (K v).chart) B W e (fun v s => (hz v s).1) hk
  refine ⟨B, i1, i2, i3, W, org, fun v => (K v).ρ.map (ι v), fun i => ?_, fun v => ((K v).rep B).1 _,
    fun R _ _ _ ρ' h => ?_, fun v g i j => hp v _ _ ((K v).hom g i j), fun v g i j => ?_,
    (Σ v, (K v).τ), inferInstance, _, _, chart_gr O (ℤ × ℤ) B W org _ _ ψ hψ, fun j => ?_⟩
  · obtain ⟨⟨v, s⟩, rfl⟩ := e.surjective i
    rw [(hz v s).1]
    exact (K v).wt_mem s
  · choose f hf hf' using fun v => ((K v).rep R).2 (ρ' v) (h v)
    obtain ⟨F, hF, hF'⟩ := hu R f
    refine ⟨F, fun v => ?_, fun F' h' => hF' F' fun v => hf' v _ (h' v)⟩
    rw [← hf v, ← hF v]
    rfl
  · rw [← (K v).at0, Lift.map_hom]
    obtain ⟨f, hf⟩ := (K v).W.surj ((K v).ρ.hom g i j)
    rw [← hf, WPres.origin_π]
    refine lb_const (((W.origin org).comp (ι v)).comp (K v).W.π) (fun s => ?_) f
    show W.origin org (ι v ((K v).W.z s)) = 0
    rw [← (hz v s).2, WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
  · refine (card_sigma (fun v => (K v).τ) (fun v => (K v).u) j).trans ?_
    exact Finset.sum_congr rfl fun v _ => (K v).card j

end Abstract

section Eqs

variable {R R' : Type} [CommRing R] [CommRing R']

private theorem prj_hom {A A' : Type} [CommRing A] [CommRing A'] (f : A →+* A') (F : GradeZeroInterpolatingElement.M4 A →+* GradeZeroInterpolatingElement.M4 A')
    (hF : ∀ (a : A) X, F (a • X) = f a • F X) (c : Fin 4 → A) (X : GradeZeroInterpolatingElement.M4 A) (i : Fin 4) :
    prj (fun a => f (c a)) (F X) i = F (prj c X i) := by
  have key : ∀ p : Polynomial A, Polynomial.aeval (F X) (p.map f) = F (Polynomial.aeval X p) := fun p => by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, map_add, hp, hq]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
        ← Algebra.smul_def, hF, map_pow]
  unfold prj
  rw [← key, Polynomial.map_prod]
  simp

private theorem smul_map' (f : R →+* R') (a : R) (X : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix (a • X) = f a • f.mapMatrix X := by
  ext i j
  simp [RingHom.mapMatrix_apply]

private theorem map_zero_iff (f : R →+* R') (X : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix X = 0 ↔ ∀ i j, f (X i j) = 0 :=
  Matrix.ext_iff.symm

private theorem gsp_iff (f : R →+* R') (ν : R) (g : GradeZeroInterpolatingElement.M4 R) :
    IsGSp (f ν) (f.mapMatrix g) ↔ ∀ i j, f ((adj g * g - ν • (1 : GradeZeroInterpolatingElement.M4 R)) i j) = 0 := by
  rw [← map_zero_iff, map_sub, sub_eq_zero, smul_map', map_one, map_mul, IsGSp, RingHom.mapMatrix_apply,
    (grp R).2.2.2.2.2.1]
  rfl

private theorem one_iff (f : R →+* R') (g : GradeZeroInterpolatingElement.M4 R) : f.mapMatrix g = 1 ↔ ∀ i j, f ((g - 1) i j) = 0 := by
  rw [← map_zero_iff, map_sub, sub_eq_zero, map_one]

variable {H : Type} [Group H]

private def ordSet (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* GradeZeroInterpolatingElement.M4 R) : Set R :=
  {x | (∃ n, x = ((r s₀).charpoly - ∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).coeff n) ∨
    (∃ g i j a b, i < j ∧ x = (prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i) a b) ∨
    ∃ s ∈ I, ∃ i a b, x = (prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) *
      prj (fun a => ps a s₀) (r s₀) i) a b}

private theorem ord_iff (f : R →+* R') (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* GradeZeroInterpolatingElement.M4 R) :
    GradeZeroInterpolatingElement.Ord I (fun i g => f (ps i g)) s₀ (mapRep f r) ↔ ∀ x ∈ ordSet I ps s₀ r, f x = 0 := by
  have hr : ∀ g, mapRep f r g = f.mapMatrix (r g) := fun _ => rfl
  have hp := prj_hom f f.mapMatrix (smul_map' f) (fun a => ps a s₀) (r s₀)
  have h1 : (mapRep f r s₀).charpoly = ∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀))) ↔
      ∀ n, f (((r s₀).charpoly - ∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).coeff n) = 0 := by
    have : ∏ j, (Polynomial.X - Polynomial.C (f (ps j s₀))) =
        (∏ j, (Polynomial.X - Polynomial.C (ps j s₀))).map f := by
      rw [Polynomial.map_prod]; simp
    rw [this, hr, RingHom.mapMatrix_apply, Matrix.charpoly_map, ← sub_eq_zero, ← Polynomial.map_sub,
      Polynomial.ext_iff]
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
  have h2 : ∀ g i j, prj (fun a => f (ps a s₀)) (mapRep f r s₀) j * mapRep f r g *
      prj (fun a => f (ps a s₀)) (mapRep f r s₀) i = 0 ↔
      ∀ a b, f ((prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i) a b) = 0 := fun g i j => by
    rw [hr, hr, hp, hp, ← map_mul, ← map_mul, map_zero_iff]
  have h3 : ∀ s i, prj (fun a => f (ps a s₀)) (mapRep f r s₀) i * (mapRep f r s - f (ps i s) • (1 : GradeZeroInterpolatingElement.M4 R')) *
      prj (fun a => f (ps a s₀)) (mapRep f r s₀) i = 0 ↔
      ∀ a b, f ((prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) *
        prj (fun a => ps a s₀) (r s₀) i) a b) = 0 := fun s i => by
    have e : f (ps i s) • (1 : GradeZeroInterpolatingElement.M4 R') = f.mapMatrix (ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) := by rw [smul_map', map_one]
    rw [hr, hr, hp, e, ← map_sub, ← map_mul, ← map_mul, map_zero_iff]
  refine ⟨fun h x hx => ?_, fun h => ⟨h1.2 fun n => h _ (.inl ⟨n, rfl⟩),
    fun g i j hij => (h2 g i j).2 fun a b => h _ (.inr (.inl ⟨g, i, j, a, b, hij, rfl⟩)),
    fun s hs i => (h3 s i).2 fun a b => h _ (.inr (.inr ⟨s, hs, i, a, b, rfl⟩))⟩⟩
  obtain ⟨n, rfl⟩ | ⟨g, i, j, a, b, hij, rfl⟩ | ⟨s, hs, i, a, b, rfl⟩ := hx
  · exact h1.1 h.charpoly n
  · exact (h2 g i j).1 (h.stable g i j hij) a b
  · exact (h3 s i).1 (h.inert s hs i) a b

private theorem ord_conj (u : (GradeZeroInterpolatingElement.M4 R)ˣ) {I : Subgroup H} {ps : Fin 4 → H → R} {s₀ : H} {r r' : H →* GradeZeroInterpolatingElement.M4 R}
    (hr : ∀ g, r' g = u * r g * (u⁻¹ : (GradeZeroInterpolatingElement.M4 R)ˣ)) (h : GradeZeroInterpolatingElement.Ord I ps s₀ r) : GradeZeroInterpolatingElement.Ord I ps s₀ r' := by
  let F : GradeZeroInterpolatingElement.M4 R →+* GradeZeroInterpolatingElement.M4 R := MulSemiringAction.toRingHom _ _ (ConjAct.toConjAct u)
  have hF : ∀ X, F X = u * X * (u⁻¹ : (GradeZeroInterpolatingElement.M4 R)ˣ) := fun X => by simp [F, ConjAct.units_smul_def]
  have hs : ∀ (a : R) X, F (a • X) = a • F X := fun a X => by rw [hF, hF, mul_smul_comm, smul_mul_assoc]
  have hp : ∀ i, prj (fun a => ps a s₀) (F (r s₀)) i = F (prj (fun a => ps a s₀) (r s₀) i) :=
    prj_hom (RingHom.id R) F hs (fun a => ps a s₀) (r s₀)
  have hr' : ∀ g, r' g = F (r g) := fun g => by rw [hr, hF]
  refine ⟨?_, fun g i j hij => ?_, fun s hs' i => ?_⟩
  · rw [hr, Matrix.coe_units_inv, Matrix.charpoly_units_conj, h.charpoly]
  · rw [hr', hr', hp, hp, ← map_mul, ← map_mul, h.stable g i j hij, map_zero]
  · have e : ps i s • (1 : GradeZeroInterpolatingElement.M4 R) = F (ps i s • (1 : GradeZeroInterpolatingElement.M4 R)) := by rw [hs, map_one]
    rw [hr', hr', hp, e, ← map_sub, ← map_mul, ← map_mul, h.inert s hs' i, map_zero]

private theorem gsp_conj (s : Rˣ × Rˣ) {ν : R} {g : GradeZeroInterpolatingElement.M4 R} (h : IsGSp ν g) : IsGSp ν (tconj s g) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, hadj, -⟩ := grp R
  show adj (tconj s _) * tconj s _ = _
  rw [hadj, ← hmul, h]
  conv_rhs => rw [← hone s]
  ext i j
  exact mul_left_comm _ _ _

end Eqs

section Stable

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* GradeZeroInterpolatingElement.M4 (ResidueField O)}

private theorem closed_of_set (P : Cond O rbar)
    (h : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rbar R), ∃ S : Set R,
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), P R' (r.map f) ↔ ∀ x ∈ S, f x = 0) :
    P.IsClosed := fun R _ _ _ r => by
  obtain ⟨S, hS⟩ := h R r
  refine ⟨Ideal.span S, fun R' _ _ _ f => (hS R' f).trans ⟨fun h x hx => ?_, fun h x hx => h x (Ideal.subset_span hx)⟩⟩
  exact (Ideal.span_le (I := RingHom.ker f)).2 h hx

private theorem tstable {P : Cond O rbar} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {ρ : Lift O rbar R}
    (hrep : Represents P ρ)
    (hP : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r r' : Lift O rbar R') (s : R'ˣ × R'ˣ),
      (∀ g, r'.hom g = tconj s (r.hom g)) → P R' r → P R' r') : ρ.TStable w4 := by
  intro R' _ _ _ f t ht
  let s : R'ˣ × R'ˣ := (t (Multiplicative.ofAdd (1, 0)), t (Multiplicative.ofAdd (0, 1)))
  have hs : ∀ j, wv s j = t (Multiplicative.ofAdd j) := fun j => by
    show t (Multiplicative.ofAdd (1, 0)) ^ j.1 * t (Multiplicative.ofAdd (0, 1)) ^ j.2 = _
    rw [← map_zpow t, ← map_zpow t, ← map_mul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add]
    simp
  obtain ⟨-, -, -, -, -, -, -, -, hmul, hone, -⟩ := grp R'
  let r' : Lift O rbar R' :=
    { hom := ⟨⟨fun g => tconj s ((ρ.map f).hom g), by rw [map_one, hone]⟩, fun g h => by
        show tconj s _ = _
        rw [map_mul, hmul]⟩
      cont := fun a b N => by
        show IsLocallyConstant fun g => Ideal.Quotient.mk _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b)
        simp only [map_mul]
        exact (IsLocallyConstant.const _).mul ((ρ.map f).cont a b N)
      red := fun g a b => by
        show res _ _ ((wv s (wt a b) : R') * (ρ.map f).hom g a b) = _
        rw [map_mul, hs, ht, one_mul, (ρ.map f).red] }
  obtain ⟨f', hf', -⟩ := (hrep R').2 r' (hP R' _ r' s (fun _ => rfl) ((hrep R').1 f))
  refine ⟨f', fun g a b => ?_⟩
  rw [hf', w4_sub_w4_eq_wt, ← hs]
  rfl

end Stable

private theorem phi_emb {Γ Δ : Type} [Group Γ] [TopologicalSpace Γ] [Group Δ] [TopologicalSpace Δ] (φ : Γ →* Δ)
    (hφ : Topology.IsOpenEmbedding φ) {l : ℕ} (h : PhiCond Δ l) : PhiCond Γ l := fun H hH => by
  haveI := h (H.map φ) (hφ.isOpenMap _ hH)
  let e := H.equivMapOfInjective φ hφ.injective
  have hc : Continuous e.symm := by
    refine Continuous.subtype_mk (f := fun x => (e.symm x : Γ)) (hφ.isInducing.continuous_iff.2 ?_) _
    refine continuous_subtype_val.congr fun x => ?_
    exact (congrArg Subtype.val (e.apply_symm_apply x)).symm
  refine Finite.of_injective
    (β := {ψ : H.map φ →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (H.map φ))})
    (fun ψ => ⟨ψ.1.comp e.symm.toMonoidHom, ψ.2.preimage hc⟩) fun ψ ψ' he => ?_
  exact Subtype.ext ((MonoidHom.cancel_right e.symm.surjective).1 (congrArg Subtype.val he))

private theorem frac_alg (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    ∃ _ : Algebra ℚ_[l] (FractionRing O), IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) ∧
      Module.Finite ℚ_[l] (FractionRing O) := by
  have hi : Function.Injective (algebraMap ℤ_[l] O) := (dvrFacts l O).1
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  exact ⟨inferInstance, inferInstance,
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])⟩

private theorem union_iff {α : Type} {S T : Set α} {p : α → Prop} :
    ((∀ x ∈ S, p x) ∧ ∀ x ∈ T, p x) ↔ ∀ x ∈ S ∪ T, p x :=
  ⟨fun h x hx => hx.elim (h.1 x) (h.2 x), fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩⟩

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem phi_dec (hP : Loc.LocalPublishedTheorems) (v : ℕ) [Fact v.Prime] (A : ValuationSubring Ω)
    (hA : A.valuation (v : Ω) < 1) : PhiCond (Dec (F := ℚ) A) l := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨-, φ, hφ, -⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).2 j
  exact phi_emb φ hφ (Loc.phiCond hP v l)

private theorem rep_ex (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (v : ℕ) (hv : v.Prime) (P : Cond c.O (D.rbarAt v))
    (hc : P.IsClosed) (ρ₀ : Lift c.O (D.rbarAt v) c.O) (h0 : P _ ρ₀) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R),
      Represents P ρ := by
  haveI : Fact v.Prime := ⟨hv⟩
  haveI : IsGalois ℚ Ω := {}
  haveI : CompactSpace (D.Gp v) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hk, -⟩ := facts D hD
  have hlc : IsLocallyConstant (D.rbarAt v) := by
    refine IsLocallyConstant.comp_continuous (g := D.rbar) ?_ continuous_subtype_val
    refine (IsLocallyConstant.iff_exists_open _).2 fun g =>
      ⟨(fun x => g⁻¹ * x) ⁻¹' (D.rbar.ker : Set _), hk.preimage (by fun_prop), by simp, fun x hx => ?_⟩
    have : D.rbar (g⁻¹ * x) = 1 := hx
    rw [← mul_inv_cancel_left g x, map_mul, this, mul_one]
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l c.O (D.Gp v) (Fin 4) (D.rbarAt v)
    (phi_dec hP v _ (hD.pl_over v hv)) hlc
  obtain ⟨R', _, _, _, p, -, h⟩ := univ_cond c.O (D.Gp v) (Fin 4) (D.rbarAt v) R r _ P hr hc
    ⟨c.O, inferInstance, inferInstance, inferInstance, ρ₀, trivial, h0⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((h C).1 f).2, fun r' h' => (h C).2 r' ⟨trivial, h'⟩⟩⟩

private theorem mult_iff {v : ℕ} {R R' : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing R'] [Algebra c.O R']
    [IsCO c.O R'] (r : Lift c.O (D.rbarAt v) R) (f : R →ₐ[c.O] R') :
    (∀ g : D.Gp v, IsGSp (algebraMap c.O R' (D.th g)) ((r.map f).hom g)) ↔
      ∀ x ∈ {x | ∃ (g : D.Gp v) (i j : Fin 4),
        x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j}, f x = 0 := by
  have key : ∀ g : D.Gp v, IsGSp (algebraMap c.O R' (D.th g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j) = 0 := fun g => by
    rw [← f.commutes]
    exact gsp_iff (f : R →+* R') _ (r.hom g)
  refine ⟨?_, fun h g => (key g).2 fun i j => h _ ⟨g, i, j, rfl⟩⟩
  rintro h _ ⟨g, i, j, rfl⟩
  exact (key g).1 (h g) i j

private theorem closedL : D.condL.IsClosed := closed_of_set _ fun R _ _ _ r => by
  refine ⟨{x | ∃ (g : D.Gp _) (i j : Fin 4),
      x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j} ∪
    ordSet ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 r.hom,
    fun R' _ _ _ f => Iff.trans (and_congr (mult_iff D r f) ?_) union_iff⟩
  have := ord_iff (f : R →+* R') ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O R (D.ps i g)) D.s0 r.hom
  simp only [RingHom.coe_coe, AlgHom.commutes] at this
  exact this

private theorem closedP (p : ℕ) : (D.condP p).IsClosed := closed_of_set _ fun R _ _ _ r => by
  refine ⟨{x | ∃ (g : D.Gp _) (i j : Fin 4),
      x = (adj (r.hom g) * r.hom g - algebraMap c.O R (D.th g) • (1 : GradeZeroInterpolatingElement.M4 R)) i j} ∪
    {x | ∃ (g : D.Gp p) (i j : Fin 4), (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker ∧ x = (r.hom g - 1) i j},
    fun R' _ _ _ f => Iff.trans (and_congr (mult_iff D r f) ?_) union_iff⟩
  refine ⟨?_, fun h g hg => (one_iff (f : R →+* R') (r.hom g)).2 fun i j => h _ ⟨g, i, j, hg, rfl⟩⟩
  rintro h _ ⟨g, i, j, hg, rfl⟩
  exact (one_iff (f : R →+* R') (r.hom g)).1 (h g hg) i j

private theorem diagonal_rep_off_diagonal_zero (v : ℕ) (g : D.Gp v) (a b : Fin 4) (h : a ≠ b) : D.r0At v g a b = 0 :=
  Matrix.diagonal_apply_ne (fun i => (D.ps i g : c.O)) h

private theorem pkL (hD : D.Good) (hP : Loc.LocalPublishedTheorems) : Nonempty (Pk D.condL (D.r0At l) dimL) := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := rep_ex D hD hP l hl.out _ (closedL D) _ ((ptMap D hD c.O ρ₀).1 hpt).atL
  obtain ⟨_, _, _⟩ := frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, hu, hw⟩ := Loc.spChartL hP D hD (FractionRing c.O) R ρ hrep
  refine pk_of _ _ (diagonal_rep_off_diagonal_zero D l) _ R ρ hrep (tstable hrep fun R' _ _ _ r r' s hr h => ⟨fun g => ?_, ?_⟩)
    x P w φ hx hφ hy hu hw
  · rw [hr]
    exact gsp_conj s (h.1 g)
  · obtain ⟨u, hu⟩ := (grp R').2.2.2.2.2.2.2.2.2.2.2.2 s
    exact ord_conj u (fun g => by rw [hr, hu]) h.2

private theorem pkP (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (p : ℕ) (hp : p ∈ D.Sb) :
    Nonempty (Pk (D.condP p) (D.r0At p) dimP) := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := rep_ex D hD hP p ((facts D hD).1 p hp).1 _ (closedP D p) _
    (((ptMap D hD c.O ρ₀).1 hpt).atP p hp)
  obtain ⟨_, _, _⟩ := frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, hu, hw⟩ := Loc.spChartP D hD p hp (FractionRing c.O) R ρ hrep
  refine pk_of _ _ (diagonal_rep_off_diagonal_zero D p) _ R ρ hrep (tstable hrep fun R' _ _ _ r r' s hr h => ⟨fun g => ?_, fun g hg => ?_⟩)
    x P w φ hx hφ hy hu hw
  · rw [hr]
    exact gsp_conj s (h.1 g)
  · rw [hr, h.2 g hg]
    exact (grp R').2.2.2.2.2.2.2.2.2.1 s

end Main

theorem UpperTheory.V.GradeZeroInterpolatingElement.locBase :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → Nonempty (LocBase D) := by
  intro Ω _ _ _ l _ c D hD hP
  have hne : ∀ p ∈ D.Sb, p ≠ l := fun p hp => ((facts D hD).1 p hp).2.1
  let P : ∀ v : ℕ, Cond c.O (D.rbarAt v) := Function.update D.condP l D.condL
  let n : ℕ → ℤ × ℤ → ℕ := Function.update (fun _ => dimP) l dimL
  have hPl : P l = D.condL := Function.update_self ..
  have hPp : ∀ p ∈ D.Sb, P p = D.condP p := fun p hp => Function.update_of_ne (hne p hp) ..
  have hnl : n l = dimL := Function.update_self ..
  have hnp : ∀ p ∈ D.Sb, n p = dimP := fun p hp => Function.update_of_ne (hne p hp) ..
  have hK : ∀ v : D.T, Nonempty (Pk (P v) (D.r0At v) (n v)) := by
    rintro ⟨v, hv⟩
    obtain rfl | hv' := Finset.mem_insert.1 hv
    · show Nonempty (Pk (P v) _ (n v))
      rw [hPl, hnl]
      exact pkL D hD hP
    · show Nonempty (Pk (P v) _ (n v))
      rw [hPp v hv', hnp v hv']
      exact pkP D hD hP v hv'
  have hE : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R),
      D.LocEqs ρ ↔ ∀ v : D.T, P v R (ρ v) := fun R _ _ _ ρ => by
    refine ⟨fun h ⟨v, hv⟩ => ?_, fun h => ⟨?_, fun p hp => ?_⟩⟩
    · obtain rfl | hv' := Finset.mem_insert.1 hv
      · show P v R _
        rw [hPl]
        exact h.1
      · show P v R _
        rw [hPp v hv']
        exact h.2 v hv'
    · have : P l R _ := h ⟨l, D.residueChar_mem_levelPrimes⟩
      rw [hPl] at this
      exact this
    · have : P p R _ := h ⟨p, D.mem_T hp⟩
      rw [hPp p hp] at this
      exact this
  obtain ⟨B, _, _, _, W, org, ρ, h1, h2, h3, h4, h5, h6⟩ := pk_sum fun v => (hK v).some
  refine ⟨{ B := B, W := W, wt_mem := h1, org := org, ρ := ρ, eqs := (hE B ρ).2 h2
            univ := fun R _ _ _ ρ' h => h3 R ρ' ((hE R ρ').1 h), hom := h4, at0 := h5, smooth := ?_ }⟩
  convert h6 using 2 with j
  rw [Finset.sum_coe_sort D.T fun v => n v j, Raw.T, Finset.sum_insert fun h => hne l h rfl, hnl,
    Finset.sum_congr rfl fun p hp => by rw [hnp p hp], Finset.sum_const, smul_eq_mul]
