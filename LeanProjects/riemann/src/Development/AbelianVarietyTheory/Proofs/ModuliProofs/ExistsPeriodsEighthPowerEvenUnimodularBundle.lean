import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransportThetaLevelUniformisationCoordinates
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLatticeUniformisationOfPrimTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EighthPowerIntegerMatrixPrimitiveAdjointStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.E8SharpClassPrimitiveIsoClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivPiRangeOfMatrixUnits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearLiftOfIsMonHomPolAV
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpPeriods

theorem zpow_finsum' {G I : Type*} [CommGroup G] (x : G) (s : Finset I) (f : I → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

section Mat
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj B]

theorem comp_finprod {T T' : Over S} (f : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ B)) :
    f ≫ (∏ v, x v) = ∏ v, f ≫ x v := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp [MonObj.comp_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem exists_matrix_action {n : ℕ} (pr : Fin n → (A ⟶ B)) (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ B)), ∃! x : T ⟶ A, ∀ u, x ≫ pr u = y u) :
    ∃ α : Matrix (Fin n) (Fin n) ℤ → (A ⟶ A), (∀ m u, α m ≫ pr u = ∏ v, pr v ^ m u v) ∧
      (∀ m, IsMonHom (α m)) ∧ α 1 = 𝟙 A ∧ (∀ m m', α (m * m') = α m' ≫ α m) ∧
      ∀ m m', α (m + m') = α m * α m' := by
  classical
  have hext : ∀ (T : Over S) (x x' : T ⟶ A), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' :=
    fun T x x' h => (hu T (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  choose α hα _ using fun m : Matrix (Fin n) (Fin n) ℤ => hu A (fun u => ∏ v, pr v ^ m u v)
  have hα' : ∀ m u (T : Over S) (x : T ⟶ A), x ≫ α m ≫ pr u = ∏ v, (x ≫ pr v) ^ m u v := by
    intro m u T x
    rw [hα, comp_finprod]
    simp only [GrpObj.comp_zpow]
  refine ⟨α, hα, fun m => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [Category.assoc, hα', MonObj.one_eq_one]
    simp [MonObj.one_comp]
  · refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [Category.assoc, hα', MonObj.mul_eq_mul]
    simp only [MonObj.comp_mul, MonObj.mul_comp, tensorHom_fst, tensorHom_snd, Category.assoc, hα', mul_zpow,
      Finset.prod_mul_distrib]
  · refine hext _ _ _ fun u => ?_
    rw [hα, Category.id_comp, Finset.prod_eq_single u]
    · simp
    · intro v _ hv
      simp [Matrix.one_apply_ne hv.symm]
    · simp
  · intro m m'
    refine hext _ _ _ fun u => ?_
    rw [Category.assoc, hα', hα]
    simp only [hα, ← Finset.prod_zpow, ← zpow_mul, Matrix.mul_apply]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [zpow_finsum']
    exact Finset.prod_congr rfl fun v _ => by rw [mul_comm]
  · intro m m'
    refine hext _ _ _ fun u => ?_
    haveI := hpr
    rw [MonObj.mul_comp, hα, hα, hα, ← Finset.prod_mul_distrib]
    simp only [Matrix.add_apply, zpow_add]
end Mat

theorem linear_eq_zero_of_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, F z ∈ Λ) : F = 0 := by
  refine LinearMap.ext fun z => ?_
  have hc : Continuous (fun t : ℂ => (⟨F (t • z), h _⟩ : Λ)) := by
    refine Continuous.subtype_mk ?_ _
    simp only [map_smul]
    fun_prop
  have := PreconnectedSpace.constant (inferInstance : PreconnectedSpace ℂ) hc (x := 1) (y := 0)
  simpa using congrArg Subtype.val this

section Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_eq_iff (z w : Fin g → ℂ) : u.ex z = u.ex w ↔ z - w ∈ u.Λ := by
  rw [← u.ker]
  have : u.ex z = u.ex (z - w) * u.ex w := by rw [← u.ex_add, sub_add_cancel]
  rw [this]
  exact mul_eq_right

theorem lift_unique {F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  haveI := u.discrete
  exact sub_eq_zero.1 (linear_eq_zero_of_mem u.Λ (F - F') fun z => (ex_eq_iff u _ _).1 (h z))

theorem exists_lattice_action {R La : Type} [Ring R] [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
    (hQ : Function.Injective Q) (hΛ : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range) (α : R → (A ⟶ A)) (hm : ∀ m, IsMonHom (α m))
    (h1 : α 1 = 𝟙 A) (hmul : ∀ m m', α (m * m') = α m' ≫ α m) (hadd : ∀ m m', α (m + m') = α m * α m')
    (F : R → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ m z, u.ex (F m z) = u.ex z ≫ α m) :
    ∃ r : R →+* Module.End ℤ La, ∀ m x, F m (Q x) = Q (r m x) := by
  have hmem : ∀ m x, F m (Q x) ∈ Q.range := by
    intro m x
    haveI := hm m
    rw [← hΛ, ← u.ker, hF, (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩), MonObj.one_comp]
  choose f hf using hmem
  have F1 : F 1 = LinearMap.id := lift_unique u fun z => by rw [hF, h1]; simp
  have Fmul : ∀ m m', F (m * m') = F m ∘ₗ F m' := fun m m' => lift_unique u fun z => by
    rw [hF, hmul, LinearMap.comp_apply, hF, hF, Category.assoc]
  have Fadd : ∀ m m', F (m + m') = F m + F m' := fun m m' => lift_unique u fun z => by
    rw [hF, hadd, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  let r₀ : R → Module.End ℤ La := fun m => (AddMonoidHom.mk' (f m) fun x y => hQ (by
    rw [map_add, hf, hf, hf, map_add, map_add])).toIntLinearMap
  have hr₀ : ∀ m x, Q (r₀ m x) = F m (Q x) := hf
  refine ⟨RingHom.mk' ⟨⟨r₀, ?_⟩, ?_⟩ ?_, fun m x => (hr₀ m x).symm⟩
  · ext x
    apply hQ
    rw [hr₀, F1]; rfl
  · intro m m'
    ext x
    apply hQ
    simp only [Module.End.mul_apply, hr₀, Fmul, LinearMap.comp_apply]
  · intro m m'
    ext x
    apply hQ
    change Q (r₀ (m + m') x) = Q (r₀ m x + r₀ m' x)
    simp only [map_add, hr₀, Fadd, LinearMap.add_apply]
end Unif

theorem exists_level_map {P P' I : Type} [Group P] [CommGroup P'] [Fintype I] {n k : ℕ} (u₀ : Fin n)
    (π : Fin n → (P →* P')) (hinj : ∀ x x', (∀ u, π u x = π u x') → x = x')
    (hsurj : ∀ y : Fin n → P', ∃ x, ∀ u, π u x = y u)
    (φ : (Fin n → (I → ℤ)) → P) (hφ : ∀ x y, φ (x + y) = φ x * φ y) (htor : ∀ p, p ^ k = 1 → ∃ x, φ x = p)
    (hψ : ∀ x u, π u (φ x) = π u₀ (φ (Pi.single u₀ (x u))))
    (lev : (I → ℤ) → P') (hadd : ∀ x y, lev (x + y) = lev x * lev y) (hlt : ∀ x, lev x ^ k = 1) :
    ∃ m : (I → ℤ) →+ (I → ℤ), ∀ (x : Fin n → (I → ℤ)) u, π u (φ fun v => m (x v)) = lev (x u) := by
  classical
  let ψ : (I → ℤ) →+ Additive P' := AddMonoidHom.mk' (fun y => Additive.ofMul (π u₀ (φ (Pi.single u₀ y))))
    fun x y => by rw [Pi.single_add, hφ, map_mul, ofMul_mul]
  let lv : (I → ℤ) →+ Additive P' := AddMonoidHom.mk' (fun y => Additive.ofMul (lev y))
    fun x y => by rw [hadd, ofMul_mul]
  have hex : ∀ y, ∃ z, ψ z = lv y := by
    intro y
    obtain ⟨p, hp⟩ := hsurj fun _ => lev y
    obtain ⟨z, rfl⟩ := htor p (hinj _ _ fun u => by rw [map_pow, hp, hlt, map_one])
    refine ⟨z u₀, ?_⟩
    change Additive.ofMul _ = Additive.ofMul _
    rw [← hψ, hp]
  choose z hz using hex
  let m : (I → ℤ) →ₗ[ℤ] (I → ℤ) := (Pi.basisFun ℤ I).constr ℤ fun s => z (Pi.basisFun ℤ I s)
  have hm : ψ.toIntLinearMap ∘ₗ m = lv.toIntLinearMap := (Pi.basisFun ℤ I).ext fun s => by
    rw [LinearMap.comp_apply, Module.Basis.constr_basis]
    exact hz _
  refine ⟨m.toAddMonoidHom, fun x u => ?_⟩
  rw [hψ]
  exact Additive.ofMul.injective (LinearMap.congr_fun hm (x u))

theorem zpow_bilin_ext {G X I : Type} [CommGroup G] [AddCommGroup X] (b : Module.Basis I ℤ X) (ξ ζ : G)
    (B B' : LinearMap.BilinForm ℤ X) (h : ∀ i j, ξ ^ B (b i) (b j) = ζ ^ B' (b i) (b j)) (x y : X) :
    ξ ^ B x y = ζ ^ B' x y := by
  have : B.compr₂ (LinearMap.toSpanSingleton ℤ (Additive G) (Additive.ofMul ξ)) =
      B'.compr₂ (LinearMap.toSpanSingleton ℤ (Additive G) (Additive.ofMul ζ)) :=
    LinearMap.ext_basis b b fun i j => congrArg Additive.ofMul (h i j)
  exact Additive.ofMul.injective (LinearMap.congr_fun₂ this x y)

theorem omegaStd_zero_left {h : ℕ} (y : Fin h ⊕ Fin h → ℤ) : omegaStd 0 y = 0 := by simp [omegaStd]

theorem omegaStd_smul_right {h : ℕ} (c : ℤ) (x y : Fin h ⊕ Fin h → ℤ) : omegaStd x (c • y) = c * omegaStd x y := by
  simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem multiplier_of_power {G₀ : Type} [CommGroup G₀] {h g k : ℕ} (G : Matrix (Fin 8) (Fin 8) ℤ) (hG : G.det = 1)
    (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ)))
    (hEF : ∀ x y, EF x y = ∑ u, ∑ v, G u v * omegaStd (x u) (y v))
    (bas : (Fin g → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ))
    (ξ ζ : G₀) (hξ : ξ ^ k = 1) (lam : Fin g → (Fin 8 → (Fin h ⊕ Fin h → ℤ)))
    (hlam : ∀ i, ∃ y, lam i = (fun u => m (bas (Pi.single i 1) u)) + k • y)
    (hlev : ∀ i j, ξ ^ EF (lam i) (lam j) = ζ ^ EF (bas (Pi.single i 1)) (bas (Pi.single j 1))) (x y) :
    ξ ^ omegaStd (m x) (m y) = ζ ^ omegaStd x y := by
  classical
  let M : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) := m.toIntLinearMap.compLeft (Fin 8)
  have hk : ∀ c : ℤ, ξ ^ (k • c) = 1 := fun c => by rw [nsmul_eq_mul, zpow_mul, zpow_natCast, hξ, one_zpow]
  have key := zpow_bilin_ext ((Pi.basisFun ℤ (Fin g)).map bas) ξ ζ (EF.compl₁₂ M M) EF (fun i j => by
    obtain ⟨y, hy⟩ := hlam i
    obtain ⟨y', hy'⟩ := hlam j
    simp only [Module.Basis.map_apply, Pi.basisFun_apply, LinearMap.compl₁₂_apply]
    rw [← hlev, hy, hy']
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, zpow_add, hk, _root_.mul_one]
    rfl)
  have hc : ∑ v, G 0 v * G.adjugate v 0 = 1 := by
    have := congrFun (congrFun (Matrix.mul_adjugate G) 0) 0
    simpa [Matrix.mul_apply, hG] using this
  have hE : ∀ x y, EF (Pi.single 0 x) (fun v => G.adjugate v 0 • y) = omegaStd x y := by
    intro x y
    rw [hEF, Finset.sum_eq_single 0]
    · simp only [Pi.single_eq_same, omegaStd_smul_right, ← _root_.mul_assoc, ← Finset.sum_mul, hc, _root_.one_mul]
    · intro u _ hu
      simp [Pi.single_eq_of_ne hu, omegaStd_zero_left]
    · simp
  have := key (Pi.single 0 x) (fun v => G.adjugate v 0 • y)
  rw [hE, LinearMap.compl₁₂_apply] at this
  rw [← this, ← hE]
  congr 2
  · congr 1
    funext u
    by_cases hu : u = 0
    · subst hu; simp [M]
    · simp [M, Pi.single_eq_of_ne hu]
  · funext u
    exact (map_zsmul m _ _).symm

end GlobalTheory.SharpPeriods

open GlobalTheory.SharpPeriods in

theorem GlobalTheory.exists_periods_of_sharpClass : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (σ : Fin 8 × Fin h ≃ Fin g) (EF : LinearMap.BilinForm ℤ (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ x y, EF x y = ∑ u, ∑ v, (W + W.transpose) u v * omegaStd (x u) (y v)) → ∀ t : TObj g k J b (spMap em), SharpClass W a bas em t → ∃ (τ : Matrix (Fin h) (Fin h) ℂ) (m : (Fin h ⊕ Fin h → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (Q : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), ((τ).IsSymm ∧ ((τ).map Complex.im).PosDef) ∧ (∀ x y, Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd (m x) (m y) : ℂ) / k) = em (b.ζ : o) ^ omegaStd x y) ∧ (∀ x u i, Q x (σ (u, i)) = (τ).mulVec (fun i' => (x u (.inl i') : ℂ)) i + (x u (.inr i) : ℂ)) ∧ (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q ((fun i u => m (bas (Pi.single i 1) u)) i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q ((fun j (x : (Fin 8 → (Fin h ⊕ Fin h → ℤ))) u => ∑ v, a j u v • x v) j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro hL hL2 hth hU o _ g k J b em w w' h W a bas σ EF hE8 hbas hw hw' hEF t ht
  classical
  have hprim := (GlobalTheory.sharpClass_prim_and_iso hth o g k J b em w w' h W a bas t ht).1 hE8 hw hw'
  obtain ⟨La, _, EF0, lam, ac, Q0, Hm0, hbij, hpol, hlev, u, χ, hAH, hΛ, hχ, hpt, hact⟩ :=
    GlobalTheory.PrimUnif.exists_unif_of_prim hL hL2 hth hU o g k J b em w w' t hprim
  obtain ⟨c, -, pr, hpr, huniv, hLB, hactpr, hptpr⟩ := ht
  have hext : ∀ (T : Over (Sp ℂ)) (x x' : T ⟶ t.A), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' :=
    fun T x x' h => (huniv T (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  obtain ⟨α, hα, hαm, hα1, hαmul, hαadd⟩ := exists_matrix_action pr hpr huniv
  have hα' : ∀ m u, α m ≫ pr u = (List.ofFn fun v => pr v ^ m u v).prod := fun m u => by
    rw [hα, List.prod_ofFn]
  have hF : ∀ m, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F z) = u.ex z ≫ α m := fun m =>
    GlobalTheory.exists_linear_lift_of_isMonHom_polAV t.pol t.pol t.L t.L u u (α m) (hαm m)
  choose F hF using hF
  obtain ⟨r, hr⟩ := exists_lattice_action u Q0 hpol.1 hΛ α hαm hα1 hαmul hαadd F hF
  have hadj : ∀ m m', m.transpose * (W + W.transpose) = (W + W.transpose) * m' →
      ∀ x y, EF0 (r m x) y = EF0 x (r m' y) := by
    intro m m' hmm' x y
    have h1 := (GlobalTheory.T.eighthPower_integerMatrix_primitive_adjoint hth W ℂ o (spMap em) h k _ c t.pol pr hpr huniv hLB m (α m) (hα' m)).2 m' (α m')
      (hα' m') hmm'
    have h2 : hermForm Hm0 (F m (Q0 x)) (Q0 y) = hermForm Hm0 (Q0 x) (F m' (Q0 y)) :=
      (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint hL hL2 hth hU t.pol u Hm0 χ (α m) (α m') (F m) (F m') hAH (hαm m) (hαm m') (hF m) (hF m')).1
        h1 (Q0 x) (Q0 y)
    rw [hr, hr] at h2
    have h3 := congrArg Complex.im h2
    rw [hpol.2.2.2.2.2, hpol.2.2.2.2.2] at h3
    exact_mod_cast h3
  have hsymm : (W + W.transpose).IsSymm := Matrix.isSymm_add_transpose_self W
  obtain ⟨τ, e, hh, hτ1, hτ2, hQe, hEe, hre⟩ := GlobalTheory.polarised_lattice_eighth_power h g (W + W.transpose) σ La EF0 Q0 Hm0 r hsymm hE8.1 hE8.2
    hbij hpol (fun m => ⟨F m, hr m⟩) hadj
  obtain ⟨Q, Hm, hQ, hpol'⟩ := (GlobalTheory.TensorSiegel.tensor_siegel_lattices h g (W + W.transpose) σ EF hsymm hE8.1 hE8.2 hEF).2.1 τ ⟨hτ1, hτ2⟩
  have hk0 : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hmul : ∀ z : Fin g → ℂ, k • ((k : ℂ)⁻¹ • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk0, one_smul]
  have hmul' : ∀ z : Fin g → ℂ, (k : ℂ)⁻¹ • (k • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hk0, one_smul]
  let φ : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) → (𝟙_ (Over (Sp ℂ)) ⟶ t.A) := fun x => u.ex ((k : ℂ)⁻¹ • Q0 (e.symm x))
  let π : Fin 8 → ((𝟙_ (Over (Sp ℂ)) ⟶ t.A) →* (𝟙_ (Over (Sp ℂ)) ⟶ c.A)) := fun v =>
    MonoidHom.mk' (fun x => x ≫ pr v) fun x y => haveI := hpr v; MonObj.mul_comp _ _ _
  have hψ : ∀ x v, π v (φ x) = π 0 (φ (Pi.single 0 (x v))) := by
    intro x v
    have h1 : α (Matrix.single 0 v 1) ≫ pr 0 = pr v := by
      rw [hα, Finset.prod_eq_single v]
      · simp
      · intro v' _ hv'
        simp [Matrix.single_apply, hv'.symm]
      · simp
    have h2 : e.symm (Pi.single 0 (x v)) = r (Matrix.single 0 v 1) (e.symm x) := by
      rw [AddEquiv.symm_apply_eq]
      funext u'
      rw [hre, AddEquiv.apply_symm_apply, Finset.sum_eq_single v]
      · by_cases hu : u' = 0
        · subst hu; simp
        · simp [Pi.single_eq_of_ne hu, Matrix.single_apply, Ne.symm hu]
      · intro v' _ hv'
        simp [Matrix.single_apply, hv'.symm]
      · simp
    change u.ex _ ≫ pr v = u.ex _ ≫ pr 0
    rw [h2, ← hr, ← LinearMap.map_smul, hF, Category.assoc, h1]
  obtain ⟨m, hm⟩ := exists_level_map (k := k) 0 π (hext _) (fun y => (huniv _ y).exists) φ
    (fun x y => by simp only [φ, map_add, smul_add, u.ex_add])
    (fun p hp => by
      obtain ⟨z, rfl⟩ := u.ex_onto p
      obtain ⟨x, hx⟩ := (hΛ _).1 ((u.ker _).1 ((holUnif_ex_nsmul_eq_pow u z k).trans hp))
      exact ⟨e x, by simp only [φ, AddEquiv.symm_apply_apply, hx, hmul']⟩)
    hψ c.lev c.lev_add c.lev_tors
  have hlam : ∀ i, ∃ y, e (lam i) = (fun u => m (bas (Pi.single i 1) u)) + k • y := by
    intro i
    have h1 : u.ex ((k : ℂ)⁻¹ • Q0 (lam i)) = φ fun u => m (bas (Pi.single i 1) u) := by
      refine hext _ _ _ fun v => ?_
      refine Eq.trans ?_ (hm (bas (Pi.single i 1)) v).symm
      apply Over.OverMorphism.ext
      rw [← hptpr, Over.comp_left, Over.comp_left, hpt]
    obtain ⟨y, hy⟩ := (hΛ _).1 ((ex_eq_iff u _ _).1 h1)
    refine ⟨e y, ?_⟩
    rw [← e.apply_symm_apply (fun u => m (bas (Pi.single i 1) u)), ← map_nsmul, ← map_add]
    congr 1
    apply hpol.1
    rw [map_add, map_nsmul, hy, ← smul_sub, hmul, add_sub_cancel]
  have hEe' : ∀ x y, EF (e x) (e y) = EF0 x y := fun x y => by rw [hEF, hEe]
  refine ⟨τ, m, Q, Hm, ⟨hτ1, hτ2⟩, ?_, hQ, hpol', ?_⟩
  · let ξ : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / k)) (Complex.exp_ne_zero _)
    have hξ : ∀ n : ℤ, ((ξ ^ n : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k) := fun n => by
      rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← Complex.exp_int_mul]
      congr 1
      ring
    have hζ : ∀ n : ℤ, ((Units.map em.toMonoidHom b.ζ ^ n : ℂˣ) : ℂ) = em (b.ζ : o) ^ n := fun n => by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    have hξk : ξ ^ k = 1 := by
      apply Units.ext
      rw [← zpow_natCast, hξ, Int.cast_natCast, mul_div_cancel_right₀ _ hk0, Complex.exp_neg,
        Complex.exp_two_pi_mul_I]
      simp
    intro x y
    rw [← hξ, ← hζ]
    congr 1
    refine multiplier_of_power (W + W.transpose) hE8.2 EF hEF bas m ξ _ hξk (fun i => e (lam i)) hlam ?_ x y
    intro i j
    apply Units.ext
    rw [hξ, hζ, hEe', hlev, hEF, hbas]
  · refine GlobalTheory.UnifTransport.transport_uniformisation o g k J b em w w' t La EF0 lam ac Q0 Hm0 _ EF (fun i u => m (bas (Pi.single i 1) u))
      (fun j x u => ∑ v, a j u v • x v) Q Hm e hh hpol hpol' ?_ hEe' ?_ hlam
      ⟨u, χ, hAH, hΛ, hχ, hpt, hact⟩
    · intro x
      funext s
      obtain ⟨⟨v, i⟩, rfl⟩ := σ.surjective s
      rw [hQ, hQe]
    · intro j x
      obtain ⟨F', hF'1, hF'2⟩ := hact j
      have h1 : t.act j = α (a j) := hext _ _ _ fun v => by rw [hactpr, hα']
      have h2 : F' = F (a j) := lift_unique u fun z => by rw [hF'2, hF, h1]
      have h3 : ac j x = r (a j) x := hpol.1 (by rw [← hF'1, h2, hr])
      funext v
      rw [h3, hre]
