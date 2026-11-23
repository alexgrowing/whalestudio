import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharpolyBcMapIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfIsogenyIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodComparisonHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparatesOnSmoothOfPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.DeRhamCharpolyZero

open GlobalTheory.AV

theorem charpoly_of_bijective {R K M V : Type*} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (E : K ⊗[R] M →ₗ[K] V) (hE : Function.Bijective E) (φ : Module.End R M) (T : Module.End K V)
    (h : ∀ m, T (E (1 ⊗ₜ m)) = E (1 ⊗ₜ φ m)) : T.charpoly = φ.charpoly.map (algebraMap R K) := by
  let e := LinearEquiv.ofBijective E hE
  have hT : T = e.conj (φ.baseChange K) := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨z, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply_apply, e.symm_apply_apply]
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x m =>
      have : x ⊗ₜ[R] m = x • ((1 : K) ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
      rw [this, map_smul, map_smul, map_smul, map_smul]
      exact congrArg (x • ·) (h m)
  rw [hT, LinearEquiv.charpoly_conj, LinearMap.charpoly_baseChange]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

theorem finite_prim {K : Type} [Field K] (B : AbVar K) : Module.Finite K (primDR B.X) :=
  (GlobalTheory.abelianDeRham.1.prim B.ab B.smooth).1

theorem finite_HdR {K : Type} [Field K] (B : AbVar K) : Module.Finite K (HdR B.X) :=
  haveI := finite_prim B
  inferInstance

theorem charpoly_push_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) [Module.Finite K (HdR B₀.X)] [Module.Finite L (HdR B.X)] :
    LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) =
      (LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom)).map (algebraMap K L) := by
  haveI := finite_prim B₀
  haveI := finite_prim B
  have m := GlobalTheory.Published.AbelianDeRham.bcMor h
  have hm : m.IsBC := (GlobalTheory.abelianDeRham.2.2.1 K B₀.X B₀.dim B₀.ab B₀.smooth L B.X φ h).1
  have h1 : LinearMap.charpoly (push (dp0 L) (𝟙 _) f.hom) = (primPull (dp0 L) (𝟙 _) f.hom).charpoly :=
    charpoly_dualMap _
  have h2 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) = (primPull (dp0 K) (𝟙 _) f₀.hom).charpoly :=
    charpoly_dualMap _
  rw [h1, h2]
  refine charpoly_of_bijective (liftSemi m.pull) hm _ _ fun c => ?_
  rw [liftSemi_tmul, liftSemi_tmul, one_smul, one_smul]
  have k := (homMor (dp0 K) (𝟙 _) f₀.hom).comp m
  exact (GrpMor.pull_pull m (homMor (dp0 L) (𝟙 _) f.hom) k (fun _ ↦ rfl) e.symm c).trans
    (GrpMor.pull_pull (homMor (dp0 K) (𝟙 _) f₀.hom) m k (fun _ ↦ rfl) rfl c).symm

theorem exists_isGrpPullback_baseChange {K : Type} (L : Type) [Field K] [Field L] [Algebra K L] {B₀ : AbVar K}
    (f₀ : B₀ ⟶ B₀) : ∃ q : (AbVar.baseChange L B₀).X.left ⟶ B₀.X.left,
      IsGrpPullback (AbVar.baseChange L B₀).X B₀.X (spMap (algebraMap K L)) q ∧
      q ≫ f₀.hom.left = (AbVar.bcMap L f₀).hom.left ≫ q :=
  ⟨pullback.fst B₀.X.hom (spMap (algebraMap K L)), isGrpPullback_pullback B₀.X _, (pullback.lift_fst _ _ _).symm⟩

theorem charpoly_of_pullback {K L : Type} [Field K] [Field L] [Algebra K L] (B₀ : AbVar K) (B : AbVar L)
    {φ : B.X.left ⟶ B₀.X.left} (h : IsGrpPullback B.X B₀.X (spMap (algebraMap K L)) φ) (f₀ : B₀ ⟶ B₀) (f : B ⟶ B)
    (e : φ ≫ f₀.hom.left = f.hom.left ≫ φ) : AbVar.charpoly f = AbVar.charpoly f₀ := by
  obtain ⟨q, h', hq⟩ := exists_isGrpPullback_baseChange L f₀
  obtain ⟨i, hi, hφ⟩ := grpPullback_iso h h'
  let u : B ⟶ AbVar.baseChange L B₀ := AbVar.Hom.mk i.hom
  have hu : AbVar.IsIsogeny u := by
    have : IsIso i.hom.left := ⟨⟨i.inv.left, by rw [← Over.comp_left, i.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, i.inv_hom_id, Over.id_left]⟩⟩
    exact ⟨inferInstanceAs (IsFinite i.hom.left), inferInstanceAs (Surjective i.hom.left)⟩
  rw [← AbVar.charpoly_bcMap K L B₀ f₀]
  refine AbVar.charpoly_eq_of_isogeny_intertwines L B _ u f _ hu (AbVar.hom_ext ?_)
  change f.hom ≫ i.hom = i.hom ≫ (AbVar.bcMap L f₀).hom
  apply Over.OverMorphism.ext
  apply h'.1.hom_ext
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hφ, ← e, ← hq, ← Category.assoc, hφ]
  · rw [Over.w, Over.w]

theorem charpoly_push_complex (B : AbVar ℂ) (f : B ⟶ B) [Module.Finite ℂ (HdR B.X)] :
    LinearMap.charpoly (push (dp0 ℂ) (𝟙 _) f.hom) = (AbVar.charpoly f).map (Int.castRingHom ℂ) := by
  obtain ⟨L, hL, ⟨u⟩⟩ : ∃ L : LB B.X.left, L.IsLB ∧ Nonempty (HolUnif B.X L B.dim) := by
    have := B.ab.proper
    obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ B.X B.ab
    have hamp : Out.RelAmple B.X H :=
      (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B.X hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
    exact ⟨_, Out.Inh.trivLB_isLB _, GlobalTheory.RealMultChart.exists_holUnif_of_compact B.X B.dim B.smooth
      (GlobalTheory.RealMultChart.compactSpace_points B.X H hamp)
      (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq B.X B.ab a n hn)⟩
  have ht := GlobalTheory.TorusTransfer.tangent_bijective u B.smooth
  obtain ⟨M, hM, hΛ, -, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom B.X B.X B.ab B.ab L L B.dim B.dim u u
    ht.1 ht.2 f.hom inferInstance
  obtain ⟨ε, hP⟩ := GlobalTheory.PeriodFamily.periodComparison_holds
  obtain ⟨P, hsp, hrk, -, hnat, -⟩ := hP B.X B.dim B.ab B.smooth L hL u
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hr : Module.finrank ℤ u.Λ = 2 * B.dim := by
    rw [ZLattice.rank ℝ u.Λ, Module.finrank_pi_fintype]
    simp [mul_comm]
  let φ : u.Λ →ₗ[ℤ] u.Λ := (M.restrictScalars ℤ).restrict hΛ
  let E : ℂ ⊗[ℤ] u.Λ →ₗ[ℂ] HdR B.X := P.toIntLinearMap.liftBaseChange ℂ
  have hE1 : ∀ x, E (1 ⊗ₜ x) = P x := fun x => one_smul ℂ (P x)
  have hs : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hE1 x⟩
  have hE : Function.Bijective E :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_baseChange, hr, hrk])).2 hs, hs⟩
  have h1 := charpoly_of_bijective E hE φ (push (dp0 ℂ) (𝟙 _) f.hom) fun x => by
    rw [hE1, hE1]
    exact hnat f.hom M hM x (φ x) rfl
  have hpow : ∀ (n : ℕ) (z : Fin B.dim → ℂ), u.ex (n • z) = u.ex z ^ n := fun n z => by
    induction n with
    | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
    | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]
  have hc : ∀ (j : ℕ) (z : Fin B.dim → ℂ), (2 ^ j : ℕ) • (((2 : ℂ) ^ j)⁻¹ • z) = z := fun j z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    simp
  have hc' : ∀ (j : ℕ) (z : Fin B.dim → ℂ), ((2 : ℂ) ^ j)⁻¹ • ((2 ^ j : ℕ) • z) = z := fun j z => by
    rw [smul_comm, hc]
  have h2 := AbVar.charpoly_eq_lattice_model ℂ B f u.Λ φ 2 Nat.prime_two (by norm_num)
    (fun j x => u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)))
    (fun j x y => by
      simp only [Submodule.coe_add, smul_add]
      exact u.ex_add _ _)
    (fun j x => by
      refine Eq.trans ?_ (hM _)
      rw [map_smul]
      rfl)
    (fun j x => by
      refine (u.ker _).trans ⟨fun h => ⟨⟨_, h⟩, Subtype.ext (hc j x).symm⟩, ?_⟩
      rintro ⟨y, rfl⟩
      rw [show ((2 ^ j • y : u.Λ) : Fin B.dim → ℂ) = (2 ^ j : ℕ) • (y : Fin B.dim → ℂ) from rfl, hc']
      exact y.2)
    (fun j q => by
      obtain ⟨z, rfl⟩ := u.ex_onto q
      constructor
      · intro h
        exact ⟨⟨_, (u.ker _).1 ((hpow _ z).trans h)⟩, congrArg u.ex (hc' j z)⟩
      · rintro ⟨x, hx⟩
        have hx' : u.ex (((2 : ℂ) ^ j)⁻¹ • (x : Fin B.dim → ℂ)) = u.ex z := hx
        change u.ex z ^ (2 ^ j) = 1
        rw [← hx', ← hpow, hc]
        exact (u.ker _).2 x.2)
  rw [h1, h2]
  rfl

theorem exists_countable_model (k : Type) [Field k] [CharZero k] [IsAlgClosed k] (B : AbVar k) (f : B ⟶ B) :
    ∃ (K : Type) (_ : Field K) (_ : Countable K) (_ : Algebra K k) (B₀ : AbVar K) (f₀ : B₀ ⟶ B₀)
      (φ : B.X.left ⟶ B₀.X.left), IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ ∧
      φ ≫ f₀.hom.left = f.hom.left ≫ φ := by
  obtain ⟨S, A, _, ψ, -, hS, hA, hg, hψ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring k B.dim B.X ∅ B.ab B.smooth
  have hSc : Countable S := by
    obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hS
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      refine (MvPolynomial.cardinalMk_le_max).trans ?_
      simp
    exact hp.countable
  let F : Subfield k := Subfield.closure (S : Set k)
  have hF : Cardinal.mk F ≤ Cardinal.aleph0 :=
    (Subfield.cardinalMk_closure_le_max _).trans (max_le (Cardinal.mk_le_aleph0_iff.2 hSc) le_rfl)
  let K : IntermediateField F k := algebraicClosure F k
  haveI : IsAlgClosed K := (algebraicClosure.isAlgClosure F k).isAlgClosed
  have hK : Countable K := Cardinal.mk_le_aleph0_iff.1
    ((Algebra.IsAlgebraic.cardinalMk_le_max F K).trans (max_le hF le_rfl))
  let j : S →+* K := S.subtype.codRestrict K fun x => K.algebraMap_mem (⟨x, Subfield.subset_closure x.2⟩ : F)
  have e : spMap (algebraMap K k) ≫ spMap j = spMap S.subtype := by
    rw [← Cris.spMap_comp]
    rfl
  let B₀ : AbVar K :=
    { X := (Over.pullback (spMap j)).obj A
      ab := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
      dim := B.dim
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange (n := B.dim)).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap j)) hg }
  obtain ⟨φ, hφ⟩ : ∃ φ : B.X.left ⟶ B₀.X.left, IsGrpPullback B.X B₀.X (spMap (algebraMap K k)) φ :=
    ⟨_, Chart.isGrpPullback_factor (spMap j) (spMap (algebraMap K k)) (hψ.congr e.symm rfl)⟩
  obtain ⟨f₀, hf₀, he⟩ := GlobalTheory.AlgClosedHomDescent.hom_descends K k (algebraMap K k) B₀.X B₀.X B.X B.X φ φ
    B₀.ab B₀.ab hφ hφ f.hom inferInstance
  exact ⟨K, inferInstance, hK, inferInstance, B₀, AbVar.Hom.mk f₀, φ, hφ, he⟩

theorem charpoly_push : ∀ (k : Type) [Field k] [CharZero k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom k) := by
  intro k _ _ _ B f _
  obtain ⟨K, _, _, _, B₀, f₀, φ, hφ, he⟩ := exists_countable_model k B f
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap K k).injective).2 inferInstance
  obtain ⟨σ⟩ := GlobalTheory.KeyRuleUnique.nonempty_ringHom_complex K
  letI : Algebra K ℂ := σ.toAlgebra
  haveI := finite_HdR B₀
  haveI := finite_HdR (AbVar.baseChange ℂ B₀)
  obtain ⟨q, hq, hq'⟩ := exists_isGrpPullback_baseChange ℂ f₀
  have h3 := charpoly_push_of_pullback B₀ _ hq f₀ _ hq'
  have h4 := charpoly_push_complex (AbVar.baseChange ℂ B₀) (AbVar.bcMap ℂ f₀)
  rw [AbVar.charpoly_bcMap] at h4
  have h5 : LinearMap.charpoly (push (dp0 K) (𝟙 _) f₀.hom) = (AbVar.charpoly f₀).map (Int.castRingHom K) := by
    apply Polynomial.map_injective (algebraMap K ℂ) σ.injective
    rw [← h3, h4, Polynomial.map_map]
    exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)
  rw [charpoly_push_of_pullback B₀ B hφ f₀ f he, h5, charpoly_of_pullback B₀ B hφ f₀ f he, Polynomial.map_map]
  exact congrArg (Polynomial.map · _) (RingHom.ext_int _ _)

end GlobalTheory.DeRhamCharpolyZero
