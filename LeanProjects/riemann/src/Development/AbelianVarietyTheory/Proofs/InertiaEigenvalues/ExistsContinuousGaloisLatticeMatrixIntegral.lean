import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar

noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_form_extending_coord {R F T V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup T] [Module R T] [AddCommGroup V] [Module R V]
    [Module F V] [IsScalarTower R F V] (b : Module.Basis ι R T) (f : T →ₗ[R] V)
    (hf : Function.Injective f) (i : ι) :
    ∃ φ : V →ₗ[F] F, ∀ x, φ (f x) = algebraMap R F (b.repr x i) := by
  classical
  set v : ι → V := fun j => f (b j) with hv
  have hR : LinearIndependent R v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hF : LinearIndependent F v := (LinearIndependent.iff_fractionRing R F).mp hR
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hF).coord i)
  refine ⟨g, fun x => ?_⟩
  have hx : f x = ∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • v j := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, algebraMap_smul]
  have hy : f x = ((∑ j ∈ (b.repr x).support,
      algebraMap R F (b.repr x j) • Module.Basis.span hF j : Submodule.span F (Set.range v)) : V) := by
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
  have h2 := LinearMap.congr_fun hg
    (∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • Module.Basis.span hF j)
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
  rw [hy, h2, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem continuous_form_of_moduleTopology {F L V : Type} [NontriviallyNormedField F]
    [CompleteSpace F] [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L] [AddCommGroup V] [Module L V]
    [Module F V] [IsScalarTower F L V] [TopologicalSpace V] [IsModuleTopology L V]
    [FiniteDimensional L V] (φ : V →ₗ[F] F) : Continuous φ := by
  let e := (Module.finBasis L V).equivFun
  have he : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let ψ : (Fin (Module.finrank L V) → L) →ₗ[F] F := φ ∘ₗ (e.symm.toLinearMap.restrictScalars F)
  have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
  have h : (φ : V → F) = ψ ∘ e.toLinearMap := by
    funext v
    simp [ψ]
  rw [h]
  exact hψ.comp he

variable {l : ℕ} [Fact l.Prime]

def zCHom (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* PadicComplex l :=
  (algebraMap ℚ_[l] (PadicComplex l)).comp (algebraMap ℤ_[l] ℚ_[l])

theorem zCHom_apply (x : ℤ_[l]) : zCHom l x = zC x := rfl

section Generic

variable {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R] [Field F] [Field L]
  [Algebra F L] [CommRing O] [Algebra O L] [TopologicalSpace L] [Algebra R O]

def mulLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (a : O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := fun x => ⟨_, T.L.T.smul_mem a x.2⟩
    map_add' := fun x y => smul_add a x y
    map_smul' := fun c x => smul_comm a (algebraMap R O c) x }

theorem mulLat_apply (T : LocLat G F L O) (a : O) (x : ↥T.L.T) :
    mulLat R T a x = ⟨_, T.L.T.smul_mem a x.2⟩ := rfl

theorem coe_actT (T : LocLat G F L O) (g : G) (x : ↥T.L.T) :
    (actT T.L g x).1 = T.ρ g x.1 := rfl

theorem actT_mulLat (T : LocLat G F L O) (g : G) (a : O) (x : ↥T.L.T) :
    actT T.L g (mulLat R T a x) = mulLat R T a (actT T.L g x) := by
  rw [mulLat_apply, mulLat_apply]
  exact (actT T.L g).map_smul a x

theorem exists_basis_lat [Nontrivial R] [Module.Free R O] [Module.Finite R O]
    (T : LocLat G F L O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) R ↥T.L.T) := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  have : IsScalarTower R O ↥T.L.T := ⟨fun r o x => by
    show (r • o) • x = algebraMap R O r • (o • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have : Module.Free R ↥T.L.T :=
    Module.Free.of_basis ((Module.Free.chooseBasis R O).smulTower (Module.Free.chooseBasis O ↥T.L.T))
  have : Module.Finite R ↥T.L.T := Module.Finite.trans O ↥T.L.T
  exact ⟨_, ⟨Module.finBasis R ↥T.L.T⟩⟩

theorem exists_form_lat [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (i : ι),
      ∃ φ : T.V →ₗ[F] F, ∀ x : ↥T.L.T, φ x.1 = algebraMap R F (b.repr x i) := by
  intro b i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  let _ : Module R T.V := Module.compHom T.V (algebraMap R F)
  have : IsScalarTower R F T.V := ⟨fun r c v => by
    show (r • c) • v = algebraMap R F r • (c • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let f : ↥T.L.T →ₗ[R] T.V :=
    { toFun := fun x => x.1
      map_add' := fun x y => rfl
      map_smul' := fun r x => by
        show algebraMap R O r • x.1 = algebraMap R F r • x.1
        rw [← algebraMap_smul L (algebraMap R O r) x.1, hc, algebraMap_smul] }
  exact exists_form_extending_coord b f Subtype.val_injective i

def actLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (g : G) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := actT T.L g
    map_add' := map_add _
    map_smul' := fun c x => (actT T.L g).map_smul (algebraMap R O c) x }

theorem matrices_lat {C : Type} [CommRing C] (z : R →+* C) (T : LocLat G F L O) {d : ℕ}
    (M : G → Matrix (Fin d) (Fin d) C) (A : O → Matrix (Fin d) (Fin d) C) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b : Module.Basis (Fin d) R ↥T.L.T,
      (∀ g i j, M g i j = z (b.repr (actT T.L g (b j)) i)) →
      (∀ a i j, A a i j = z (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)) →
      (∀ g h, M (g * h) = M g * M h) ∧ M 1 = 1 ∧ ∀ g a, M g * A a = A a * M g := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b hM hA
  have kM : ∀ g, M g = (LinearMap.toMatrix b b (actLat R T g)).map z := by
    intro g; ext i j; rw [hM, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have kA : ∀ a, A a = (LinearMap.toMatrix b b (mulLat R T a)).map z := by
    intro a; ext i j; rw [hA, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have hmul : ∀ g h, actLat R T (g * h) = actLat R T g * actLat R T h := by
    intro g h
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ (g * h) x.1 = T.ρ g (T.ρ h x.1)
    rw [map_mul]; rfl
  have hone : actLat R T 1 = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ 1 x.1 = x.1
    rw [map_one]; rfl
  have hcomm : ∀ g a, actLat R T g * mulLat R T a = mulLat R T a * actLat R T g :=
    fun g a => LinearMap.ext fun x => actT_mulLat (R := R) T g a x
  refine ⟨fun g h => ?_, ?_, fun g a => ?_⟩
  · rw [kM, kM, kM, hmul, LinearMap.toMatrix_mul, Matrix.map_mul]
  · rw [kM, hone, LinearMap.toMatrix_one]
    exact Matrix.map_one _ z.map_zero z.map_one
  · rw [kM, kA, ← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_mul, hcomm]

end Generic

theorem continuous_coord_lat {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R]
    [NontriviallyNormedField F] [CompleteSpace F] [Field L] [Algebra F L] [CommRing O]
    [Algebra O L] [TopologicalSpace L] [Algebra R O] [FiniteDimensional F L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L]
    [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (x : ↥T.L.T) (i : ι),
      Continuous fun g : G => algebraMap R F (b.repr (actT T.L g x) i) := by
  intro b x i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  obtain ⟨φ, hφ⟩ := exists_form_lat (R := R) hc T b i
  have hφc : Continuous φ := continuous_form_of_moduleTopology (L := L) φ
  have h : (fun g : G => algebraMap R F (b.repr (actT T.L g x) i)) = fun g => φ (T.ρ g x.1) := by
    funext g
    rw [← hφ, coe_actT]
  rw [h]
  exact hφc.comp (T.cont x.1)

theorem exists_basis_lattice {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥T.L.T) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] _
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  exact exists_basis_lat (R := ℤ_[l]) T

theorem isMat_exists_and_props : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  intro l _ K LL T
  classical
  let _ : Module ℤ_[l] ↥T.L.T := zlMod LL T
  have hc : ∀ c : ℤ_[l], algebraMap (↥(OL LL)) (↥LL.1) (algebraMap ℤ_[l] (↥(OL LL)) c) =
      algebraMap ℚ_[l] (↥LL.1) (algebraMap ℤ_[l] ℚ_[l] c) := fun c => rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨d, ⟨b⟩⟩ := exists_basis_lattice (G := ↥(GK K)) LL T
    refine ⟨d, fun σ => Matrix.of fun i j =>
        if h : σ ∈ GK K then zC (b.repr (actT T.L ⟨σ, h⟩ (b j)) i) else 0,
      fun a => Matrix.of fun i j => zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i),
      b, fun g i j => ?_, fun a i j => rfl⟩
    show (if h : (g : GQ l) ∈ GK K then zC (b.repr (actT T.L ⟨g, h⟩ (b j)) i) else 0) = _
    exact dif_pos g.2
  · intro d M A hMA
    obtain ⟨b, hM, hA⟩ := hMA
    have key := matrices_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (zCHom l) T
      (fun g : ↥(GK K) => M g) A b (fun g i j => (hM g i j).trans (zCHom_apply _).symm)
      (fun a i j => (hA a i j).trans (zCHom_apply _).symm)
    refine ⟨fun i j => ?_, fun σ hσ τ hτ => key.1 ⟨σ, hσ⟩ ⟨τ, hτ⟩, key.2.1,
      fun σ hσ a => key.2.2 ⟨σ, hσ⟩ a⟩
    rw [continuousOn_iff_continuous_domRestrict]
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have h1 := continuous_coord_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (O := ↥(OL LL)) hc T b
      (b j) i
    have h2 : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := continuous_algebraMap _ _
    refine (h2.comp h1).congr fun g => ?_
    exact ((hM ⟨g.1, g.2⟩ i j).trans (zCHom_apply _).symm).symm

end GlobalTheory.Cyc
