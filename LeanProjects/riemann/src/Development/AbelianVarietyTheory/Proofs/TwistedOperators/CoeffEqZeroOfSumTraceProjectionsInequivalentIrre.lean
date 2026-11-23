import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EndoApplyEq
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.TraceSep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.TraceSep

namespace GlobalTheory.TraceSep

theorem hasFinTrace_compress {V : Type} [AddCommGroup V] [Module ℂ V] (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P)
    [FiniteDimensional ℂ (LinearMap.range P)] (A : V →ₗ[ℂ] V) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P ∘ₗ A ∘ₗ P)
      (LinearMap.trace ℂ (LinearMap.range P) (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype)) := by
  have hfix : ∀ u ∈ LinearMap.range P, P u = u := by
    rintro u ⟨w, rfl⟩; exact LinearMap.congr_fun hP w
  have hBU : LinearMap.range (P ∘ₗ A ∘ₗ P) ≤ LinearMap.range P := LinearMap.range_comp_le_range _ _
  haveI : FiniteDimensional ℂ (LinearMap.range (P ∘ₗ A ∘ₗ P)) := Submodule.finiteDimensional_of_le hBU
  refine ⟨inferInstance, ?_⟩
  have hQ : ∀ u, (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype) u ∈
      (LinearMap.range (P ∘ₗ A ∘ₗ P)).comap (LinearMap.range P).subtype := by
    intro u
    refine ⟨u, ?_⟩
    simp [hfix u u.2]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hQ,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hBU)]
  congr 1
  ext ⟨x, hx⟩
  simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe, hfix x (hBU hx)]

theorem coeff_eq_zero_of_sum_trace_eq_zero : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  intro G _ n W _ _ σ hirr hne P hP hfin a hsum i₀ hi₀
  let Q : ∀ i, MonoidAlgebra ℂ G → Module.End ℂ (LinearMap.range (P i)) := fun i y =>
    (P i).rangeRestrict ∘ₗ (σ i).asAlgebraHom y ∘ₗ (LinearMap.range (P i)).subtype
  have hlin : ∀ y, ∑ i, a i * LinearMap.trace ℂ _ (Q i y) = 0 := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      refine hsum g _ fun i => ?_
      have := hasFinTrace_compress (P i) (hP i) (σ i g)
      simpa [Q, Representation.asAlgebraHom_of] using this
    | add x y hx hy =>
      simp only [Q, map_add, LinearMap.add_comp, LinearMap.comp_add, mul_add,
        Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy, add_zero]
    | smul c x hx =>
      simp only [Q, map_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_eq_mul] at hx ⊢
      rw [Finset.sum_congr rfl fun i _ => mul_left_comm (a i) c _, ← Finset.mul_sum, hx, mul_zero]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hirr i)
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).asModule →ₗ[MonoidAlgebra ℂ G] (σ j).asModule, f = 0 := by
    intro i j hij f
    haveI := hirr i
    haveI := hirr j
    haveI := hne i j hij
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) (σ j)).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (LinearMap.range (P i)))) ℂ (LinearMap.range (P i)) :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := exists_smul_eq_ite (R := MonoidAlgebra ℂ G) (fun i => (σ i).asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : LinearMap.range (P i)) : W i) : (σ i).asModule))
  have hQx : ∀ i, Q i x = if i = i₀ then LinearMap.id else 0 := by
    intro i
    refine (b i).ext fun k => ?_
    have h1 := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    change (σ i).asAlgebraHom x (b i k : W i) = _ at h1
    have hfix : P i (b i k : W i) = b i k := by
      obtain ⟨w, hw⟩ := (b i k).2
      rw [← hw]; exact LinearMap.congr_fun (hP i) w
    apply Subtype.ext
    by_cases hi : i = i₀
    · subst hi
      have h1' : (σ i).asAlgebraHom x (b i k : W i) = b i k := by simpa using h1
      simp [Q, h1', hfix]
    · have h1' : (σ i).asAlgebraHom x (b i k : W i) = 0 :=
        h1.trans (if_neg hi)
      simp [Q, h1', hi]
  have h := hlin x
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hQx i, if_neg hi, map_zero, mul_zero])
    (by simp)] at h
  rw [hQx i₀, if_pos rfl, LinearMap.trace_id] at h
  have hpos : 0 < Module.finrank ℂ (LinearMap.range (P i₀)) := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot, Ne, LinearMap.range_eq_bot]
    exact hi₀
  have hne0 : (Module.finrank ℂ (LinearMap.range (P i₀)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact (mul_eq_zero.1 h).resolve_right hne0

end GlobalTheory.TraceSep
