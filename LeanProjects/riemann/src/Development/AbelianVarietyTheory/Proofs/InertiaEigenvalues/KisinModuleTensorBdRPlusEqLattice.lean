import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DeRhamIdent

section Generic

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
  [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem TWincl_inj {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G ℚ_[l] K O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem fix_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) (r : R)
    (hr : IsUnit r) (m : M) (h : f (r • m) = r • m) : f m = m := by
  obtain ⟨u, rfl⟩ := hr
  have h2 := congrArg (fun y => ((u⁻¹ : Rˣ) : R) • y) h
  simp only [← map_smul, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

end Generic

section Incl

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ι : Type)

theorem inclV_apply (c : ι → OA l O) (i : ι) : inclV l O ι c i = inclO l O (c i) := rfl

theorem inclV_smul (r : OA l O) (c : ι → OA l O) : inclV l O ι (r • c) = inclO l O r • inclV l O ι c := by
  funext i
  simp only [inclV_apply, Pi.smul_apply, smul_eq_mul, map_mul]

theorem inclV_inj [Module.Free ℤ_[l] O] : Function.Injective (inclV l O ι) := fun c d h =>
  funext fun i => inclO_injective (congrFun h i)

end Incl

end GlobalTheory.DeRhamIdent

namespace GlobalTheory.DeRhamIdent

open GlobalTheory.DeRhamIdent

set_option maxHeartbeats 2000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨⟨ε, hε⟩, hεall⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2

  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  set u : (OD l O)ˣ := hu.unit with hudef
  have hu' : (u : OD l O) = toOD l O ν := hu.unit_spec
  have hV := inclV_inj l O ι

  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  have hsum : ∀ c : ι → OA l O,
      inclV l O ι c = ∑ i, inclO l O (c i) • inclV l O ι (Pi.single i 1) := by
    intro c
    funext j
    simp [inclV_apply, Finset.sum_apply, Pi.single_apply]
  have hJ0 : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ν ^ α • z' = ∑ i, c i • z i := by
    intro c z' h
    apply TWincl_inj (inclO l O) inclO_injective T
    calc TWincl (inclO l O) T (ν ^ α • z') = inclO l O (ν ^ α) • I.j (inclV l O ι c) := by
          rw [TWincl_smul, h]
      _ = ∑ i, inclO l O (c i) • I.j (inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1)) := by
          rw [← I.j.map_smul, hsum c, Finset.smul_sum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, I.j.map_smul]
      _ = TWincl (inclO l O) T (∑ i, c i • z i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hz i, TWincl_smul]
  let w : ι → TW (OD l O) T := fun i => ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • TWincl (toOD l O) T (z i)
  let jD : (ι → OD l O) →ₗ[OD l O] TW (OD l O) T := ∑ i, (LinearMap.proj i).smulRight (w i)
  have hjD : ∀ d, jD d = ∑ i, d i • w i := fun d => by
    simp [jD, LinearMap.sum_apply]
  have hJ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z' := by
    intro c z' h
    have h2 : toOD l O (ν ^ α) • TWincl (toOD l O) T z' =
        ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
      rw [← TWincl_smul, hJ0 c z' h, map_sum]
      simp only [TWincl_smul]
    rw [hjD]
    calc ∑ i, toOD l O (c i) • w i
        = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • (toOD l O (ν ^ α) • TWincl (toOD l O) T z') := by rw [h2]
      _ = TWincl (toOD l O) T z' := by
          rw [smul_smul, map_pow, ← hu', ← mul_pow, Units.inv_mul, one_pow, one_smul]

  have hK1' : ∀ x, ∃ y, inclV l O ι y = inclO l O (ν ^ β) • I.ofT x := fun x => LinearMap.mem_range.1 (hK1 x)
  choose Cx hC using hK1'
  let C : ↥T.L.T →ₗ[O] (ι → OA l O) :=
    { toFun := Cx
      map_add' := fun x y => hV (by rw [map_add, hC, hC, hC, map_add, smul_add])
      map_smul' := fun o x => hV (by rw [map_smul, hC, hC, map_smul, RingHom.id_apply, smul_comm]) }
  let CA : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) := LinearMap.liftBaseChange (OA l O) C
  have hP1 : ∀ z' : TW (OA l O) T,
      inclV l O ι (CA z') = inclO l O (ν ^ β) • I.j.symm (TWincl (inclO l O) T z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
    | tmul b x =>
      have e1 : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
        simp [TWincl, TensorProduct.smul_tmul']
      have e2 : I.j.symm ((1 : OW l O) ⊗ₜ[O] x) = I.ofT x := rfl
      rw [e1, I.j.symm.map_smul, e2, LinearMap.liftBaseChange_tmul, inclV_smul]
      change inclO l O b • inclV l O ι (Cx x) = _
      rw [hC, smul_comm]
  let ψ : TW (OD l O) T →ₗ[OD l O] (ι → OD l O) := ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β •
    LinearMap.liftBaseChange (OD l O) (((toOD l O).toLinearMap.compLeft ι) ∘ₗ C)
  have hP2 : ∀ z' : TW (OA l O) T,
      ψ (TWincl (toOD l O) T z') = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β • fun i => toOD l O (CA z' i) := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      funext i
      simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← smul_add]
      congr 1
      funext i
      simp
    | tmul b x =>
      simp only [ψ, CA, TWincl, LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, LinearMap.liftBaseChange_tmul]
      congr 1
      funext i
      simp [C, LinearMap.compLeft, map_mul]
  have hΨ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ψ (TWincl (toOD l O) T z') = fun i => toOD l O (c i) := by
    intro c z' h
    have h1 : CA z' = ν ^ β • c := hV (by rw [hP1, ← h, I.j.symm_apply_apply, inclV_smul])
    rw [hP2, h1]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu', ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have h1 : jD ∘ₗ ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d x
    have e0 : d ⊗ₜ[O] x = d • ((1 : OD l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e0, map_smul, map_smul]
    congr 1
    have hx : I.j (inclV l O ι (Cx x)) = TWincl (inclO l O) T ((ν ^ β) ⊗ₜ[O] x) := by
      rw [hC, I.j.map_smul, I.j_ofT]
      simp [TWincl, TensorProduct.smul_tmul']
    have e3 : TWincl (toOD l O) T ((ν ^ β) ⊗ₜ[O] x) = ((u : OD l O) ^ β) • ((1 : OD l O) ⊗ₜ[O] x) := by
      simp [TWincl, TensorProduct.smul_tmul', hu']
    refine fix_of_unit (jD ∘ₗ ψ) ((u : OD l O) ^ β) ((Units.isUnit u).pow β) _ ?_
    rw [← e3, LinearMap.comp_apply, hΨ _ _ hx, hJ _ _ hx]
  have h2 : ψ ∘ₗ jD = LinearMap.id := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    have hzi : I.j (inclV l O ι (Pi.single i (ν ^ α))) = TWincl (inclO l O) T (z i) := by rw [hc, hz i]
    have e4 : (fun j => toOD l O ((Pi.single i (ν ^ α) : ι → OA l O) j)) =
        ((u : OD l O) ^ α) • (LinearMap.single (OD l O) (fun _ => OD l O) i 1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hu', map_pow]
      · simp [Pi.single_apply, hj]
    refine fix_of_unit (ψ ∘ₗ jD) ((u : OD l O) ^ α) ((Units.isUnit u).pow α) _ ?_
    rw [← e4, LinearMap.comp_apply, hJ _ _ hzi, hΨ _ _ hzi]
  exact ⟨LinearEquiv.ofLinear jD ψ h1 h2, fun c z' h => hJ c z' h⟩

end GlobalTheory.DeRhamIdent
