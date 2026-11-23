import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsCompactStabGLHat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul

noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Sand

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem tensMap_smul' {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (c : R) (z : R ⊗[F] E) : tensMap (E := E) φ (c • z) = φ c • tensMap (E := E) φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem continuous_tensEval (v : HeightOneSpectrum (𝓞 F)) : Continuous (tensMap (E := E) (evalV F v)) := by
  let f : Af F ⊗[F] E →ₛₗ[(evalV F v : Af F →+* Fv F v)] Fv F v ⊗[F] E :=
    { toFun := tensMap (E := E) (evalV F v), map_add' := map_add _,
      map_smul' := fun c z => tensMap_smul' (evalV F v) c z }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (R := Af F) (S := Fv F v)
    (σ := (evalV F v : Af F →+* Fv F v)) (by exact RestrictedProduct.continuous_eval v) f

theorem continuous_pv (v : HeightOneSpectrum (𝓞 F)) : Continuous (pv (E := E) (n := n) v) :=
  continuous_pi fun i => (continuous_tensEval v).comp (continuous_apply i)

theorem pv_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → Af F ⊗[F] E) : pv v (x + y) = pv v x + pv v y := by
  funext i; simp [pv]

theorem pv_zero (v : HeightOneSpectrum (𝓞 F)) : pv (E := E) (n := n) v 0 = 0 := by
  funext i; simp [pv]

theorem pv_neg (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : pv v (-x) = -pv v x := by
  funext i; simp [pv]

theorem pv_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → Af F ⊗[F] E) : pv v (N • x) = N • pv v x := by
  funext i; simp [pv]

theorem ratV_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (N • x) = N • ratV (F := F) (Fv F v) x := by
  funext i; simp [ratV]

theorem zsmul_mem_latLoc_of (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v L0) :
    N • y ∈ latLoc (E := E) v L := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨μ, hμ, rfl⟩ := hz
    rw [← ratV_zsmul]
    exact Submodule.subset_span ⟨_, h μ hμ, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem zsmul_mem_latHat (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    {x : Fin n → Af F ⊗[F] E} (hx : x ∈ latHat (F := F) L0) : N • x ∈ latHat (F := F) L := by
  intro v
  rw [pv_zsmul]
  exact zsmul_mem_latLoc_of L0 L N h v (hx v)

def stdSub : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E)

theorem single_mem_std (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) := by
  classical
  rw [stdSub, Submodule.mem_pi]
  intro i _
  rw [Pi.single_apply]
  split_ifs
  · exact LinearMap.mem_range.2 ⟨1, by simp⟩
  · exact zero_mem _

theorem span_std : Submodule.span E ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : (Pi.single i (x i) : Fin n → E) = x i • (Pi.single i (1 : E) : Fin n → E) := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_std i))

theorem std_mult (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)), N • μ ∈ (L : Set (Fin n → E)) := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : ∀ j, ∃ a : 𝓞 E, Algebra.linearMap (𝓞 E) E a = μ j := fun j =>
    LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) j (Set.mem_univ _))
  choose a ha using hμ'
  have e : N • μ = ∑ j, a j • (N • (Pi.single j (1 : E) : Fin n → E)) := by
    ext k
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← ha k, Algebra.linearMap_apply]
    simp only [Algebra.smul_def, mul_one, eq_intCast, zsmul_eq_mul]
    ring
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hN j)

theorem lat_mult (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ (L : Set (Fin n → E)), N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨N, hN0, hN⟩ := exists_common_mult (stdSub : Submodule (𝓞 E) (Fin n → E)) span_std
    (fun s : S => (s : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : μ ∈ Submodule.span (𝓞 E) (S : Set (Fin n → E)) := by rw [hS]; exact hμ
  clear hμ
  induction hμ' using Submodule.span_induction with
  | mem z hz => exact hN ⟨z, hz⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

end Sand

def StdHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsOpen (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

def StdHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsCompact (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

theorem zsmul_eq_cast_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (N : ℤ)
    (x : Fin n → Af F ⊗[F] E) : N • x = (N : F) • x :=
  (Int.cast_smul_eq_zsmul F N x).symm

theorem latHatOpen_of (h0 : StdHatOpen) : LatHatOpen := by
  intro F E _ _ _ _ _ n L hL _
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := std_mult L hL
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) (L : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) :=
    {x | (N : F)⁻¹ • x ∈ latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))}
  have hWo : IsOpen W := (h0 (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    have h00 : (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) = 0 := smul_zero _
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [h00]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem latHatCompact_of (h0 : StdHatCompact) : LatHatCompact := by
  intro F E _ _ _ _ _ n L hL hfg
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := lat_mult L hfg
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L hL))).preimage (continuous_pv v)
  refine ((h0 (F := F) (E := E) (n := n)).image (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

open KCptW

theorem kCompactOpen_of_std (hO : StdHatOpen) (hC : StdHatCompact) : KCompactOpen :=
  kCompactOpen_of (latHatOpen_of @hO) (latHatCompact_of @hC)

end MassDataMassesW
