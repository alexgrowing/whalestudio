import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.EigenformTranslates

open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter MeasureTheory
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm CuspidalSpectrum

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem finite_range_of_isOpen_stabilizer {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) {v : V}
    (hv : IsOpen (stabilizerOf ρ v : Set G)) (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    (Set.range fun k : K => ρ k v).Finite := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : G => (fun x => c⁻¹ * x) ⁻¹' (stabilizerOf ρ v : Set G))
    (fun c => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, show x⁻¹ * x ∈ (stabilizerOf ρ v : Set G) by
      rw [inv_mul_cancel]; exact one_mem _⟩)
  refine ((t.finite_toSet).image fun c => ρ c v).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨c, hc, hck⟩ := Set.mem_iUnion₂.1 (ht k.2)
  refine ⟨c, hc, ?_⟩
  have h1 : ρ (c⁻¹ * k) v = v := hck
  change ρ c v = ρ k v
  conv_lhs => rw [← h1]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem translateSpanCusp_le_smoothVectors (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    translateSpanCusp f ≤ smoothVectors (finRepCusp ℚ 2) := by
  rw [translateSpanCusp, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  refine smooth_apply_mem _ ?_ g
  refine Subgroup.isOpen_mono (H₁ := Gamma0Level N) (fun u hu => ?_) (isOpen_Gamma0Level N)
  rw [mem_stabilizerOf]
  refine Subtype.ext (funext fun x => ?_)
  exact (liftEquiv N k f.toSlashInvariantForm).2.right_level x u hu

theorem coe_finRepCusp_apply (g : FiniteAdelicGL ℚ 2) (ψ : cuspForms ℚ 2) (x : AdelicGL ℚ 2) :
    ((finRepCusp ℚ 2 g ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) x = (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) :=
  rfl

theorem coe_rightTranslate_apply (y : AdelicGL ℚ 2) (ψ : AdelicGL ℚ 2 → ℂ) (x : AdelicGL ℚ 2) :
    Automorphic.rightTranslate y ψ x = ψ (x * y) :=
  rfl

variable (μ : Measure (Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure]

theorem cuspToL2_finRepCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (g : FiniteAdelicGL ℚ 2) :
    ∃ y : Reduction.normOneGL ℚ 2, ∀ ψ ∈ translateSpanCusp f,
      cuspToL2 μ (finRepCusp ℚ 2 g ψ) = cuspRep μ y (cuspToL2 μ ψ) := by
  have hex : ∃ (s : {r : ℝ // 0 < r}) (y : AdelicGL ℚ 2), y ∈ Reduction.normOneGL ℚ 2 ∧
      AutomorphicForm.finEmb ℚ 2 g = Reduction.centralSection ℚ 2 s * y :=
    CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL _
  obtain ⟨s, y, hy, hxy⟩ := hex
  refine ⟨⟨y, hy⟩, fun ψ hψ => ?_⟩
  refine cuspToL2_rightTranslate μ ⟨y, hy⟩ ψ (finRepCusp ℚ 2 g ψ) ?_
  funext x
  rw [coe_finRepCusp_apply, coe_rightTranslate_apply]
  change (ψ : AdelicGL ℚ 2 → ℂ) (x * finEmb ℚ 2 g) = (ψ : AdelicGL ℚ 2 → ℂ) (x * y)
  rw [hxy, ← mul_assoc, ← Reduction.centralSection_mul_comm, mul_assoc,
    centralSection_of_mem_translateSpanCusp f hψ]

theorem eq_zero_of_cuspFormLp_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {v : cuspForms ℚ 2} (hv : v ∈ translateSpanCusp f) (h0 : cuspToL2 μ v = 0) : v = 0 :=
  injOn_cuspToL2 μ (fun s x => centralSection_of_mem_translateSpanCusp f hv s x)
    (fun _ _ => rfl) (h0.trans (map_zero _).symm)

variable (k) in

def descendL : cuspForms ℚ 2 →ₗ[ℂ] (ℍ → ℂ) where
  toFun ψ := descend k ψ
  map_add' ψ ψ' := by funext z; simp [descend, mul_add]
  map_smul' c ψ := by funext z; simp [descend]; ring

def cuspFormCoeL : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun F := F
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finRightRep_eq_of_mem_invariants {ψ : cuspForms ℚ 2}
    (hψ : ψ ∈ Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)) :
    ∀ u ∈ Gamma0Level N, finRightRep u (ψ : AdelicGL ℚ 2 → ℂ) = ψ := fun u hu =>
  congrArg Subtype.val (hψ ⟨u, hu⟩)

theorem finiteDimensional_translateSpanCusp_fixed (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) :
    FiniteDimensional ℂ ↥(translateSpanCusp f ⊓
      Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)) := by
  set M := translateSpanCusp f ⊓ Representation.invariants ((finRepCusp ℚ 2).comp (Gamma0Level N).subtype)
  have hmem : ∀ ψ ∈ M, descendL k ψ ∈ LinearMap.range (cuspFormCoeL (N := N) (k := k)) := by
    intro ψ hψ
    obtain ⟨F, hF⟩ := exists_cuspForm_of_mem_translateSpan f (coe_mem_translateSpan f hψ.1)
      (finRightRep_eq_of_mem_invariants hψ.2)
    refine ⟨F, ?_⟩
    change (F : ℍ → ℂ) = descend k ψ
    rw [← hF, liftEquiv_apply,
      descend_adelicLift (fun γ hγ => SlashInvariantForm.slash_action_eqn F.toSlashInvariantForm γ hγ)]
    rfl
  let Φ : M →ₗ[ℂ] LinearMap.range (cuspFormCoeL (N := N) (k := k)) :=
    (descendL k ∘ₗ M.subtype).codRestrict _ (fun ψ => hmem ψ ψ.2)
  have hinj : Function.Injective Φ := by
    refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 (fun (ψ : M) (hψ : Φ ψ = 0) => ?_))
    have h0 : descend k (ψ : AdelicGL ℚ 2 → ℂ) = 0 := congrArg Subtype.val hψ
    have hW : IsWeightLevel N k (ψ : AdelicGL ℚ 2 → ℂ) :=
      isWeightLevel_of_mem_translateSpan f.toSlashInvariantForm (coe_mem_translateSpan f ψ.2.1)
        (finRightRep_eq_of_mem_invariants ψ.2.2)
    apply Subtype.ext
    apply Subtype.ext
    rw [← adelicLift_descend hW, h0]
    funext x
    simp [adelicLift, archLift]
  exact Module.Finite.of_injective Φ hinj

open Classical in

def heckeFin (N p : ℕ) [NeZero p] : Finset (FiniteAdelicGL ℚ 2) :=
  (heckeReps N p).image (finiteDiagonal ℚ 2)

theorem coe_sum_heckeFin (p : ℕ) [NeZero p] [Fact p.Prime] (ψ : cuspForms ℚ 2) :
    ((∑ g ∈ heckeFin N p, finRepCusp ℚ 2 g ψ : cuspForms ℚ 2) : AdelicGL ℚ 2 → ℂ) = heckeSum N p ψ := by
  classical
  rw [heckeFin, Finset.sum_image (fun a ha b hb hab => eq_of_inv_mul_mem_Gamma0Level N p ha hb
    (by rw [hab, inv_mul_cancel]; exact one_mem _))]
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem liftCusp_mem_of_le_translateSpanCusp_alt (μ : Measure (Reduction.normOneGL ℚ 2)) [μ.IsHaarMeasure]
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (ev : ℕ → ℂ) (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) (Y : Submodule ℂ (cuspForms ℚ 2)) (hYT : Y ≤ translateSpanCusp f)
    (hY : ∀ g, ∀ y ∈ Y, finRepCusp ℚ 2 g y ∈ Y) (hY0 : Y ≠ ⊥) : liftCusp f ∈ Y := by
  have hex : ∀ g : FiniteAdelicGL ℚ 2, ∃ y : Reduction.normOneGL ℚ 2, ∀ ψ ∈ translateSpanCusp f,
      cuspToL2 μ (finRepCusp ℚ 2 g ψ) = cuspRep μ y (cuspToL2 μ ψ) := fun g => cuspToL2_finRepCusp μ f g
  have hφS : ∀ j : {p : ℕ // p.Prime}, ∑ g ∈ @heckeFin N j.1 ⟨j.2.ne_zero⟩, finRepCusp ℚ 2 g (liftCusp f) =
      (heckeConst j.1 k * ev j.1) • liftCusp f := by
    rintro ⟨p, hp⟩
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    apply Subtype.ext
    rw [coe_sum_heckeFin]
    change heckeSum N p (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) = _
    rw [heckeSum_liftEquiv, ← heckeCusp_toSlashInvariantForm, hf p]
    have e : (ev p • f).toSlashInvariantForm = ev p • f.toSlashInvariantForm := rfl
    rw [e, map_smul, Submodule.coe_smul, Submodule.coe_smul, mul_smul]
    rfl
  have hP : ∀ z ∈ translateSpanCusp f, (∀ u : Gamma0Level N, finRepCusp ℚ 2 u z = z) →
      (∀ j : {p : ℕ // p.Prime}, ∑ g ∈ @heckeFin N j.1 ⟨j.2.ne_zero⟩, finRepCusp ℚ 2 g z =
        (heckeConst j.1 k * ev j.1) • z) → ∃ c : ℂ, z = c • liftCusp f := by
    intro z hzT hzK hzE
    obtain ⟨F, hF⟩ := exists_cuspForm_of_mem_translateSpan f (coe_mem_translateSpan f hzT)
      (fun u hu => congrArg Subtype.val (hzK ⟨u, hu⟩))
    have hFe : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k F = ev p • F := by
      intro p hp
      have : NeZero p := ⟨hp.out.ne_zero⟩
      have h1 : heckeSum N p (z : AdelicGL ℚ 2 → ℂ) = (heckeConst p k * ev p) • (z : AdelicGL ℚ 2 → ℂ) := by
        rw [← coe_sum_heckeFin]
        have := congrArg Subtype.val (hzE ⟨p, hp.out⟩)
        exact this
      rw [← hF, heckeSum_liftEquiv, mul_smul] at h1
      have h2 := smul_right_injective _ (heckeConst_ne_zero (k := k) p) h1
      have h3 : liftEquiv N k (heckeSlash N p k F.toSlashInvariantForm) =
          liftEquiv N k (ev p • F.toSlashInvariantForm) := by
        apply Subtype.ext
        rw [map_smul, Submodule.coe_smul]
        exact h2
      have h4 := (liftEquiv N k).injective h3
      ext w
      exact congrArg (fun G : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k => G w) h4
    obtain ⟨c, hc⟩ : ∃ c : ℂ, F = c • f := ⟨_, eq_smul_of_eigen f F ev hf hFe hf1⟩
    subst hc
    refine ⟨c, Subtype.ext ?_⟩
    rw [← hF]
    have e : (c • f).toSlashInvariantForm = c • f.toSlashInvariantForm := rfl
    rw [e, map_smul, Submodule.coe_smul, Submodule.coe_smul]
    rfl
  have key := mem_of_stable_of_eigen (ρ := finRepCusp ℚ 2) (ι := cuspToL2 μ) (T := translateSpanCusp f)
    (φ := liftCusp f) (K := Gamma0Level N) (J := {p : ℕ // p.Prime})
    (S := fun j => @heckeFin N j.1 ⟨j.2.ne_zero⟩) (ev := fun j => heckeConst j.1 k * ev j.1)
  have k2 := key rfl (fun v hv h0 => eq_zero_of_cuspFormLp_eq_zero μ f hv h0)
  have hunit : ∀ g : FiniteAdelicGL ℚ 2, ∀ v ∈ translateSpanCusp f, ∀ w ∈ translateSpanCusp f,
      @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner (cuspToL2 μ (finRepCusp ℚ 2 g v))
        (cuspToL2 μ (finRepCusp ℚ 2 g w)) =
      @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner (cuspToL2 μ v) (cuspToL2 μ w) := by
    intro g v hv w hw
    have hy := (hex g).choose_spec
    exact (congrArg₂ (fun a b : cuspidalL2 μ => @inner ℂ (cuspidalL2 μ) InnerProductSpace.toInner a b)
      (hy v hv) (hy w hw)).trans (UnitaryRep.inner_map_map _ _ _ _)
  exact k2 hunit (fun u => Subtype.ext (funext fun x => (liftEquiv N k f.toSlashInvariantForm).2.right_level x u u.2))
    (fun v hv => finite_range_of_isOpen_stabilizer _ (mem_smoothVectors.1 (translateSpanCusp_le_smoothVectors f hv)) _
      (isCompact_Gamma0Level N))
    (finiteDimensional_translateSpanCusp_fixed f) hφS hP Y hYT hY hY0

theorem liftCusp_mem_of_le_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (ev : ℕ → ℂ) (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) (Y : Submodule ℂ (cuspForms ℚ 2)) (hYT : Y ≤ translateSpanCusp f)
    (hY : ∀ g, ∀ y ∈ Y, finRepCusp ℚ 2 g y ∈ Y) (hY0 : Y ≠ ⊥) : liftCusp f ∈ Y :=
  liftCusp_mem_of_le_translateSpanCusp_alt Measure.haar f ev hf hf1 Y hYT hY hY0

end GL2Classical

end

end GroundTheory.Automorphic
