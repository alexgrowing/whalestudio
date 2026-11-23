import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosureOrbits.FinClosure
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FormsIrr
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ClsBasic
import GroundTheory.AutomorphicForms.UnitaryAdmissible

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KF

open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V GroundTheory.Automorphic.UnitaryAdmissible

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem gen_orbit {Γ H : Type*} [Group Γ] [AddCommGroup H] [Module ℂ H] (ρ : Γ → H →ₗ[ℂ] H)
    (hm : ∀ a b x, ρ (a * b) x = ρ a (ρ b x)) (v : H) (k : Γ) :
    ∀ x ∈ Submodule.span ℂ (Set.range fun k => ρ k v), ρ k x ∈ Submodule.span ℂ (Set.range fun k => ρ k v) := by
  have : Submodule.span ℂ (Set.range fun k => ρ k v) ≤ (Submodule.span ℂ (Set.range fun k => ρ k v)).comap (ρ k) := by
    rw [Submodule.span_le]
    rintro _ ⟨k', rfl⟩
    exact Submodule.subset_span ⟨k * k', hm k k' v⟩
  exact this

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure]

noncomputable def rk (k : KG K n) : L2 μ →ₗ[ℂ] L2 μ := (rightRegularRep (Gam K n) μ (k : G1 K n)).toLinearMap

private theorem rk_adj (k : KG K n) : ∃ k', ∀ x y, ⟪x, rk μ k y⟫_ℂ = ⟪rk μ k' x, y⟫_ℂ :=
  ⟨k⁻¹, fun x y => by
    have := (rightRegularRep (Gam K n) μ).inner_map_left ((k⁻¹ : KG K n) : G1 K n) x y
    rw [← Subgroup.coe_inv, inv_inv] at this
    exact this.symm⟩

theorem rk_mul (k k' : KG K n) (x : L2 μ) : rk μ (k * k') x = rk μ k (rk μ k' x) :=
  (rightRegularRep (Gam K n) μ).map_mul_apply (k : G1 K n) (k' : G1 K n) x

private theorem rk_one (x : L2 μ) : rk μ (1 : KG K n) x = x :=
  (rightRegularRep (Gam K n) μ).map_one_apply x

private theorem orbit_stable (v : L2 μ) (k : KG K n) :
    ∀ x ∈ Submodule.span ℂ (Set.range fun k => rk μ k v), rk μ k x ∈ Submodule.span ℂ (Set.range fun k => rk μ k v) :=
  gen_orbit (rk μ) (rk_mul μ) v k

private theorem mem_orbit (v : L2 μ) : v ∈ Submodule.span ℂ (Set.range fun k => rk μ k v) :=
  Submodule.subset_span ⟨1, rk_one μ v⟩

private theorem cls_tr {φ : cuspForms K n} (hφ : φ ∈ centralCuspForms K n) (ψ : cuspForms K n) (k : KG K n)
    (h : ∀ x, ψ.1 x = φ.1 (x * ((k : G1 K n) : AdelicGLn.AdelicGL K n))) : clsL μ ψ = rk μ k (clsL μ φ) := by
  rw [(clsBasic K n μ).2.2.1 φ hφ ψ _ h, RG, retractOne_coe]
  rfl

private theorem exists_level (F : Submodule ℂ (L2 μ)) [FiniteDimensional ℂ F] (hF : ∀ k, ∀ x ∈ F, rk μ k x ∈ F) :
    ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
      ∀ u ∈ U, ∀ x ∈ F, rightRegularRep (Gam K n) μ (finOne K n u) x = x := by
  have : CompactSpace (AdelicGLn.integralFiniteGL K n) :=
    isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
  have h1 : ∀ x ∈ F, ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
      ∀ u ∈ U, rightRegularRep (Gam K n) μ (finOne K n u) x = x := by
    intro x hx
    refine UnitaryRep.exists_isOpen_forall_eq_of_finiteDimensional
      ((rightRegularRep (Gam K n) μ).comapHom (finOne K n) continuous_finOne) x
      (Submodule.finiteDimensional_of_le (S₂ := F) (Submodule.span_le.2 ?_))
    rintro _ ⟨u, rfl⟩
    exact hF ⟨finOne K n u, finEmb_mem_maxCompact u.2⟩ x hx
  set b := Module.finBasis ℂ F
  choose U hU hUx using fun i => h1 (b i) (b i).2
  refine ⟨⨅ i, U i, ?_, fun u hu x hx => ?_⟩
  · rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hU
  · have e : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : L2 μ) := by
      have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hUx i u (Subgroup.mem_iInf.1 hu i)]

private theorem loc_fin {V : Submodule ℂ (L2 μ)} (hV : IsSummand μ V) : ∀ w ∈ (formsIn μ V).map (clsL μ),
    ∃ S ≤ (formsIn μ V).map (clsL μ), FiniteDimensional ℂ S ∧ w ∈ S ∧ ∀ g, ∀ x ∈ S, rk μ g x ∈ S := by
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨_, Submodule.span_le.2 ?_, ?_, mem_orbit μ _, orbit_stable μ _⟩
  · rintro _ ⟨k, rfl⟩
    let ψ : cuspForms K n := ⟨_, φ.2.1.rightTranslate_of_mem_maxCompact k.2, φ.2.2.translate _⟩
    have e : clsL μ ψ = rk μ k (clsL μ φ) := cls_tr μ hφ.1 ψ k fun _ => rfl
    refine ⟨ψ, ⟨fun s x => ?_, ?_⟩, e⟩
    · show φ.1 (_ * x * _) = φ.1 (x * _)
      rw [mul_assoc]
      exact hφ.1 s _
    · show clsL μ ψ ∈ V
      rw [e]
      exact hV.inv _ _ hφ.2
  · have := finiteDimensional_span_cuspRep_maxCompact μ φ
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k :
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
        cuspRep μ ⟨k, maxCompact_le_normOneGL k.2⟩ (cuspToL2 μ φ))).map (cuspidalL2 μ).subtype) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨⟨_, k.2⟩, rfl⟩, rfl⟩

set_option maxHeartbeats 2000000 in
theorem kfin {V : Submodule ℂ (L2 μ)} (hV : IsSummand μ V) {v : L2 μ} (hv : v ∈ V)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => rk μ k v))) : v ∈ (formsIn μ V).map (clsL μ) := by
  obtain ⟨hs, hne, hirr, hcl⟩ := formsIrr K n μ V hV
  have hirr' := hs.isIrreducible_iff.2 ⟨hne, hirr⟩
  set F := Submodule.span ℂ (Set.range fun k => rk μ k v) with hFdef
  have hF : ∀ k, ∀ x ∈ F, rk μ k x ∈ F := orbit_stable μ v
  obtain ⟨U₀, hU₀, hfix⟩ := exists_level μ F hF
  set U := formsIn μ V with hU
  have hUc : U ≤ centralCuspForms K n := inf_le_left
  set Mx := cuspSubmodule K n U hs.ρ hs.σ hs.τ with hMx
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := K) (n := n)
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hK : ∀ i, ε i = -1 → ∀ t : ℝ,
      (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
    intro i hi t
    refine expG_mem_archCompact_of_skew _ ?_
    have h := hskew i hi
    rw [mem_archSkew] at h
    show Matrix.conjTranspose (t • mat (b i : ArchMatrix K n)) = -(t • mat (b i : ArchMatrix K n))
    rw [Matrix.conjTranspose_smul, star_trivial, h, smul_neg]
  obtain ⟨ω, hω⟩ := exists_casimir_eq_smul U hs.ρ hs.σ hs.τ hirr' b ε hε2 horth
  set C : Module.End ℂ U := ∑ i, Mx.gk.ρ (lapZ b ε i) * Mx.gk.ρ (lapZ b ε i) with hC
  set ι : U →ₗ[ℂ] L2 μ := clsL μ ∘ₗ U.subtype with hι
  have hinj : ∀ φ : U, ι φ = 0 → φ = 0 := fun φ h => Subtype.ext ((clsBasic K n μ).1 φ.1 (hUc φ.2) h)
  have hCS : ∀ S : Submodule ℂ (L2 μ), (∀ k, ∀ x ∈ S, rk μ k x ∈ S) → ∀ φ ∈ S.comap ι, C φ ∈ S.comap ι := by
    intro S hS φ hφ
    refine sumSq_mem_of_stable Mx.gk (lapZ b ε) (lapZ_mem b ε hε hK) (fun k ψ hψ => ?_) hφ
    have e : ι (Mx.gk.σ k ψ) = rk μ ⟨⟨infEmb K n k, maxCompact_le_normOneGL k.2⟩, k.2⟩ (ι ψ) :=
      cls_tr μ (hUc ψ.2) _ _ fun _ => rfl
    rw [Submodule.mem_comap, e]
    exact hS _ _ hψ
  have hFo := orth_stable (rk μ) (rk_adj μ) hF
  have hq : FiniteDimensional ℂ (U ⧸ Fᗮ.comap ι) := by
    have e : Fᗮ.comap ι = LinearMap.ker ((F.orthogonalProjection : L2 μ →ₗ[ℂ] F) ∘ₗ ι) := by
      ext x
      simp [Submodule.orthogonalProjection_eq_zero_iff]
    rw [e]
    exact (LinearMap.quotKerEquivRange _).symm.finiteDimensional
  obtain ⟨q, hqm, hqd, hqN⟩ := exists_monic_aeval_mem C (Fᗮ.comap ι) (hCS _ hFo)
  set P := q.comp (Polynomial.X - Polynomial.C ω) with hP
  have hPm : P.Monic := hqm.comp (Polynomial.monic_X_sub_C ω) (by rw [Polynomial.natDegree_X_sub_C]; exact one_ne_zero)
  have hPd : 0 < P.natDegree := by rwa [hP, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
  set E : Submodule ℂ (cuspForms K n) := U ⊓ LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) P) ⊓
    ⨅ u ∈ U₀, LinearMap.ker (finRepCusp K n (u : AdelicGLn.FiniteAdelicGL K n) - 1) with hE
  have hEfd : FiniteDimensional ℂ E := by
    refine finiteDimensional_of_eigen b P hPm hPd 0 U₀ hU₀ E fun φ hφ => ⟨hφ.1.2, ?_, fun u hu => ?_⟩
    · rw [zero_smul]
      exact ρ_centralZ_eq_zero (hUc hφ.1.1)
    · have := LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hφ.2 u) hu)
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
  refine mem_of_mem_closure_of_finite (rk μ) (rk_adj μ) _ F (E.map (clsL μ)) hF (loc_fin μ hV) ?_ (mem_orbit μ v)
    (by rw [hcl]; exact hv)
  intro S hSW hS hbot x hx
  obtain ⟨φ, hφ, rfl⟩ := hSW hx
  have hz : ∀ ψ : U, ι ψ ∈ S → ι ψ ∈ Fᗮ → ψ = 0 := fun ψ h1 h2 =>
    hinj ψ ((Submodule.mem_bot ℂ).1 (hbot ▸ (⟨h1, h2⟩ : ι ψ ∈ S ⊓ Fᗮ)))
  refine ⟨φ, ⟨⟨hφ, ?_⟩, (Submodule.mem_iInf _).2 fun u => (Submodule.mem_iInf _).2 fun hu => ?_⟩, rfl⟩
  · exact aeval_laplacian_eq_zero U hs.ρ hs.σ hs.τ b ε hε ω hω q (φ := ⟨φ, hφ⟩)
      (hz _ (Polynomial.aeval_apply_smul_mem_of_le_comap (q := S.comap ι) hx q C (hCS S hS)) (hqN _))
  · set r := rk μ (⟨finOne K n u, finEmb_mem_maxCompact u.2⟩ : KG K n) with hr
    have e : clsL μ (finRepCusp K n (u : AdelicGLn.FiniteAdelicGL K n) φ) = r (clsL μ φ) :=
      cls_tr μ (hUc hφ) _ _ fun _ => rfl
    set ψ : U := ⟨_, hs.τ u φ hφ⟩ - ⟨φ, hφ⟩ with hψ
    have e2 : ι ψ = r (clsL μ φ) - clsL μ φ := by
      rw [hψ, map_sub, ← e]
      rfl
    have h1 : ι ψ ∈ S := by
      rw [e2]
      exact S.sub_mem (hS _ _ hx) hx
    have h2 : ι ψ ∈ Fᗮ := by
      rw [e2, Submodule.mem_orthogonal]
      intro f hf
      have h3 : ⟪f, r (clsL μ φ)⟫_ℂ = ⟪f, clsL μ φ⟫_ℂ := by
        have h4 := (rightRegularRep (Gam K n) μ).inner_map_map (finOne K n u) f (clsL μ φ)
        rw [hfix u hu f hf] at h4
        exact h4
      rw [inner_sub_right, h3, sub_self]
    have h0 := hz ψ h1 h2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    exact congrArg Subtype.val h0

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KF
