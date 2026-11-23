import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkEquationAllPlaces
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

def AlgCoef (D : D7) {N N' : ℕ} (G : VC D N N' → ℂ) : Prop :=
  ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D G M

def ZeroAlg : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ N N' : ℕ, Even N → Even N' → AlgCoef D (B.thZero N N')

def TransAlg : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      ∀ G : VC D N N' → ℂ, G ∈ Th D (tor0 D cc δ) L₁ L₁' → AlgCoef D G →
        ∀ x ∈ La D (tor0 D cc δ) L₂ L₂', AlgCoef D (U D (tor0 D cc δ) x G)

def LinkVecCoef : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ : IdE D → ℂ, IsChi D χ → TaylorCoeffsInNumberField D (B.eNat χ)

section Coef

variable {D : D7} {N N' : ℕ}

theorem algCoef_iff (G : VC D N N' → ℂ) :
    AlgCoef D G ↔ ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ CoefIn D G M := Iff.rfl

theorem taylor_lin {ι : Type*} [Fintype ι] (r : ι → ℂ) (F : ι → VC D N N' → ℂ)
    (hF : ∀ k (m : ℕ), ContDiff ℂ m (F k)) (α : Mono D N N') :
    taylor D (fun z => ∑ k, r k * F k z) α = ∑ k, r k * taylor D (F k) α := by
  unfold taylor
  have h1 : (fun z => ∑ k, r k * F k z) = fun z => ∑ k ∈ Finset.univ, r k • F k z := rfl
  rw [h1, iteratedFDeriv_sum (fun k _ => (hF k _).const_smul (r k)), Finset.sum_apply, _root_.sum_apply,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun x => r k • F k x) = r k • F k := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hF k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]

theorem isIntegral_of_mem_Qbar {x : ℂ} (h : x ∈ Qbar) : IsIntegral ℚ x :=
  (mem_algebraicClosure_iff.1 h).isIntegral

theorem algCoef_sum {ι : Type*} [Fintype ι] (r : ι → ℂ) (hr : ∀ k, r k ∈ Qbar) (F : ι → VC D N N' → ℂ)
    (hF : ∀ k (m : ℕ), ContDiff ℂ m (F k)) (hA : ∀ k, AlgCoef D (F k)) :
    AlgCoef D (fun z => ∑ k, r k * F k z) := by
  choose M hM hC using hA
  let M' : ι → IntermediateField ℚ ℂ := fun k => M k ⊔ IntermediateField.adjoin ℚ {r k}
  haveI : ∀ k, FiniteDimensional ℚ (M k) := hM
  haveI : ∀ k, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {r k}) := fun k =>
    IntermediateField.adjoin.finiteDimensional (isIntegral_of_mem_Qbar (hr k))
  haveI : ∀ k, FiniteDimensional ℚ (M' k) := fun k => IntermediateField.finiteDimensional_sup _ _
  refine ⟨⨆ k, M' k, IntermediateField.finiteDimensional_iSup_of_finite, fun α => ?_⟩
  rw [taylor_lin r F hF α]
  refine sum_mem fun k _ => mul_mem ?_ ?_
  · exact le_iSup M' k (le_sup_right (a := M k) (b := IntermediateField.adjoin ℚ {r k})
      (IntermediateField.subset_adjoin ℚ {r k} (Set.mem_singleton _)))
  · exact le_iSup M' k (le_sup_left (a := M k) (b := IntermediateField.adjoin ℚ {r k}) (hC k α))

theorem algCoef_const_mul (c : ℂ) (hc : c ∈ Qbar) (G : VC D N N' → ℂ) (hG : ∀ m : ℕ, ContDiff ℂ m G)
    (hA : AlgCoef D G) : AlgCoef D (fun z => c * G z) := by
  have h := algCoef_sum (ι := Unit) (fun _ => c) (fun _ => hc) (fun _ => G) (fun _ => hG) (fun _ => hA)
  simpa using h

theorem U_contDiff (T : Tor D) (x : VC D N N') {G : VC D N N' → ℂ} (hG : ∀ m : ℕ, ContDiff ℂ m G) (m : ℕ) :
    ContDiff ℂ m (U D T x G) := by
  have h1 : ContDiff ℂ m (fun z : VC D N N' => G (z + x)) := (hG m).comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℂ m (fun z : VC D N N' => Formalism.MainNotions.TaylorLogMetric.Hf D T z x) := by
    unfold Formalism.MainNotions.TaylorLogMetric.Hf
    fun_prop
  exact h1.mul (((contDiff_const.mul h2).sub contDiff_const).cexp)

theorem sqrt_inv_mem_Qbar (n : ℕ) : (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) ∈ Qbar := by
  rw [Complex.ofReal_inv]
  refine inv_mem (mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2) two_pos ?_))
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n), Complex.ofReal_natCast]
  exact mem_algebraicClosure_iff.1 (natCast_mem Qbar n)

theorem al_mem_Qbar (T : Tor D) (x : VC D N N') : al D T x ∈ Qbar := by
  rcases al_sign D T x with h | h <;> rw [h]
  · exact one_mem _
  · exact neg_mem (one_mem _)

theorem algCoef_Iop (T : Tor D) (La₁ La₂ : AddSubgroup (VC D N N')) [Finite (La₂ ⧸ La₁.addSubgroupOf La₂)]
    (G : VC D N N' → ℂ) (hG : ∀ m : ℕ, ContDiff ℂ m G) (hA : ∀ x ∈ La₂, AlgCoef D (U D T x G)) :
    AlgCoef D (Iop D T La₁ La₂ G) := by
  haveI := Fintype.ofFinite (La₂ ⧸ La₁.addSubgroupOf La₂)
  have e : Iop D T La₁ La₂ G = fun z => ∑ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      ((((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℝ) : ℂ) * al D T ((Quotient.out q : La₂) : VC D N N')) *
        U D T ((Quotient.out q : La₂) : VC D N N') G z := by
    funext z
    simp only [Iop, finsum_eq_sum_of_fintype, Finset.mul_sum, mul_assoc, Complex.ofReal_inv]
  rw [e]
  exact algCoef_sum _ (fun q => mul_mem (sqrt_inv_mem_Qbar _) (al_mem_Qbar T _)) _
    (fun q m => U_contDiff T _ hG m) (fun q => hA _ (Quotient.out q).2)

end Coef

theorem chi_mem_Qbar {D : D7} (χ : IdE D → ℂ) (hχ : IsChi D χ) {𝔞 : IdE D} (ha : N1 D 𝔞) : χ 𝔞 ∈ Qbar := by
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  have h1 := hχ.2 ⟨z, hzu⟩
  simp only at h1
  rw [← hspan, CU.chi_pow D χ hχ ha k hk] at h1
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := k) (by omega) ?_)
  rw [h1]
  refine mem_algebraicClosure_iff.1 (prod_mem fun τ _ => inv_mem ?_)
  refine mem_algebraicClosure_iff.2 ?_
  have hz' : IsIntegral ℚ z := Algebra.IsIntegral.isIntegral z
  exact (hz'.map (embT D τ).toRatAlgHom).isAlgebraic

theorem LinkVecCoef_of (h0 : ZeroAlg) (hT : TransAlg) : LinkVecCoef := by
  intro D cc hcc δ hδ B χ hχ N N' L L' hA
  have hδ0 : δ ≠ 0 := base_linkage_nonempty D cc δ B
  have hS : B.StdOK := standard_basis_ok_link D cc hcc δ hδ B
  have hL : B.LatAll := B.latAll hcc hδ hδ0
  have hA0 : admitted D N N' (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := Base.first_coordinate_admissible hA
  have hA1 : admitted D N N' L (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := Base.isAdmissible_flagPair_of_unitriangular_left_automorphism hA

  have z0 : AlgCoef D (B.thZero N N') := h0 D cc hcc δ hδ B N N' hA.1 hA.2.1
  have z0T := B.thZeroMem hS N N'
  have z0m : B.thZero N N' ∈ Th D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of D B.tor _ _ z0T
  have z0s : ∀ m : ℕ, ContDiff ℂ m (B.thZero N N') := fun m => z0T.1.contDiff

  haveI := IO.La_index_finite cc hcc δ (Formalism.MainNotions.StandardLatticesGL3.stdL D N) L (Formalism.MainNotions.StandardLatticesGL3.stdL D N') (Formalism.MainNotions.StandardLatticesGL3.stdL D N') hA0 hA1
  have h1 : AlgCoef D (B.thHalf N N' L) :=
    algCoef_Iop _ _ _ _ z0s fun x hx => hT D cc hcc δ hδ N N' _ _ _ _ hA0 hA1 _ z0m z0 x hx
  have h1T := B.thHalf_mem hS hL hA
  have h1m : B.thHalf N N' L ∈ Th D (tor0 D cc δ) L (Formalism.MainNotions.StandardLatticesGL3.stdL D N') := mem_ThSp_of D B.tor _ _ h1T
  have h1s : ∀ m : ℕ, ContDiff ℂ m (B.thHalf N N' L) := fun m => h1T.1.contDiff

  haveI := IO.La_index_finite cc hcc δ L L (Formalism.MainNotions.StandardLatticesGL3.stdL D N') L' hA1 hA
  have h2 : AlgCoef D (B.thMoved N N' L L') :=
    algCoef_Iop _ _ _ _ h1s fun x hx => hT D cc hcc δ hδ N N' _ _ _ _ hA1 hA _ h1m h1 x hx
  have h2s : ∀ m : ℕ, ContDiff ℂ m (B.thMoved N N' L L') := fun m => (B.thMoved_mem hL z0T hA).1.contDiff

  have hd := relative_determinant_norm_one D
  have c1 := chi_mem_Qbar χ hχ (hd N _ L hA.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hA.2.2.1)
  have c2 := chi_mem_Qbar χ hχ (hd N' _ L' hA.2.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hA.2.2.2)
  have hc : Base.chiFac χ N N' L L' ∈ Qbar := mul_mem (zpow_mem c1 _) (zpow_mem c2 _)
  exact algCoef_const_mul _ hc _ h2s h2

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

end
