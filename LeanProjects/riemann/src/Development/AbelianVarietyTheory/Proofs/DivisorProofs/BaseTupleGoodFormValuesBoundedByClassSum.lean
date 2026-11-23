import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefAtOfPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFormCoordinatesCoeffMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActsUnitarily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqBotOrTopOfTensor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FormNorm

open GlobalTheory.CoefModel
open scoped ComplexOrder

private theorem schur_form {H Γ : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : Γ → Module.End ℂ H) (hu : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hirr : ∀ U : Submodule ℂ H, (∀ g, ∀ x ∈ U, ρ g x ∈ U) → U = ⊥ ∨ U = ⊤)
    (B : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (ρ g y) = B x y) : ∃ c : ℂ, ∀ x y, B x y = c * inner ℂ x y := by
  classical
  let b := stdOrthonormalBasis ℂ H
  let T : Module.End ℂ H := ∑ i, (B (b i)).smulRight (b i)
  have hT : ∀ x y, inner ℂ x (T y) = B x y := by
    intro x y
    conv_rhs => rw [← b.sum_repr' x]
    simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, inner_sum, inner_smul_right, map_sum, LinearMap.map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, inner_conj_symm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hs : ∀ g, Function.Surjective (ρ g) := fun g => by
    refine LinearMap.injective_iff_surjective.1 ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    have := hu g x x
    rw [hx, inner_zero_left] at this
    exact inner_self_eq_zero.1 this.symm
  have hc : ∀ g y, T (ρ g y) = ρ g (T y) := fun g y => by
    refine ext_inner_left ℂ fun x => ?_
    obtain ⟨x, rfl⟩ := hs g x
    rw [hT, hB, hu, hT]
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue T
  rcases hirr (Module.End.eigenspace T c) (fun g x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hc, hx, map_smul]) with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc')
  · refine ⟨c, fun x y => ?_⟩
    have hy : y ∈ Module.End.eigenspace T c := by rw [h]; trivial
    rw [← hT, Module.End.mem_eigenspace_iff.1 hy, inner_smul_right]

variable {ι : Type} [Fintype ι] {n : ℕ}

private theorem posDef_one : ∀ τ : ι, ((fun _ => 1 : ι → Matrix (Fin n) (Fin n) ℂ) τ).PosDef := fun _ => Matrix.PosDef.one

private theorem schur_vv (lam : ι → DomWeight n) (B : VV ℂ lam →ₗ⋆[ℂ] VV ℂ lam →ₗ[ℂ] ℂ)
    (hB : ∀ g : ι → GL (Fin n) ℂ, (∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 * g τ = 1) →
      ∀ x y, B (rhoK lam g x) (rhoK lam g y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = c * pairK lam (fun _ => 1) x y := by
  haveI : FiniteDimensional ℂ (Hilb lam posDef_one) := Module.Finite.of_basis (bVV ℂ lam)
  haveI : Nontrivial (Hilb lam posDef_one) := Formalism.L2.Col.VV_nontrivial ℂ lam
  exact schur_form (H := Hilb lam posDef_one)
    (Γ := {g : ι → GL (Fin n) ℂ // ∀ τ, (g τ : Matrix (Fin n) (Fin n) ℂ)ᴴ * 1 * g τ = 1})
    (fun g => rhoK lam g.1) (fun g x y => pairInv ℂ ι n lam _ g.1 g.2 x y)
    (fun U hU => eq_bot_or_top lam posDef_one U fun g hg => hU ⟨g, hg⟩) B fun g => hB g.1 g.2

private theorem ext_mem_del (lam : ι → DomWeight n) : Formalism.L2.Col.extVV ℚ lam ∈ delStd ℚ lam := by
  refine Submodule.subset_span ⟨fun τ => extremal ℚ n (lam τ), fun τ => ⟨extremal (𝓞 ℚ) n (lam τ),
    Submodule.subset_span ⟨[], rfl⟩, ?_⟩, rfl⟩
  exact Formalism.GradedWeylDivisibility.lclosedeq_hw_map (algebraMap (𝓞 ℚ) ℚ) le_rfl _

private theorem funEquiv_mapVV {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n) (F : VV K lam) :
    funEquiv lam (mapVV φ lam F) = mapVV φ _ (funEquiv lam F) :=
  ((isFunForm_iff_eq lam _ _).1 (GlobalTheory.BrRat.isFunForm_map φ lam (isFunForm_funEquiv lam F))).symm

private theorem pairK_one_nonneg (lam : ι → DomWeight n) (x : VV ℂ lam) : 0 ≤ pairK lam (fun _ => 1) x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (GlobalTheory.CoefModel.pairK_pos lam posDef_one x hx).le

private theorem funEquiv_le (lam : ι → DomWeight n) (x : VV ℂ lam) :
    (pairK (fun τ => (lam τ).dual) (fun _ => 1) (funEquiv lam x) (funEquiv lam x)).re ≤ (pairK lam (fun _ => 1) x x).re := by
  obtain ⟨c, hc⟩ := schur_vv lam (((pairK (K := ℂ) (fun τ => (lam τ).dual) (fun _ => 1)).comp
      (funEquiv (K := ℂ) lam).toLinearMap).compl₂ (funEquiv (K := ℂ) lam).toLinearMap) (fun g hg x y => by
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, funEquiv_rhoK]
    refine pairInv ℂ ι n _ _ _ (fun τ => ?_) _ _
    have := invTr_unitary (hg τ)
    rwa [inv_one, Matrix.transpose_one] at this)
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] at hc
  let e : VV ℚ (fun τ => (lam τ).dual) := ⟨_, Formalism.L2.Col.extVV_mem ℚ _⟩
  let f : VV ℚ lam := (funEquiv lam).symm e
  have hfe : funEquiv lam f = e := LinearEquiv.apply_symm_apply _ _
  have hd : f.1 ∈ delStd ℚ lam := (funEquiv_mem_delStd lam f).2 (by rw [hfe]; exact ext_mem_del _)
  have hn : f.1 ∈ nabStd ℚ lam := delStd_le_nabStd ℚ lam hd
  obtain ⟨z, hz⟩ := (GlobalTheory.StdDual.std_dual ℚ ι n lam f.1 f.2).1.2 hn f.1 hd
  have hφ : ∀ a : ℚ, algebraMap ℚ ℂ (star a) = starRingEnd ℂ (algebraMap ℚ ℂ a) := fun a => by simp
  have hone : (fun τ : ι => ((fun _ => 1 : ι → Matrix (Fin n) (Fin n) ℚ) τ).map (algebraMap ℚ ℂ)) = fun _ => 1 :=
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : pairK lam (fun _ => 1) (mapVV (algebraMap ℚ ℂ) lam f) (mapVV (algebraMap ℚ ℂ) lam f) =
      ((Rat.ringOfIntegersEquiv z : ℤ) : ℂ) := by
    rw [← hone, pairK_mapVV _ _ hφ, pairK_apply, ← hz]
    simp [← Rat.ringOfIntegersEquiv_apply_coe]
  have h2 : pairK (fun τ => (lam τ).dual) (fun _ => 1) (mapVV (algebraMap ℚ ℂ) _ e) (mapVV (algebraMap ℚ ℂ) _ e) = 1 := by
    rw [← hone, pairK_mapVV _ _ hφ, pairK_apply]
    have := Formalism.L2.DIV.pairingExtremal_holds ℚ ι n (fun τ => (lam τ).dual) (fun _ => 1) 1 (fun τ => by simp)
    rw [show actP (fun τ => (lam τ).dual) (1 : ι → GL (Fin n) ℚ) = 1 from (rhoP _).map_one] at this
    rw [show pairP (fun τ => (lam τ).dual) (fun _ => 1) e.1 e.1 = 1 from this, map_one]
  have h3 := hc (mapVV (algebraMap ℚ ℂ) lam f) (mapVV (algebraMap ℚ ℂ) lam f)
  rw [funEquiv_mapVV, hfe, h2, h1] at h3
  set N : ℤ := Rat.ringOfIntegersEquiv z
  have hN0 : (0 : ℂ) ≤ N := h1 ▸ pairK_one_nonneg _ _
  have hN1 : N ≠ 0 := by
    rintro h
    simp [h] at h3
  have hN2 : (1 : ℝ) ≤ N := by
    have : (0 : ℝ) ≤ N := by simpa using (Complex.le_def.1 hN0).1
    have h0 : 0 ≤ N := by exact_mod_cast this
    exact_mod_cast (by omega : 1 ≤ N)
  have hc' : c = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    exact eq_inv_of_mul_eq_one_left h3.symm
  rw [hc, hc', Complex.re_ofReal_mul]
  exact mul_le_of_le_one_left (Complex.le_def.1 (pairK_one_nonneg lam x)).1 (inv_le_one_of_one_le₀ hN2)

private theorem pairK_neg_one (lam : ι → DomWeight n) : ∃ c : ℂ, c * c = 1 ∧
    ∀ x y : VV ℂ lam, pairK lam (fun _ => -1) x y = c * pairK lam (fun _ => 1) x y := by
  obtain ⟨c, hc⟩ := schur_vv lam (pairK lam fun _ => -1) fun g hg x y => pairInv ℂ ι n lam _ g (fun τ => by
    have := hg τ
    rw [Matrix.mul_one] at this
    simp [this]) x y
  refine ⟨c, ?_, hc⟩
  let m : ι → GL (Fin n) ℂ := fun _ => -1
  have ht : ∀ x y : VV ℂ lam, pairK lam (fun _ => 1) x (rhoK lam m y) = pairK lam (fun _ => -1) x y := fun x y => by
    have := pairTransport ℂ ι n lam (fun _ => 1) 1 m x.1 y.1
    rw [show actP lam (1 : ι → GL (Fin n) ℂ) = 1 from (rhoP _).map_one] at this
    simpa [pairK_apply, rhoK_coe, m] using this
  obtain ⟨x, hx⟩ := exists_ne (0 : VV ℂ lam)
  have h1 := ht x (rhoK lam m x)
  rw [← Module.End.mul_apply, ← map_mul, show m * m = 1 from
    funext fun _ => by simp [m], map_one, Module.End.one_apply, hc, ht, hc, ← mul_assoc] at h1
  have h2 := (GlobalTheory.CoefModel.pairK_pos lam posDef_one x hx).ne'
  exact (mul_left_eq_self₀.1 h1.symm).resolve_right h2

section Idem

variable {G : Type} [Group G] [Fintype G]

private theorem coeff_gaStar (a : MonoidAlgebra ℂ G) (u : G) : (gaStar a).coeff u = star (a.coeff u⁻¹) := by
  classical
  unfold gaStar
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single u⁻¹]
  · simp
  · intro s _ hs
    rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne]
    rintro rfl
    exact hs (inv_inv s).symm
  · simp

private theorem gaStar_idem (a : MonoidAlgebra ℂ G) (hi : a * a = a) (hc : ∀ b, b * a = a * b) : gaStar a = a := by
  have hss : gaStar (gaStar a) = a := by
    ext u
    simp [coeff_gaStar]
  have hf : gaStar a * gaStar a = gaStar a := by rw [← gaStar_mul, hi]
  have hsub : gaStar (a - a * gaStar a) = gaStar a - a * gaStar a := by
    have : gaStar (a * gaStar a) = a * gaStar a := by rw [gaStar_mul, hss]
    conv_rhs => rw [← this]
    ext u
    simp [coeff_gaStar]
  have h0 : gaStar (a - a * gaStar a) * (a - a * gaStar a) = 0 := by
    have e1 : gaStar a * (a * gaStar a) = a * gaStar a := by rw [← mul_assoc, hc, mul_assoc, hf]
    have e2 : a * gaStar a * a = a * gaStar a := by rw [mul_assoc, hc, ← mul_assoc, hi]
    rw [hsub, sub_mul, mul_sub, mul_sub, e1, e2, mul_assoc, e1, ← mul_assoc, hi, hc]
    simp
  have h1 : a - a * gaStar a = 0 := by
    generalize a - a * gaStar a = x at h0
    have := congrArg (fun y : MonoidAlgebra ℂ G => y.coeff 1) h0
    simp only [coeff_mul_fin, coeff_gaStar, mul_one, MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    rw [Finset.sum_eq_zero_iff_of_nonneg fun s _ => star_mul_self_nonneg _] at this
    ext u
    have h := this u⁻¹ (Finset.mem_univ _)
    simpa using h
  rw [h1, gaStar_zero] at hsub
  rw [sub_eq_zero] at h1
  exact (sub_eq_zero.1 hsub.symm).trans h1.symm

private theorem conj_of_idem (c : G → ℂ) (hi : ∀ u, ∑ s, c s * c (s⁻¹ * u) = c u) (hc : ∀ g h, c (g * h) = c (h * g)) (g : G) :
    star (c g) = c g⁻¹ := by
  let a : MonoidAlgebra ℂ G := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c)
  have ha : ∀ u, a.coeff u = c u := fun _ => rfl
  have h := gaStar_idem a (by ext u; simp only [coeff_mul_fin, ha, hi]) fun b => by
    ext u
    simp only [coeff_mul_fin, ha]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft u)) _ _ fun s => ?_
    simp [hc u, mul_comm]
  have := congrArg (fun y : MonoidAlgebra ℂ G => y.coeff g⁻¹) h
  simpa only [coeff_gaStar, ha, inv_inv] using this

private theorem idem_mem_cmMax {K : Type} [Field K] [StarRing K] (σ₀ : K →+* ℂ) (hσ : ∀ a, σ₀ (star a) = starRingEnd ℂ (σ₀ a))
    (c : G → K) (hi : ∀ u, ∑ s, σ₀ (c s) * σ₀ (c (s⁻¹ * u)) = σ₀ (c u)) (hc : ∀ g h, σ₀ (c (g * h)) = σ₀ (c (h * g))) (g : G) :
    c g ∈ Formalism.DivisionValues.cmMax K := by
  intro σ
  have h1 : star (c g) = c g⁻¹ := σ₀.injective (by rw [hσ]; exact conj_of_idem (fun g => σ₀ (c g)) hi hc g)
  have hi' : ∀ u, ∑ s, c s * c (s⁻¹ * u) = c u := fun u => σ₀.injective (by simpa using hi u)
  rw [h1]
  exact (conj_of_idem (fun g => σ (c g)) (fun u => by rw [← hi' u]; simp) (fun g h => congrArg σ (σ₀.injective (hc g h))) g).symm

end Idem

section ClassSum

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces Formalism.DivisionValues

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ)

private theorem pairAt_sesq {W : Type} [AddCommGroup W] [Module ℂ W] (j : S.V →ₛₗ[σ] W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (h : ∀ i k, B (j (S.bV i)) (j (S.bV k)) = σ (S.pair (S.bV i) (S.bV k))) (x y : S.V) : pairAt S σ x y = B (j x) (j y) := by
  conv_rhs => rw [← S.bV.sum_repr x, ← S.bV.sum_repr y]
  simp only [pairAt, map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, h,
    CSD.gramV, Matrix.of_apply, RingHom.id_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem csumAt_sum {I : Type} [Fintype I] (a : I → K) (f : I → S.Cl → S.V) :
    csumAt S σ (∑ i, a i • f i) (∑ i, a i • f i) = ∑ i, ∑ k, starRingEnd ℂ (σ (a i)) * csumAt S σ (f i) (f k) * σ (a k) := by
  simp only [csumAt, pairAt, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, smul_eq_mul,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  conv_rhs =>
    rw [Finset.sum_comm]
    enter [2, k]
    rw [Finset.sum_comm]
    enter [2, c]
    rw [Finset.sum_comm]
    enter [2, p]
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem herm_eq_csumAt (hb : S.HasRatBasis) (z : Fin S.dim → K) :
    star (fun i => σ (z i)) ⬝ᵥ (S.H.map σ).mulVec (fun i => σ (z i)) =
      csumAt S σ (S.basis.equivFun.symm z : S.Forms) (S.basis.equivFun.symm z : S.Forms) := by
  have hr : ∀ i, S.IsRat (S.basis i : S.Cl → S.V) := by
    have : S.basis = hb.choose := by unfold CSD.basis; exact dif_pos hb
    rw [this]
    exact hb.choose_spec
  rw [Module.Basis.equivFun_symm_apply, Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  rw [csumAt_sum]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, CSD.H, Matrix.of_apply, Pi.star_apply,
    GlobalTheory.FiniteGroupUnitary.csumAt_eq_of_rat S σ _ _ (hr _), mul_assoc]
  rfl

private theorem herm_cut {d m : ℕ} (H : Matrix (Fin d) (Fin d) K) (E : Matrix (Fin d) (Fin m) K) (hE : ∀ i j, E i j ∈ cmMax K)
    (N : ℕ) (x : Fin m → K) :
    star (fun i => σ (x i)) ⬝ᵥ (((N : K)⁻¹ • (Eᴴ * H * E)).map σ).mulVec (fun i => σ (x i)) =
      (N : ℂ)⁻¹ * (star (fun i => σ (E.mulVec x i)) ⬝ᵥ (H.map σ).mulVec (fun i => σ (E.mulVec x i))) := by
  have h1 : (Eᴴ).map σ = (E.map σ)ᴴ := by
    ext i j
    exact hE j i σ
  have h2 : ((N : K)⁻¹ • (Eᴴ * H * E)).map σ = (N : ℂ)⁻¹ • ((E.map σ)ᴴ * H.map σ * E.map σ) := by
    have h4 : (Eᴴ * H * E).map σ = (E.map σ)ᴴ * H.map σ * E.map σ := by rw [Matrix.map_mul, Matrix.map_mul, h1]
    rw [← h4]
    generalize Eᴴ * H * E = M
    ext i j
    simp
  have h3 : (fun i => σ (E.mulVec x i)) = (E.map σ).mulVec fun i => σ (x i) := funext fun i => RingHom.map_mulVec σ E x i
  rw [h2, h3, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem term_le (f : S.Cl → S.V) (h : ∀ c, 0 ≤ (pairAt S σ (f c) (f c)).re) :
    0 ≤ (csumAt S σ f f).re ∧ ∀ c, (pairAt S σ (f c) (f c)).re ≤ (S.DGam : ℝ) * (csumAt S σ f f).re := by
  have e : (csumAt S σ f f).re = ∑ c, (S.wt c : ℝ)⁻¹ * (pairAt S σ (f c) (f c)).re := by
    unfold csumAt
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Complex.re_ofReal_mul]
    push_cast
    rfl
  have hp : ∀ c, 0 ≤ (S.wt c : ℝ)⁻¹ * (pairAt S σ (f c) (f c)).re := fun c => mul_nonneg (by positivity) (h c)
  have h0 : 0 ≤ (csumAt S σ f f).re := e ▸ Finset.sum_nonneg fun c _ => hp c
  refine ⟨h0, fun c => ?_⟩
  have hw : ∀ c, 0 < S.wt c := fun c => Fintype.card_pos
  have hD : S.wt c ≤ S.DGam := Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.2 fun c _ => (hw c).ne'))
    (Finset.dvd_lcm (Finset.mem_univ c))
  have h1 : (S.wt c : ℝ)⁻¹ * (pairAt S σ (f c) (f c)).re ≤ (csumAt S σ f f).re :=
    e ▸ Finset.single_le_sum (fun c _ => hp c) (Finset.mem_univ c)
  have hw' : (0 : ℝ) < S.wt c := by exact_mod_cast hw c
  rw [inv_mul_le_iff₀ hw'] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hD) h0)

end ClassSum

section Comparison₂

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces Formalism.DivisionValues Formalism.IndefR.Bridge

private theorem pairK_mapVV_rat {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) (hx : ∀ j, (bVV K lam).repr x j ∈ cmMax K) :
    pairK lam (fun τ => (G τ).map σ) (mapVV σ lam x) (mapVV σ lam y) = σ (pairK lam G x y) := by
  have hb : ∀ j, pairK lam (fun τ => (G τ).map σ) (mapVV σ lam (bVV K lam j)) (mapVV σ lam y) =
      σ (pairK lam G (bVV K lam j) y) := fun j => by
    obtain ⟨P, hP⟩ := bVVfun_int K lam j
    exact pairK_mapVV_int σ lam G _ y P ((bVV_coe _ lam j).trans hP)
  rw [← (bVV K lam).sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hb, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply (R := K), hx j σ]

private theorem pairAt_tie {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ₀ : K →+* ℂ)
    (hσ : ∀ a, σ₀ (star a) = starRingEnd ℂ (σ₀ a)) (hpos : ∀ x, 0 ≤ σ₀ (S.pair x x)) (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) K) (hG : (G = fun _ => 1) ∨ G = fun _ => -1) (e : S.V ≃ₗ[K] VV K lam)
    (hr : ∀ i j, (bVV K lam).repr (e (S.bV i)) j ∈ cmMax K) (hp : ∀ x x', pairK lam G (e x) (e x') = S.pair x x')
    (σ : K →+* ℂ) (x : S.V) :
    pairAt S σ x x = pairK lam (fun _ => 1) (mapVV σ lam (e x)) (mapVV σ lam (e x)) := by
  have key : ∀ φ : K →+* ℂ, pairAt S φ x x = pairK lam (fun τ => (G τ).map φ) (mapVV φ lam (e x)) (mapVV φ lam (e x)) := fun φ =>
    pairAt_sesq S φ ((mapVV φ lam).comp e.toLinearMap) _ (fun i k => by
      rw [← hp]
      exact pairK_mapVV_rat φ lam G _ _ (hr i)) x x
  rcases hG with rfl | rfl
  · rw [key]
    simp only [Matrix.map_one _ (map_zero σ) (map_one σ)]
  · obtain ⟨c, hc, h⟩ := pairK_neg_one lam
    have key' : ∀ φ : K →+* ℂ, pairAt S φ x x = c * pairK lam (fun _ => 1) (mapVV φ lam (e x)) (mapVV φ lam (e x)) := fun φ => by
      rw [key, ← h]
      simp only [Matrix.map_neg _ (map_neg φ), Matrix.map_one _ (map_zero φ) (map_one φ)]
    by_cases hx : x = 0
    · rw [key']
      simp [hx]
    have h0 : mapVV σ₀ lam (e x) ≠ 0 := fun h0 => hx (e.map_eq_zero_iff.1 (Subtype.ext
      (MvPolynomial.map_injective σ₀ σ₀.injective ((congrArg Subtype.val h0).trans (map_zero _).symm))))
    have h1 := GlobalTheory.CoefModel.pairK_pos lam posDef_one _ h0
    have h2 := hpos x
    rw [← pairAt_eq S σ₀ hσ, key'] at h2
    rcases mul_self_eq_one_iff.1 hc with rfl | rfl
    · rw [key', one_mul]
    · rw [neg_one_mul, Left.nonneg_neg_iff] at h2
      exact absurd h1 (not_lt_of_ge h2)

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}

private theorem rat_of_tie (l : LevDatG G) (P : ClassPres ι S σ₀ ρ l.J l.χ) {G₀ : Type} [Group G₀] [Fintype G₀]
    (act : Representation K G₀ S.Forms) (T : ActTie ι P l.Q l.ch act)
    (hσ : ∀ a : K, σ₀ (star a) = starRingEnd ℂ (σ₀ a)) (hch : ∀ q, ∃ n : ℕ, 0 < n ∧ l.ch q ^ n = 1)
    (hrat : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ₀ (c i) • P.coef (S.bV i)) :
    S.HasRatBasis ∧ S.ActRat act := by
  have hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ l.χ k ^ n = 1 := fun k => by rw [← l.ch_J]; exact hch _
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ₀ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hrat _ _ _ (fun m => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, fun g => (forms_rat S).2 (act g) hb fun f hf c i => ?_⟩
  obtain ⟨κ, hκ⟩ := T.red_surj g
  rw [← PresRat.mem_cmComplex_iff σ₀ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, T.act_eq g κ hκ]
  unfold g0Act
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨n, h0, h1⟩ := hch κ
  refine PresRat.cmComplex.mul_mem (PresRat.mem_cmComplex_of_pow h0 ?_) (PresRat.act_mem P hσ hχ hrat _ _ _ (hf _) i)
  rw [← Units.val_pow_eq_pow_val, inv_pow, h1, inv_one, Units.val_one]

private theorem ext_val {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ₀ ρ J χ) {X : Type} [AddCommGroup X] [Module K X]
    (c0 : X →ₛₗ[σ₀] W) (e : S.V → X) (he : ∀ x, P.coef x = c0 (e x)) (f : S.Forms) (g : G) (a : K)
    (ha : σ₀ a = (χ (P.decK g) : ℂ)) (v : X) (hv : c0 v = ρ (P.decG g) (c0 (e (f.1 (P.decC g))))) :
    P.extL f g = c0 (a • v) := by
  rw [map_smulₛₗ, ha, hv, ← he]
  rfl

end Comparison₂

section Value

variable {D : D7}

private theorem unit_map (σ : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * 1 * M = 1) :
    ((M.map (labLL D τ)).map σ)ᴴ * (M.map (labLL D τ)).map σ = 1 := by
  set φ : D.host.E →+* ℂ := σ.comp (labLL D τ) with hφ
  have hc : ∀ x, φ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = starRingEnd ℂ (φ x) := fun x => D.sp.cm.cmUnram.2.1 φ x
  have e : (M.map φ)ᴴ = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M).map φ := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    exact (hc _).symm
  show (M.map φ)ᴴ * M.map φ = 1
  rw [Matrix.mul_one] at h
  rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem pair_rhoV (σ : D.what₂.LL →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (g : GL (Fin n) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g.1 * 1 * g.1 = 1) (v : VV D.what₂.LL lam) :
    pairK lam (fun _ => 1) (mapVV σ lam (rhoV (labLL D) lam g v)) (mapVV σ lam (rhoV (labLL D) lam g v)) =
      pairK lam (fun _ => 1) (mapVV σ lam v) (mapVV σ lam v) := by
  rw [show mapVV σ lam (rhoV (labLL D) lam g v) = _ from mapVV_rhoK σ lam _ v]
  refine pairInv ℂ _ n lam _ _ (fun τ => ?_) _ _
  rw [Matrix.mul_one]
  exact unit_map σ τ _ h

private theorem pair_rhoVr (σ : D.what₂.LL →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (g : GL (Fin n) D.host.E)
    (h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) g.1 * 1 * g.1 = 1) (v : VV D.what₂.LL lam) :
    pairK lam (fun _ => 1) (mapVV σ lam (rhoVr (labLL D) lam g⁻¹ v)) (mapVV σ lam (rhoVr (labLL D) lam g⁻¹ v)) =
      pairK lam (fun _ => 1) (mapVV σ lam v) (mapVV σ lam v) := by
  rw [show mapVV σ lam (rhoVr (labLL D) lam g⁻¹ v) = _ from mapVV_rhoK σ lam _ v]
  refine pairInv ℂ _ n lam _ _ (fun τ => ?_) _ _
  have h4 : ((Formalism.UG.bc σ (invTrK (embGL (labLL D) g⁻¹) τ) : GL _ ℂ) : Matrix _ _ ℂ) = ((g.1.map (labLL D τ)).map σ)ᵀ := by
    rw [bc_coe, invTrK_coe, embGL_inv, inv_inv, embGL_coe]
    ext a b
    rfl
  have h5 := mul_eq_one_comm.1 (unit_map σ τ _ h)
  show (Formalism.UG.bc σ (invTrK (embGL (labLL D) g⁻¹) τ)).1ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) *
    (Formalism.UG.bc σ (invTrK (embGL (labLL D) g⁻¹) τ)).1 = 1
  rw [h4, Matrix.mul_one, conjTranspose_transpose', ← Matrix.transpose_mul, h5, Matrix.transpose_one]

private theorem value_le {N : ℕ} (h : N = n) (lam : D.what₂.Tau → DomWeight N) (lam' : D.what₂.Tau → DomWeight n)
    (hw : ∀ τ a, (lam' τ).w (Fin.cast h a) = (lam τ).w a) (σ : D.what₂.LL →+* ℂ) (v : VV D.what₂.LL lam) (V : VV ℂ lam')
    (hV : V.1 = MvPolynomial.rename (Prod.map id (Prod.map (Fin.cast h) (Fin.cast h))) (MvPolynomial.map D.what₂.embLL v.1))
    (fr : GL (Fin n) D.host.E) (hfr : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * 1 * fr.1 = 1) (B : ℝ)
    (hB : (pairK lam (fun _ => 1) (mapVV σ lam v) (mapVV σ lam v)).re ≤ B) :
    NrmLe (fun τ => (lam' τ).dual) σ (rhoVr (tauE D) _ fr⁻¹ (funOf lam' V)) B := by
  subst h
  have e : lam' = lam := funext fun τ => by
    have := hw τ
    generalize lam' τ = a at this
    generalize lam τ = b at this
    cases a
    cases b
    congr
    funext i
    exact this i
  subst e
  have hr : (Prod.map id (Prod.map (Fin.cast rfl) (Fin.cast rfl)) : D.what₂.Tau × Fin N × Fin N → _) = id := by
    funext x
    rfl
  rw [hr, MvPolynomial.rename_id_apply] at hV
  obtain rfl : V = mapVV D.what₂.embLL lam' v := Subtype.ext hV
  rw [(isFunForm_iff_eq _ _ _).1 ((SumModel.readOK lam').1 _), funEquiv_mapVV, TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.rhoVr_mapVV]
  refine ⟨_, rfl, ?_⟩
  unfold nrm
  rw [pair_rhoVr σ _ fr hfr, ← funEquiv_mapVV]
  exact (funEquiv_le _ _).trans hB

private theorem gram_one {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (Y : LSp D) (hY : Y = ⟨D.sp.X', Λ⟩)
    (h : D.sp.X'.gram = 1) : Y.sp.gram = 1 := by
  subst hY
  exact h

end Value

section Main

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAtAllPlaces Formalism.DivisionValues Formalism.IndefR.Bridge

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

private theorem idemOf_mem (h : R.grp_record) (g : Γ) : (idemOf A.X).coeff g ∈ cmMax D.what₂.LL := by
  obtain ⟨eR, -, -, he, -⟩ := h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Γ eR.toEquiv
  refine idem_mem_cmMax D.what₂.embLL D.starLL_cx _ (fun u => ?_) (fun g h => ?_) g
  · simp only [he]
    conv_rhs => rw [← Formalism.BasicNotions.Examples₂.NZ.idempotent_sum D.ntypes, coeff_mul_fin]
    exact Fintype.sum_equiv eR.toEquiv _ _ fun s => by simp
  · have := congrArg (fun y : MonoidAlgebra ℂ (G0g D.nd) => y.coeff (eR g))
      (Subalgebra.mem_center_iff.1 (Formalism.BasicNotions.Examples₂.NZ.idempotent_mem_center D.ntypes) (MonoidAlgebra.single (eR h)⁻¹ 1))
    simp only [MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_single_mul_apply, inv_inv, mul_one, one_mul] at this
    rw [he, he, map_mul eR, map_mul eR, this]

set_option maxHeartbeats 1600000 in
private theorem herm_eq (F : Face D A) (hc : GlobalTheory.Hk3.Core R F) (t : T) (σ : D.what₂.LL →+* ℂ)
    (x : Fin ((A.fam.R t).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL) :
    (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R t).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re =
      (csumAt (A.MtildeCSD t) σ (formOf F t x).1 (formOf F t x).1).re := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := hc.fam.tie
  obtain ⟨hb, hr⟩ := rat_of_tie (levEnv D.sp.X' R.βX (R.datXt t)) (R.B.R t).pres _ (R.B.R t).act_tie D.starLL_cx
    (GlobalTheory.FiniteGroupUnitary.levEnv_ch_pow _ _ _)
    (HeckeRational.action_rational D.sp.X' R.cX.coef (R.B.R t).pres (hT.coefR t) hT.mapR
      fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ HeckeRational.labLL_mem_cmMax g i j).1)
  obtain ⟨v0, hv0⟩ := GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩
  have hE : ∀ i j, (A.fam.R t).vE (A.fam.lvl F.P0 F.ψ0) i j ∈ cmMax D.what₂.LL :=
    image_idempotent_rational _ _ _ (gaMat_rat (A.MtildeCSD t) (A.leftGroupActionRight t) hr (goodAt A.X F.P0 F.ψ0) fun g => by
      unfold goodAt
      rw [coeff_mul_fin]
      exact (cmMax _).sum_mem fun s _ => (cmMax _).mul_mem (idemOf_mem hc.grp.record s)
        ((level_idempotent_spec _ v0 hv0 Γ F.P0 F.ψ0).1.rat _))
  have h1 := herm_cut σ (A.MtildeCSD t).H ((A.fam.R t).vE (A.fam.lvl F.P0 F.ψ0)) hE (Nat.card (A.fam.lvl F.P0 F.ψ0).P) x
  have h2 := herm_eq_csumAt (A.MtildeCSD t) σ hb (((A.fam.R t).vE (A.fam.lvl F.P0 F.ψ0)).mulVec x)
  have h3 : star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R t).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec (fun i => σ (x i)) =
      (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℂ)⁻¹ * csumAt (A.MtildeCSD t) σ (formOf F t x).1 (formOf F t x).1 :=
    h1.trans (congrArg _ h2)
  have hN : (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [h3, ← Complex.re_ofReal_mul, Complex.ofReal_natCast, mul_inv_cancel_left₀ hN]

set_option maxHeartbeats 1600000 in
private theorem value_nonneg_and_norm_bound (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (hS : HidaSetting large₂ R F) (t : T) (σ : D.what₂.LL →+* ℂ)
    (f : (A.MtildeCSD t).Forms) :
    0 ≤ (csumAt (A.MtildeCSD t) σ f.1 f.1).re ∧ ∀ y, NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC t (R.jX t f) y))
      (((A.MtildeCSD t).DGam : ℝ) * (csumAt (A.MtildeCSD t) σ f.1 f.1).re) := by
  obtain ⟨gram, c₀, c₁, hT, hco⟩ := ch.S.co_is
  have hc := hS.core
  have hg : D.sp.X'.gram = 1 := Matrix.ext fun i j => (hS.stdX.1 _ _).trans (by simp [Matrix.one_apply])
  obtain ⟨e, hr, he, hp, -⟩ := hT.coefR t
  have hG : (gramK (labLL D) gram = fun _ => 1) ∨ gramK (labLL D) gram = fun _ => -1 := by
    refine hT.gramR_eq.imp (fun h => ?_) fun h => ?_ <;> funext τ <;> rw [h, hg, gramK]
    · exact Matrix.map_one _ (map_zero _) (map_one _)
    · rw [Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)]
  have hpa := pairAt_tie (A.MtildeCSD t) D.what₂.embLL D.starLL_cx (fun x => by
    rw [← (R.B.R t).pres.coef_pair]
    exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ((R.B.R t).pres.coef x) ▸ by positivity) _ _ hG e hr hp σ
  obtain ⟨h0, hle⟩ := term_le (A.MtildeCSD t) σ f.1 fun c => by
    rw [hpa]
    exact (Complex.le_def.1 (pairK_one_nonneg _ _)).1
  refine ⟨h0, fun y => ?_⟩
  set P := (R.B.R t).pres
  obtain ⟨γE, hγ1, hγ2⟩ := (P.decG (toXf y)).2
  have hγ : IsRatMat D.sp.X' (P.decG (toXf y)) γE := hγ2.symm
  have hγu : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γE.1 * D.sp.X'.gram * γE.1 = D.sp.X'.gram := hγ1
  rw [hg] at hγu
  have i0 : Fin D.R.m := ⟨0, by have := D.R.two_le_m; omega⟩
  obtain ⟨a, ha⟩ := GlobalTheory.FormCoef.typeX_mem R t D.what₂.embLL.fieldRange (GlobalTheory.RationalValues.chiVal_of_chiW R hc.grp.chiW)
    (GlobalTheory.RationalValues.xiR_mem R hc.lev hc.fam.pl_onto hc.fam.muVal hT.ok i0 t) (P.decK (toXf y))
  obtain ⟨k, hk, hak⟩ := HeckeRational.levEnv_chi_pow D.sp.X' R.βX (R.datXt t) (P.decK (toXf y))
  have hak' : a ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, hak, map_one, Units.val_one])
  have hn : starRingEnd ℂ (σ a) * σ a = 1 := by
    rw [Complex.conj_mul', Complex.norm_eq_one_of_pow_eq_one (n := k) (by rw [← map_pow, hak', map_one]) hk.ne']
    simp
  have h1 : (R.HX t).e (R.jX t f) (toXf y) =
      c₀ (a • rhoV (labLL D) _ γE (e (f.1 (P.decC (toXf y))))) := by
    exact (congrFun (hc.models.jX t f) (toXf y)).trans
      (ext_val P c₀ _ he f (toXf y) a ha _ (hT.mapR.1 _ _ hγ _))
  have hw : ∀ τ a, (listedWt ch.G (.grid 0 D.R.m) τ).w (Fin.cast (rank_zero_m ch.G) a) =
      (Bridge.lamRdef (Ptw D) τ).w a := fun τ a => by
    change (wtOf _ (GlobalTheory.SignedHC.entries (parV D ch.sc.cGap 0 D.R.m τ))).w _ = _
    rw [parV_zero D ch.sc.cGap le_rfl τ]
    exact wtOf_entries_eq (rank_zero_m ch.G) (GlobalTheory.ForcedWeights.lamRForced D τ) a
  have hfr := ch.S.N.fr_on (.grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩
  rw [show (ch.G.V (.grid 0 D.R.m)).gram = 1 from gram_one _ (colY_m _) hg] at hfr
  refine value_le (rank_zero_m ch.G) _ _ hw σ (a • rhoV (labLL D) _ γE (e (f.1 (P.decC (toXf y))))) _
    (by rw [SumChoice.formC, h1, hco]) _ hfr _ ?_
  rw [map_smulₛₗ, LinearMap.map_smulₛₗ₂, map_smul, smul_smul, hn, one_smul, pair_rhoV σ _ _ hγu, ← hpa]
  exact hle _

end Main

end GlobalTheory.FormNorm

set_option maxHeartbeats 1600000 in
open GlobalTheory.FormNorm in
theorem _root_.GlobalTheory.T.baseTupleGoodForm_values_bounded_by_classSum : BigC fun {D} {_} _ _ {_} {_} {A} {_} _ _ _ {R} F ch _ _ => ∀ (σ : D.what₂.LL →+* ℂ) (x : Fin ((A.fam.R A.μ0).nV (A.fam.lvl F.P0 F.ψ0)) → D.what₂.LL),
  0 ≤ (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re ∧ ∀ y,
  NrmLe _ σ (rowVal ch.S.toGridChoice (ch.S.formC A.μ0 (R.jX A.μ0 (formOf F A.μ0 x)) y))
    ((Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ) * ((A.fam.R A.μ0).S.DGam : ℝ) *
      (star (fun i => σ (x i)) ⬝ᵥ (((A.fam.R A.μ0).HV (A.fam.lvl F.P0 F.ψ0)).map σ).mulVec fun i => σ (x i)).re) := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ x
  have h1 := herm_eq F s.core A.μ0 σ x
  obtain ⟨h2, h3⟩ := value_nonneg_and_norm_bound ch large₂ F s A.μ0 σ (formOf F A.μ0 x)
  rw [← h1] at h2 h3
  refine ⟨nonneg_of_mul_nonneg_right ?_ (a := _) (b := _) (show (0 : ℝ) < Nat.card (A.fam.lvl F.P0 F.ψ0).P from
    Nat.cast_pos.2 Nat.card_pos), fun y => ?_⟩
  · exact h2
  · rw [mul_comm (Nat.card (A.fam.lvl F.P0 F.ψ0).P : ℝ), mul_assoc]
    exact h3 y
