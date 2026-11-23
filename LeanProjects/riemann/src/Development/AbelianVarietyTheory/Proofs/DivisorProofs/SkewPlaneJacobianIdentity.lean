import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineToGAdDerivative
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsSecondKindFormPreservingGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieAlgebraVectorDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneStabilizerActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieAlgebraExpGeneratorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanOrbitExpEigenvectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureDiagonalisingBasisStatement

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.ThK.CuspTransfer.Smooth

theorem lie_frame : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (C : GL (Fin n) ℂ) (ε : Fin n → Bool),
    C.1ᴴ * A * C.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) → ∀ x : Fin n → ℂ, star x ⬝ᵥ A *ᵥ x = 0 →
    ∀ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * A + A * Z = 0 → ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * A + A * Y = 0 ∧
      ((C⁻¹).1 * Y * C.1)ᴴ = -((C⁻¹).1 * Y * C.1) ∧ ∃ l : ℂ, (Z - Y) *ᵥ x = l • x := by
  intro n A C ε hC x hx Z hZ
  have h1 : (C⁻¹).1ᴴ * C.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have h2 : C.1ᴴ * (C⁻¹).1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.inv_mul, Matrix.conjTranspose_one]
  have h2' : ∀ B : Matrix (Fin n) (Fin n) ℂ, (C⁻¹).1ᴴ * (C.1ᴴ * B) = B := fun B => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have key : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ((C⁻¹).1 * Y * C.1)ᴴ * (C.1ᴴ * A * C.1) + C.1ᴴ * A * C.1 * ((C⁻¹).1 * Y * C.1) =
      C.1ᴴ * (Yᴴ * A + A * Y) * C.1 := fun Y => by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, h2', Units.mul_inv_cancel_left, Matrix.mul_add, Matrix.add_mul]
  have hx' : C.1 *ᵥ ((C⁻¹).1 *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  obtain ⟨Y, l, hY1, hY2, hl⟩ := GlobalTheory.LieIwasawa.decomp n ε _ hC ((C⁻¹).1 *ᵥ x) (by
    rw [← Matrix.mulVec_mulVec, hx', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hx', hx])
    ((C⁻¹).1 * Z * C.1) (by rw [key, hZ, Matrix.mul_zero, Matrix.zero_mul])
  have e : (C⁻¹).1 * (C.1 * Y * (C⁻¹).1) * C.1 = Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Units.inv_mul_cancel_left]
  refine ⟨C.1 * Y * (C⁻¹).1, ?_, by rw [e, hY1], l, ?_⟩
  · have := key (C.1 * Y * (C⁻¹).1)
    rw [e, hY2] at this
    have h3 := congrArg (fun B => (C⁻¹).1ᴴ * B * (C⁻¹).1) this
    simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_assoc C.1ᴴ, h2', Units.mul_inv_cancel_right] at h3
    exact h3.symm
  · have := congrArg (C.1 *ᵥ ·) hl
    simp only [Matrix.mulVec_smul, hx', Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      Units.mul_inv, Matrix.mul_one, Units.mul_inv_cancel_left, Matrix.one_mulVec] at this
    simpa only [Matrix.mul_assoc] using this

theorem pi_exp {ι 𝔸 : Type} [Fintype ι] [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] (Y : ι → 𝔸) (i : ι) :
    NormedSpace.exp Y i = NormedSpace.exp (Y i) := by
  haveI : CompleteSpace 𝔸 := FiniteDimensional.complete ℝ _
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact Pi.coe_exp Y i

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (e : ℕ) (γ : Fin e → ℝ → GAd σ J)
      (Z : Fin e → InfinitePlace F → Matrix (Fin n) (Fin n) ℂ), (∀ j t, γ j t ∈ infPts σ J) →
      (∀ (j : Fin e) (t : ℝ) (w : InfinitePlace F), GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w (γ j t)) = NormedSpace.exp (t • Z j w)) →
      (∀ Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ, (∀ w, (Y w)ᴴ * J.map (τ w).1 + J.map (τ w).1 * Y w = 0) →
        Y ∈ Submodule.span ℝ (Set.range Z)) →
      ∀ (m : ℕ) (u : (Fin m → ℝ) → GAd σ J), GlobalTheory.Orb.IsSmoothRealFam u → ∀ t₀ : Fin m → ℝ, u t₀ = 1 →
      ∃ s : (Fin m → ℝ) → Fin e → ℝ, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s t₀ ∧
        ∀ᶠ t in 𝓝 t₀, u t = (List.ofFn fun j => γ j (s t j)).prod := by
  intro F E _ _ _ _ _ σ h n J _ τ e γ Z hγ hZ hspan m u hu t₀ h0
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  let ι : GAd σ J →* (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :=
    MonoidHom.pi fun w => (GlobalTheory.Orb.archMat σ J (τ w)).comp (projArch σ J w)
  have hι : ∀ g w, ι g w = GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w g) := fun _ _ => rfl
  let S : Set (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) := {X | ∀ w, (X w)ᴴ * J.map (τ w).1 * X w = J.map (τ w).1}
  have hS : ∀ g, ι g ∈ S := fun g w => (archEquiv J h (τ w) (projArch σ J w g)).2
  have hpe : ∀ (Y : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) w, NormedSpace.exp Y w = NormedSpace.exp (Y w) :=
    fun Y w => pi_exp Y w
  have hZ' : ∀ j (t : ℝ), NormedSpace.exp (t • Z j) = ι (γ j t) := fun j t => funext fun w => by
    rw [hpe, hι, hZ]; rfl
  obtain ⟨s, hs, hev⟩ := GlobalTheory.T.exists_lie_algebra_exp_generators (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) S
    (by
      simp only [S, Set.setOf_forall]
      exact isClosed_iInter fun w => isClosed_eq (((continuous_apply w).matrix_conjTranspose.matrix_mul
        continuous_const).matrix_mul (continuous_apply w)) continuous_const)
    (fun w => by simp)
    (fun a ha b hb w => by
      rw [Pi.mul_apply, Matrix.conjTranspose_mul]
      calc _ = (b w)ᴴ * ((a w)ᴴ * J.map (τ w).1 * a w) * b w := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [ha w, hb w])
    (fun Y hY w => by
      have h1 : (NormedSpace.exp (Y w))ᴴ * J.map (τ w).1 * NormedSpace.exp (Y w) = J.map (τ w).1 := hpe Y w ▸ hY w
      suffices (NormedSpace.exp ((-Y) w))ᴴ * J.map (τ w).1 * NormedSpace.exp ((-Y) w) = J.map (τ w).1 from
        (hpe (-Y) w).symm ▸ this
      have h2 : NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w) = 1 := by
        rw [Pi.neg_apply, ← Matrix.exp_add_of_commute _ _ (Commute.refl (Y w)).neg_right, add_neg_cancel,
          NormedSpace.exp_zero]
      calc _ = (NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w))ᴴ * J.map (τ w).1 *
            (NormedSpace.exp (Y w) * NormedSpace.exp ((-Y) w)) := by
            conv_lhs => rw [← h1]
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [h2]; simp)
    e Z (fun j t => hZ' j t ▸ hS _)
    (fun Y hY => hspan Y fun w => GlobalTheory.ClosedMatGroup.skew_of_exp_smul_mem _ _ fun t => by
      have h1 : (NormedSpace.exp ((t • Y) w))ᴴ * J.map (τ w).1 * NormedSpace.exp ((t • Y) w) = J.map (τ w).1 :=
        hpe (t • Y) w ▸ hY t w
      exact h1)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => ι (u t) := contDiff_pi.2 fun w => by
    let T : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap
    exact T.contDiff.comp (f := fun t i j => GlobalTheory.Orb.archMat σ J (τ w) (projArch σ J w (u t)) i j)
      (contDiff_pi.2 fun i => contDiff_pi.2 fun j => hu.2 w (τ w) i j)
  have h1 : ι (u t₀) = 1 := by rw [h0, map_one]
  refine ⟨fun t => s (ι (u t)), (h1 ▸ hs).comp t₀ hc.contDiffAt, ?_⟩
  have ht : Tendsto (fun t => ι (u t)) (𝓝 t₀) (𝓝 1) := h1 ▸ hc.continuous.tendsto t₀
  filter_upwards [ht.eventually hev] with t ht
  have h2 : ι (u t) = ι (List.ofFn fun j => γ j (s (ι (u t)) j)).prod := by
    rw [map_list_prod, List.map_ofFn]
    exact (ht (hS _)).trans (congrArg (fun f => (List.ofFn f).prod) (funext fun j => hZ' j _))
  refine ext_inf_fin σ J (GInf_ext σ J fun w => ?_) ?_
  · rw [projInfArch_projInf, projInfArch_projInf]
    exact (GlobalTheory.Orb.isEmbedding_archMat J h (τ w)).injective (congrFun h2 w)
  · rw [hu.1, eq_comm, ← mem_infPts]
    refine list_prod_mem fun z hz => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hγ j _

theorem map_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
    (φ : AF F →ₐ[F] R) {n n₁ : ℕ} {A : Matrix (Fin n₁) (Fin n) E} {B : Matrix (Fin n) (Fin n₁) E} (hAB : A * B = 1)
    {g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} (hg : g.map (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = 1) :
    (GlobalTheory.SiegelSet.adMat F A * g * GlobalTheory.SiegelSet.adMat F B).map
      (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom = 1 := by
  rw [Matrix.map_mul, Matrix.map_mul, hg, Matrix.mul_one, ← Matrix.map_mul, ← Matrix.map_mul, hAB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.SiegelSet (IsRealLine)
open GlobalTheory.Orb (archMat IsSmoothRealFam)

namespace GlobalTheory.ThK.CuspTransfer.Smooth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem contDiff_of_oneParam {f : ℝ → ℂ} (hc : Continuous f) (h0 : f 0 = 1) (hm : ∀ s t, f (s + t) = f s * f t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  obtain ⟨Y, hY⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => (Matrix.diagonal fun _ : Fin 1 => f t)) (Continuous.matrix_diagonal (continuous_pi fun _ => hc))
    (by simp [h0]) (fun s t => by simp [hm, Matrix.diagonal_mul_diagonal])
  have h := GlobalTheory.Orb.contDiff_exp_smul_entry Y 0 0
  simp only [← hY, Matrix.diagonal_apply_eq] at h
  exact h

theorem line_fam (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : IsSmoothRealFam γ ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  choose y e1 e2 using hγ
  obtain rfl : γ = fun t => embArch σ J w (y t) := funext e1
  exact GlobalTheory.Orb.isSmoothRealFam_embArch h τ fun i j => by
    simp only [e2]; exact GlobalTheory.Orb.contDiff_exp_smul_entry Z i j

theorem line_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have := GlobalTheory.SiegelSet.isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

omit [NumberField E] in

theorem fam_translate {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {u : P → GAd σ J} (hu : IsSmoothRealFam u)
    {a b : GAd σ J} (hab : projFin σ J (a * b) = 1) : IsSmoothRealFam fun t => a * u t * b := by
  refine ⟨fun t => by rw [map_mul, map_mul, hu.1, mul_one, ← map_mul, hab], fun w τ i j => ?_⟩
  simp only [map_mul, Matrix.mul_apply]
  exact ContDiff.sum fun k _ => (ContDiff.sum fun l _ => contDiff_const.mul (hu.2 w τ l k)).mul contDiff_const

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_conj_unitary (C : GL (Fin n) ℂ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : ((C⁻¹).1 * Y * C.1)ᴴ = -((C⁻¹).1 * Y * C.1)) (t : ℝ) :
    ((C⁻¹).1 * NormedSpace.exp (t • Y) * C.1)ᴴ * ((C⁻¹).1 * NormedSpace.exp (t • Y) * C.1) = 1 := by
  have e : (C⁻¹).1 * NormedSpace.exp (t • Y) * C.1 = NormedSpace.exp (t • ((C⁻¹).1 * Y * C.1)) := by
    rw [← Matrix.exp_units_conj', Matrix.mul_smul, Matrix.smul_mul]
  rw [e, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hY, smul_neg,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • ((C⁻¹).1 * Y * C.1))).neg_left, neg_add_cancel, NormedSpace.exp_zero]

def Gen {w : InfinitePlace F} (τ : EmbOver E w) (Z : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → GAd σ J) : Prop :=
  Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0 ∧ ∀ t : ℝ, ∃ y : GArch σ J w, γ t = embArch σ J w y ∧ archMat σ J τ y = NormedSpace.exp (t • Z)

theorem exists_gen (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0) : ∃ γ : ℝ → GAd σ J, Gen τ Z γ := by
  obtain ⟨γ, -, hγ⟩ := GlobalTheory.SiegelSet.exists_isRealLine h hJ τ hZ
  exact ⟨fun t => embArch σ J w (projArch σ J w (γ t)), hZ, fun t => ⟨_, rfl, hγ t⟩⟩

omit [NumberField E] in
theorem Gen.line {w : InfinitePlace F} {τ : EmbOver E w} {Z : Matrix (Fin n) (Fin n) ℂ} {γ : ℝ → GAd σ J}
    (h : Gen τ Z γ) : IsRealLine σ J γ := ⟨w, τ, Z, h.1, h.2⟩

omit [NumberField E] in
open Classical in
theorem Gen.arch {τ : ∀ w : InfinitePlace F, EmbOver E w} {w : InfinitePlace F} {Z : Matrix (Fin n) (Fin n) ℂ}
    {γ : ℝ → GAd σ J} (h : Gen (τ w) Z γ) (t : ℝ) : γ t ∈ infPts σ J ∧ ∀ v, archMat σ J (τ v) (projArch σ J v (γ t)) =
      NormedSpace.exp (t • (Pi.single w Z : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) v) := by
  obtain ⟨y, e1, e2⟩ := h.2 t
  refine ⟨mem_infPts.2 (by rw [e1, projFin_embArch]), fun v => ?_⟩
  by_cases e : v = w
  · subst e
    rw [e1, projArch_embArch_self, e2, Pi.single_eq_same]
  · rw [e1, projArch_embArch_ne σ J e, map_one, Pi.single_eq_of_ne e, smul_zero, NormedSpace.exp_zero]

theorem lie_split (h : IsCMExt F E σ) (hJ : IsHermND σ J) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : (fun i => σ (x i)) ⬝ᵥ J *ᵥ x = 0) {K' : Subgroup (GAd σ J)} (hK : GlobalTheory.UAut.IsMaxCpt σ J K') (k : GAd σ J)
    {w : InfinitePlace F} (τ : EmbOver E w) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ * J.map τ.1 + J.map τ.1 * Z = 0) :
    ∃ (Y : Matrix (Fin n) (Fin n) ℂ) (π κ : ℝ → GAd σ J), Gen τ (Z - Y) π ∧ Gen τ Y κ ∧
      (∀ t, ∃ a : AE F E, (matHom _ σ J (π t)).1 *ᵥ incV F x = a • incV F x) ∧ ∀ t, k⁻¹ * κ t * k ∈ K' := by
  obtain ⟨C, ε, hC, hCK⟩ := GlobalTheory.T.exists_signature_diagonalising_basis F E σ h n J hJ K' hK k w τ
  have hxx' : star (fun i => τ.1 (x i)) ⬝ᵥ J.map τ.1 *ᵥ (fun i => τ.1 (x i)) = 0 := by
    have := congrArg τ.1 hxx
    simpa [dotProduct, Matrix.mulVec, h.2.2.2] using this
  obtain ⟨Y, hY, hYC, l, hl⟩ := lie_frame n _ C ε hC _ hxx' Z hZ
  obtain ⟨π, hπ⟩ := exists_gen h hJ τ (Z := Z - Y) (by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, sub_add_sub_comm, hZ, hY, sub_zero])
  obtain ⟨κ, hκ⟩ := exists_gen h hJ τ hY
  refine ⟨Y, π, κ, hπ, hκ, fun t => ?_, fun t => ?_⟩
  · obtain ⟨y, e1, e2⟩ := hπ.2 t
    rw [e1]
    exact GlobalTheory.T.archimedean_orbit_exp_eigenvector F E σ h n J x hx w τ _ l hl t y e2
  · obtain ⟨y, e1, e2⟩ := hκ.2 t
    rw [e1]
    exact hCK y (by rw [e2]; exact exp_conj_unitary C hYC t)

theorem local_iwasawa (h : IsCMExt F E σ) (hJ : IsHermND σ J) {x : Fin n → E} (hx : x ≠ 0)
    (hxx : (fun i => σ (x i)) ⬝ᵥ J *ᵥ x = 0) {K' : Subgroup (GAd σ J)} (hK : GlobalTheory.UAut.IsMaxCpt σ J K') (k : GAd σ J)
    {m : ℕ} {u : (Fin m → ℝ) → GAd σ J} (hu : IsSmoothRealFam u) {t₀ : Fin m → ℝ} (h0 : u t₀ = 1) :
    ∃ (d : ℕ) (π κ : Fin d → ℝ → GAd σ J) (s s' : (Fin m → ℝ) → Fin d → ℝ),
      (∀ j, IsRealLine σ J (π j)) ∧ (∀ j, IsRealLine σ J (κ j)) ∧
      (∀ j t, ∃ a : AE F E, (matHom _ σ J (π j t)).1 *ᵥ incV F x = a • incV F x) ∧ (∀ j t, κ j t ∈ K') ∧
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s t₀ ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) s' t₀ ∧
      ∀ᶠ t in 𝓝 t₀, k * u t = (List.ofFn fun j => π j (s t j)).prod * (k * (List.ofFn fun j => κ j (s' t j)).prod) := by
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun _ => Classical.arbitrary _
  let T : Set (InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) :=
    {Y | ∃ w Z, Zᴴ * J.map (τ w).1 + J.map (τ w).1 * Z = 0 ∧ Y = Pi.single w Z}
  obtain ⟨f, hfT, hf, -⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ T
  choose w Z hZ hfZ using hfT
  choose Y π κ hπ hκ hπx hκK using fun j => lie_split h hJ hx hxx hK k (τ (w j)) (hZ j)
  obtain ⟨s, hs, hev⟩ := chart F E σ h n J hJ τ _ (Fin.append π κ)
    (Fin.append (fun j => Pi.single (w j) (Z j - Y j)) fun j => Pi.single (w j) (Y j))
    (fun j t => Fin.addCases (fun j => by simpa using ((hπ j).arch t).1) (fun j => by simpa only [Fin.append_right] using ((hκ j).arch t).1) j)
    (fun j t v => Fin.addCases (fun j => by simpa only [Fin.append_left] using ((hπ j).arch t).2 v)
      (fun j => by simpa only [Fin.append_right] using ((hκ j).arch t).2 v) j)
    (fun A hA => by
      have h1 : A ∈ Submodule.span ℝ T := by
        rw [← Finset.univ_sum_single A]
        exact sum_mem fun v _ => Submodule.subset_span ⟨v, A v, hA v, rfl⟩
      rw [← hf] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨j, rfl⟩
      rw [hfZ j, ← sub_add_cancel (Z j) (Y j), Pi.single_add]
      exact add_mem (Submodule.subset_span ⟨Fin.castAdd _ j, by simp⟩) (Submodule.subset_span ⟨Fin.natAdd _ j, Fin.append_right _ _ _⟩))
    m (fun t => k * u t * k⁻¹) (fam_translate hu (by simp)) t₀ (by simp [h0])
  refine ⟨_, π, fun j t => k⁻¹ * κ j t * k, fun t j => s t (Fin.castAdd _ j), fun t j => s t (Fin.natAdd _ j),
    fun j => (hπ j).line, fun j => GlobalTheory.EisCont.CentreFinite.isRealLine_conj h (hκ j).line k, hπx, hκK,
    contDiffAt_pi.2 fun j => contDiffAt_pi.1 hs _, contDiffAt_pi.2 fun j => contDiffAt_pi.1 hs _, hev.mono fun t ht => ?_⟩
  have hf : (fun j => Fin.append π κ j (s t j)) =
      Fin.append (fun j => π j (s t (Fin.castAdd _ j))) fun j => κ j (s t (Fin.natAdd _ j)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp only [Fin.append_left, Fin.append_right]
  rw [hf, List.ofFn_fin_append, List.prod_append, mul_inv_eq_iff_eq_mul] at ht
  have hc := map_list_prod (MulAut.conj k⁻¹) (List.ofFn fun j => κ j (s t (Fin.natAdd _ j)))
  rw [List.map_ofFn] at hc
  simp only [MulAut.conj_apply, inv_inv, Function.comp_def] at hc
  rw [ht, ← hc]
  group

theorem contDiff_list_prod {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ∀ (d : ℕ) (f : Fin d → X → ℂ), (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j)) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s => (List.ofFn fun j => f j s).prod := fun d f hf => by
  simp only [List.prod_ofFn]
  exact contDiff_prod fun j _ => hf j

theorem isRealLine_image (h : IsCMExt F E σ) {n₁ : ℕ} {J₁ : Matrix (Fin n₁) (Fin n₁) E} {P : Subgroup (GAd σ J)}
    (yy : P →* GAd σ J₁) (hc : Continuous yy) (h1 : ∀ (p : P) w, projArch σ J w p = 1 → projArch σ J₁ w (yy p) = 1)
    (h2 : ∀ p : P, (p : GAd σ J) ∈ infPts σ J → yy p ∈ infPts σ J₁) {π : ℝ → GAd σ J} (hπ : IsRealLine σ J π)
    (hP : ∀ t, π t ∈ P) : IsRealLine σ J₁ fun t => yy ⟨π t, hP t⟩ := by
  have hadd := GlobalTheory.SiegelSet.isRealLine_add F E σ h n J π hπ
  have hcont := (line_fam h hπ).2
  have h0 := line_zero h hπ
  obtain ⟨w, τ, Z, -, hγ⟩ := hπ
  convert GlobalTheory.LineDerSum.isRealLine_component h J₁ (fun t => yy ⟨π t, hP t⟩) (hc.comp (hcont.subtype_mk _))
    (by rw [← map_one yy]; exact congrArg yy (Subtype.ext h0))
    (fun s t => by rw [← map_mul]; exact congrArg yy (Subtype.ext (hadd s t))) w using 2 with t
  obtain ⟨y, e, -⟩ := hγ t
  refine GAd_ext σ J₁ (fun v => ?_) fun v => ?_
  · by_cases hv : v = w
    · subst hv
      rw [projArch_embArch_self]
    · rw [projArch_embArch_ne σ J₁ hv]
      exact h1 _ v ((congrArg _ e).trans (projArch_embArch_ne σ J hv y))
  · rw [proj_embArch]
    exact mem_infPts_iff_forall.1 (h2 _ (mem_infPts.2 ((congrArg _ e).trans (projFin_embArch σ J w y)))) v

end GlobalTheory.ThK.CuspTransfer.Smooth

open GlobalTheory.ThK.CuspTransfer.Smooth in

theorem GlobalTheory.ThK.CuspTransfer.isSm_of_isInd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∀ i, ContinuousOn (a i) Kc) → (∀ i, ∀ k ∈ Kc, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * (List.ofFn fun j => γ j (t j)).prod)) → GlobalTheory.UAut.IsSm σ (c₀ • W.J.map σ) Ψ := by
  intro F E _ _ _ _ _ σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M _ hM _ r Xf Yf _ X' Y' hW' hX0 _ _ S' χ _ hχ
    K₁ _ K' hK' Kc d ψs a Ψ hI hψ hKc _ ha e γ hγ g
  obtain ⟨P, yy, tt, hP, hdec, hmem, hyc, htt, A, hA, hyA⟩ :=
    GlobalTheory.T.skew_plane_stabilizer_action F E σ hCM hσ n n₁ W W₁ H hsk hn hxx hyy hxy hι hJ₁ c₀ hc₀ hN₁ hN M hM r X' Y' hW' hX0
  have hy1 : ∀ (p : P) w, projArch σ _ w (p : GAd σ (c₀ • W.J.map σ)) = 1 → projArch σ _ w (yy p) = 1 := fun p w hp => by
    refine Subtype.ext (Units.ext ?_)
    have := map_eq_one (evInf F w) hA (g := (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1) (congrArg (fun z => z.1.1) hp)
    rw [← hyA] at this
    exact this
  have hy2 : ∀ p : P, (p : GAd σ (c₀ • W.J.map σ)) ∈ infPts σ _ → yy p ∈ infPts σ _ := fun p hp => by
    refine mem_infPts.2 (Subtype.ext (Units.ext ?_))
    have := map_eq_one (sndA F) hA (g := (matHom _ σ _ (p : GAd σ (c₀ • W.J.map σ))).1)
      (congrArg (fun z => z.1.1) (mem_infPts.1 hp))
    rw [← hyA] at this
    exact this
  have hΨ : ∀ q : P, ∀ k ∈ Kc, Ψ (q * k) = (χ (tt q) : ℂ) * ∑ i, ψs i (yy q) * a i k := fun q k hk => by
    obtain ⟨u, hu, m, hm, e⟩ := hdec q
    conv_lhs => rw [e]
    exact hI.2 u hu _ m _ k hk hm
  have hx : H.x ≠ 0 := fun h0 => by simp [form, h0] at hxy
  have hxx' : (fun i => σ (H.x i)) ⬝ᵥ (c₀ • W.J.map σ) *ᵥ H.x = 0 := by
    have := congrArg (fun z => c₀ * σ z) hxx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, mul_zero, Finset.mul_sum] at this
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum]
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  have hfam : IsSmoothRealFam fun t : Fin e → ℝ => (List.ofFn fun j => γ j (t j)).prod :=
    GlobalTheory.Orb.isSmoothRealFam_prod fun j => (line_fam hCM (hγ j)).1.comp (contDiff_apply ℝ ℝ j)
  obtain ⟨u, hu, t₁, m, y, k, hk, hm, hg⟩ := hI.1 (g * (List.ofFn fun j => γ j (t₀ j)).prod)
  obtain ⟨d', π, κ, s, s', hπ, hκ, hπx, hκK, hs, hs', hev⟩ := local_iwasawa hCM hN hx hxx' hK' k
    (fam_translate hfam (a := (List.ofFn fun j => γ j (t₀ j)).prod⁻¹) (b := 1)
      (by rw [mul_one, map_inv, hfam.1, inv_one])) (t₀ := t₀) (by simp)
  have hπP : ∀ j t, π j t ∈ P := fun j t => (hP _).2 (hπx j t)
  set p₀ : P := ⟨_, hmem u hu t₁ m y hm⟩ with hp₀
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v : Fin d' → ℝ =>
      (χ (tt (p₀ * (List.ofFn fun j => (⟨π j (v j), hπP j _⟩ : P)).prod)) : ℂ) := by
    let φ : P →* ℂ := Circle.coeHom.comp (χ.comp tt)
    have hφ : Continuous φ := hχ.comp htt
    change ContDiff ℝ _ fun v : Fin d' → ℝ => φ (p₀ * (List.ofFn fun j => (⟨π j (v j), hπP j _⟩ : P)).prod)
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def]
    refine contDiff_const.mul (contDiff_list_prod _ _ fun j => ?_)
    refine (contDiff_of_oneParam (f := fun t => φ ⟨π j t, hπP j t⟩) (hφ.comp ((line_fam hCM (hπ j)).2.subtype_mk _))
      ?_ fun s t => ?_).comp (contDiff_apply ℝ ℝ j)
    · rw [← map_one φ]; exact congrArg φ (Subtype.ext (line_zero hCM (hπ j)))
    · rw [← map_mul]; exact congrArg φ (Subtype.ext (GlobalTheory.SiegelSet.isRealLine_add F E σ hCM _ _ _ (hπ j) s t))
  have h2 : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun v : Fin d' → ℝ =>
      ψs i (yy (p₀ * (List.ofFn fun j => (⟨π j (v j), hπP j _⟩ : P)).prod)) := fun i => by
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def]
    exact (hψ i).1.smooth d' (fun j t => yy ⟨π j t, hπP j t⟩)
      (fun j => isRealLine_image hCM yy hyc hy1 hy2 (hπ j) (hπP j)) (yy p₀)
  refine ContDiffAt.congr_of_eventuallyEq ((h1.contDiffAt.comp t₀ hs).mul (ContDiffAt.sum (s := Finset.univ) fun i _ =>
    ((h2 i).contDiffAt.comp t₀ hs).mul ((ha i k hk d' κ hκ hκK).contDiffAt.comp t₀ hs'))) (hev.mono fun t ht => ?_)
  simp only [Function.comp_apply]
  rw [← hΨ _ _ (hKc.2.2 k hk _ (list_prod_mem fun z hz => by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hz
    exact hκK j _))]
  congr 1
  rw [Subgroup.coe_mul, Subgroup.val_list_prod, List.map_ofFn, mul_assoc]
  refine Eq.trans ?_ (congrArg ((p₀ : GAd σ (c₀ • W.J.map σ)) * ·) ht)
  rw [← mul_assoc, hp₀, Subgroup.coe_mk, ← hg]
  group

end
