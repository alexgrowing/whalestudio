import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmTypeStatement
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Arch

theorem unit_iff {E : Type} [CommRing E] {n : Type} [Fintype n] (τ : E →+* ℂ) (G : Matrix n n E) (u : Matrix n n ℂ) :
    uᵀ * (-Gᵀ).map τ * u.map (starRingEnd ℂ) = (-Gᵀ).map τ ↔ uᴴ * G.map τ * u = G.map τ := by
  have e : (-Gᵀ).map τ = -(G.map τ)ᵀ := by
    ext a b; simp
  have e2 : u.map (starRingEnd ℂ) = (uᴴ)ᵀ := by
    ext a b; simp
  rw [e, e2, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_injective.eq_iff

theorem form_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) :
    (Formalism.UG.cT s M * J * M).map φ = (M.map φ)ᴴ * J.map φ * M.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  exact h _

theorem mat_ext {A : Type} [CommRing A] {n ι : Type} (θ : ι → (A →+* ℂ))
    (hθ : Function.Injective fun (z : A) (i : ι) => θ i z) {M N : Matrix n n A}
    (h : ∀ i, M.map (θ i) = N.map (θ i)) : M = N :=
  Matrix.ext fun a b => hθ (funext fun i => congrFun (congrFun (h i) a) b)

theorem exists_lift {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (θ : ι → (A →+* ℂ)) (hθ : Function.Bijective fun (z : A) (i : ι) => θ i z)
    (hs : ∀ i z, θ i (s z) = starRingEnd ℂ (θ i z)) (J : Matrix n n A) (hJ : ∀ i, (J.map (θ i)).det ≠ 0)
    (u : ι → Matrix n n ℂ) (hu : ∀ i, (u i)ᴴ * J.map (θ i) * u i = J.map (θ i)) :
    ∃ g : GL n A, g ∈ Formalism.UG.UJ s J ∧ ∀ i, g.1.map (θ i) = u i := by
  have lift : ∀ w : ι → Matrix n n ℂ, ∃ M : Matrix n n A, ∀ i, M.map (θ i) = w i := by
    intro w
    choose M hM using fun a b => hθ.2 fun i => w i a b
    exact ⟨Matrix.of M, fun i => Matrix.ext fun a b => congrFun (hM a b) i⟩
  have hd : ∀ i, IsUnit (u i).det := by
    intro i
    refine IsUnit.mk0 _ fun h0 => hJ i ?_
    rw [← hu i, Matrix.det_mul, h0, mul_zero]
  obtain ⟨M, hM⟩ := lift u
  obtain ⟨N, hN⟩ := lift fun i => (u i)⁻¹
  refine ⟨⟨M, N, mat_ext θ hθ.1 fun i => ?_, mat_ext θ hθ.1 fun i => ?_⟩, mat_ext θ hθ.1 fun i => ?_, hM⟩
  · rw [Matrix.map_mul, hM, hN, Matrix.mul_nonsing_inv _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hM, hN, Matrix.nonsing_inv_mul _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [form_map s (θ i) (hs i), hM, hu]

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem continuous_inf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AF F ⊗[F] E → Ainf F ⊗[F] E) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(fstA F).toRingHom] Ainf F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((fstA F).toRingHom : AF F → Ainf F) := continuous_fst
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem inf_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J := by
  let π : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hπ : ∀ z, π (sigR (AF F) σ z) = sigR (Ainf F) σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
    | tmul a x => rfl
  have hg' : Formalism.UG.cT (sigR (AF F) σ) g.1 * JR (AF F) J * g.1 = JR (AF F) J := hg
  have hJ : (JR (F := F) (AF F) J).map π = JR (Ainf F) J := rfl
  have hc : (Formalism.UG.cT (sigR (AF F) σ) g.1).map π = Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) :=
    Matrix.ext fun a b => hπ _
  change Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) * JR (Ainf F) J * g.1.map π = JR (Ainf F) J
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

variable {D : D7}

theorem JR_map (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map θ = V.gram.map τ :=
  Matrix.ext fun _ _ => h.1 _

theorem archM_of_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : infHom V k = 1) : archM V θ k = 1 := by
  rw [archM, hk, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_archM (V : HSp D) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (hθ : Continuous θ) :
    Continuous fun h => archM V θ h := by
  have h1 : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  exact (h1.matrix_map (continuous_inf D.host.F D.host.E)).matrix_map hθ

theorem archM_spec : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  intro D V θ hθ
  obtain ⟨hc, hs, hb⟩ := (GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType D).2 θ hθ
  refine ⟨fun τ => ⟨archM_of_one V _ (map_one _), fun h h' => ?_, fun k hk => archM_of_one V _ hk,
    continuous_archM V (hc τ), fun h => ?_⟩, fun h hh => ?_, fun u hu => ?_⟩
  · rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
  · have hm : Formalism.UG.cT (sigR (Ainf D.host.F) D.sp.cm.sig) (infHom V h).1 * JR (Ainf D.host.F) V.gram * (infHom V h).1 =
        JR (Ainf D.host.F) V.gram := inf_mem D.sp.cm.sig V.gram (matHom V h) h.2
    rw [unit_iff, ← JR_map V (hθ τ), archM, ← form_map _ _ (hs τ), hm]
  · refine Units.ext (mat_ext _ hb.1 fun τ => ?_)
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hh τ.1 τ.2
  · obtain ⟨g, hg, hgu⟩ := exists_lift (sigR (Ainf D.host.F) D.sp.cm.sig) _ hb (fun τ => hs τ.1)
      (JR (Ainf D.host.F) V.gram) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        have : (V.gram.map τ.1).det = τ.1 V.gram.det := (τ.1.map_det V.gram).symm
        rw [this]
        exact (map_ne_zero τ.1).2 (gram_det_ne_zero V)) (fun τ => u τ.1) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        exact (unit_iff _ _ _).1 (hu τ.1 τ.2))
    obtain ⟨a, ha, hag⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.2 g hg
    refine ⟨a, ha, fun τ hτ => ?_⟩
    rw [archM, hag]
    exact hgu ⟨τ, hτ⟩

end GlobalTheory.Member.Arch
