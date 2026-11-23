import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabCompact

theorem exists_compact_of_entries {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (C : Set (R ⊗[F] E)) (hC : IsCompact C) :
    ∃ K : Set (HA R σ J), IsCompact K ∧ ∀ h : HA R σ J, (∀ i j, (HA.mat R σ J h).1 i j ∈ C) → h ∈ K := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) R
  haveI : T2Space (R ⊗[F] E) := e.isEmbedding.t2Space
  have hc : IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  let S : Set (Matrix (Fin M) (Fin M) (R ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  let f : Matrix (Fin M) (Fin M) (R ⊗[F] E) → (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    fun A => MulOpposite.op (JR (F := F) R J⁻¹ * (Formalism.UG.cT (sigR R σ) A * JR (F := F) R J))
  have hf : Continuous f := MulOpposite.continuous_op.comp (continuous_const.matrix_mul
    ((continuous_id.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ)).matrix_transpose.matrix_mul
      continuous_const))
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (R ⊗[F] E))).comp
    hc.isClosedEmbedding_subtypeVal
  refine ⟨_, hemb.isCompact_preimage (hS.prod (hS.image hf)), fun h hh => ?_⟩
  have hm : (HA.mat R σ J h).1 ∈ S := fun i _ j _ => hh i j
  refine ⟨hm, (HA.mat R σ J h).1, hm, ?_⟩
  have hu : Formalism.UG.cT (sigR R σ) (HA.mat R σ J h).1 * JR (F := F) R J * (HA.mat R σ J h).1 = JR (F := F) R J := h.2
  have h1 : JR (F := F) R J⁻¹ * JR (F := F) R J = 1 := by
    unfold JR
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  change MulOpposite.op _ = MulOpposite.op ((HA.mat R σ J h)⁻¹).1
  congr 1
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  rw [Matrix.mul_assoc, hu, h1]

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finset_sum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem det_gram_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
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

theorem exists_compact_adele (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (R : ℝ) (C : Set (Af D.host.F ⊗[D.host.F] D.host.E)) (hC : IsCompact C) :
    ∃ K : Set (AE D), IsCompact K ∧ ∀ z : AE D, finPart D z ∈ C → (∀ ρ, ‖θ ρ (infPart D z)‖ ≤ R) → z ∈ K := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  obtain ⟨s, hs⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let j : Af D.host.F ⊗[D.host.F] D.host.E → AE D := fun w => e.symm (0, w)
  have hj : Continuous j := hc.comp (continuous_const.prodMk continuous_id)
  have hj1 : ∀ w, infPart D (j w) = 0 := fun w =>
    (he (e.symm (0, w))).1.symm.trans (by rw [e.apply_symm_apply])
  have hj2 : ∀ w, finPart D (j w) = w := fun w =>
    (he (e.symm (0, w))).2.symm.trans (by rw [e.apply_symm_apply])
  have hB : IsCompact (Set.pi Set.univ fun _ : D.what₂.Tau => Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨_, (hB.prod hC).image ((hs.cont.comp continuous_fst).add (hj.comp continuous_snd)), fun z hz hR => ?_⟩
  refine ⟨(fun ρ => θ ρ (infPart D z), finPart D z), ⟨fun ρ _ => mem_closedBall_zero_iff.2 (hR ρ), hz⟩, ?_⟩
  refine sub_eq_zero.1 (hs.ext _ ?_ fun τ => ?_)
  · change finPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z) = 0
    rw [RingHom.map_sub, RingHom.map_add, hs.fin, hj2, zero_add, sub_self]
  · change θ τ (infPart D (s (fun ρ => θ ρ (infPart D z)) + j (finPart D z) - z)) = 0
    rw [RingHom.map_sub, RingHom.map_add, hj1, add_zero, RingHom.map_sub, hs.comp, sub_self]

theorem exists_compact_stab : ∀ (D : D7) (V : HSp D) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ R : ℝ, ∃ K : Set (GA D V), IsCompact K ∧ ∀ h : GA D V, (∀ y, y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V) ↔ (finMat D.sp.cm.sig V.gram h).mulVec y ∈ Formalism.MainNotions.StandardLattice.latHat D.host.F D.host.E (L0c D V)) → (∀ ρ i j, ‖infMat D.sp.cm.sig V.gram (θ ρ) h i j‖ ≤ R) → h ∈ K := by
  intro D V θ hθ R
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [V.standardTuple_isLattice.span_eq_top]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries D.host.F D.host.E L (V.standardTuple_isLattice.fg.map _) hsp
  rw [hL] at hCe
  obtain ⟨C', hC', hCe'⟩ := exists_compact_adele D θ hθ R C hC
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨K, hK, hKe⟩ := exists_compact_of_entries (AF D.host.F) D.sp.cm.sig V.gram (det_gram_ne_zero V) C' hC'
  exact ⟨K, hK, fun h h1 h2 => hKe h fun i j =>
    hCe' _ (hCe _ (fun y hy => (h1 y).1 hy) i j) fun ρ => h2 ρ i j⟩

end GlobalTheory.StabCompact
