import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumFiniteDimensionalOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedInvariantHermitianFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveFormOrthonormalBasisUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimFunctionalPointEvaluationsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.KTypeFin

theorem sesq_onb : ∀ (Wt : Type) [AddCommGroup Wt] [Module ℂ Wt] (S : Submodule ℂ Wt) [FiniteDimensional ℂ S] (Bf : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) → ∃ (m : ℕ) (b : Fin m → S), (∀ i j, Bf (b i) (b j) = if i = j then 1 else 0) ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧ ∀ T : S →ₗ[ℂ] S, (∀ x y, Bf (T x) (T y) = Bf x y) → (∀ j, T (b j) = ∑ i, Bf (b i) (T (b j)) • b i) ∧ Matrix.of (fun i j => Bf (b i) (T (b j))) ∈ Matrix.unitaryGroup (Fin m) ℂ := GlobalTheory.T.positive_form_orthonormal_basis_unitary

theorem eval_combo : ∀ (Xt : Type) (S : Submodule ℂ (Xt → ℂ)) [FiniteDimensional ℂ S] (l : S →ₗ[ℂ] ℂ), ∃ (n : ℕ) (x : Fin n → Xt) (c : Fin n → ℂ), ∀ f : S, l f = ∑ i, c i * (f : Xt → ℂ) (x i) := GlobalTheory.T.finite_dim_functional_point_evaluations

theorem exists_matched_l2_inner_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∃ Bf : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ⋆[ℂ] ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) →ₗ[ℂ] ℂ, (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) ∧ (∀ x, x ≠ 0 → 0 < (Bf x x).re) ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ x y x' y' : ↥(GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (x' : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) x → (y' : GlobalTheory.ThK.Fn F a' (a + a')) = om' (1, k) y → Bf x' y' = Bf x y := GlobalTheory.T.matched_invariant_hermitian_form

theorem kInf_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}
    {W : Spc F E d} {τ : ∀ w : InfinitePlace F, EmbOver E w} {k k' : UA σ W.J} (hk : k ∈ KInf σ W τ)
    (hk' : k' ∈ KInf σ W τ) : k * k' ∈ KInf σ W τ := by
  have e0 : mat (k * k') = mat k * mat k' := rfl
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · have h1 : u • (mat k - 1) = 0 := hk.1 u hu
    have h2 : u • (mat k' - 1) = 0 := hk'.1 u hu
    have e : mat (k * k') - 1 = (mat k - 1) * mat k' + (mat k' - 1) := by
      rw [e0]; noncomm_ring
    show u • (mat (k * k') - 1) = 0
    rw [e, smul_add, ← Matrix.smul_mul, h1, h2, zero_mul, add_zero]
  · rw [e0, Matrix.map_mul]
    exact (hk.2 w).mul_left (hk'.2 w)

theorem cont_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    {R : RealMaps F a a'} {Rf : FinMaps F a a'} (h : IsMatched B G X om om' R Rf)
    (Φ : Fn F a' (a + a')) (hΦ : Φ ∈ schA F (Fin a' × Fin (a + a'))) (x : Fin a' × Fin (a + a') → AF F) :
    Continuous fun k : UA σ G.W.J => om' (1, k) Φ x := by
  classical
  have hc : IsContOn (adeleClass F) om' := (IsUWeilPair.isUSplitting h.triple.weil').cont
  have hl : (LinearMap.proj x : Fn F a' (a + a') →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin a' × Fin (a + a')) := by
    intro g _
    refine ⟨g (fun i => (x i).2) • (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
      SchwartzMap.toBoundedContinuousFunctionCLM_apply, smul_eq_mul, LinearMap.proj_apply, pureA, mul_comm]
  exact (hc _ hl Φ hΦ).comp (continuous_const.prodMk continuous_id)

theorem kfin : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Ψ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ (m : ℕ) (b : Fin m → GlobalTheory.ThK.Fn F a' (a + a')) (A : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J → Matrix (Fin m) (Fin m) ℂ), LinearIndependent ℂ b ∧ (∀ i, b i ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁)) ∧ Ψ ∈ Submodule.span ℂ (Set.range b) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, ∀ j, om' (1, k) (b j) = ∑ i, A k i j • b i) ∧ (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) ∧ ContinuousOn A (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ G.W B.emb) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf h Ψ hΨ
  have hP := GlobalTheory.ThK.Inhab.pairV' h.triple
  have hstab := (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf h).2
  obtain ⟨S, hSfin, hSle, hSk⟩ := GlobalTheory.FockKFin.polData_kfin F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _
    hKP hP Ψ hΨ.1
  set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hD
  let V : Submodule ℂ (Fn F a' (a + a')) :=
    Submodule.span ℂ (insert Ψ {Φ | ∃ k ∈ KInf σ G.W B.emb, Φ = om' (1, k) Ψ})
  have hVD : V ≤ D := Submodule.span_le.2 (by
    rintro _ (rfl | ⟨k, hk, rfl⟩)
    exacts [hΨ, hstab k hk Ψ hΨ])
  have hVS : V ≤ S ⊔ Submodule.span ℂ {Ψ} := Submodule.span_le.2 (by
    rintro _ (rfl | ⟨k, hk, rfl⟩)
    exacts [Submodule.mem_sup_right (Submodule.mem_span_singleton_self _), Submodule.mem_sup_left (hSk k hk)])
  haveI : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVS
  have hVk : ∀ k ∈ KInf σ G.W B.emb, ∀ Φ ∈ V, om' (1, k) Φ ∈ V := by
    intro k hk Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      rcases hx with rfl | ⟨k', hk', rfl⟩
      · exact Submodule.subset_span (Or.inr ⟨k, hk, rfl⟩)
      · refine Submodule.subset_span (Or.inr ⟨k * k', kInf_mul hk hk', ?_⟩)
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    | zero => rw [map_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact V.smul_mem c hx
  obtain ⟨Bf, hsym, hpos, hinv⟩ := exists_matched_l2_inner_product F E σ B a a' G X om om' R Rf h
  let ι : V →ₗ[ℂ] D := Submodule.inclusion hVD
  let BV : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := (Bf.comp ι).compl₂ ι
  have hBV : ∀ x y : V, BV x y = Bf (ι x) (ι y) := fun _ _ => rfl
  obtain ⟨m, b, horth, hspan, hT⟩ := sesq_onb _ V BV (fun x y => by rw [hBV, hBV]; exact hsym _ _)
    (fun x hx => by
      rw [hBV]
      exact hpos _ (fun h0 => hx (Submodule.inclusion_injective hVD (h0.trans (map_zero ι).symm))))
  let T : ∀ k ∈ KInf σ G.W B.emb, V →ₗ[ℂ] V := fun k hk => (om' (1, k)).restrict (hVk k hk)
  have hTi : ∀ k (hk : k ∈ KInf σ G.W B.emb), ∀ x y, BV (T k hk x) (T k hk y) = BV x y := fun k hk x y => by
    rw [hBV, hBV]; exact hinv k hk _ _ _ _ rfl rfl
  classical
  let A : UA σ G.W.J → Matrix (Fin m) (Fin m) ℂ := fun k =>
    if hk : k ∈ KInf σ G.W B.emb then Matrix.of fun i j => BV (b i) (T k hk (b j)) else 0
  let b' : Fin m → Fn F a' (a + a') := fun i => ((b i : V) : Fn F a' (a + a'))
  have hli : LinearIndependent ℂ b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (BV (b j)) hg
    simpa [map_sum, horth, Finset.sum_ite_eq] using this
  have hspan' : Submodule.span ℂ (Set.range b') = V := by
    rw [show Set.range b' = V.subtype '' Set.range b from (Set.range_comp _ _), ← Submodule.map_span, hspan,
      Submodule.map_top, Submodule.range_subtype]
  have hΨV : Ψ ∈ V := Submodule.subset_span (Or.inl rfl)
  choose n xs cs hcs using fun i => eval_combo _ V (BV (b i))
  refine ⟨m, b', A, hli.map' V.subtype (Submodule.ker_subtype V), fun i => hVD (b i).2, hspan'.symm ▸ hΨV,
    fun k hk j => ?_, fun k hk => ?_, ?_⟩
  · have e := congrArg Subtype.val ((hT (T k hk) (hTi k hk)).1 j)
    simp only [A, dif_pos hk]
    simpa [T, b', Submodule.coe_sum, Submodule.coe_smul] using e
  · simp only [A, dif_pos hk]
    exact (hT (T k hk) (hTi k hk)).2
  · have hc : Continuous fun k : UA σ G.W.J => (Matrix.of fun i j => ∑ l, cs i l * om' (1, k) (b' j) (xs i l) :
        Matrix (Fin m) (Fin m) ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.of_apply]
      exact continuous_finset_sum _ fun l _ => continuous_const.mul
        (cont_eval h (b' j) (GlobalTheory.ThKRatInv.polData_le_schA B G.M' h.triple.geo.hM' (hVD (b j).2).1) _)
    refine hc.continuousOn.congr fun k hk => ?_
    simp only [A, dif_pos hk]
    ext i j
    simp only [Matrix.of_apply]
    rw [hcs i (T k hk (b j))]
    rfl

end GlobalTheory.KTypeFin
