import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdmCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ComapIrreducible
import GroundTheory.AutomorphicForms.L2LocalComponents.NonEmpty

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem admissible_finite_window {R M : Type*} [Ring R] [AddCommGroup M] [Module ℂ M] [Module R M]
    [IsSemisimpleModule R M] (Y : Submodule R M)
    (hY : ∀ (c : Submodule R M) (hc : c ∈ isotypicComponents R M), ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧
      ∀ y ∈ Y, CompactRep.isoProj hc y ∈ W) (T : Finset M) :
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧
      ∀ x ∈ Y, (∀ r : R, (∀ t ∈ T, r • t = 0) → r • x = 0) → x ∈ W := by
  classical
  let G : Module.End R M → Prop := fun q => (∀ (f : Module.End R M) v, q (f v) = f (q v)) ∧ (∀ y ∈ Y, q y ∈ Y) ∧
    ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ ∀ y ∈ Y, y - q y ∈ W
  have g1 : G 1 := ⟨fun _ _ => rfl, fun _ h => h, ⊥, inferInstance, fun y _ => by simp⟩
  have gm : ∀ p q, G p → G q → G (p * q) := by
    rintro p q ⟨a, b, W, hW, c⟩ ⟨a', b', W', hW', c'⟩
    refine ⟨fun f v => by rw [Module.End.mul_apply, Module.End.mul_apply, a', a], fun y hy => b _ (b' y hy),
      W ⊔ W', inferInstance, fun y hy => ?_⟩
    have := Submodule.add_mem_sup (c _ (b' y hy)) (c' y hy)
    rwa [sub_add_sub_cancel'] at this
  have g2 : ∀ p q v w, G p → G q → p v = 0 → q w = 0 → (p * q) v = 0 ∧ (p * q) w = 0 := fun p q v w hp _ hv hw =>
    ⟨by rw [Module.End.mul_apply, hp.1, hv, map_zero], by rw [Module.End.mul_apply, hw, map_zero]⟩
  have h1 : ∀ v : M, ∃ q, G q ∧ q v = 0 := by
    intro v
    have hv : v ∈ ⨆ c : isotypicComponents R M, c.1 := by rw [← sSup_eq_iSup', sSup_isotypicComponents]; trivial
    induction hv using Submodule.iSup_induction' with
    | mem c x hx =>
      obtain ⟨c, hc⟩ := c
      obtain ⟨W, hW, h⟩ := hY c hc
      refine ⟨1 - CompactRep.isoProj hc, ⟨fun f v => ?_, fun y hy => Y.sub_mem hy (CompactRep.isoProj_mem hc Y hy),
        W, hW, fun y hy => by simpa using h y hy⟩, ?_⟩
      · simp [CompactRep.isoProj_comm hc f v]
      · simp [CompactRep.isoProj_apply_of_mem hc hx]
    | zero => exact ⟨1, g1, rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, hp, hx⟩ := hx
      obtain ⟨q, hq, hy⟩ := hy
      obtain ⟨a, b⟩ := g2 p q x y hp hq hx hy
      exact ⟨p * q, gm p q hp hq, by rw [map_add, a, b, add_zero]⟩
  have h2 : ∃ q, G q ∧ ∀ t ∈ T, q t = 0 := by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, g1, by simp⟩
    | insert v T _ ih =>
      obtain ⟨p, hp, hx⟩ := h1 v
      obtain ⟨q, hq, hy⟩ := ih
      refine ⟨p * q, gm p q hp hq, fun t ht => ?_⟩
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact (g2 p q t 0 hp hq hx (map_zero _)).1
      · exact (g2 p q v t hp hq hx (hy t ht)).2
  obtain ⟨q, ⟨a, -, W, hW, c⟩, hq⟩ := h2
  refine ⟨W, hW, fun x hx h => ?_⟩
  obtain ⟨r, hr⟩ := jacobson_density (R := R) (M := M)
    { toFun := q, map_add' := map_add q, map_smul' := fun f v => a f v } (insert x T)
  have h0 : q x = 0 := (hr x (Finset.mem_insert_self _ _)).trans
    (h r fun t ht => (hr t (Finset.mem_insert_of_mem ht)).symm.trans (hq t ht))
  simpa [h0] using c x hx

private theorem finite_dim_tested_on_finset {ι F : Type*} [AddCommGroup F] [Module ℂ F] (B : Submodule ℂ F) [FiniteDimensional ℂ B]
    (f : ι → F) (hf : ∀ i, f i ∈ B) : ∃ T : Finset ι, ∀ l : F →ₗ[ℂ] ℂ, (∀ i ∈ T, l (f i) = 0) → ∀ i, l (f i) = 0 := by
  classical
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (Set.range_subset_iff.2 hf))
  obtain ⟨s, hs, hsp⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (Module.Finite.iff_fg.1 hfd)
  obtain ⟨T, hT⟩ := Finset.subset_set_image_iff.1 (show (s : Set F) ⊆ f '' Set.univ by rwa [Set.image_univ])
  refine ⟨T, fun l hl i => ?_⟩
  have : Submodule.span ℂ (Set.range f) ≤ LinearMap.ker l := by
    rw [hsp, Submodule.span_le, ← hT.2]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    exact hl j hj
  exact this (Submodule.subset_span ⟨i, rfl⟩)

private theorem admissible_induced_finite {G : Type*} [Group G] (U : Subgroup G) [U.FiniteIndex] {X : Type*} (e : X → U)
    (A : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ A] (he : Function.Surjective e) :
    ∃ B : Submodule ℂ (G → ℂ), FiniteDimensional ℂ B ∧ ∀ a : G → ℂ, (∀ k, (fun x => a (k * e x)) ∈ A) → a ∈ B := by
  let B : Submodule ℂ (G → ℂ) := ⨅ k : G, A.comap (LinearMap.funLeft ℂ ℂ fun x => k * e x)
  have hB : ∀ a, a ∈ B ↔ ∀ k, (fun x => a (k * e x)) ∈ A := fun a => Submodule.mem_iInf _
  let L : B →ₗ[ℂ] (G ⧸ U → A) := LinearMap.pi fun c =>
    LinearMap.codRestrict A ((LinearMap.funLeft ℂ ℂ fun x => c.out * e x) ∘ₗ B.subtype) fun a => (hB a).1 a.2 _
  refine ⟨B, FiniteDimensional.of_injective L ((injective_iff_map_eq_zero _).2 fun a ha => ?_), fun a => (hB a).2⟩
  ext g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  obtain ⟨x, hx⟩ := he u⁻¹
  have := congrFun (congrArg Subtype.val (congrFun ha (g : G ⧸ U))) x
  change a.1 (_ * (e x : G)) = 0 at this
  rw [hu, hx] at this
  simpa using this

private theorem finite_dim_translates {X Y : Type*} (B : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ B] (f : X → Y → ℂ)
    (hf : ∀ x, f x ∈ B) : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun y => fun x => f x y)) := by
  let L : Module.Dual ℂ B →ₗ[ℂ] (X → ℂ) := LinearMap.pi fun x => Module.Dual.eval ℂ B ⟨f x, hf x⟩
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
  rintro _ ⟨y, rfl⟩
  exact ⟨LinearMap.proj y ∘ₗ B.subtype, rfl⟩

private theorem admissible_k_finite_window {C X : Type*} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
    [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ C X} (hσ : CompactRep.IsKFinite σ) (Y : Submodule ℂ X)
    (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y)
    (hf : ∀ (c : Submodule (MonoidAlgebra ℂ C) σ.asModule) (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ C) σ.asModule),
      FiniteDimensional ℂ (LinearMap.range (CompactRep.kProj hσ hc ∘ₗ Y.subtype))) (T : Finset X) :
    ∃ W : Submodule ℂ X, FiniteDimensional ℂ W ∧
      ∀ x ∈ Y, (∀ r, (∀ t ∈ T, σ.asAlgebraHom r t = 0) → σ.asAlgebraHom r x = 0) → x ∈ W :=
  have := CompactRep.isSemisimpleModule_asModule hσ
  admissible_finite_window (R := MonoidAlgebra ℂ C) (M := σ.asModule)
    (Subrepresentation.subrepresentationSubmoduleOrderIso (⟨Y, hY⟩ : Subrepresentation σ))
    (fun c hc => ⟨_, hf c hc, fun y hy => ⟨⟨y, hy⟩, rfl⟩⟩) T

private theorem admissible_cusp_forms_finite {K : Type} [Field K] [NumberField K] {n : ℕ} (π : CuspidalAutomorphicRepresentation K n)
    (B : Submodule ℂ (KG K n → ℂ)) [FiniteDimensional ℂ B] :
    ∃ W : Submodule ℂ π.carrier, FiniteDimensional ℂ W ∧ ∀ Φ : π.carrier,
      (∀ g : AdelicGLn.AdelicGL K n, (fun k : KG K n => Φ.1.1 (g * k.1.1)) ∈ B) → Φ ∈ W := by
  classical
  obtain ⟨T, hT⟩ := finite_dim_tested_on_finset B (ι := {Φ : π.carrier // ∀ g : AdelicGLn.AdelicGL K n,
    (fun k : KG K n => Φ.1.1 (g * k.1.1)) ∈ B} × AdelicGLn.AdelicGL K n)
    (fun p k => p.1.1.1.1 (p.2 * k.1.1)) fun p => p.1.2 p.2
  let j : ∀ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), KG K n := fun k hk =>
    ⟨⟨k, maxCompact_le_normOneGL hk⟩, hk⟩
  choose O hO hO' using fun Φ : π.carrier =>
    AutomorphicForm.exists_openSubgroup_rightInvariant Φ.1.2.1.isSmooth Φ.1.2.1.isKFinite
  let H : Subgroup (AdelicGLn.FiniteAdelicGL K n) :=
    AdelicGLn.integralFiniteGL K n ⊓ ⨅ p ∈ T, (O p.1.1).toSubgroup
  have hHo : IsOpen (H : Set (AdelicGLn.FiniteAdelicGL K n)) := by
    simp only [H, Subgroup.coe_inf, Subgroup.coe_iInf]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).inter (isOpen_biInter_finset fun p _ => (O p.1.1).isOpen)
  have hHc : IsCompact (H : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (H.isClosed_of_isOpen hHo) fun _ h => h.1
  let σ := π.toModule.gk.σ
  obtain ⟨W, hW, h⟩ := admissible_k_finite_window π.toModule.gk.isKFinite (fixedVectors π.toModule.τ H) (fun k y hy g hg => by
    rw [← Module.End.mul_apply, ← π.toModule.comm_σ, Module.End.mul_apply, hy g hg])
    (π.isAdmissible.2 H hHc hHo) (T.image fun p => p.1.1)
  refine ⟨W, hW, fun Φ hΦ => h Φ (fun u hu => ?_) fun r hr => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    have := hT (LinearMap.proj (φ := fun _ => ℂ) (j _ (finEmb_mem_maxCompact hu.1)) -
      LinearMap.proj (R := ℂ) (φ := fun _ : KG K n => ℂ) 1)
      (fun p hp => ?_) (⟨Φ, hΦ⟩, g)
    · change Φ.1.1 (g * finEmb K n u) - Φ.1.1 (g * 1) = 0 at this
      rw [mul_one, sub_eq_zero] at this
      exact this
    · change p.1.1.1.1 (p.2 * finEmb K n u) - p.1.1.1.1 (p.2 * 1) = 0
      rw [mul_one, sub_eq_zero]
      exact hO' p.1.1 p.2 u (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hu.2 p) hp)
  · have key : ∀ r : MonoidAlgebra ℂ (archCompact K n), ∃ l : (KG K n → ℂ) →ₗ[ℂ] ℂ, ∀ (Ψ : π.carrier) g,
        (σ.asAlgebraHom r Ψ).1.1 g = l fun k => Ψ.1.1 (g * k.1.1) := by
      intro r
      induction r using MonoidAlgebra.induction_on with
      | of k => exact ⟨LinearMap.proj (j _ k.2), fun Ψ g => by rw [Representation.asAlgebraHom_of]; rfl⟩
      | add a b ha hb =>
        obtain ⟨l, hl⟩ := ha
        obtain ⟨l', hl'⟩ := hb
        exact ⟨l + l', fun Ψ g => by rw [map_add, LinearMap.add_apply, LinearMap.add_apply, ← hl, ← hl']; rfl⟩
      | smul c a ha =>
        obtain ⟨l, hl⟩ := ha
        exact ⟨c • l, fun Ψ g => by rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, ← hl]; rfl⟩
    obtain ⟨l, hl⟩ := key r
    change σ.asAlgebraHom r Φ = 0
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    rw [hl]
    refine hT l (fun p hp => ?_) (⟨Φ, hΦ⟩, g)
    have h0 : σ.asAlgebraHom r p.1.1 = 0 := hr _ (Finset.mem_image_of_mem _ hp)
    exact (hl p.1.1 p.2).symm.trans (by rw [h0]; rfl)

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.adm :
    ∀ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (τ : Submodule ℂ (L2 μ₂)), CuspIrr μ₂ τ → ∀ U : Subgroup (G1 K 2), U ≤ KG K 2 → (∃ O : Set (G1 K 2), IsOpen O ∧ ∀ g ∈ KG K 2, g ∈ U ↔ g ∈ O) →
      ∀ 𝒜 : Submodule ℂ (U → ℂ), FiniteDimensional ℂ 𝒜 → (∀ a ∈ 𝒜, Continuous a ∧ ∀ u : U, (fun x => a (x * u)) ∈ 𝒜) →
      ∃ E : Submodule ℂ (G1 K 2 → ℂ), FiniteDimensional ℂ E ∧ (∀ φ ∈ E, Rd τ φ) ∧
        ∀ φ : G1 K 2 → ℂ, Continuous φ → (∃ v ∈ τ, Reps μ₂ v φ) → (∀ m, (fun u : U => φ (m * u)) ∈ 𝒜) → φ ∈ E := by
  intro K _ _ _ μ _ τ hτ U hU ⟨O, hO, hUO⟩ 𝒜 h𝒜 _
  have hK : CompactSpace (KG K 2) := isCompact_iff_compactSpace.1 ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 2).1
  have hUo : IsOpen ((U.subgroupOf (KG K 2) : Subgroup (KG K 2)) : Set (KG K 2)) := by
    convert hO.preimage (continuous_subtype_val : Continuous ((↑) : KG K 2 → G1 K 2)) using 1
    ext g
    exact hUO g g.2
  have : Finite (KG K 2 ⧸ U.subgroupOf (KG K 2)) := Subgroup.quotient_finite_of_isOpen _ hUo
  have : (U.subgroupOf (KG K 2)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨B, hB, hB'⟩ := admissible_induced_finite (U.subgroupOf (KG K 2)) (Subgroup.subgroupOfEquivOfLe hU).symm 𝒜
    (Subgroup.subgroupOfEquivOfLe hU).symm.surjective
  obtain ⟨hcs, hI, hirr⟩ := UpperTheory.ConvolutionTheory.Dp.sumT K 2 μ τ ⟨hτ.le, hτ.closed, hτ.inv, hτ.ne, hτ.irr⟩
  let π := CuspidalAutomorphicRepresentation.ofSummand _ hI hirr (summandCuspForms_ne_bot μ _ hI hirr)
  obtain ⟨W, hW, hW'⟩ := admissible_cusp_forms_finite π B
  let E : Submodule ℂ (G1 K 2 → ℂ) :=
    { carrier := {φ | Continuous φ ∧ (∃ v ∈ τ, Reps μ v φ) ∧ ∀ m, (fun u : U => φ (m * u)) ∈ 𝒜}
      zero_mem' := ⟨continuous_const, ⟨0, τ.zero_mem, by
        filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ).ae (Lp.coeFn_zero ℂ 2 (quotientMeasure (Gam K 2) μ))]
          with y e using e⟩, fun _ => 𝒜.zero_mem⟩
      add_mem' := by
        rintro a b ⟨h1, ⟨v, hv, h2⟩, h3⟩ ⟨h1', ⟨v', hv', h2'⟩, h3'⟩
        refine ⟨h1.add h1', ⟨v + v', τ.add_mem hv hv', ?_⟩, fun m => 𝒜.add_mem (h3 m) (h3' m)⟩
        filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ).ae (Lp.coeFn_add v v'), h2, h2'] with y e p q
        rw [e, Pi.add_apply, p, q, Pi.add_apply]
      smul_mem' := by
        rintro c a ⟨h1, ⟨v, hv, h2⟩, h3⟩
        refine ⟨h1.const_smul c, ⟨c • v, τ.smul_mem c hv, ?_⟩, fun m => 𝒜.smul_mem c (h3 m)⟩
        filter_upwards [(quasiMeasurePreserving_mk (Gam K 2) μ).ae (Lp.coeFn_smul c v), h2] with y e p
        rw [e, Pi.smul_apply, p, Pi.smul_apply] }
  have hsl : ∀ φ ∈ E, ∀ m : G1 K 2, (fun k : KG K 2 => φ (m * k)) ∈ B := fun φ hφ m => hB' _ fun k => by
    convert hφ.2.2 (m * k) using 2 with u
    rw [mul_assoc]
    rfl
  have hE := fun φ (hφ : φ ∈ E) => cuspIrr_kFinite_rep_eq_centralCuspForm μ τ hτ φ hφ.1 hφ.2.1 (finite_dim_translates B (fun m k => φ (m * k)) (hsl φ hφ))
  let res : π.carrier →ₗ[ℂ] (G1 K 2 → ℂ) :=
    LinearMap.funLeft ℂ ℂ Subtype.val ∘ₗ (cuspForms K 2).subtype ∘ₗ π.carrier.subtype
  refine ⟨E, Submodule.finiteDimensional_of_le (S₂ := W.map res) fun φ hφ => ?_, fun φ hφ => (hE φ hφ).1,
    fun φ a b c => ⟨a, b, c⟩⟩
  obtain ⟨-, Φ, h1, h2, h3⟩ := hE φ hφ
  refine ⟨⟨Φ, h1, h3⟩, hW' _ fun g => ?_, funext h2⟩
  obtain ⟨s, y, hy, rfl⟩ := exists_centralSection_mul_mem_normOneGL g
  convert hsl φ hφ ⟨y, hy⟩ using 2 with k
  rw [mul_assoc, ← h2]
  exact mem_centralCuspForms.1 h1 s _
