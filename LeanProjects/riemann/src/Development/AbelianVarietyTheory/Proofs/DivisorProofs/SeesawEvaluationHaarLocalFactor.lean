import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIntegralFinite

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.ConeSliceBound

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic GlobalTheory.DiffDecay GlobalTheory.XTermDecay

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_support {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil ψ χX χW om) {K : Set (UA σ X.J)} (hK : IsCompact K) (h : UA σ W.J)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {V : Type} [AddCommGroup V] [Module ℂ V] (e : Fn F n d →ₗ[ℂ] V)
    {ι : Type} [Fintype ι] (S U : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hSU : ∀ i j, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (S j) (U i) = if i = j then 1 else 0)
    (hinv : ∀ i (a : AF F), ∀ Ψ ∈ schA F _, e (M.co.rho ψ (a • U i) Ψ) = e Ψ) :
    ∃ Ω : Set (ι → Af F), IsCompact Ω ∧ ∀ k ∈ K, ∀ x : ι → AF F, (fun i => (x i).2) ∉ Ω →
      e (M.co.rho ψ (∑ i, x i • S i) (om (k, h) Φ)) = 0 := by
  have hw : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hom
  have hΨ : ∀ k, om (k, h) Φ ∈ schA F _ := fun k => hw.isUSplitting.pres (k, h) Φ hΦ
  have hO := fun i => GlobalTheory.XTermSupp.rho_om_fixed M ψ hψ.1 hom hK h Φ hΦ (U i)
  obtain ⟨V, hV, hVm⟩ := GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F ψ hψ.1 (GlobalTheory.PsiNontriv.isStd_fin_rat hψ) _
    (Filter.eventually_all.2 hO)
  have hΩ : IsCompact (Set.pi Set.univ fun _ : ι => V) := isCompact_univ_pi fun _ => hV
  have hSU' : ∀ i j, (M.co.e (S j)).1 ⬝ᵥ (M.co.e (U i)).2 - (M.co.e (U i)).1 ⬝ᵥ (M.co.e (S j)).2 =
      if i = j then 1 else 0 := fun i j => by rw [← M.co.form, hSU]
  refine ⟨_, hΩ, fun k hk x hx => ?_⟩
  by_contra hne
  refine hx fun i _ => hVm _ fun a ha => ?_
  have h1 := congrArg e (GlobalTheory.XTermSupp.rho_comm M.co ψ (∑ j, x j • S j) (pairA F 0 a • U i) (om (k, h) Φ))
  have hω : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (∑ j, x j • S j) (pairA F 0 a • U i) =
      pairA F 0 a * x i := by
    have : ∀ j, (x j • M.co.e (S j)).1 ⬝ᵥ (pairA F 0 a • M.co.e (U i)).2 -
        (pairA F 0 a • M.co.e (U i)).1 ⬝ᵥ (x j • M.co.e (S j)).2 = if i = j then pairA F 0 a * x j else 0 := fun j => by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have := hSU' i j
      split_ifs at this ⊢
      · linear_combination (pairA F 0 a * x j) * this
      · linear_combination (pairA F 0 a * x j) * this
    rw [M.co.form]
    simp only [map_sum, map_smul]
    rw [Prod.fst_sum, Prod.snd_sum, sum_dotProduct, dotProduct_sum, ← Finset.sum_sub_distrib]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [ha i k hk, map_smul, hinv _ _ _ (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ _ _ (hΨ k)), hω] at h1
  have h2 : pairA F 0 a * x i = pairA F 0 (a * (x i).2) := Prod.ext (zero_mul _) rfl
  rw [h2] at h1
  exact smul_left_injective ℂ hne (h1.symm.trans (one_smul ℂ _).symm)

theorem exists_decay {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    {χX χW : Chr F E} {om : Rep σ X W} (hom : M.IsWeil ψ χX χW om) {K : Set (UA σ X.J)} (hK : IsCompact K) (h : UA σ W.J)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) {κ : Type} [Fintype κ]
    (e : Fn F n d →ₗ[ℂ] (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (hsl : ∀ g ∈ SB (Fin n × Fin d → Af F), ∃ L : SInf F (Fin n × Fin d) →L[ℂ] SInf F κ, ∀ f, ⇑(L f) = e (pureA F f g))
    {ι : Type} [Fintype ι] (S U : ι → Matrix (Fin n) (Fin d) (AE F E))
    (hSU : ∀ i j, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (S j) (U i) = if i = j then 1 else 0)
    (hinv : ∀ i (a : AF F), ∀ Ψ ∈ schA F _, e (M.co.rho ψ (a • U i) Ψ) = e Ψ)
    {Ω : Set (ι → Af F)} (hΩ : IsCompact Ω) (p : Seminorm ℂ (SInf F κ)) (hp : Continuous p) (N : ℕ) :
    ∃ C : ℝ, ∀ k ∈ K, ∀ x : ι → AF F, (fun i => (x i).2) ∈ Ω → ∃ f : SInf F κ,
      ⇑f = e (M.co.rho ψ (∑ i, x i • S i) (om (k, h) Φ)) ∧
        p f ≤ C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(x i).1 v‖) ^ (-(N : ℝ)) := by
  have hw : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hom
  have hSU' : ∀ i j, (M.co.e (S j)).1 ⬝ᵥ (M.co.e (U i)).2 - (M.co.e (U i)).1 ⬝ᵥ (M.co.e (S j)).2 =
      if i = j then 1 else 0 := fun i j => by rw [← M.co.form, hSU]
  have hrho : ∀ x : ι → AF F, M.co.rho ψ (∑ i, x i • S i) = schr ψ (∑ i, x i • M.co.e (S i)) := fun x => by
    simp only [Darboux.rho, map_sum, map_smul]
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : K => om (k.1, h) Φ)
    (fun k => hw.isUSplitting.pres (k.1, h) Φ hΦ) fun l hl => by
      have hc := (hw.2.2 l hl Φ hΦ).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ X.J => (g, h))
      obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  choose C hCb using fun j => slice_decay ψ hψ (fun i => M.co.e (S i)) (fun i => M.co.e (U i)) hSU' e hsl
    (fun i a Ψ hΨ => by
      have := hinv i a Ψ hΨ
      rwa [Darboux.rho, map_smul] at this) (hg j) (f j) (hf j) hΩ p hp N
  refine ⟨∑ j, C j, fun k hk x hx => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ x hx
  refine ⟨∑ j, f₁ j, ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, hrho]
    change coeL (∑ j, f₁ j) = e (schrL ψ _ _)
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hf₁ j
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans (Finset.sum_le_sum fun j _ => hb₁ j)

theorem exists_continuous_bound (μ : Measure (AE F E)ˣ) [μ.IsHaarMeasure] {z : ℕ} (hz : 1 < z)
    {Ω : Set (Fin (Module.finrank F E) → Af F)} (hΩ : IsCompact Ω) :
    ∃ (N : ℕ) (D : (AE F E)ˣ → ℝ), Continuous D ∧ Integrable D μ ∧ (∀ l, 0 ≤ D l) ∧
      ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ Ω →
        (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ z ≤ D l := by
  haveI : BorelSpace (AE F E)ˣ := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := inferInstance
  obtain ⟨φ, hφ1, -, hφc, hφ⟩ := exists_continuous_one_zero_of_isCompact hΩ isClosed_empty (Set.disjoint_empty _)
  obtain ⟨N, hN⟩ := GlobalTheory.ThetaConeSwap.lintegral_maj_lt_top μ (s := (z : ℝ)) (by exact_mod_cast hz) hφc.isCompact
  have hcrd : Continuous fun l : (AE F E)ˣ => GlobalTheory.XTermMaj.crd F E (l : AE F E) :=
    (IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun.toLinearMap).comp Units.continuous_val
  let r : (AE F E)ˣ → ℝ := fun l => 1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖
  have hr0 : ∀ l, 0 < r l := fun l => by positivity
  have hr : Continuous r := continuous_const.add <| continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun v _ =>
    ((continuous_apply v).comp (continuous_fst.comp ((continuous_apply i).comp hcrd))).norm
  let y : (AE F E)ˣ → Fin (Module.finrank F E) → Af F := fun l i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2
  have hy : Continuous y := continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp hcrd)
  let D : (AE F E)ˣ → ℝ := fun l => φ (y l) * (r l ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ z)
  have hD : Continuous D := (φ.continuous.comp hy).mul ((hr.rpow_const fun l => Or.inl (hr0 l).ne').mul
    ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow z))
  have hw : ∀ l, 0 ≤ r l ^ (-(N : ℝ)) * (absE F E l : ℝ) ^ z := fun l =>
    mul_nonneg (Real.rpow_nonneg (hr0 l).le _) (pow_nonneg (NNReal.coe_nonneg _) _)
  have hD0 : ∀ l, 0 ≤ D l := fun l => mul_nonneg (hφ _).1 (hw l)
  refine ⟨N, D, hD, ⟨hD.measurable.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono fun l => ?_) hN⟩, hD0,
    fun l hl => ?_⟩
  · rw [Real.enorm_of_nonneg (hD0 l)]
    by_cases hl : y l ∈ tsupport φ
    · rw [GlobalTheory.XTermMaj.maj, Set.indicator_of_mem hl, ← ENNReal.ofReal_mul (Real.rpow_nonneg (hr0 l).le _), Real.rpow_natCast]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (hw l) (hφ _).2)
    · have : D l = 0 := by simp only [D, image_eq_zero_of_notMem_tsupport hl, zero_mul]
      rw [this, ENNReal.ofReal_zero]
      exact zero_le
  · have : φ (y l) = 1 := hφ1 hl
    simp only [D, this, one_mul]
    exact le_rfl

theorem seminorm_slice_le : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h, ∀ (c : Fin b × Fin (a + b) → FiniteAdeleRing (𝓞 F) F) (S : K → (AE F E)ˣ → SchwartzMap (Fin b × Fin (a + b) → mixedEmbedding.mixedSpace F) ℂ),
        (∀ k l s, S k l s = e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ'))
            (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i), c i) : AdeleRing (𝓞 F) F)) * (X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) →
        ∀ m n : ℕ, ∃ C : (AE F E)ˣ → ℝ, Continuous C ∧ Integrable C μ ∧ ∀ k l, SchwartzMap.seminorm ℂ m n (S k l) ≤ C l := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC e he K μK μ hK _ hμ X om om' om₁ om₁' hT _ Φ hΦ h c S hS m n
  have hψ := hT.base.std
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B G.V' :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B G.V' g).symm
  have hKc : IsCompact (K : Set (UA σ G.V'.J)) := by
    have hX := hT.geo.hV'
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B (b + 2) G.V' _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B G.V' (GlobalTheory.T.isClosed_adelic_lattice_closure F E (b + 2) G.V' hX.lat)) hsub
  have hΦA : Φ ∈ schA F _ := GlobalTheory.ConeTermCont.polData_le B G.M' hT.geo.hM' hΦ.1
  obtain ⟨t, ht⟩ := GlobalTheory.ThetaConeSwap.exists_dual (x := H.x) (y := H.y) hT.base.cm
    (by rw [GlobalTheory.ThetaConeSwap.form_herm hT.base.cm hT.geo.hV'.herm, hC.hH.xy, map_one]) hC.hH'.xy
  have hinv : ∀ i (a' : AF F), ∀ Ψ ∈ schA F _, (sliceL c ∘ₗ e) (G.M'.co.rho B.ψ
      (a' • inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ) = (sliceL c ∘ₗ e) Ψ :=
    fun i a' Ψ hΨ => congrArg (sliceL c) (he.inv _ (Or.inl ⟨a' • inclR (F := F) (AF F) (t i) • incV F H'.y, by
        rw [Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩) Ψ hΨ)
  obtain ⟨Ω, hΩ, hsupp⟩ := exists_support G.M' B.ψ hψ hT.weil' hKc h hΦA (sliceL c ∘ₗ e)
    (fun j => inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
    (fun i => inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
    (fun i j => by convert ht i j) hinv
  set z : ℕ := (a - (b + 2)) / 2 + 1 with hz
  have hz1 : 1 < z := by
    have := hT.geo.eBig
    omega
  obtain ⟨N, D, hDc, hDi, hD0, hD⟩ := exists_continuous_bound μ hz1 hΩ
  obtain ⟨C, hCb⟩ := exists_decay G.M' B.ψ hψ hT.weil' hKc h hΦA (sliceL c ∘ₗ e) (exists_slice_clm hT.geo.hM' he c)
    (fun j => inclR (F := F) (AF F) (σ (Module.finBasis F E j)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x))
    (fun i => inclR (F := F) (AF F) (t i) • Matrix.vecMulVec (incV F H.x) (incV F H'.y))
    (fun i j => by convert ht i j) hinv hΩ (SchwartzMap.seminorm ℂ m n)
    ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (m, n)) N
  have hsh : ∀ l : (AE F E)ˣ, shiftB σ H H' l = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i •
      inclR (F := F) (AF F) (σ (Module.finBasis F E i)) • Matrix.vecMulVec (incV F H.y) (incV F H'.x) := fun l => by
    simp only [← smul_assoc, ← Finset.sum_smul]
    rw [shiftB, GlobalTheory.ThetaConeSwap.cA_eq_sum]
  have hS' : ∀ (k : K) (l : (AE F E)ˣ) (f : SInf F (Fin b × Fin (a + b))),
      ⇑f = (sliceL c ∘ₗ e) (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, h) Φ)) →
      S k l = ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) • f := fun k l f hf => by
    ext s
    rw [hS, SchwartzMap.smul_apply, hf, smul_eq_mul, mul_assoc, mul_comm]
    rfl
  refine ⟨fun l => |C| * D l, continuous_const.mul hDc, hDi.const_mul _, fun k l => ?_⟩
  by_cases hl : (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ Ω
  · obtain ⟨f, hf, hb⟩ := hCb k.1 k.2 _ hl
    rw [← hsh] at hf
    rw [hS' k l f hf, map_smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hD l hl) (abs_nonneg C))
    rw [mul_comm, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right (hb.trans ?_) (pow_nonneg (NNReal.coe_nonneg _) _)
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)
  · have h0 := hsupp k.1 k.2 _ hl
    rw [← hsh] at h0
    rw [hS' k l 0 (by rw [h0]; rfl), smul_zero, map_zero]
    exact mul_nonneg (abs_nonneg C) (hD0 l)

end GlobalTheory.ConeSliceBound

end
