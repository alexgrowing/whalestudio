import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenStabilizerIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerHaarAdelicStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
open scoped Classical
open GlobalTheory.ThKSoDecay

namespace GlobalTheory.OuterFinInt

private theorem ideles_lcsc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    IsTopologicalGroup (AE F E)ˣ ∧ LocallyCompactSpace (AE F E)ˣ ∧ SecondCountableTopology (AE F E)ˣ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : SecondCountableTopology (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (AE F E)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact ⟨inferInstance, Units.isClosedEmbedding_embedProduct.locallyCompactSpace,
    Units.isEmbedding_embedProduct.secondCountableTopology⟩

private theorem hasFiniteIntegral_of_bound {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) (μ₁ : Measure β) (μ₂ : Measure γ) [IsFiniteMeasure ν] [IsFiniteMeasure μ₁] [SFinite μ₂]
    (f : α × β × γ → ℂ) (c : γ → ℝ) (hc : Integrable c μ₂) (hf : ∀ p, ‖f p‖ ≤ c p.2.2) :
    HasFiniteIntegral f (ν.prod (μ₁.prod μ₂)) :=
  ((hc.comp_snd μ₁).comp_snd ν).2.mono' (Eventually.of_forall hf)

variable {F : Type} [Field F] [NumberField F]

private def mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : AF F :=
  (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a) b : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem evI_mkA (a : mixedEmbedding.mixedSpace F) (b : Af F) : evI F (mkA a b) = a := by
  simp [evI, mkA]

private theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a b : (κ → Af F) → ℂ) :
    pureA F f (a + b) = pureA F f a + pureA F f b := by
  funext x; simp [pureA, mul_add]

private theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ) (a : (κ → Af F) → ℂ) :
    pureA F f (c • a) = c • pureA F f a := by
  funext x; simp [pureA]; ring

private theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
  funext x; simp [pureA]

private theorem pureA_mkA {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (a : (κ → Af F) → ℂ)
    (y : κ → mixedEmbedding.mixedSpace F) (z : κ → Af F) : pureA F f a (fun i => mkA (y i) (z i)) = f y * a z := by
  simp only [pureA]
  congr 1
  congr 1
  funext i
  exact evI_mkA (y i) (z i)

private theorem thetaSum_finset_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ)
    (h : ∀ i ∈ s, Φ i ∈ schA F κ) : thetaSum F (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaSum F (Φ i) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      thetaSum_add F (h a (Finset.mem_insert_self a s)) (Submodule.sum_mem _ fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

private theorem semK_le_sum {κ : Type} [Fintype κ] (k : ℕ) (f : SInf F κ) :
    semK κ k f ≤ ∑ p ∈ Finset.Iic (k, k), SchwartzMap.seminorm ℂ p.1 p.2 f := by
  have := Seminorm.finset_sup_le_sum (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) (Finset.Iic (k, k)) f
  refine this.trans (le_of_eq ?_)
  induction (Finset.Iic (k, k)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem bound_sum (hP : KP) {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hPair : IsPair B M χX χW om r s r' s')
    {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ) (hφ : ∀ j, φ j ∈ SB (Fin n × Fin d → Af F)) (h : UA σ W.J) :
    ∃ (C : Fin m → ℝ) (k : Fin m → ℕ), (∀ j, 0 ≤ C j) ∧ ∀ w : Fin m → SInf F (Fin n × Fin d),
      ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ → ∀ x,
        ‖theta om (∑ j, pureA F (w j) (φ j)) x h‖ ≤ ∑ j, C j * semK (Fin n × Fin d) (k j) (w j) := by
  have hU := soDecayUnif hP F E σ B n d X W M χX χW om r s r' s' hPair
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    hPair.weil.isUSplitting.pres
  let So := M.So B.ψ B.τ₁
  let T' : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) :=
    { carrier := {a | ∀ g : SInf F (Fin n × Fin d), pureA F g a ∈ So}
      add_mem' := fun ha hb g => by rw [pureA_add]; exact So.add_mem (ha g) (hb g)
      zero_mem' := fun g => by rw [pureA_zero]; exact So.zero_mem
      smul_mem' := fun c a ha g => by rw [pureA_smul]; exact So.smul_mem c (ha g) }
  let T := SB (Fin n × Fin d → Af F) ⊓ T'
  have hslice : ∀ Φ ∈ So, ∀ y : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      (fun z : Fin n × Fin d → Af F => Φ (fun i => mkA (y i) (z i))) ∈ T' := by
    intro Φ hΦ y
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, ψ, h1, h2, h3, rfl⟩ := hΦ
      let a : (Fin n × Fin d → Af F) → ℂ := fun z => ∏ᶠ v, ψ v fun i => evFin F v (mkA 0 (z i))
      have e1 : (fun z : Fin n × Fin d → Af F => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g ψ (fun i => mkA (y i) (z i))) = g y • a := by
        funext z
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, a]
        congr 1
        congr 1
        funext i
        exact evI_mkA (y i) (z i)
      have e2 : ∀ g' : SInf F (Fin n × Fin d), pureA F g' a = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' ψ := fun g' => by
        funext x
        rfl
      rw [e1]
      refine T'.smul_mem _ fun g' => ?_
      rw [e2]
      exact Submodule.subset_span ⟨g', ψ, h1, h2, h3, rfl⟩
    | zero =>
      have e0 : (fun z : Fin n × Fin d → Af F => (0 : (Fin n × Fin d → AF F) → ℂ) (fun i => mkA (y i) (z i))) = 0 := rfl
      rw [e0]
      exact T'.zero_mem
    | add Φ Ψ _ _ hΦ hΨ => exact T'.add_mem hΦ hΨ
    | smul c Φ _ hΦ => exact T'.smul_mem c hΦ
  obtain ⟨Cm, hC⟩ := Submodule.exists_isCompl T
  have hdec : ∀ j, ∃ t ∈ T, ∃ c ∈ Cm, t + c = φ j := fun j =>
    Submodule.mem_sup.1 (hC.sup_eq_top ▸ Submodule.mem_top)
  choose t htT c hcC htc using hdec
  have hcSB : ∀ j, c j ∈ SB (Fin n × Fin d → Af F) := fun j => by
    have : c j = φ j - t j := by rw [← htc j]; abel
    rw [this]; exact Submodule.sub_mem _ (hφ j) (htT j).1
  have hred : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ So →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) := by
    intro w hw
    have e : ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (t j) + ∑ j, pureA F (w j) (c j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [← pureA_add, htc j]
    have hΨ : ∑ j, pureA F (w j) (c j) ∈ So := by
      have : ∑ j, pureA F (w j) (c j) = ∑ j, pureA F (w j) (φ j) - ∑ j, pureA F (w j) (t j) := by
        rw [e]; abel
      rw [this]
      exact So.sub_mem hw (So.sum_mem fun j _ => (htT j).2 (w j))
    have h0 : ∀ y, ∑ j, w j y • c j = 0 := by
      intro y
      have h1 : ∑ j, w j y • c j ∈ T := by
        refine ⟨SB _ |>.sum_mem fun j _ => (SB _).smul_mem _ (hcSB j), ?_⟩
        have := hslice _ hΨ y
        have e' : (fun z : Fin n × Fin d → Af F => (∑ j, pureA F (w j) (c j)) (fun i => mkA (y i) (z i))) =
            ∑ j, w j y • c j := by
          funext z
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureA_mkA]
        rwa [e'] at this
      have h2 : ∑ j, w j y • c j ∈ Cm := Cm.sum_mem fun j _ => Cm.smul_mem _ (hcC j)
      have := hC.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨h1, h2⟩)
      exact (Submodule.mem_bot ℂ).1 this
    rw [e, add_eq_left]
    funext x
    have := congrFun (h0 fun i => evI F (x i)) (fun i => (x i).2)
    simpa [pureA, Finset.sum_apply, evI] using this
  have hmem : ∀ (a : (Fin n × Fin d → Af F) → ℂ), a ∈ SB (Fin n × Fin d → Af F) → ∀ g : SInf F (Fin n × Fin d),
      pureA F g a ∈ schA F (Fin n × Fin d) := fun a ha g => Submodule.subset_span ⟨g, a, ha, rfl⟩
  have hbd : ∀ j, ∃ (C0 : ℝ) (k0 : ℕ), 0 ≤ C0 ∧ ∀ (g : SInf F (Fin n × Fin d)) x,
      ‖theta om (pureA F g (t j)) x h‖ ≤ C0 * semK (Fin n × Fin d) k0 g := by
    intro j
    obtain ⟨C0, k0, hC0⟩ := hU (t j) (htT j).1 (htT j).2 0
    have hh : (0 : ℝ) ≤ (ht h : ℝ) ^ k0 := pow_nonneg (NNReal.coe_nonneg _) _
    refine ⟨max C0 0 * (ht h : ℝ) ^ k0, k0, mul_nonneg (le_max_right _ _) hh, fun g x => ?_⟩
    have := hC0 g x h
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    have hs : 0 ≤ semK (Fin n × Fin d) k0 g := apply_nonneg _ _
    calc C0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0
        ≤ max C0 0 * semK (Fin n × Fin d) k0 g * (ht h : ℝ) ^ k0 := by gcongr; exact le_max_left _ _
      _ = max C0 0 * (ht h : ℝ) ^ k0 * semK (Fin n × Fin d) k0 g := by ring
  choose C k hC0 hCb using hbd
  refine ⟨C, k, hC0, fun w hw x => ?_⟩
  rw [hred w hw]
  have e : theta om (∑ j, pureA F (w j) (t j)) x h = ∑ j, theta om (pureA F (w j) (t j)) x h := by
    simp only [theta]
    rw [map_sum]
    exact thetaSum_finset_sum _ _ fun j _ => hpres _ _ (hmem _ (htT j).1 (w j))
  rw [e]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hCb j (w j) x)

private theorem integrand_hasFiniteIntegral : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        HasFiniteIntegral (fun p : UA σ G₁.V'.J × K × (AE F E)ˣ => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, h) Φ'))) p.1 h₁ * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ((G₁.M'.μ.restrict G₁.M'.dom).prod (μK.prod μ)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h h₁
  obtain ⟨_, _, _⟩ := ideles_lcsc F E
  haveI : SigmaCompactSpace (AE F E)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SFinite μ := @instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.SigmaFinite.of_isFiniteMeasureOnCompacts μ)
  obtain ⟨K₀, -, -, hK₀, hc, -, -⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B (b + 2) G.V' G.q (b + 2 - G.q) hT.base hT.geo.hV'
  have hKK : (K : Set (UA σ G.V'.J)) = K₀ := by
    ext g
    exact (hK g).trans (hK₀ g).symm
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp (hKK ▸ hc)
  haveI : IsFiniteMeasure μK := CompactSpace.isFiniteMeasure
  haveI : IsFiniteMeasure (G₁.M'.μ.restrict G₁.M'.dom) := isFiniteMeasure_restrict.2
    (GlobalTheory.ThKContSmall.measure_dom_lt_top hKP.siegelSetUnitary hT₁.base hT₁.geo.hV' hT₁.geo.hM').ne
  obtain ⟨r, g, f, hg, hsum, -, hbd⟩ :=
    GlobalTheory.T.config_b_stabilizer_haar_adelic hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  have hSo := GlobalTheory.T.config_b_eigen_stabilizer_integral hKP F E σ B a b G G₁ H H' hC e' he' K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h
  obtain ⟨C, k, hC0, hCb⟩ := bound_sum hKP (GlobalTheory.ThKContSmall.isPair_small hT₁) g hg h₁
  choose c _hcc hci hcb using hbd
  refine hasFiniteIntegral_of_bound _ _ _ _ (fun l => ∑ j, C j * ∑ p ∈ Finset.Iic (k j, k j), c j p.1 p.2 l)
    (integrable_finset_sum _ fun j _ => (integrable_finset_sum _ fun p _ => hci j p.1 p.2).const_mul _) ?_
  rintro ⟨x, κ, l⟩
  have e : ∑ j, pureA F (f j κ l) (g j) =
      ((X.ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) •
        e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (κ.1, h) Φ')) := by
    funext y
    rw [Finset.sum_apply, ← hsum κ l y, Pi.smul_apply, smul_eq_mul]
    ring
  have hmem : ∑ j, pureA F (f j κ l) (g j) ∈ G₁.M'.So B.ψ B.τ₁ := by
    rw [e]
    exact Submodule.smul_mem _ _ (hSo κ l)
  have h1 := hCb (fun j => f j κ l) hmem x
  have e2 : theta om₁' (∑ j, pureA F (f j κ l) (g j)) x h₁ =
      theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (κ.1, h) Φ'))) x h₁ * (X.ν l : ℂ) *
        ((absE F E l : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1) := by
    rw [e]
    simp only [theta]
    rw [map_smul, thetaSum_smul]
    ring
  rw [e2] at h1
  refine h1.trans (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hC0 j))
  exact (semK_le_sum _ _).trans (Finset.sum_le_sum fun p _ => hcb j p.1 p.2 κ l)

end GlobalTheory.OuterFinInt

end

theorem _root_.GlobalTheory.T.haar_stabilizer_period_case_b_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ h h₁,
        HasFiniteIntegral (fun p : UA σ G₁.V'.J × K × (AE F E)ˣ => theta om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' p.2.2) (om' (p.2.1.1, h) Φ'))) p.1 h₁ * (X.ν p.2.2 : ℂ) * ((absE F E p.2.2 : ℝ) : ℂ) ^ ((a - (b + 2)) / 2 + 1)) ((G₁.M'.μ.restrict G₁.M'.dom).prod (μK.prod μ)) :=
  GlobalTheory.OuterFinInt.integrand_hasFiniteIntegral
