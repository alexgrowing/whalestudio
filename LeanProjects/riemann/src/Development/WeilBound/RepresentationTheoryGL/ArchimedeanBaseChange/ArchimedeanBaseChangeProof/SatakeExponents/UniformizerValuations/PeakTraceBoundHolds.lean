import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularizedExponentialSumStatement

noncomputable section

set_option linter.style.haveILetI false

open scoped ComplexOrder

namespace PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures

section Gel

variable {E : Type*} [CStarAlgebra E]

theorem restr (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (ψ : S.topologicalClosure →ₐ[ℂ] ℂ) :
    ∃ χ : S →⋆ₐ[ℂ] ℂ, (∀ y, ‖χ y‖ ≤ ‖(y : E)‖) ∧
      ∀ y, χ y = ψ (StarSubalgebra.inclusion S.le_topologicalClosure y) := by
  have : IsClosed (S.topologicalClosure : Set E) := S.isClosed_topologicalClosure
  have : Nontrivial S.topologicalClosure :=
    ⟨⟨0, 1, fun h => by simpa using congrArg ψ h⟩⟩
  have : StarHomClass (S.topologicalClosure →ₐ[ℂ] ℂ) S.topologicalClosure ℂ :=
    AlgHomClass.instStarHomClass
  refine ⟨{ ψ.comp (StarSubalgebra.inclusion S.le_topologicalClosure).toAlgHom with
    map_star' := fun y => ?_ }, fun y => ?_, fun y => rfl⟩
  · change ψ (StarSubalgebra.inclusion S.le_topologicalClosure (star y)) =
      star (ψ (StarSubalgebra.inclusion S.le_topologicalClosure y))
    rw [map_star, map_star]
  · change ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure y)‖ ≤ ‖(y : E)‖
    exact (AlgHom.norm_apply_le_self ψ _).trans_eq rfl

theorem norm_le_of_chars (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (x : E) (hx : x ∈ S) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨x, hx⟩)‖ ≤ c) : ‖x‖ ≤ c := by
  have : IsClosed (S.topologicalClosure : Set E) := S.isClosed_topologicalClosure
  have hs' : ∀ x y : S, x * y = y * x := fun x y => Subtype.ext (hS _ x.2 _ y.2)
  letI : NormedCommRing S.topologicalClosure :=
    { SubringClass.toNormedRing S.topologicalClosure with
      mul_comm := (S.commRingTopologicalClosure hs').mul_comm }
  letI : CommCStarAlgebra S.topologicalClosure := { }
  set xc := StarSubalgebra.inclusion S.le_topologicalClosure ⟨x, hx⟩
  have h1 : ‖x‖ = ‖xc‖ := rfl
  rw [h1, ← (AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry S.topologicalClosure) xc]
  refine (ContinuousMap.norm_le _ hc).2 fun φ => ?_
  have := h (WeakDual.CharacterSpace.equivAlgHom φ)
  rwa [WeakDual.CharacterSpace.equivAlgHom_coe] at this

theorem finite_cover (S : StarSubalgebra ℂ E) (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    {κ : Type*} (f : κ → E) (hf : ∀ i, f i ∈ S) (b : E) (hb : b ∈ S) (ε : ℝ)
    (h : ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ε ≤ ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖ →
        ∃ i, 1 < ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖) :
    ∃ t : Finset κ, ∀ ψ : S.topologicalClosure →ₐ[ℂ] ℂ,
      ε ≤ ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖ →
        ∃ i ∈ t, 1 < ‖ψ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖ := by
  classical
  have : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe
  have hev : ∀ a : S.topologicalClosure,
      Continuous (fun φ : WeakDual.characterSpace ℂ S.topologicalClosure => φ a) :=
    fun a => (WeakDual.eval_continuous a).comp continuous_subtype_val
  let K : Set (WeakDual.characterSpace ℂ S.topologicalClosure) :=
    {φ | ε ≤ ‖φ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨b, hb⟩)‖}
  have hK : IsClosed K := isClosed_le continuous_const (hev _).norm
  let U : κ → Set (WeakDual.characterSpace ℂ S.topologicalClosure) :=
    fun i => {φ | 1 < ‖φ (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖}
  have hU : ∀ i, IsOpen (U i) := fun i => isOpen_lt continuous_const (hev _).norm
  have hcov : K ⊆ ⋃ i, U i := by
    intro φ hφ
    obtain ⟨i, hi⟩ := h (WeakDual.CharacterSpace.equivAlgHom φ)
      (by rw [WeakDual.CharacterSpace.equivAlgHom_coe]; exact hφ)
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rw [WeakDual.CharacterSpace.equivAlgHom_coe] at hi
    exact hi
  obtain ⟨t, ht⟩ := hK.isCompact.elim_finite_subcover U hU hcov
  refine ⟨t, fun ψ hψ => ?_⟩
  have hmem : WeakDual.CharacterSpace.equivAlgHom.symm ψ ∈ K := by
    show ε ≤ ‖(WeakDual.CharacterSpace.equivAlgHom.symm ψ) _‖
    rw [WeakDual.CharacterSpace.equivAlgHom_symm_coe]; exact hψ
  have := ht hmem
  simp only [Set.mem_iUnion] at this
  obtain ⟨i, hi, hi'⟩ := this
  refine ⟨i, hi, ?_⟩
  have hi'' : 1 < ‖(WeakDual.CharacterSpace.equivAlgHom.symm ψ)
      (StarSubalgebra.inclusion S.le_topologicalClosure ⟨f i, hf i⟩)‖ := hi'
  rwa [WeakDual.CharacterSpace.equivAlgHom_symm_coe] at hi''

end Gel

theorem nil_pow_sub {R : Type*} [Ring R] {x y : R} (h : Commute x y) (hn : IsNilpotent (x - y))
    (k : ℕ) : IsNilpotent (x ^ k - y ^ k) := by
  rw [← h.geom_sum₂_mul k]
  refine Commute.isNilpotent_mul_left ?_ hn
  refine Commute.sum_left _ _ _ fun i _ => ?_
  exact (((Commute.refl x).sub_right h).pow_left i).mul_left
    ((h.symm.sub_right (Commute.refl y)).pow_left _)

theorem trace_pow_eq {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hfin : {μ | T.maxGenEigenspace μ ≠ ⊥}.Finite) (k : ℕ) :
    LinearMap.trace ℂ V (T ^ k) =
      ∑ μ ∈ hfin.toFinset, (Module.finrank ℂ (T.maxGenEigenspace μ) : ℂ) * μ ^ k := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    T.independent_maxGenEigenspace (Module.End.iSup_maxGenEigenspace_eq_top T)
  have hk : ∀ μ, Set.MapsTo (T ^ k) (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) :=
    fun μ => T.mapsTo_maxGenEigenspace_of_comm (Commute.self_pow T k) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds hfin hk]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h1 := T.mapsTo_maxGenEigenspace_of_comm (Commute.refl T) μ
  have hnil := T.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hpow : (T ^ k).restrict (hk μ) = (T.restrict h1) ^ k :=
    (Module.End.pow_restrict (f' := T) k h1).symm
  have hA : Set.MapsTo (algebraMap ℂ (Module.End ℂ V) μ) (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) :=
    fun x hx => by simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ μ hx
  have hAe : (algebraMap ℂ (Module.End ℂ V) μ).restrict hA =
      algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ := by
    ext x
    show (algebraMap ℂ (Module.End ℂ V) μ) x.1 = _
    simp [Module.algebraMap_end_apply]
  have hnil' : IsNilpotent (T.restrict h1 - algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ) := by
    rw [← hAe, LinearMap.restrict_sub h1 hA]; exact hnil
  have hcomm : Commute (T.restrict h1) (algebraMap ℂ (Module.End ℂ (T.maxGenEigenspace μ)) μ) :=
    Algebra.commute_algebraMap_right _ _
  have hn2 : IsNilpotent ((T.restrict h1) ^ k - algebraMap ℂ _ (μ ^ k)) := by
    rw [map_pow]
    exact nil_pow_sub hcomm hnil' k
  have := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent (μ ^ k)
    (Commute.one_left ((T.restrict h1) ^ k)) hn2
  rw [Module.End.one_eq_id, LinearMap.id_comp] at this
  rw [hpow, this, LinearMap.trace_id]
  ring

theorem trace_contra {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (v : V) (hv : v ≠ 0) (μ : ℂ) (hTv : T v = μ • v) (r C : ℝ) (N j : ℕ)
    (hr : 0 ≤ r) (hrμ : r < ‖μ‖)
    (h : ∀ᶠ k : ℕ in Filter.atTop, ‖LinearMap.trace ℂ V (T ^ k)‖ ≤ C * (1 + k) ^ N * r ^ (k - j)) :
    False := by
  classical
  have hfin : {μ | T.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep T.independent_maxGenEigenspace
  set r' : ℝ := (r + ‖μ‖) / 2 with hr'
  have hr'0 : 0 < r' := by
    have : 0 < ‖μ‖ := lt_of_le_of_lt hr hrμ
    rw [hr']; linarith
  have hrr' : r ≤ r' := by rw [hr']; linarith
  have hr'μ : r' < ‖μ‖ := by rw [hr']; linarith
  let ι := (hfin.toFinset : Set ℂ)
  have key := GlobalTheory.T.regularized_exponential_sum ι (fun i => (Module.finrank ℂ (T.maxGenEigenspace i.1) : ℂ))
    (fun i => i.1) r' (max C 0 * (r' ^ j)⁻¹) N hr'0.le ?_ μ hr'μ
  ·
    have hmem : μ ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      intro hbot
      have hvm : v ∈ T.maxGenEigenspace μ :=
        Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hTv)
      rw [hbot] at hvm
      exact hv ((Submodule.mem_bot ℂ).mp hvm)
    rw [Finset.sum_eq_single_of_mem (⟨μ, Finset.mem_coe.mpr hmem⟩ : ι) (by simp)
      (fun b _ hb => by
        exfalso
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at *
        exact hb (Subtype.ext (by assumption)))] at key
    simp only [Nat.cast_eq_zero] at key
    have hpos : Module.finrank ℂ (T.maxGenEigenspace μ) ≠ 0 := by
      rw [Set.Finite.mem_toFinset] at hmem
      exact Submodule.finrank_eq_zero.not.mpr hmem
    exact hpos key
  · filter_upwards [h, Filter.eventually_ge_atTop j] with k hk hkj
    have hsum : ∑ i : ι, (Module.finrank ℂ (T.maxGenEigenspace i.1) : ℂ) * i.1 ^ k =
        LinearMap.trace ℂ V (T ^ k) := by
      rw [trace_pow_eq T hfin k]
      exact Finset.sum_coe_sort hfin.toFinset (fun i => (Module.finrank ℂ (T.maxGenEigenspace i) : ℂ) * i ^ k)
    rw [hsum]
    refine hk.trans ?_
    have h1 : r ^ (k - j) ≤ r' ^ (k - j) := pow_le_pow_left₀ hr hrr' _
    have h2 : r' ^ (k - j) = (r' ^ j)⁻¹ * r' ^ k := by
      rw [pow_sub₀ _ hr'0.ne' hkj]; ring
    have h3 : (0 : ℝ) ≤ (1 + k) ^ N := by positivity
    calc C * (1 + k) ^ N * r ^ (k - j) ≤ max C 0 * (1 + k) ^ N * r ^ (k - j) := by
          gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (1 + k) ^ N * r' ^ (k - j) := by gcongr
      _ = max C 0 * (r' ^ j)⁻¹ * (1 + k) ^ N * r' ^ k := by rw [h2]; ring

theorem adjoin_comm {A : Type} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : H →L[ℂ] H) (m : ℕ) (hβ : ∀ g, Commute β (R g)) :
    ∀ x ∈ StarAlgebra.adjoin ℂ (Set.range R ∪ {star (β ^ m) * β ^ m}),
      ∀ y ∈ StarAlgebra.adjoin ℂ (Set.range R ∪ {star (β ^ m) * β ^ m}), x * y = y * x := by
  have hB : ∀ g, Commute (star (β ^ m) * β ^ m) (R g) := by
    intro g
    have h1 : Commute (β ^ m) (R g) := (hβ g).pow_left m
    have h2 : Commute (star (β ^ m)) (R g) := by
      have h3 := ((hβ (star g)).pow_left m).star_star
      rwa [map_star, star_star] at h3
    exact h2.mul_left h1
  have hcomm : ∀ a ∈ Set.range R ∪ {star (β ^ m) * β ^ m},
      ∀ b ∈ Set.range R ∪ {star (β ^ m) * β ^ m}, a * b = b * a := by
    rintro a (⟨g, rfl⟩ | ha) b (⟨g', rfl⟩ | hb)
    · rw [← map_mul, ← map_mul, mul_comm]
    · rw [Set.mem_singleton_iff] at hb; subst hb; exact ((hB g).eq).symm
    · rw [Set.mem_singleton_iff] at ha; subst ha; exact (hB g').eq
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  have hcs : ∀ a ∈ Set.range R ∪ {star (β ^ m) * β ^ m},
      ∀ b ∈ Set.range R ∪ {star (β ^ m) * β ^ m}, a * star b = star b * a := by
    intro a ha b hb
    rcases hb with ⟨g', rfl⟩ | hb
    · rw [← map_star]; exact hcomm a ha _ (Or.inl ⟨_, rfl⟩)
    · rw [Set.mem_singleton_iff] at hb; subst hb
      rw [star_mul, star_star]; exact hcomm a ha _ (Or.inr rfl)
  intro x hx y hy
  letI := StarAlgebra.adjoinCommRingOfComm ℂ hcomm hcs
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : StarAlgebra.adjoin ℂ _) ⟨y, hy⟩)

theorem peak {A : Type} [CommRing A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
    [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)]
    (R : ∀ s, A →⋆ₐ[ℂ] (H s →L[ℂ] H s)) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ) (p : A →⋆ₐ[ℂ] ℂ)
    (hβ : ∀ s g, Commute (β s) (R s g))
    (hne : ∀ s (χ : StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m}) →⋆ₐ[ℂ] ℂ),
      (∀ x, ‖χ x‖ ≤ ‖(x : H s →L[ℂ] H s)‖) →
      (∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g) →
      χ ⟨star (β s ^ m) * β s ^ m, StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)⟩ = 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ g : A, p g = 1 ∧ ∀ s, ‖β s ^ m * R s g‖ ≤ ε := by
  classical
  let S : ∀ s, StarSubalgebra ℂ (H s →L[ℂ] H s) :=
    fun s => StarAlgebra.adjoin ℂ (Set.range (R s) ∪ {star (β s ^ m) * β s ^ m})
  have hSc : ∀ s, ∀ x ∈ S s, ∀ y ∈ S s, x * y = y * x := fun s => adjoin_comm (R s) (β s) m (hβ s)
  have hR : ∀ s g, R s g ∈ S s := fun s g => StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)
  have hB : ∀ s, star (β s ^ m) * β s ^ m ∈ S s :=
    fun s => StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  let θ : ∀ s, (S s →⋆ₐ[ℂ] ℂ) → (A →⋆ₐ[ℂ] ℂ) :=
    fun s χ => χ.comp (StarAlgHom.codRestrict (R s) (S s) (hR s))
  have hθ : ∀ s χ g, θ s χ g = χ ⟨R s g, hR s g⟩ := fun _ _ _ => rfl
  set ε0 : ℝ := ε ^ 2 with hε0
  have hε0p : 0 < ε0 := by positivity
  let d : A → A := fun g => g - algebraMap ℂ A (p g)
  have hpd : ∀ g, p (d g) = 0 := by
    intro g; simp only [d, map_sub]; rw [AlgHomClass.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hcov : ∀ s, ∃ t : Finset A, ∀ ψ : (S s).topologicalClosure →ₐ[ℂ] ℂ,
      ε0 ≤ ‖ψ (StarSubalgebra.inclusion (S s).le_topologicalClosure ⟨_, hB s⟩)‖ →
        ∃ g ∈ t, 1 < ‖ψ (StarSubalgebra.inclusion (S s).le_topologicalClosure ⟨_, hR s (d g)⟩)‖ := by
    intro s
    apply finite_cover (S s) (hSc s) (fun g => R s (d g)) (fun g => hR s (d g)) _ (hB s) ε0
    intro ψ hψ
    by_contra hno
    push_neg at hno
    obtain ⟨χ, hχb, hχ⟩ := restr (S s) (hSc s) ψ
    have hz : ∀ g, θ s χ (d g) = 0 := by
      intro g
      by_contra hz
      have h2 := hno ((2 / θ s χ (d g)) • g)
      rw [← hχ, ← hθ] at h2
      have hd : d ((2 / θ s χ (d g)) • g) = (2 / θ s χ (d g)) • d g := by
        simp only [d, map_smul, smul_sub, smul_eq_mul, Algebra.algebraMap_eq_smul_one, smul_smul]
      rw [hd, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz] at h2
      norm_num at h2
    have hp : ∀ g, χ ⟨R s g, StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)⟩ = p g := by
      intro g
      have := hz g
      rw [show d g = g - algebraMap ℂ A (p g) from rfl, map_sub, AlgHomClass.commutes] at this
      rw [← hθ]
      simpa [sub_eq_zero] using this
    have h0 := hne s χ hχb hp
    rw [← hχ] at hψ
    rw [h0, norm_zero] at hψ
    linarith
  choose t ht using hcov
  set h : A := ∑ s, ∑ g ∈ t s, star (d g) * d g with hh
  have hph : p h = 0 := by simp [hh, map_sum, map_mul, map_star, hpd]
  set M : ℝ := 2 + ∑ s, ‖R s h‖ with hM
  have hM2 : ∀ s, ‖R s h‖ + 2 ≤ M := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖R s h‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
    linarith
  have hMpos : 0 < M := by have := hM2 (Classical.arbitrary ι); linarith [norm_nonneg (R (Classical.arbitrary ι) h)]
  set b0 : ℝ := 1 + ∑ s, ‖star (β s ^ m) * β s ^ m‖ with hb0
  have hb0s : ∀ s, ‖star (β s ^ m) * β s ^ m‖ ≤ b0 := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖star (β s ^ m) * β s ^ m‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ s)
    linarith
  have hb0p : 0 < b0 := by positivity
  set q : ℝ := 1 - 1 / M with hq
  have hq0 : 0 ≤ q := by
    rw [hq, sub_nonneg, div_le_one hMpos]
    have := hM2 (Classical.arbitrary ι); linarith [norm_nonneg (R (Classical.arbitrary ι) h)]
  have hq1 : q < 1 := by rw [hq]; have : 0 < 1 / M := by positivity
                         linarith
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one (div_pos hε0p hb0p) hq1
  refine ⟨(1 - ((M : ℂ)⁻¹) • h) ^ L, by simp [map_pow, map_sub, hph], fun s => ?_⟩
  set g : A := (1 - ((M : ℂ)⁻¹) • h) ^ L with hg
  set B := star (β s ^ m) * β s ^ m with hBdef
  have hx : R s (star g) * B * R s g ∈ S s :=
    mul_mem (mul_mem (hR s _) (hB s)) (hR s g)
  have hkey : ‖R s (star g) * B * R s g‖ ≤ ε0 := by
    apply norm_le_of_chars (S s) (hSc s) _ hx ε0 hε0p.le
    intro ψ
    obtain ⟨χ, hχb, hχ⟩ := restr (S s) (hSc s) ψ
    rw [← hχ]
    have hsplit : (⟨R s (star g) * B * R s g, hx⟩ : S s) =
        ⟨R s (star g), hR s _⟩ * ⟨B, hB s⟩ * ⟨R s g, hR s g⟩ := rfl
    rw [hsplit, map_mul, map_mul, ← hθ, ← hθ, map_star]

    set w := θ s χ g
    set T : ℝ := ∑ s', ∑ g' ∈ t s', ‖θ s χ (d g')‖ ^ 2 with hT
    have hTh : θ s χ h = (T : ℂ) := by
      simp only [hh, hT, map_sum, map_mul, map_star, Complex.star_def, Complex.conj_mul']
      push_cast; rfl
    have hT0 : 0 ≤ T := by positivity
    have hTM : T + 2 ≤ M := by
      have h1 : ‖θ s χ h‖ ≤ ‖R s h‖ := by rw [hθ]; exact hχb _
      rw [hTh, Complex.norm_real, Real.norm_of_nonneg hT0] at h1
      linarith [hM2 s]
    have hw : w = ((1 - T / M : ℝ) : ℂ) ^ L := by
      simp only [w, hg, map_pow, map_sub, map_one, map_smul, hTh, smul_eq_mul]
      push_cast; ring
    have hwn : ‖w‖ = (1 - T / M) ^ L := by
      rw [hw, norm_pow, Complex.norm_real, Real.norm_of_nonneg]
      rw [sub_nonneg, div_le_one hMpos]; linarith
    have hw1 : ‖w‖ ≤ 1 := by
      rw [hwn]; apply pow_le_one₀
      · rw [sub_nonneg, div_le_one hMpos]; linarith
      · have : 0 ≤ T / M := by positivity
        linarith
    have hχB : ‖χ ⟨B, hB s⟩‖ ≤ b0 := (hχb _).trans (hb0s s)
    rw [norm_mul, norm_mul, norm_star]
    by_cases hbig : ε0 ≤ ‖χ ⟨B, hB s⟩‖
    · obtain ⟨g', hg't, hg'⟩ := ht s ψ (by rw [← hχ]; exact hbig)
      rw [← hχ, ← hθ] at hg'
      have hT1 : 1 < T := by
        have a1 : ‖θ s χ (d g')‖ ^ 2 ≤ ∑ g'' ∈ t s, ‖θ s χ (d g'')‖ ^ 2 :=
          Finset.single_le_sum (f := fun g'' => ‖θ s χ (d g'')‖ ^ 2) (fun _ _ => by positivity) hg't
        have a2 : ∑ g'' ∈ t s, ‖θ s χ (d g'')‖ ^ 2 ≤ T :=
          Finset.single_le_sum (f := fun s' => ∑ g'' ∈ t s', ‖θ s χ (d g'')‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ s)
        nlinarith
      have hwq : ‖w‖ ≤ q ^ L := by
        rw [hwn]; apply pow_le_pow_left₀
        · rw [sub_nonneg, div_le_one hMpos]; linarith
        · rw [hq]; have : 1 / M ≤ T / M := div_le_div_of_nonneg_right hT1.le hMpos.le
          linarith
      calc ‖w‖ * ‖χ ⟨B, hB s⟩‖ * ‖w‖ ≤ 1 * b0 * q ^ L := by
            apply mul_le_mul (mul_le_mul hw1 hχB (norm_nonneg _) zero_le_one) hwq (norm_nonneg _)
              (by positivity)
        _ ≤ ε0 := by
            have := (lt_div_iff₀ hb0p).1 hL
            nlinarith
    · push_neg at hbig
      calc ‖w‖ * ‖χ ⟨B, hB s⟩‖ * ‖w‖ ≤ 1 * ε0 * 1 := by
            apply mul_le_mul (mul_le_mul hw1 hbig.le (norm_nonneg _) zero_le_one) hw1 (norm_nonneg _)
              (by positivity)
        _ = ε0 := by ring
  have hsq : ‖β s ^ m * R s g‖ ^ 2 ≤ ε ^ 2 := by
    have e1 : star (β s ^ m * R s g) * (β s ^ m * R s g) = R s (star g) * B * R s g := by
      rw [star_mul, map_star, hBdef]; noncomm_ring
    rw [sq, ← CStarRing.norm_star_mul_self, e1]
    exact hkey
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg (β s ^ m * R s g)]

end PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures

open PositivityTheory.Rg.BcB.F.ExponentialIntegralMeasures in
theorem PositivityTheory.Rg.BcB.F.peak_trace_bound_holds : PositivityTheory.Rg.BcB.F.PeakTraceBound := by
  intro A _ _ _ _ ι _ _ H _ _ _ R β m V _ _ _ ρ u p a₀ hβ hu ha₀ hbound hv
  obtain ⟨v, hv0, huv, hρv⟩ := hv
  by_contra hne
  push_neg at hne
  have hμpos : 0 < ‖p a₀‖ := norm_pos_iff.2 ha₀
  set K : ℝ := 1 + ∑ s, ‖R s a₀‖ with hK
  have hKs : ∀ s, ‖R s a₀‖ ≤ K := by
    intro s
    have := Finset.single_le_sum (f := fun s => ‖R s a₀‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
    linarith
  have hKp : 0 < K := by positivity
  obtain ⟨g, hg1, hgs⟩ := peak R β m p hβ hne (‖p a₀‖ / 2 / K) (by positivity)
  obtain ⟨C, N, j, hC⟩ := hbound (a₀ * g) (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  refine trace_contra (u * ρ (a₀ * g)) v hv0 (p a₀) ?_ (‖p a₀‖ / 2) (max C 0) N j (by positivity)
    (by linarith) ?_
  · simp [Module.End.mul_apply, map_mul, hρv, hg1, huv, map_smul]
  · filter_upwards [hC, Filter.eventually_gt_atTop j] with k hk hkj
    refine hk.trans ?_
    have hX : ∀ s, ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖ ≤ (‖p a₀‖ / 2) ^ (k - j) := by
      intro s
      have h1 : ‖β s ^ m * R s (a₀ * g)‖ ≤ ‖p a₀‖ / 2 := by
        have e : β s ^ m * R s (a₀ * g) = R s a₀ * (β s ^ m * R s g) := by
          rw [map_mul, ← mul_assoc, ← mul_assoc, ((hβ s a₀).pow_left m).eq]
        rw [e]
        calc _ ≤ ‖R s a₀‖ * ‖β s ^ m * R s g‖ := norm_mul_le _ _
          _ ≤ K * (‖p a₀‖ / 2 / K) := mul_le_mul (hKs s) (hgs s) (norm_nonneg _) hKp.le
          _ = ‖p a₀‖ / 2 := by field_simp
      calc _ ≤ ‖β s ^ m * R s (a₀ * g)‖ ^ (k - j) := norm_pow_le' _ (by omega)
        _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) h1 _
    have hsup : Finset.univ.sup' Finset.univ_nonempty
        (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖) ≤ (‖p a₀‖ / 2) ^ (k - j) :=
      Finset.sup'_le _ _ (fun s _ => hX s)
    have hsup0 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖) :=
      (norm_nonneg _).trans (Finset.le_sup' (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖)
        (Finset.mem_univ (Classical.arbitrary ι)))
    have hk0 : (0 : ℝ) ≤ (1 + (k : ℝ)) ^ N := by positivity
    set σ := Finset.univ.sup' Finset.univ_nonempty (fun s => ‖(β s ^ m * R s (a₀ * g)) ^ (k - j)‖)
    calc C * (1 + (k : ℝ)) ^ N * σ ≤ max C 0 * (1 + (k : ℝ)) ^ N * σ := by
          apply mul_le_mul_of_nonneg_right _ hsup0
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
      _ ≤ max C 0 * (1 + (k : ℝ)) ^ N * (‖p a₀‖ / 2) ^ (k - j) := by
          apply mul_le_mul_of_nonneg_left hsup
          exact mul_nonneg (le_max_right _ _) hk0

end
