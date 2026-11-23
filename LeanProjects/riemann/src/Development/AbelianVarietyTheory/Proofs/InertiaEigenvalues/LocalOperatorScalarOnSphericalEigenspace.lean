import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eig

theorem mem_of_fibres {X Q H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] {g : X → H} {a : H}
    (hg : HasSum g a) (π : X → Q) (L : Submodule ℂ H) (hL : IsClosed (L : Set H))
    (h : ∀ x₀, ∃ s : Finset X, (∀ x, π x = π x₀ ↔ x ∈ s) ∧ ∑ x ∈ s, g x ∈ L) : a ∈ L := by
  have h1 := hg.tsum_fiberwise π
  refine hL.mem_of_tendsto h1 (Filter.Eventually.of_forall fun s => L.sum_mem fun c _ => ?_)
  by_cases hc : ∃ x₀, π x₀ = c
  · obtain ⟨x₀, rfl⟩ := hc
    obtain ⟨s, hs, hm⟩ := h x₀
    have e : π ⁻¹' {π x₀} = (s : Set X) := Set.ext fun x => hs x
    rw [e, Finset.tsum_subtype' s g]
    exact hm
  · have e : π ⁻¹' {c} = ((∅ : Finset X) : Set X) := Set.ext fun x => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_empty, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hc ⟨x, hx⟩
    rw [e, Finset.tsum_subtype' ∅ g, Finset.sum_empty]
    exact L.zero_mem

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isFinIdem_fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (Eu.fid D v) := by
  have h : ∃ f, IsFinIdem D v f := by
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
    exact ⟨_, ε, hε, rfl⟩
  unfold Eu.fid
  rw [dif_pos h]
  exact h.choose_spec

theorem exists_primeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) :
    ∃ P e, P.under (𝓞 D.host.F) = v ∧ IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hne⟩
  have hP : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv.over.symm
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨P, e, hP, h⟩

theorem primeIdem_of_under {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P.under (𝓞 D.host.F) = v) : ∃ e, IsPrimeIdem P e f := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f', h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  obtain ⟨ε', hε', rfl⟩ := hf
  rw [hP] at hε
  rw [GlobalTheory.IdemSupport.placeIdem_unique hε' hε]
  exact ⟨e, h⟩

variable {R : RealDat D A Ks} {i : Fin D.R.m}

theorem bop_spec (hTL : TransLaws R i) {γ : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i)) (x y) :
    trPair R i γ x y = ⟪x, Eu.Bop R i γ y⟫_ℂ := by
  have hex := hTL.2.2.1 γ hγ
  unfold Eu.Bop
  rw [dif_pos hex]
  exact hex.choose_spec.2 x y

theorem bop_mul_lev (hLP : LevProd R i) (hTL : TransLaws R i) {γ k : GA D (Wc D i)} (hγ : γ ∈ GfC (Wc D i))
    (hk : k ∈ levW R i) : Eu.Bop R i (γ * k) = Eu.Bop R i γ := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [← bop_spec hTL hγ, ← bop_spec hTL (mul_mem hγ (hLP.1 hk))]
  have := hTL.2.2.2.1 γ hγ 1 (one_mem _) k hk x y
  rwa [one_mul] at this

theorem hecke_sum_good {F : Face D A} (hL : Laws R F) (hTL : TransLaws R i) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    (hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v) {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    ∃ z : ℂ, ∑ δ ∈ C, Eu.Bop R i δ y = z • y := by
  obtain ⟨y', hy', hs⟩ := hTL.2.1 v f hf α hα C hC hCR y
  have e1 : ∑ δ ∈ C, Eu.Bop R i δ y = y' := by
    apply ext_inner_left ℂ
    intro x
    rw [← hTL.2.2.2.2.2 x y', hs 1 (one_mem _) x, inner_sum]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    rw [one_mul, bop_spec hTL (hCR.1 δ hδ).1]
  obtain ⟨P, e, hPv, hP⟩ := exists_primeIdem hf
  obtain ⟨n, hβ⟩ := hL.lev.βW i
  obtain ⟨hJ, hχ, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ n) (R.datWp i R.triv) hβ).2 P e f hP
    (by rw [one_pow, Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top)
    (by
      intro PP hPP
      have h1 : PP ∈ R.Pg := hPP.resolve_right (Finset.notMem_empty _)
      refine ⟨fun h => hv PP h1 (h ▸ hPv), fun h => hv PP h1 ?_⟩
      rw [(GlobalTheory.IdemSupport.isConjPl_iff _ _).1 h, GlobalTheory.IdemSupport.under_cP] at hPv
      exact hPv)
  obtain ⟨-, ϖ, -, h1, h2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have he : e * e = e := GlobalTheory.IdemSupport.delta_idem hΦ (GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hP).1
  obtain ⟨d, hd, hD⟩ := GlobalTheory.SphLabelOps.exists_divAt (Wc D i) he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP) h1 h2 α
  have hop : Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) ∅ P d C :=
    ⟨e, f, ϖ, α, fun w hw => absurd hw (Finset.notMem_empty w), hP, h1, h2, hd, hJ, hχ, hα, hD, hC, hCR⟩
  have hm := (Submodule.mem_comap.1 hy).2
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at hm
  have hk := hm P d C hop
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hk
  refine ⟨c P d, e1.trans ((hL.models.HW i (sg0 D A)).1 ?_)⟩
  rw [hy', hk, map_smul]
  rfl

theorem hecke_sum_mem {F : Face D A} (hL : Laws R F) {t : T} (hB : BadSupp R i t) (hLP : LevProd R i)
    (hTL : TransLaws R i) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) {c} {y} (hy : y ∈ part R i ∅ c)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f)
    {α : GA D (Wc D i)} (hα : SuppF (Wc D i) f α)
    {C : Finset (GA D (Wc D i))} (hC : ∀ γ ∈ C, SuppF (Wc D i) f γ)
    (hCR : IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C) :
    coef R i t μ 𝓕 α • ∑ δ ∈ C, Eu.Bop R i δ y ∈ Submodule.span ℂ {y} := by
  by_cases hv : ∀ P ∈ R.Pg, P.under (𝓞 D.host.F) ≠ v
  · obtain ⟨z, hz⟩ := hecke_sum_good hL hTL hy hf hv hα hC hCR
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self y))
  · push_neg at hv
    obtain ⟨P, hP, hPv⟩ := hv
    obtain ⟨e, he⟩ := primeIdem_of_under hf hPv
    by_cases hk : α ∈ levW R i
    · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun δ hδ => ?_)
      obtain ⟨-, k₁, hk₁, k₂, hk₂, rfl⟩ := hCR.1 δ hδ
      have := bop_mul_lev hLP hTL (one_mem _) (mul_mem (mul_mem hk₁.1 hk) hk₂.1)
      rw [one_mul] at this
      rw [this, Eu.bop_one hTL]
      exact Submodule.mem_span_singleton_self y
    · rw [hB μ 𝓕 hμ P (Or.inl hP) e f he α hα hk, zero_smul]
      exact Submodule.zero_mem _

theorem mk_eq_iff {v : HeightOneSpectrum (𝓞 D.host.F)} (g : Eu.locSet R i v) (x : Eu.LX R i v) :
    (Quotient.mk _ g : Eu.LX R i v) = x ↔ g.1⁻¹ * Eu.rep x ∈ levW R i := by
  rw [← QuotientGroup.leftRel_apply]
  exact Quotient.mk_eq_iff_out

set_option maxHeartbeats 800000 in

theorem zop_eigen : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, BadSupp R i t → LevFix R i t → LocSmall R i t → LevProd R i → TransLaws R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → (∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g) → ∀ c, ∀ y ∈ part R i ∅ c, ∀ v, ∃ z : ℂ, Eu.Zop R i t μ 𝓕 v y = z • y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hB hLF _ hLP hTL μ 𝓕 hμ hleft c y hy v
  suffices h : Eu.Zop R i t μ 𝓕 v y ∈ Submodule.span ℂ {y} by
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.1 h
    exact ⟨z, hz.symm⟩
  unfold Eu.Zop
  by_cases hs : Summable fun x : Eu.LX R i v => Eu.acoef R i t μ 𝓕 v x • Eu.Bop R i (Eu.rep x)
  swap
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Submodule.zero_mem _
  have hf := isFinIdem_fid D v
  obtain ⟨P, e, -, hP⟩ := exists_primeIdem hf
  have h0 := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).2.2.1 P e _ hP
  obtain ⟨S, hS⟩ := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)).1 _ h0.1 h0.2.1).1
  have hloc : ∀ g, g ∈ S → g ∈ Eu.locSet R i v := fun g hg => ⟨h0.2.2.1 g ((hS g).1 hg), (hS g).1 hg⟩
  have hrep : ∀ x : Eu.LX R i v, Eu.rep x ∈ S := fun x => (hS _).2 (Quotient.out x).2.2
  have hsum := (ContinuousLinearMap.apply ℂ _ y).hasSum hs.hasSum
  refine mem_of_fibres hsum (fun x => DoubleCoset.mk (levW R i ⊓ S) (levW R i ⊓ S) (Eu.rep x)) _
    (Submodule.closed_of_finiteDimensional _) fun x₀ => ?_
  have hα : SuppF (Wc D i) (Eu.fid D v) (Eu.rep x₀) := (hS _).1 (hrep x₀)
  obtain ⟨C, hC, hCR⟩ := hTL.1 v _ hf _ hα
  have hK : ∀ k, k ∈ {k | k ∈ levW R i ∧ SuppF (Wc D i) (Eu.fid D v) k} ↔ k ∈ levW R i ⊓ S := fun k =>
    and_congr_right fun _ => (hS k).symm
  obtain ⟨φ, hφ⟩ : ∃ φ : GA D (Wc D i) → Eu.LX R i v, ∀ δ ∈ C, ∀ x, φ δ = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
    have key : ∀ δ : GA D (Wc D i), ∃ x' : Eu.LX R i v, δ ∈ C → ∀ x, x' = x ↔ δ⁻¹ * Eu.rep x ∈ levW R i ⊓ S := by
      intro δ
      by_cases hδ : δ ∈ C
      · have h1 := (hS δ).2 (hC δ hδ)
        exact ⟨Quotient.mk _ ⟨δ, hloc δ h1⟩, fun _ x =>
          (mk_eq_iff ⟨δ, hloc δ h1⟩ x).trans ⟨fun h => ⟨h, S.mul_mem (S.inv_mem h1) (hrep x)⟩, fun h => h.1⟩⟩
      · exact ⟨Eu.lx0 R i v, fun h => absurd h hδ⟩
    choose φ hφ using key
    exact ⟨φ, hφ⟩
  have hdc : ∀ δ ∈ C, ∃ k₁ ∈ levW R i ⊓ S, ∃ k₂ ∈ levW R i ⊓ S, Eu.rep (φ δ) = k₁ * Eu.rep x₀ * k₂ := fun δ hδ => by
    obtain ⟨-, k₁, hk₁, k₂, hk₂, e1⟩ := hCR.1 δ hδ
    refine ⟨k₁, (hK _).1 hk₁, k₂ * (δ⁻¹ * Eu.rep (φ δ)), mul_mem ((hK _).1 hk₂) ((hφ δ hδ _).1 rfl), ?_⟩
    rw [← mul_assoc, ← e1, mul_inv_cancel_left]
  refine ⟨C.image φ, fun x => ?_, ?_⟩
  · rw [eq_comm, DoubleCoset.eq, Finset.mem_image]
    constructor
    · rintro ⟨k₁, hk₁, k₂, hk₂, e1⟩
      obtain ⟨δ, ⟨hδ, h1⟩, -⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact ⟨δ, hδ, (hφ δ hδ x).2 ((hK _).1 h1)⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact hdc δ hδ
  · rw [Finset.sum_image]
    · have := hecke_sum_mem hL hB hLP hTL hμ hy hf hα hC hCR
      rw [Finset.smul_sum] at this
      refine (congrArg (· ∈ Submodule.span ℂ {y}) (Finset.sum_congr rfl fun δ hδ => ?_)).mpr this
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      have e2 : Eu.acoef R i t μ 𝓕 v (φ δ) = coef R i t μ 𝓕 (Eu.rep x₀) := by
        unfold Eu.acoef
        rw [e1, Model.coef_mul_lev R i t hLF μ 𝓕 _ _ hk₂.1, hleft _ hk₁.1]
      have e3 : Eu.Bop R i (Eu.rep (φ δ)) = Eu.Bop R i δ := by
        rw [← bop_mul_lev hLP hTL (hCR.1 δ hδ).1 ((hφ δ hδ _).1 rfl).1, mul_inv_cancel_left]
      rw [ContinuousLinearMap.apply_apply, e2, e3, ContinuousLinearMap.smul_apply]
    · intro δ hδ δ' hδ' h
      obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hdc δ hδ
      obtain ⟨δ₀, -, hu⟩ := hCR.2 _ ⟨k₁, (hK _).2 hk₁, k₂, (hK _).2 hk₂, e1⟩
      exact (hu δ ⟨hδ, (hK _).2 ((hφ δ hδ _).1 rfl)⟩).trans (hu δ' ⟨hδ', (hK _).2 ((hφ δ' hδ' _).1 h.symm)⟩).symm

end GlobalTheory.RawLift.Eig

end
