import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KirillovVanishingOfLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeylStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerJHypEqOrbitalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepEvalZeroMemInducedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerWeilRepEventuallyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppoStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.RankOneTransfer

theorem inI_comb : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    A.InI (fun g => Φ₁ g + r * Φ₂ g) := by
  intro F E _ _ _ _ A Φ₁ Φ₂ r h₁ h₂
  obtain ⟨⟨U₁, hU₁, i₁⟩, e₁⟩ := h₁
  obtain ⟨⟨U₂, hU₂, i₂⟩, e₂⟩ := h₂
  refine ⟨⟨U₁ ∩ U₂, Filter.inter_mem hU₁ hU₂, fun g k hk => ?_⟩, fun z s g => ?_⟩
  · simp only
    rw [i₁ g k (fun i j => (hk i j).1), i₂ g k (fun i j => (hk i j).2)]
  · simp only
    rw [e₁, e₂]
    ring

theorem inI_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E), A.InI (fun _ => 0) := by
  intro F E _ _ _ _ A
  exact ⟨⟨Set.univ, Filter.univ_mem, fun _ _ _ => rfl⟩, fun _ _ _ => by simp⟩

theorem nS_add {k : Type} [CommRing k] (a b : k) : nS (a + b) = nS a * nS b := by
  apply Subtype.ext
  show !![1, a + b; 0, 1] = !![1, a; 0, 1] * !![1, b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

theorem psi_cont {F : Type} [NormedField F] (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have : ∀ᶠ x in 𝓝 x₀, ψ x₀ = ψ x := by
    filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    have h1 : ψ (x - x₀) = 1 := hψ.1 _ (by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx.le)
    calc ψ x₀ = ψ x₀ * ψ (x - x₀) := by rw [h1, mul_one]
      _ = ψ (x₀ + (x - x₀)) := (AddChar.map_add_eq_mul ψ _ _).symm
      _ = ψ x := by congr 1; abel
  exact continuousAt_const.congr this

theorem lam_integrand_cont {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (a : A.K)
    (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (hΦ : A.InI Φ) :
    Continuous fun z => Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) := by
  refine Continuous.mul ?_ ?_
  · obtain ⟨⟨U, hU, hinv⟩, -⟩ := hΦ
    refine continuous_iff_continuousAt.2 fun z₀ => ?_
    have hpre : {z : A.K | z - z₀ ∈ U} ∈ 𝓝 z₀ := by
      have ht : Tendsto (fun z : A.K => z - z₀) (𝓝 z₀) (𝓝 0) := by
        simpa using (continuous_id.sub continuous_const).tendsto z₀ (f := fun z : A.K => z - z₀)
      exact ht hU
    have h0 : (0 : A.K) ∈ U := mem_of_mem_nhds hU
    have : ∀ᶠ z in 𝓝 z₀, Φ (wS A.K * nS z₀) = Φ (wS A.K * nS z) := by
      filter_upwards [hpre] with z hz
      have hz' : z = z₀ + (z - z₀) := by abel
      rw [hz', nS_add, ← mul_assoc]
      symm
      apply hinv
      intro i j
      fin_cases i <;> fin_cases j <;> simp [nS, h0, hz]
    exact continuousAt_const.congr this
  · have htr : Continuous (Algebra.trace F A.K) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact (psi_cont ψ hψ).comp (htr.comp (continuous_const.mul continuous_id).neg)

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem lam_comb : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K),
    μK.IsAddHaarMeasure → ∀ (a : A.K) (Φ₁ Φ₂ : SpecialLinearGroup (Fin 2) A.K → ℂ) (r : ℂ), A.InI Φ₁ → A.InI Φ₂ →
    ∀ c : F, c ≠ 0 → A.abelian₂ μK ψ a (fun g => Φ₁ g + r * Φ₂ g) c = A.abelian₂ μK ψ a Φ₁ c + r * A.abelian₂ μK ψ a Φ₂ c := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ a Φ₁ Φ₂ r h₁ h₂ c hc
  obtain ⟨-, -, -, -, -, -, -, -, -, hOKo, hOKc, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hsm : Continuous fun z : A.K => c • z := continuous_const_smul c
  have hKc : IsCompact {z : A.K | c • z ∈ A.OK} := by
    have := (Homeomorph.smulOfNeZero c hc (α := A.K)).isCompact_preimage.2 hOKc
    exact this
  have hKm : MeasurableSet {z : A.K | c • z ∈ A.OK} := (hOKo.preimage hsm).measurableSet
  have i₁ : IntegrableOn (fun z => Φ₁ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₁ h₁).continuousOn.integrableOn_compact' hKc hKm
  have i₂ : IntegrableOn (fun z => Φ₂ (wS A.K * nS z) * A.psiK ψ (-(a * z))) {z : A.K | c • z ∈ A.OK} μK :=
    (lam_integrand_cont A ψ hψ a Φ₂ h₂).continuousOn.integrableOn_compact' hKc hKm
  simp only [Et.abelian₂]
  rw [← integral_const_mul, ← integral_add i₁ (i₂.const_mul r)]
  congr 1
  funext z
  ring

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem lam_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (μK : Measure A.K) (ψ : AddChar F ℂ) (a : A.K) (c : F),
    A.abelian₂ μK ψ a (fun _ => 0) c = 0 := by
  intro F E _ _ _ _ A μK ψ a c
  simp [Et.abelian₂]

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem inI_sum (A : Et F E) {ι : Type} (s : Finset ι) (r : ι → ℂ) (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ)
    (h : ∀ i ∈ s, A.InI (Φ i)) : A.InI (fun g => ∑ i ∈ s, r i * Φ i g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inI_zero F E A
  | insert i s hi ih =>
    have := inI_comb F E A (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj)) (h i (Finset.mem_insert_self i s))
    simpa [Finset.sum_insert hi, add_comm] using this

theorem lam_sum [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (μK : Measure A.K)
    (hμ : μK.IsAddHaarMeasure) (a : A.K) {ι : Type} (s : Finset ι) (r : ι → ℂ)
    (Φ : ι → SpecialLinearGroup (Fin 2) A.K → ℂ) (h : ∀ i ∈ s, A.InI (Φ i)) (c : F) (hc : c ≠ 0) :
    A.abelian₂ μK ψ a (fun g => ∑ i ∈ s, r i * Φ i g) c = ∑ i ∈ s, r i * A.abelian₂ μK ψ a (Φ i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lam_zero F E A μK ψ a c
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, A.InI (Φ j) := fun j hj => h j (Finset.mem_insert_of_mem hj)
    have := lam_comb F E A ψ hψ μK hμ a (fun g => ∑ j ∈ s, r j * Φ j g) (Φ i) (r i)
      (inI_sum A s r Φ hs) (h i (Finset.mem_insert_self i s)) c hc
    rw [Finset.sum_insert hi, ← ih hs, add_comm, ← this]
    congr 1
    funext g
    rw [Finset.sum_insert hi, add_comm]

end GlobalTheory.JR.RankOneTransfer

namespace GlobalTheory.JR.RankOneTransfer

theorem rankOne : RankOne := by
  intro F E _ _ _ _ _ A ψ hψ m S hS γ W hW φ' φ κ hφ' hφ hmatch x hx y hy
  classical
  obtain ⟨-, -, -, -, -, -, -, hfin, -⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have hSf := hfin S hS
  set Sf := hSf.toFinset with hSfdef
  have hmem : ∀ x', x' ∈ Sf ↔ x' ∈ S := fun x' => hSf.mem_toFinset
  have hμ : m.μK.IsAddHaarMeasure := m.sdK.1

  have huniq : ∀ (x₀ x₁ : A.Kˣ) (y₀ y₁ : A.L), x₀ ∈ S → x₁ ∈ S → IsUnit y₀ → IsUnit y₁ →
      (x₀ : A.K) * A.NL y₀ = x₁ * A.NL y₁ → x₀ = x₁ := by
    intro x₀ x₁ y₀ y₁ h₀ h₁ u₀ u₁ he
    have hu : IsUnit ((x₀ : A.K) * A.NL y₀) := x₀.isUnit.mul (u₀.map (Algebra.norm A.K))
    obtain ⟨z, -, hz⟩ := hS hu.unit
    have e0 := hz x₀ ⟨h₀, y₀, u₀, by simp⟩
    have e1 := hz x₁ ⟨h₁, y₁, u₁, by simp [he]⟩
    rw [e0, e1]
  let jx : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φ x') 0
  let φw : A.Kˣ → A.L → ℂ := fun x' => W x' (wS A.K) (φ x')
  let jw : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → ℂ := fun x' g => W x' g (φw x') 0
  let r : A.Kˣ → ℂ := fun x' => -(γ x')⁻¹
  let Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ := fun g =>
    (∑ x' ∈ Sf, r x' * jx x' g) + κ * A.jHyp m.μK ψ φ' g
  have hφw : ∀ x' ∈ S, IsTest (φw x') := fun x' hx' => (hW x' hx').1.1 _ _ (hφ x' hx')
  have hjx : ∀ x' ∈ Sf, A.InI (jx x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφ x' ((hmem x').1 hx'))).1
  have hjw : ∀ x' ∈ Sf, A.InI (jw x') := fun x' hx' =>
    (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x' _ _ _ (hW x' ((hmem x').1 hx')) _ (hφw x' ((hmem x').1 hx'))).1
  have h14 := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK φ' hφ'
  have hF' : IsTest (A.fourK m.μK ψ φ') := GlobalTheory.T.fourierTransformKProd_locallyConstantCompactSupport F E A ψ hψ m.μK m.sdK φ' hφ'
  have h14F := GlobalTheory.T.jHyp_mem_induced_fourier_weyl F E A ψ hψ m.μK m.sdK _ hF'
  have hΨ : A.InI Ψ := inI_comb F E A _ _ κ (inI_sum A Sf r jx hjx) h14.1

  have hlim : ∀ a : A.K, IsUnit a → Tendsto (A.abelian₂ m.μK ψ a Ψ) (𝓝[≠] 0) (𝓝 0) := by
    intro a ha
    obtain ⟨x₀, ⟨hx₀, y₀, hy₀, ha₀⟩, -⟩ := hS ha.unit
    have ha₀' : a = x₀ * A.NL y₀ := by simpa using ha₀
    have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
    have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK φ' hφ' a ha
    have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
        A.abelian₂ m.μK ψ a (jx x') c = if x' = x₀ then γ x₀ * A.orbL m.ν (φ x₀) y₀ else 0 := by
      rw [Finset.eventually_all]
      intro x' hx'
      have hx'S := (hmem x').1 hx'
      have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφ x' hx'S) a ha
      by_cases hxx : x' = x₀
      · subst hxx
        simpa using this.1 y₀ hy₀ ha₀'
      · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
          rintro ⟨y', hy', he⟩
          exact hxx (huniq x' x₀ y' y₀ hx'S hx₀ hy' hy₀ (he.symm.trans ha₀'))
        simpa [hxx] using this.2 hno
    have hev : ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a Ψ c = 0 := by
      filter_upwards [hne, h14b, h15] with c hc e14 e15
      have hl := lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jx hjx) h14.1 c hc
      rw [hl, lam_sum A ψ hψ m.μK hμ a Sf r jx hjx c hc, e14]
      rw [Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])]
      have hx₀f : x₀ ∈ Sf := (hmem x₀).2 hx₀
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hx₀f, if_true]
      have hm := hmatch x₀ hx₀ y₀ hy₀
      rw [← ha₀'] at hm
      rw [hm]
      by_cases hg : γ x₀ = 0
      · have h0 : φ x₀ = 0 := by
          by_contra hne0
          exact (GlobalTheory.T.weilRep_evalZero_mem_induced F E A ψ hψ x₀ _ _ _ (hW x₀ hx₀) _ (hφ x₀ hx₀)).2 hne0 hg
        simp [h0, Et.orbL]
      · simp only [r]
        field_simp
        ring
    exact tendsto_const_nhds.congr' (hev.mono fun c hc => hc.symm)
  have h13 := (GlobalTheory.T.kirillov_vanishing_of_limit F E A ψ hψ m.μK m.sdK Ψ hΨ hlim).2

  have hΨw : (fun h => Ψ (h * wS A.K)) = fun g => (∑ x' ∈ Sf, r x' * jw x' g) +
      κ * A.jHyp m.μK ψ (A.fourK m.μK ψ φ') g := by
    funext g
    simp only [Ψ]
    rw [h14.2 g]
    congr 1
    refine Finset.sum_congr rfl fun x' hx' => ?_
    have hx'S := (hmem x').1 hx'
    simp only [jx, jw, φw]
    rw [(hW x' hx'S).1.2.2.1 g (wS A.K) (φ x') (hφ x' hx'S)]
  set a := (x : A.K) * A.NL y with hadef
  have ha : IsUnit a := x.isUnit.mul (hy.map (Algebra.norm A.K))
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  have h14b := GlobalTheory.T.truncatedWhittaker_jHyp_eq_orbitalIntegral F E A ψ hψ m.μK m.sdK _ hF' a ha
  have h15 : ∀ᶠ c in 𝓝[≠] (0 : F), ∀ x' ∈ Sf,
      A.abelian₂ m.μK ψ a (jw x') c = if x' = x then γ x * A.orbL m.ν (φw x) y else 0 := by
    rw [Finset.eventually_all]
    intro x' hx'
    have hx'S := (hmem x').1 hx'
    have := GlobalTheory.T.truncatedWhittaker_weilRep_eventually F E A ψ hψ m x' _ _ (hW x' hx'S) _ (hφw x' hx'S) a ha
    by_cases hxx : x' = x
    · subst hxx
      simpa using this.1 y hy rfl
    · have hno : ¬ ∃ y' : A.L, IsUnit y' ∧ a = x' * A.NL y' := by
        rintro ⟨y', hy', he⟩
        exact hxx (huniq x' x y' y hx'S hx hy' hy he.symm)
      simpa [hxx] using this.2 hno
  obtain ⟨c, hc, e14, e15⟩ := (hne.and (h14b.and h15)).exists
  have hz := h13 a c
  rw [hΨw, lam_comb F E A ψ hψ m.μK hμ a _ _ κ (inI_sum A Sf r jw hjw) h14F.1 c hc,
    lam_sum A ψ hψ m.μK hμ a Sf r jw hjw c hc, e14,
    Finset.sum_congr rfl (fun x' hx' => by rw [e15 x' hx'])] at hz
  have hxf : x ∈ Sf := (hmem x).2 hx
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', hxf, if_true] at hz
  have horb : A.orbL m.ν (φw x) y = γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y := by
    simp only [Et.orbL, φw]
    rw [← integral_const_mul]
    congr 1
    funext t
    exact ((hW x hx).2 (φ x) (hφ x hx)).2.2 _
  rw [horb] at hz
  simp only [r] at hz
  by_cases hg : γ x = 0
  · simp [hg] at hz
    simp [hg, hz]
  · field_simp at hz
    linear_combination hz

end GlobalTheory.JR.RankOneTransfer
