import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsContent
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareMulOfNonsquareUnits
import GroundTheory.GlobalFields.LocalFieldAtPlace
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.SW.SplitIdeals

section Abs

variable {K A : Type} [Field K] [CommRing A] [Algebra K A]

noncomputable def br (δ : A) (e a b : K) : A :=
  algebraMap K A ((a + b) / 2) + algebraMap K A ((a - b) / (2 * e)) * δ

theorem br_mul (δ : A) (e : K) (h2 : (2 : K) ≠ 0) (he : e ≠ 0)
    (hδ : δ * δ = algebraMap K A (e ^ 2)) (a b a' b' : K) :
    br δ e a b * br δ e a' b' = br δ e (a * a') (b * b') := by
  have e1 : (a * a' + b * b') / 2 =
      (a + b) / 2 * ((a' + b') / 2) + (a - b) / (2 * e) * ((a' - b') / (2 * e)) * e ^ 2 := by
    field_simp
    ring
  have e2 : (a * a' - b * b') / (2 * e) =
      (a + b) / 2 * ((a' - b') / (2 * e)) + (a - b) / (2 * e) * ((a' + b') / 2) := by
    field_simp
    ring
  unfold br
  rw [e1, e2]
  simp only [map_add, map_mul]
  linear_combination (algebraMap K A ((a - b) / (2 * e)) *
    algebraMap K A ((a' - b') / (2 * e))) * hδ

theorem br_diag (δ : A) (e : K) (h2 : (2 : K) ≠ 0) (t : K) :
    br δ e t t = algebraMap K A t := by
  have e1 : (t + t) / 2 = t := by field_simp; ring
  simp [br, e1]

theorem br_swap (δ : A) (e : K) (τ : A →+* A) (hτa : ∀ c, τ (algebraMap K A c) = algebraMap K A c)
    (hτδ : τ δ = -δ) (a b : K) : τ (br δ e a b) = br δ e b a := by
  have e1 : (b + a) / 2 = (a + b) / 2 := by rw [add_comm]
  have e2 : (b - a) / (2 * e) = -((a - b) / (2 * e)) := by rw [← neg_div, neg_sub]
  unfold br
  rw [e1, e2]
  simp only [map_add, map_mul, hτa, hτδ, map_neg]
  ring

theorem br_of (δ : A) (e : K) (h2 : (2 : K) ≠ 0) (he : e ≠ 0) (p q : K) :
    br δ e (p + q * e) (p - q * e) = algebraMap K A p + algebraMap K A q * δ := by
  have e1 : (p + q * e + (p - q * e)) / 2 = p := by field_simp; ring
  have e2 : (p + q * e - (p - q * e)) / (2 * e) = q := by field_simp; ring
  rw [br, e1, e2]

theorem br_repr (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (e a b : K) :
    B.repr (br (B 1) e a b) 0 = (a + b) / 2 ∧ B.repr (br (B 1) e a b) 1 = (a - b) / (2 * e) :=
  GlobalTheory.CompanionTheory.SW.GoodRing.coord_two B hB0 _ _

theorem br_inj (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (e : K) (h2 : (2 : K) ≠ 0)
    (he : e ≠ 0) {a b a' b' : K} (h : br (B 1) e a b = br (B 1) e a' b') : a = a' ∧ b = b' := by
  have h0 := (br_repr B hB0 e a b).1
  have h1 := (br_repr B hB0 e a b).2
  rw [h, (br_repr B hB0 e a' b').1] at h0
  rw [h, (br_repr B hB0 e a' b').2] at h1
  field_simp at h0 h1
  exact ⟨mul_left_cancel₀ h2 (by linear_combination -h0 - h1),
    mul_left_cancel₀ h2 (by linear_combination -h0 + h1)⟩

theorem exists_br (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (e : K) (h2 : (2 : K) ≠ 0)
    (he : e ≠ 0) (y : A) : ∃ a b : K, y = br (B 1) e a b ∧
      a = B.repr y 0 + B.repr y 1 * e ∧ b = B.repr y 0 - B.repr y 1 * e :=
  ⟨_, _, by rw [br_of _ _ h2 he]; exact GlobalTheory.CompanionTheory.SW.GoodRing.eq_coord B hB0 y, rfl, rfl⟩

theorem br_mem_iff (Rs : Subring K) (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1) (e : K)
    (h2 : (2 : K) ≠ 0) (he : e ≠ 0) (heR : e ∈ Rs) (heR' : e⁻¹ ∈ Rs) (h2R : (2 : K)⁻¹ ∈ Rs)
    (a b : K) : (∀ j, B.repr (br (B 1) e a b) j ∈ Rs) ↔ a ∈ Rs ∧ b ∈ Rs := by
  obtain ⟨h0, h1⟩ := br_repr B hB0 e a b
  constructor
  · intro h
    have m0 := h 0
    have m1 := h 1
    rw [h0] at m0
    rw [h1] at m1
    have ea : a = (a + b) / 2 + (a - b) / (2 * e) * e := by field_simp; ring
    have eb : b = (a + b) / 2 - (a - b) / (2 * e) * e := by field_simp; ring
    refine ⟨?_, ?_⟩
    · rw [ea]; exact Rs.add_mem m0 (Rs.mul_mem m1 heR)
    · rw [eb]; exact Rs.sub_mem m0 (Rs.mul_mem m1 heR)
  · rintro ⟨ha, hb⟩
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [h0, div_eq_mul_inv]; exact Rs.mul_mem (Rs.add_mem ha hb) h2R
    · rw [h1, div_eq_mul_inv, mul_inv]
      exact Rs.mul_mem (Rs.sub_mem ha hb) (Rs.mul_mem h2R heR')

theorem pow_eq_of_unit (Rs : Subring K) (ϖ : K) (hϖ0 : ϖ ≠ 0) (hϖR : ϖ ∈ Rs) (hϖ' : ϖ⁻¹ ∉ Rs)
    {i j : ℕ} {a a' : K} (ha : a ∈ Rs) (ha' : a' ∈ Rs) (haa : a * a' = 1)
    (h : ϖ ^ i = ϖ ^ j * a) : i = j := by
  have key : ∀ (k : ℕ) (c : K), c ∈ Rs → ϖ ^ (k + 1) * c = 1 → False := by
    intro k c hc h
    apply hϖ'
    have e : ϖ ^ k * c = ϖ⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← h]; ring)
    rw [← e]
    exact Rs.mul_mem (Rs.pow_mem hϖR k) hc
  rcases lt_trichotomy i j with hl | hl | hl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hl
    exact (key k a ha (mul_left_cancel₀ (pow_ne_zero i hϖ0) (by
      linear_combination -h))).elim
  · exact hl
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hl
    exact (key k a' ha' (mul_left_cancel₀ (pow_ne_zero j hϖ0) (by
      linear_combination a' * h + ϖ ^ j * haa))).elim

theorem abs_main (Rs : Subring K) (τ : A →+* A) (B : Module.Basis (Fin 2) K A) (hB0 : B 0 = 1)
    (e : K) (h2 : (2 : K) ≠ 0) (he : e ≠ 0) (hδ : B 1 * B 1 = algebraMap K A (e ^ 2))
    (hτa : ∀ c, τ (algebraMap K A c) = algebraMap K A c) (hτδ : τ (B 1) = -B 1)
    (heR : e ∈ Rs) (heR' : e⁻¹ ∈ Rs) (h2R : (2 : K)⁻¹ ∈ Rs)
    (ϖ : K) (hϖ0 : ϖ ≠ 0) (hϖR : ϖ ∈ Rs) (hϖ' : ϖ⁻¹ ∉ Rs)
    (hfac : ∀ a ∈ Rs, a ≠ 0 → ∃ (u : K) (n : ℕ), u ∈ Rs ∧ u⁻¹ ∈ Rs ∧ a = u * ϖ ^ n)
    (S : Set A) (hS : ∀ y, y ∈ S ↔ ∀ j, B.repr y j ∈ Rs) :
    ¬ IsField A ∧ ∃ c : ℕ × ℕ → A, (∀ i, IsUnit (c i) ∧ c i ∈ S) ∧
      (∀ i : ℕ × ℕ, algebraMap K A (ϖ ^ (i.1 + i.2)) = τ (c i) * c i) ∧
      (∀ x ∈ S, IsUnit x → ∃ i, ∃ u ∈ S, ∃ u' ∈ S, u * u' = 1 ∧ x = c i * u) ∧
      (∀ i j, ∀ u ∈ S, ∀ u' ∈ S, u * u' = 1 → c i = c j * u → i = j) := by
  have hmul := br_mul (B 1) e h2 he hδ
  have hone : br (B 1) e (1 : K) 1 = 1 := by rw [br_diag _ _ h2, map_one]
  have hzero : br (B 1) e (0 : K) 0 = 0 := by rw [br_diag _ _ h2, map_zero]
  have hinj : ∀ {a b a' b' : K}, br (B 1) e a b = br (B 1) e a' b' → a = a' ∧ b = b' :=
    fun h => br_inj B hB0 e h2 he h
  have hmem : ∀ a b : K, br (B 1) e a b ∈ S ↔ a ∈ Rs ∧ b ∈ Rs := fun a b =>
    (hS _).trans (br_mem_iff Rs B hB0 e h2 he heR heR' h2R a b)
  have hall : ∀ y : A, ∃ a b : K, y = br (B 1) e a b := fun y => by
    obtain ⟨a, b, h, -, -⟩ := exists_br B hB0 e h2 he y
    exact ⟨a, b, h⟩
  refine ⟨fun hf => ?_, fun i => br (B 1) e (ϖ ^ i.1) (ϖ ^ i.2), ?_, ?_, ?_, ?_⟩
  · have hne : br (B 1) e (1 : K) 0 ≠ 0 := fun h => by
      rw [← hzero] at h
      exact one_ne_zero (hinj h).1
    have hne' : br (B 1) e (0 : K) 1 ≠ 0 := fun h => by
      rw [← hzero] at h
      exact one_ne_zero (hinj h).2
    obtain ⟨w, hw⟩ := hf.mul_inv_cancel hne
    have h0 : br (B 1) e (1 : K) 0 * br (B 1) e (0 : K) 1 = 0 := by
      rw [hmul, mul_zero, zero_mul, hzero]
    apply hne'
    calc br (B 1) e (0 : K) 1 = (br (B 1) e (1 : K) 0 * w) * br (B 1) e (0 : K) 1 := by
          rw [hw, one_mul]
      _ = (br (B 1) e (1 : K) 0 * br (B 1) e (0 : K) 1) * w := by ring
      _ = 0 := by rw [h0, zero_mul]
  · intro i
    refine ⟨IsUnit.of_mul_eq_one (br (B 1) e ((ϖ ^ i.1)⁻¹) ((ϖ ^ i.2)⁻¹)) ?_, ?_⟩
    · rw [hmul, mul_inv_cancel₀ (pow_ne_zero _ hϖ0), mul_inv_cancel₀ (pow_ne_zero _ hϖ0), hone]
    · exact (hmem _ _).2 ⟨Rs.pow_mem hϖR _, Rs.pow_mem hϖR _⟩
  · intro i
    show _ = τ (br (B 1) e (ϖ ^ i.1) (ϖ ^ i.2)) * br (B 1) e (ϖ ^ i.1) (ϖ ^ i.2)
    rw [br_swap _ _ τ hτa hτδ, hmul, ← br_diag (B 1) e h2, pow_add, mul_comm (ϖ ^ i.2)]
  · intro x hx hxu
    obtain ⟨a, b, rfl⟩ := hall x
    obtain ⟨ha, hb⟩ := (hmem a b).1 hx
    obtain ⟨w, hw⟩ := hxu.exists_right_inv
    obtain ⟨a', b', rfl⟩ := hall w
    rw [hmul, ← hone] at hw
    obtain ⟨h1, h2'⟩ := hinj hw
    have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one h2'
    obtain ⟨u₁, i₁, hu₁, hu₁', rfl⟩ := hfac a ha ha0
    obtain ⟨u₂, i₂, hu₂, hu₂', rfl⟩ := hfac b hb hb0
    have hu₁0 : u₁ ≠ 0 := left_ne_zero_of_mul ha0
    have hu₂0 : u₂ ≠ 0 := left_ne_zero_of_mul hb0
    refine ⟨(i₁, i₂), br (B 1) e u₁ u₂, (hmem _ _).2 ⟨hu₁, hu₂⟩, br (B 1) e u₁⁻¹ u₂⁻¹,
      (hmem _ _).2 ⟨hu₁', hu₂'⟩, ?_, ?_⟩
    · rw [hmul, mul_inv_cancel₀ hu₁0, mul_inv_cancel₀ hu₂0, hone]
    · show _ = br (B 1) e (ϖ ^ i₁) (ϖ ^ i₂) * br (B 1) e u₁ u₂
      rw [hmul, mul_comm u₁, mul_comm u₂]
  · intro i j u hu u' hu' huu h
    obtain ⟨a, b, rfl⟩ := hall u
    obtain ⟨a', b', rfl⟩ := hall u'
    obtain ⟨ha, hb⟩ := (hmem a b).1 hu
    obtain ⟨ha', hb'⟩ := (hmem a' b').1 hu'
    rw [hmul, ← hone] at huu
    obtain ⟨h1, h2'⟩ := hinj huu
    have h' : br (B 1) e (ϖ ^ i.1) (ϖ ^ i.2) = br (B 1) e (ϖ ^ j.1 * a) (ϖ ^ j.2 * b) := by
      rw [← hmul]; exact h
    obtain ⟨e1, e2⟩ := hinj h'
    exact Prod.ext (pow_eq_of_unit Rs ϖ hϖ0 hϖR hϖ' ha ha' h1 e1)
      (pow_eq_of_unit Rs ϖ hϖ0 hϖR hϖ' hb hb' h2' e2)

end Abs

section Place

open GlobalTheory.CompanionTheory.SW.GoodRing

theorem sigR_incl {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (x : E) :
    sigR (Fv F v) σ (inclR (Fv F v) x) = inclR (Fv F v) (σ x) := by
  simp [sigR, inclR]

end Place

theorem split_content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (b₂ : Module.Basis (Fin 2) F E) (D : F), b₂ 0 = 1 → σ (b₂ 1) = -b₂ 1 → b₂ 1 * b₂ 1 = algebraMap F E D → ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (algebraMap F (Fv F v) D) = 1 → Valued.v (algebraMap F (Fv F v) 2) = 1 → (∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈ v.adicCompletionIntegers F) → (∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈ v.adicCompletionIntegers F) → ∀ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D → ¬ IsField (Fv F v ⊗[F] E) ∧ ∃ c : ℕ × ℕ → Fv F v ⊗[F] E, (∀ i, IsUnit (c i) ∧ c i ∈ intK b v) ∧ (∀ i, ∃ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ (c i) * c i ∧ ‖t‖ = ((qv v : ℝ) ^ (i.1 + i.2))⁻¹) ∧ (∀ x ∈ intK b v, IsUnit x → ∃ i, ∃ u ∈ intK b v, ∃ u' ∈ intK b v, u * u' = 1 ∧ x = c i * u) ∧ (∀ i j, ∀ u ∈ intK b v, ∀ u' ∈ intK b v, u * u' = 1 → c i = c j * u → i = j) := by
  intro F E _ _ _ _ _ σ _ d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB
  set K := Fv F v with hK
  set B := Algebra.TensorProduct.basis K b₂ with hB
  set C := Algebra.TensorProduct.basis K b with hC
  intro e he
  let Rs : Subring K := (v.adicCompletionIntegers F).toSubring
  have hB0 : B 0 = 1 := by
    rw [hB, Algebra.TensorProduct.basis_apply, hb0]; rfl
  have hB1 : B 1 = inclR K (b₂ 1) := by
    rw [hB, Algebra.TensorProduct.basis_apply]; rfl
  have hBD : B 1 * B 1 = algebraMap K (K ⊗[F] E) (algebraMap F K D) := by
    rw [hB1, ← map_mul, hD]
    show (1 : Fv F v) ⊗ₜ[F] algebraMap F E D = (algebraMap F (Fv F v) D) ⊗ₜ[F] (1 : E)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  have hDR : algebraMap F K D ∈ Rs := hD1.le
  obtain ⟨O', hOC, hOB'⟩ := GlobalTheory.CompanionTheory.SW.GoodRing.exists_subring Rs B C (algebraMap F K D) hB0 hBD hDR
    (fun k j => by
      have := hBC k j
      rwa [show inclR K (b k) = C k by rw [hC, Algebra.TensorProduct.basis_apply]; rfl] at this)
    (fun j k => by
      have := hCB j k
      rwa [show inclR K (b₂ j) = B j by rw [hB, Algebra.TensorProduct.basis_apply]; rfl] at this)
  have hS : ∀ y, y ∈ intK b v ↔ ∀ j, B.repr y j ∈ Rs := fun y =>
    Iff.trans (Iff.rfl) ((hOC y).symm.trans (hOB' y))
  have hve : Valued.v e = 1 := by
    have h1 : Valued.v e ^ 2 = 1 := by rw [← map_pow, he, hD1]
    exact (pow_eq_one_iff.1 h1).resolve_right two_ne_zero
  have he0 : e ≠ 0 := fun h => by
    rw [h, map_zero] at hve
    exact zero_ne_one hve
  have hv2 : Valued.v (2 : K) = 1 := by simpa [map_ofNat] using h21
  have h20 : (2 : K) ≠ 0 := fun h => by
    rw [h, map_zero] at hv2
    exact zero_ne_one hv2
  have heR : e ∈ Rs := hve.le
  have heR' : e⁻¹ ∈ Rs := by
    show Valued.v e⁻¹ ≤ 1
    rw [map_inv₀, hve, inv_one]
  have h2R : (2 : K)⁻¹ ∈ Rs := by
    show Valued.v (2 : K)⁻¹ ≤ 1
    rw [map_inv₀, hv2, inv_one]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hϖ' : (ϖ : K)⁻¹ ∉ Rs := fun h =>
    hϖ.not_isUnit (IsUnit.of_mul_eq_one (⟨(ϖ : K)⁻¹, h⟩ : v.adicCompletionIntegers F)
      (Subtype.ext (mul_inv_cancel₀ hϖ0)))
  have hfac : ∀ a ∈ Rs, a ≠ 0 → ∃ (u : K) (n : ℕ), u ∈ Rs ∧ u⁻¹ ∈ Rs ∧ a = u * (ϖ : K) ^ n := by
    intro a ha ha0
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨a, ha⟩ : v.adicCompletionIntegers F)) (fun h => ha0 (congrArg Subtype.val h)) hϖ
    refine ⟨((u : v.adicCompletionIntegers F) : K), n, (u : v.adicCompletionIntegers F).2, ?_, ?_⟩
    · have e1 : ((u : v.adicCompletionIntegers F) : K)⁻¹ =
          (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : K) := by
        exact inv_eq_of_mul_eq_one_right (congrArg Subtype.val u.mul_inv)
      rw [e1]
      exact (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)).2
    · exact congrArg Subtype.val hu
  obtain ⟨hnf, c, c1, c2, c3, c4⟩ := abs_main Rs (sigR K σ) B hB0 e h20 he0 (by rw [he]; exact hBD)
    (fun t => GlobalTheory.CompanionTheory.SW.GoodRing.sigR_algebraMap σ v t) (by rw [hB1, sigR_incl, hσ1, map_neg]) heR heR' h2R
    (ϖ : K) hϖ0 ϖ.2 hϖ' hfac (intK b v) hS
  refine ⟨hnf, c, c1, fun i => ⟨(ϖ : K) ^ (i.1 + i.2), c2 i, ?_⟩, c3, c4⟩
  have hn := GroundTheory.Global.normalizedAbv_of_irreducible v hϖ
  rw [GroundTheory.Global.normalizedAbv_apply] at hn
  rw [norm_pow, hn, inv_pow]
  simp [qv]

end GlobalTheory.CompanionTheory.SW.SplitIdeals
