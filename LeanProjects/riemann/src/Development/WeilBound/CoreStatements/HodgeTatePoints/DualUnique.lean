import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LeadMinor
import Development.WeilBound.CoreStatements.HodgeTatePoints.GaGram
import Development.WeilBound.CoreStatements.HodgeTatePoints.GaSurj

noncomputable section

namespace PositivityTheory.HtPt.Ga

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

section

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {N : ℕ}

theorem dual_exists (y : Fin N → M) (t : A) (G H Z : Matrix (Fin N) (Fin N) A)
    (h : H * G = 1 + t • Z) :
    ∃ i : Module.Dual A M →ₗ[A] (Fin N → A), ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z := by
  let ev : Module.Dual A M →ₗ[A] (Fin N → A) := LinearMap.pi fun j => Module.Dual.eval A M (y j)
  refine ⟨(Matrix.vecMulLinear H).comp ev, fun w j => ⟨Matrix.vecMul (ev w) Z j, ?_⟩⟩
  change Matrix.vecMul (Matrix.vecMul (ev w) H) G j = _
  rw [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul]
  rfl

theorem dual_unique (t : A) (G H Z : Matrix (Fin N) (Fin N) A) (h : G * H = 1 + t • Z)
    (a a' r : Fin N → A) (ha : ∀ j, ∃ z, ∑ l, a l * G l j = r j + t * z)
    (ha' : ∀ j, ∃ z, ∑ l, a' l * G l j = r j + t * z) : ∃ x : Fin N → A, a = a' + t • x := by
  choose z hz using ha
  choose z' hz' using ha'
  have h1 : Matrix.vecMul (a - a') G = t • (z - z') := by
    ext j
    rw [Matrix.sub_vecMul]
    change ∑ l, a l * G l j - ∑ l, a' l * G l j = t * (z j - z' j)
    rw [hz, hz']
    ring
  have h2 := congrArg (fun v => Matrix.vecMul v H) h1
  simp only [Matrix.vecMul_vecMul, h, Matrix.vecMul_add, Matrix.vecMul_one, Matrix.vecMul_smul,
    Matrix.smul_vecMul] at h2
  refine ⟨Matrix.vecMul (z - z') H - Matrix.vecMul (a - a') Z, ?_⟩
  rw [smul_sub, ← h2]
  abel

theorem dual_split [Module.Projective A M] (y : Fin N → M) (t : A) (G : Matrix (Fin N) (Fin N) A)
    (hs : ∀ x : M, ∃ a : Fin N → A, ∃ x' : M, x = ∑ j, a j • y j + t • x')
    (i : Module.Dual A M →ₗ[A] (Fin N → A))
    (hi : ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + t * z) :
    ∃ r : (Fin N → A) →ₗ[A] Module.Dual A M, ∀ w, ∃ w', r (i w) = w + t • w' := by
  let f : ((Fin N → A) × M) →ₗ[A] M :=
    (Fintype.linearCombination A y).coprod (t • LinearMap.id)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, x', e⟩ := hs x
    exact ⟨(a, x'), by rw [e]; simp [f, Fintype.linearCombination_apply]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let s₁ := (LinearMap.fst A _ _).comp s
  let s₂ := (LinearMap.snd A _ _).comp s
  have hs' : ∀ x, ∑ j, s₁ x j • y j + t • s₂ x = x := by
    intro x
    have := LinearMap.congr_fun hs x
    simpa [f, s₁, s₂, Fintype.linearCombination_apply] using this
  let B : (Fin N → A) →ₗ[A] Module.Dual A M := (dotProductBilin A A).compl₂ s₁
  refine ⟨B.comp (Matrix.vecMulLinear G), fun w => ?_⟩
  choose z hz using hi w
  refine ⟨B z - w.comp s₂, ?_⟩
  ext x
  change ∑ j, (∑ l, i w l * G l j) * s₁ x j = w x + t * (∑ j, z j * s₁ x j - w (s₂ x))
  conv_rhs => rw [← hs' x]
  rw [hs' x]
  nth_rewrite 2 [← hs' x]
  simp only [hz, map_add, map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_add_distrib, mul_sub,
    Finset.mul_sum, mul_assoc]
  simp only [mul_comm (w _)]
  ring

end

theorem dual_map : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' := by
  intro A K _ _ _ _ hAK E _ _ c hc p R N _ Ω _ _ _ _ D κ σ d m hσ hd hκ hom hproj
  obtain ⟨G, H, Z, Z', hG, hGH, hHG⟩ := gram_unit A K hAK E c hc p R N Ω D σ d (hσ σ) hd
  obtain ⟨-, -, hsurj⟩ := q_surj A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hσ _) hκ hom
  obtain ⟨t, ht⟩ := hκ
  have hR : ∀ Y : Matrix (Fin N) (Fin N) A, ((p : A) ^ R) • Y = ((p : A) ^ m) • (κ * t) • Y := by
    intro Y
    rw [ht, smul_smul]
    congr 1
    ring
  rw [hR] at hGH hHG
  let y : Fin N → D.omHT (σ.comp c.toRingHom) := fun j =>
    ⟨_, proj_mem_omHT D (σ.comp c.toRingHom) (h_mem_om' D (Pi.single j 1))⟩
  have key : ∀ i, D.IsDualMap σ d m i ↔
      ∀ w j, ∃ z, ∑ l, i w l * G l j = w (y j) + (p : A) ^ m * z := by
    intro i
    constructor
    · intro h w j
      obtain ⟨z, hz⟩ := h w j (y j) rfl
      refine ⟨z, hAK ?_⟩
      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
    · intro h w j y' hy'
      obtain rfl : y' = y j := Subtype.ext hy'
      obtain ⟨z, hz⟩ := h w j
      refine ⟨z, ?_⟩
      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hG]
  simp only [key]
  refine ⟨dual_exists y _ G H _ hHG, fun i i' hi hi' w =>
    dual_unique _ G H _ hGH _ _ (fun j => w (y j)) (hi w) (hi' w), fun i hi =>
    dual_split y _ G (fun x => ?_) i hi⟩
  obtain ⟨a, x', hx', e⟩ := hsurj x x.2
  refine ⟨a, ⟨x', hx'⟩, Subtype.ext ?_⟩
  rw [e, Submodule.coe_add, Submodule.coe_sum]
  rfl

end PositivityTheory.HtPt.Ga
