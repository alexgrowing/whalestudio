import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Giv

namespace ResProj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]

theorem evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (f : MRing ι) :
    evC z (rename (joinInl ι ι₂) f) = evC (z ∘ joinInl ι ι₂) f := by
  unfold evC
  rw [map_rename, eval_rename]

theorem cone_rename_inl {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) :
    (mConeMap (joinVec y y₂)).comp (rename (joinInl ι ι₂)) =
      ((rename (Sum.inl : K → K ⊕ K₂) : MvPolynomial K Ω →ₐ[Ω] _).restrictScalars ℤ).comp (mConeMap y) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  obtain ⟨k, i⟩ := p
  simp [mConeMap, joinInl, joinVec]

theorem rename_mem_iff {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) (f : MRing ι) :
    rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y y₂) ↔ f ∈ mCoordIdeal y := by
  have h1 := AlgHom.congr_fun (cone_rename_inl y y₂) f
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h1
  unfold mCoordIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  show mConeMap (joinVec y y₂) (rename (joinInl ι ι₂) f) = 0 ↔ mConeMap y f = 0
  rw [h1]
  exact ⟨fun h => rename_injective _ Sum.inl_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

theorem comp_inl_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω)
    {z : (Σ k, joinIdx ι ι₂ k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y₂))) :
    z ∘ joinInl ι ι₂ ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => hz.1 (Sum.inl k), fun f hf =>
    (evC_rename_inl z f).symm.trans (hz.2 _ ((rename_mem_iff y y₂ f).2 hf))⟩

theorem sameOrbit_comp_inl {z z' : (Σ k, joinIdx ι ι₂ k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (z ∘ joinInl ι ι₂) (z' ∘ joinInl ι ι₂) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (Sum.inl k), fun k => hc _, rfl⟩

theorem cone_homog {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    mConeMap y f = C (aeval y f) * ∏ k, X k ^ a k := by
  unfold mConeMap
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), (X i.1 : MvPolynomial K Ω) ^ d i) = ∏ k, X k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, (X k : MvPolynomial K Ω) ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc, map_mul, map_prod, map_pow]
  rw [mul_assoc]
  congr 1

theorem evC_smul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    evC (fun p => c p.1 * z p) f = (∏ k, c k ^ a k) * evC z f :=
  eval_smul_homog f a hf c z

theorem mem_mcPts_span_iff {γ : MRing ι} {w : (Σ k, ι k) → ℂ} :
    w ∈ mcPts (Ideal.span {γ}) ↔ (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) ∧ evC w γ = 0 := by
  refine ⟨fun h => ⟨h.1, h.2 γ (Ideal.subset_span rfl)⟩, fun h => ⟨h.1, fun f hf => ?_⟩⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
  have h2 : eval w (map (Int.castRingHom ℂ) γ) = 0 := h.2
  rw [map_mul, map_mul, h2, mul_zero]

variable {M : ℕ}

local notation "𝔅" => (fun _ : Unit => Fin M)

section Forms

variable {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω) {G : Fin M → MRing ι} {g : K → ℕ}

theorem cross_mem (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) (i j : Fin M) :
    (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k) : MRing (joinIdx ι 𝔅)) * rename (joinInl ι 𝔅) (G j) -
      X (⟨Sum.inr (), j⟩ : Σ k, joinIdx ι 𝔅 k) * rename (joinInl ι 𝔅) (G i) ∈ mCoordIdeal (joinVec y y') := by
  have key : ∀ (f : MRing ι) (a : K → ℕ), IsMultiHomog f a → mConeMap (joinVec y y') (rename (joinInl ι 𝔅) f) =
      C (aeval y f) * ∏ k, X (Sum.inl k) ^ a k := by
    intro f a hf
    have h1 := AlgHom.congr_fun (cone_rename_inl (ι₂ := 𝔅) y y') f
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h1
    have h2 : mConeMap (joinVec y y') (rename (joinInl ι 𝔅) f) =
        rename (Sum.inl : K → K ⊕ Unit) (mConeMap y f) := h1
    rw [h2, cone_homog y hf, map_mul, rename_C, map_prod]
    exact congrArg _ (Finset.prod_congr rfl fun k _ => by rw [map_pow, rename_X])
  have hX : ∀ i : Fin M, mConeMap (joinVec y y') (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) =
      C (y' ⟨(), i⟩) * X (Sum.inr ()) := by
    intro i
    simp [mConeMap, joinVec]
  unfold mCoordIdeal
  rw [RingHom.mem_ker]
  show mConeMap (joinVec y y') _ = 0
  rw [map_sub, map_mul, map_mul, key _ _ (hG j), key _ _ (hG i), hX, hX]
  have h3 := congrArg (C : Ω →+* MvPolynomial (K ⊕ Unit) Ω) (hrel i j)
  simp only [map_mul] at h3
  linear_combination (X (Sum.inr ()) * ∏ k, (X (Sum.inl k) : MvPolynomial (K ⊕ Unit) Ω) ^ g k) * h3

theorem cross_eval (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i))
    {z : (Σ k, joinIdx ι 𝔅 k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (joinVec y y'))) (i j : Fin M) :
    z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) = z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i) := by
  have h := hz.2 _ (cross_mem y y' hG hrel i j)
  rw [map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, map_X, map_X, eval_X, eval_X] at h
  have e := fun f => evC_rename_inl (ι₂ := 𝔅) z f
  simp only [evC] at e ⊢
  rw [e, e] at h
  exact sub_eq_zero.mp h

end Forms

theorem proportional {G : Fin M → MRing ι} {z : (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hb : ∃ i : Fin M, z ⟨Sum.inr (), i⟩ ≠ 0)
    (hc : ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    {l : Fin M} (hl : evC (z ∘ joinInl ι 𝔅) (G l) ≠ 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ ∀ i : Fin M, z ⟨Sum.inr (), i⟩ = μ * evC (z ∘ joinInl ι 𝔅) (G i) := by
  have hall : ∀ i : Fin M, z ⟨Sum.inr (), i⟩ = z ⟨Sum.inr (), l⟩ / evC (z ∘ joinInl ι 𝔅) (G l) *
      evC (z ∘ joinInl ι 𝔅) (G i) := by
    intro i
    rw [div_mul_eq_mul_div, eq_div_iff hl]
    exact hc i l
  refine ⟨_, fun h0 => ?_, hall⟩
  obtain ⟨i, hi⟩ := hb
  exact hi ((hall i).trans (by rw [h0, zero_mul]))

theorem sameOrbit_of_inl {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    {z u : (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hzb : ∃ i : Fin M, z ⟨Sum.inr (), i⟩ ≠ 0) (hub : ∃ i : Fin M, u ⟨Sum.inr (), i⟩ ≠ 0)
    (hzc : ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (huc : ∀ i j : Fin M, u ⟨Sum.inr (), i⟩ * evC (u ∘ joinInl ι 𝔅) (G j) =
      u ⟨Sum.inr (), j⟩ * evC (u ∘ joinInl ι 𝔅) (G i))
    (ho : SameOrbit (z ∘ joinInl ι 𝔅) (u ∘ joinInl ι 𝔅))
    {l : Fin M} (hl : evC (z ∘ joinInl ι 𝔅) (G l) ≠ 0) : SameOrbit z u := by
  obtain ⟨c, hc, hcz⟩ := ho
  have e : ∀ i, evC (z ∘ joinInl ι 𝔅) (G i) = (∏ k, c k ^ g k) * evC (u ∘ joinInl ι 𝔅) (G i) := by
    intro i
    rw [hcz]
    exact evC_smul (hG i) c _
  have hC0 : (∏ k, c k ^ g k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hl' : evC (u ∘ joinInl ι 𝔅) (G l) ≠ 0 := by
    intro h0
    apply hl
    rw [e, h0, mul_zero]
  obtain ⟨μ, hμ, hz⟩ := proportional hzb hzc hl
  obtain ⟨ν, hν, hu⟩ := proportional hub huc hl'
  refine ⟨Sum.elim c fun _ => μ * (∏ k, c k ^ g k) / ν, ?_, ?_⟩
  · rintro (k | ⟨⟩)
    · exact hc k
    · exact div_ne_zero (mul_ne_zero hμ hC0) hν
  · funext q
    obtain ⟨k | ⟨⟩, i⟩ := q
    · exact congrFun hcz ⟨k, i⟩
    · have h1 := hz i
      have h2 := hu i
      show z ⟨Sum.inr (), i⟩ = μ * (∏ k, c k ^ g k) / ν * u ⟨Sum.inr (), i⟩
      rw [h1, h2, e i]
      field_simp

noncomputable def subst (G : Fin M → MRing ι) : MRing (joinIdx ι 𝔅) →ₐ[ℤ] MRing ι :=
  aeval (joinVec (fun q => X q) fun q => G q.2)

theorem evC_subst (G : Fin M → MRing ι) (z : (Σ k, ι k) → ℂ) (F : MRing (joinIdx ι 𝔅)) :
    evC z (subst G F) = evC (joinVec z fun q => evC z (G q.2)) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [evC, subst]
  | add p q hp hq =>
    simp only [evC, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p n hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    congr 1
    obtain ⟨k | ⟨⟩, i⟩ := n
    · simp [subst, joinVec]
    · simp [subst, joinVec, evC]

theorem subst_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω)
    {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i))
    (hy' : ∃ i, y' ⟨(), i⟩ ≠ 0) {F : MRing (joinIdx ι 𝔅)} (hF : F ∈ mCoordIdeal (joinVec y y')) :
    subst G F ∈ mCoordIdeal y := by
  obtain ⟨i₀, hi₀⟩ := hy'
  have hlam : ∀ i, aeval y (G i) = y' ⟨(), i⟩ * (aeval y (G i₀) / y' ⟨(), i₀⟩) := by
    intro i
    rw [mul_div_assoc', eq_div_iff hi₀, mul_comm]
    exact hrel i₀ i
  let S : MvPolynomial (K ⊕ Unit) Ω →ₐ[Ω] MvPolynomial K Ω :=
    aeval (Sum.elim X fun _ => C (aeval y (G i₀) / y' ⟨(), i₀⟩) * ∏ k, X k ^ g k)
  have hc : (mConeMap y).comp (subst G) = (S.restrictScalars ℤ).comp (mConeMap (joinVec y y')) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    obtain ⟨k | ⟨⟩, i⟩ := p
    · simp [subst, mConeMap, joinVec, S]
    · have h1 : subst G (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) = G i := by simp [subst, joinVec]
      have h2 : mConeMap (joinVec y y') (X (⟨Sum.inr (), i⟩ : Σ k, joinIdx ι 𝔅 k)) =
          C (y' ⟨(), i⟩) * X (Sum.inr ()) := by simp [mConeMap, joinVec]
      simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply]
      rw [h1, h2, cone_homog y (hG i), hlam i]
      simp [S, map_mul, mul_assoc]
  have h0 := AlgHom.congr_fun hc F
  have hF' : mConeMap (joinVec y y') F = 0 := hF
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hF', map_zero] at h0
  exact h0

theorem joinVec_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ _ : Unit, Fin M) → Ω)
    {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i))
    (hy' : ∃ i, y' ⟨(), i⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hi : ∃ i, evC z (G i) ≠ 0) :
    joinVec z (fun q => evC z (G q.2)) ∈ mcPts (mCoordIdeal (joinVec y y')) := by
  refine ⟨?_, fun F hF => (evC_subst G z F).symm.trans (hz.2 _ (subst_mem y y' hG hrel hy' hF))⟩
  rintro (k | ⟨⟩)
  · exact hz.1 k
  · exact hi

theorem immersion_inl {e : ℕ} {Y : Type} [TopologicalSpace Y] {A : FinHolAtlas e Y}
    {P' : Ideal (MRing (joinIdx ι 𝔅))} {U : Y → Set Y} {lam : Y → Y → (Σ k, joinIdx ι 𝔅 k) → ℂ}
    (hE : IsEmbedded A P' U lam) {G : Fin M → MRing ι} {g : K → ℕ} (hG : ∀ i, IsMultiHomog (G i) g)
    (hrel : ∀ z ∈ mcPts P', ∀ i j : Fin M, z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι 𝔅) (G j) =
      z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι 𝔅) (G i))
    (x : Y) (l : Fin M) (hl : lam x x ⟨Sum.inr (), l⟩ ≠ 0) (hGl : evC (lam x x ∘ joinInl ι 𝔅) (G l) ≠ 0)
    (p : (k : K) → ι k) (hp : ∀ k, lam x x ⟨Sum.inl k, p k⟩ ≠ 0) (j : Fin A.n) (hx : x ∈ (A.chart j).source) :
    (fderiv ℂ (fun t => affCoord p (lam x ((A.chart j).symm t) ∘ joinInl ι 𝔅)) (A.chart j x)).ker = ⊥ := by
  classical
  have ht₀ : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hsymm : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hx
  let L : (Fin e → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ := fun t => lam x ((A.chart j).symm t)
  have hL0 : L (A.chart j x) = lam x x := by simp only [L, hsymm]
  have hnhd : (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x ∈ 𝓝 (A.chart j x) :=
    inter_mem ((A.chart j).open_target.mem_nhds ht₀)
      (((A.chart j).continuousAt_symm ht₀).preimage_mem_nhds
        ((hE.isOpen x).mem_nhds (by rw [hsymm]; exact hE.mem_U x)))
  have hL : ∀ q, AnalyticAt ℂ (fun t => L t q) (A.chart j x) := fun q =>
    hE.holo x q j _ ⟨ht₀, by rw [Set.mem_preimage, hsymm]; exact hE.mem_U x⟩
  let Ψ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun t => affCoord p (L t ∘ joinInl ι 𝔅)
  let pt : (k : K ⊕ Unit) → joinIdx ι 𝔅 k := fun k => match k with
    | Sum.inl k => p k
    | Sum.inr _ => l
  let Φ : (Fin e → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ := fun t => affCoord pt (L t)
  have hp0 : ∀ k, L (A.chart j x) ⟨Sum.inl k, p k⟩ ≠ 0 := fun k => by rw [hL0]; exact hp k
  have hΨ : DifferentiableAt ℂ Ψ (A.chart j x) :=
    differentiableAt_pi.2 fun q => (AnalyticAt.fun_div (hL (joinInl ι 𝔅 q))
      (hL ⟨Sum.inl q.1, p q.1⟩) (hp0 q.1)).differentiableAt

  have hsc : ∀ t, (∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0) → ∀ f : MRing ι, ∀ a : K → ℕ, IsMultiHomog f a →
      evC (L t ∘ joinInl ι 𝔅) f = (∏ k, L t ⟨Sum.inl k, p k⟩ ^ a k) * evC (Ψ t) f := by
    intro t ht f a hf
    rw [← evC_smul hf]
    congr 1
    funext q
    show L t (joinInl ι 𝔅 q) = L t ⟨Sum.inl q.1, p q.1⟩ * (L t (joinInl ι 𝔅 q) / L t ⟨Sum.inl q.1, p q.1⟩)
    rw [mul_div_cancel₀ _ (ht q.1)]
  have hprod : ∀ t, (∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0) → (∏ k, L t ⟨Sum.inl k, p k⟩ ^ g k) ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (ht k)
  have hGl' : evC (Ψ (A.chart j x)) (G l) ≠ 0 := by
    intro h0
    apply hGl
    rw [← hL0, hsc _ hp0 _ _ (hG l), h0, mul_zero]
  let F : ((Σ k, ι k) → ℂ) → (Σ k, joinIdx ι 𝔅 k) → ℂ :=
    fun a => joinVec a fun q => evC a (G q.2) / evC a (G l)
  have hev : ∀ (a : (Σ k, ι k) → ℂ) (f : MRing ι), AnalyticAt ℂ (fun b : (Σ k, ι k) → ℂ => evC b f) a := fun a f =>
    analyticAt_eval_comp (F := fun b => b) (fun q => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt a) f
  have hF : DifferentiableAt ℂ F (Ψ (A.chart j x)) := by
    refine differentiableAt_pi.2 ?_
    rintro ⟨k | ⟨⟩, i⟩
    · exact differentiableAt_apply (𝕜 := ℂ) (⟨k, i⟩ : Σ k, ι k) _
    · exact (AnalyticAt.fun_div (hev _ _) (hev _ _) hGl').differentiableAt
  have hcont : ContinuousAt (fun t => evC (L t ∘ joinInl ι 𝔅) (G l)) (A.chart j x) :=
    (analyticAt_eval_comp (F := fun t => L t ∘ joinInl ι 𝔅) (fun q => hL (joinInl ι 𝔅 q)) (G l)).continuousAt
  have hEv : Φ =ᶠ[𝓝 (A.chart j x)] F ∘ Ψ := by
    have e1 : ∀ᶠ t in 𝓝 (A.chart j x), L t ⟨Sum.inr (), l⟩ ≠ 0 :=
      (hL _).continuousAt.eventually_ne (by rw [hL0]; exact hl)
    have e2 : ∀ᶠ t in 𝓝 (A.chart j x), evC (L t ∘ joinInl ι 𝔅) (G l) ≠ 0 :=
      hcont.eventually_ne (by rw [hL0]; exact hGl)
    have e3 : ∀ᶠ t in 𝓝 (A.chart j x), ∀ k, L t ⟨Sum.inl k, p k⟩ ≠ 0 :=
      eventually_all.2 fun k => (hL _).continuousAt.eventually_ne (hp0 k)
    filter_upwards [hnhd, e1, e2, e3] with t ht h1 h2 h3
    funext q
    obtain ⟨k | ⟨⟩, i⟩ := q
    · rfl
    · have hm := hrel (L t) (hE.mem x _ ht.2) i l
      show L t ⟨Sum.inr (), i⟩ / L t ⟨Sum.inr (), l⟩ = evC (Ψ t) (G i) / evC (Ψ t) (G l)
      rw [hsc t h3 _ _ (hG i), hsc t h3 _ _ (hG l)] at hm
      have h2' : evC (Ψ t) (G l) ≠ 0 := by
        intro h0
        apply h2
        rw [hsc t h3 _ _ (hG l), h0, mul_zero]
      have hC := hprod t h3
      rw [div_eq_div_iff h1 h2']
      apply mul_left_cancel₀ hC
      linear_combination hm
  have hD : fderiv ℂ Φ (A.chart j x) = (fderiv ℂ F (Ψ (A.chart j x))).comp (fderiv ℂ Ψ (A.chart j x)) := by
    rw [hEv.fderiv_eq]
    exact fderiv_comp _ hF hΨ
  have hpt : ∀ k, lam x x ⟨k, pt k⟩ ≠ 0 := by
    rintro (k | ⟨⟩)
    · exact hp k
    · exact hl
  have himm := hE.immersion x pt hpt j hx
  rw [eq_bot_iff]
  intro v hv
  have hv' : fderiv ℂ Ψ (A.chart j x) v = 0 := hv
  have hv2 : v ∈ (fderiv ℂ Φ (A.chart j x)).ker := by
    show fderiv ℂ Φ (A.chart j x) v = 0
    rw [hD]
    simp [hv']
  have hv3 : v ∈ (fderiv ℂ (fun t => affCoord pt (lam x ((A.chart j).symm t))) (A.chart j x)).ker := hv2
  rw [himm] at hv3
  exact hv3

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem joinInl_injective : Function.Injective (joinInl ι 𝔅) := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  obtain rfl : k = k' := Sum.inl.inj (congrArg Sigma.fst h)
  have h2 : i = i' := eq_of_heq (Sigma.mk.inj h).2
  rw [h2]

theorem homog_rename_inl {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d) :
    IsMultiHomog (rename (joinInl ι 𝔅) f : MRing (joinIdx ι 𝔅)) (Sum.elim d 0) := by
  classical
  intro m hm k
  rw [support_rename_of_injective joinInl_injective, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases k with
  | inl k =>
    rw [Sum.elim_inl, ← hf m' hm' k]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply joinInl_injective m' ⟨k, i⟩
  | inr k =>
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact Sum.inl_ne_inr (congrArg Sigma.fst hq)

theorem eval_rename_inl (z : (Σ k, joinIdx ι 𝔅 k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename (joinInl ι 𝔅) f)) =
      eval (z ∘ joinInl ι 𝔅) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

end ResProj

open ResProj in

theorem anLogRes_of_embedded_join : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))) (R : AnLogRes (mCoordIdeal (joinVec y y')) J e) (γ : MRing ι) (c : K → ℕ), IsEmbedded R.A (mCoordIdeal (joinVec y y')) R.U R.lift → (∃ i, y' ⟨(), i⟩ ≠ 0) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsMultiHomog γ c → γ ∉ mCoordIdeal y → (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) γ) = 0 → z ∈ mcPts J) → (∀ z ∈ mcPts (mCoordIdeal y), evC z γ ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0) → Nonempty (AnLogRes (mCoordIdeal y) (Ideal.span {γ}) e) := by
  intro K _ ι _ Ω _ _ y e M y' J R γ c hE hy' hy hγ hγP hJ hGex
  have hnot : ∀ w : (Σ k, ι k) → ℂ, w ∈ mcPts (mCoordIdeal y) → w ∉ mcPts (Ideal.span {γ}) → evC w γ ≠ 0 :=
    fun w hw hn h0 => hn (mem_mcPts_span_iff.2 ⟨hw.1, h0⟩)
  have hcross : ∀ {G : Fin M → MRing ι} {g : K → ℕ}, (∀ i, IsMultiHomog (G i) g) →
      (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) →
      ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), ∀ i j : Fin M,
        z ⟨Sum.inr (), i⟩ * evC (z ∘ joinInl ι fun _ : Unit => Fin M) (G j) =
          z ⟨Sum.inr (), j⟩ * evC (z ∘ joinInl ι fun _ : Unit => Fin M) (G i) :=
    fun hG hrel z hz i j => cross_eval y y' hG hrel hz i j
  have hxm : ∀ x, R.lift x x ∈ mcPts (mCoordIdeal (joinVec y y')) := fun x => R.mem x x (R.mem_U x)
  refine ⟨{
    homog := ⟨{γ}, fun f hf => ⟨c, by rw [Set.mem_singleton_iff.mp hf]; exact hγ⟩, rfl⟩
    nondeg := fun h => hγP (h (Ideal.subset_span rfl))
    X := R.X
    top := R.top
    compact := R.compact
    t2 := R.t2
    A := R.A
    U := R.U
    isOpen_U := R.isOpen_U
    mem_U := R.mem_U
    lift := fun x t => R.lift x t ∘ joinInl ι fun _ : Unit => Fin M
    holo := fun x p => R.holo x (joinInl ι (fun _ : Unit => Fin M) p)
    mem := fun x t ht => comp_inl_mem y y' (R.mem x t ht)
    compat := fun x x' t ht => sameOrbit_comp_inl (R.compat x x' t ht)
    surj := ?_
    inj := ?_
    immersion := ?_
    snc := ?_
    null := ?_ }⟩
  · intro z hz hzγ
    obtain ⟨G, g, hG, hrel, hi⟩ := hGex z hz (hnot z hz hzγ)
    obtain ⟨x, hx⟩ := hE.surj _ (joinVec_mem y y' hG hrel hy' hz hi)
    exact ⟨x, sameOrbit_comp_inl hx⟩
  · intro x x' hx ho
    have hw := comp_inl_mem y y' (hxm x)
    obtain ⟨G, g, hG, hrel, l, hl⟩ := hGex _ hw (hnot _ hw hx)
    exact hE.inj x x' (sameOrbit_of_inl hG ((hxm x).1 (Sum.inr ())) ((hxm x').1 (Sum.inr ()))
      (hcross hG hrel _ (hxm x)) (hcross hG hrel _ (hxm x')) ho hl)
  · intro x hx p hp j hxj
    have hw := comp_inl_mem y y' (hxm x)
    obtain ⟨G, g, hG, hrel, i, hi⟩ := hGex _ hw (hnot _ hw hx)
    obtain ⟨μ, hμ, hprop⟩ := proportional ((hxm x).1 (Sum.inr ())) (hcross hG hrel _ (hxm x)) hi
    obtain ⟨l, hl⟩ : ∃ l : Fin M, R.lift x x ⟨Sum.inr (), l⟩ ≠ 0 := (hxm x).1 (Sum.inr ())
    have hGl : evC (R.lift x x ∘ joinInl ι fun _ : Unit => Fin M) (G l) ≠ 0 := by
      intro h0
      apply hl
      rw [hprop l, h0, mul_zero]
    exact immersion_inl hE hG (hcross hG hrel) x l hl hGl p hp j hxj
  · intro f a hfP hfa hz
    have hfP' : rename (joinInl ι fun _ : Unit => Fin M) f ∉ mCoordIdeal (joinVec y y') :=
      fun h => hfP ((rename_mem_iff y y' f).1 h)
    have hz' : ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')),
        eval z (map (Int.castRingHom ℂ) (rename (joinInl ι fun _ : Unit => Fin M) f)) = 0 → z ∈ mcPts J := by
      intro z hzm h0
      have h1 : evC (z ∘ joinInl ι fun _ : Unit => Fin M) f = 0 := (evC_rename_inl z f).symm.trans h0
      have h2 := hz _ (comp_inl_mem y y' hzm) h1
      exact hJ z hzm ((evC_rename_inl z γ).trans (mem_mcPts_span_iff.1 h2).2)
    obtain ⟨r, m, W, hW⟩ := R.snc _ (Sum.elim a 0) hfP' (homog_rename_inl hfa) hz'
    refine ⟨r, m, W, ?_⟩
    simp only [eval_rename_inl] at hW
    exact hW
  · intro j
    refine measure_mono_null ?_ (R.null j)
    intro t ht
    refine ⟨ht.1, ?_⟩
    have h1 := (mem_mcPts_span_iff.1 ht.2).2
    exact hJ _ (hxm _) ((evC_rename_inl _ γ).trans h1)

end GlobalTheory.CompanionTheory.Ar.Giv
