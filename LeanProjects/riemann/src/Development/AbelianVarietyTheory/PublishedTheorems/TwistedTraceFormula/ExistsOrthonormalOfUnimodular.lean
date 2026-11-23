import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique

open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass

namespace GlobalTheory.HermLocal

theorem exists_zero_coord {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {ι : Type*} [Fintype ι]
    {a : ι → F} (ha : ∀ i, a i ≠ 0) {z : ι → F} (hz : z ≠ 0) (h : ∑ i, a i * z i ^ 2 = 0)
    (i : ι) : ∃ w : ι → F, w i ≠ 0 ∧ ∑ k, a k * w k ^ 2 = 0 := by
  classical
  by_cases hi : z i = 0
  swap
  · exact ⟨z, hi, h⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hj : z j ≠ 0 := hj
  have hij : i ≠ j := by
    rintro rfl
    exact hj hi
  have haj := ha j
  set t : F := -(a i + a j) / (2 * a j * z j) with ht
  refine ⟨fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k, ?_, ?_⟩
  · simp [hij, hi]
  · have : ∀ k, a k * ((if k = i then 1 else 0) + (if k = j then 1 else 0) + t * z k) ^ 2 =
        (if k = i then a i else 0) + (if k = j then a j + 2 * t * a j * z j else 0) +
          t ^ 2 * (a k * z k ^ 2) := by
      intro k
      by_cases h1 : k = i
      · subst h1
        simp [hij, hi]
      · by_cases h2 : k = j
        · subst h2
          simp only [h1, if_false, if_true]
          ring
        · simp only [h1, h2, if_false]
          ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [ht]
    field_simp
    ring

section Abstract

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}

theorem exists_represent_of_five (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    (hF : ∀ t : L, c t = t ↔ ∃ s : K, algebraMap K L s = t) {θ : L} (h0 : θ ≠ 0) (hθ : c θ = -θ)
    {r : ℕ} (hr : 2 ≤ r) {g : Fin r → L}
    (hg : ∀ i, c (g i) = g i) (hg0 : ∀ i, g i ≠ 0) {b : L} (hb : c b = b) (hb0 : b ≠ 0) :
    ∃ z : Fin r → L, z ⬝ᵥ Matrix.diagonal g *ᵥ (c ∘ z) = b := by
  obtain ⟨d, hd⟩ := (hF (θ * θ)).1 (by rw [map_mul, hθ]; ring)
  choose γ hγ' using fun i => (hF (g i)).1 (hg i)
  obtain ⟨κ, hκ'⟩ := (hF b).1 hb
  have hγ : ∀ i, γ i ≠ 0 := fun i h => hg0 i (by rw [← hγ', h, map_zero])
  have hκ : κ ≠ 0 := fun h => hb0 (by rw [← hκ', h, map_zero])
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (by rw [← hd, h, map_zero])
  let a : Option (Fin r ⊕ Fin r) → K := fun o => o.elim (-κ) (Sum.elim γ fun i => -d * γ i)
  have ha : ∀ o, a o ≠ 0 := by
    rintro (_ | i | i)
    · exact neg_ne_zero.mpr hκ
    · exact hγ i
    · exact mul_ne_zero (neg_ne_zero.mpr hd0) (hγ i)
  obtain ⟨e⟩ : Nonempty (Fin 5 ↪ Option (Fin r ⊕ Fin r)) :=
    Function.Embedding.nonempty_of_card_le (by simp; omega)
  obtain ⟨x, hx, hx0⟩ : ∃ x : Option (Fin r ⊕ Fin r) → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 :=
    isotropic_of_injective e e.injective (H _)
  obtain ⟨w, hw, hw0⟩ := exists_zero_coord h2 ha hx hx0 none
  rw [Fintype.sum_option, Fintype.sum_sum_type] at hw0
  have hw1 := congrArg (algebraMap K L) hw0
  have hw2 : algebraMap K L (w none) ≠ 0 := (map_ne_zero _).2 hw
  simp only [a, Option.elim, Sum.elim_inl, Sum.elim_inr, map_add, map_mul, map_neg, map_pow, map_sum,
    hγ', hκ', hd, map_zero] at hw1
  have hs : ∀ s : K, c (algebraMap K L s) = algebraMap K L s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨fun i => (algebraMap K L (w (some (Sum.inl i))) +
    algebraMap K L (w (some (Sum.inr i))) * θ) / algebraMap K L (w none), ?_⟩
  simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_div₀, map_add, map_mul,
    hs, hθ]
  have : ∀ i, (algebraMap K L (w (some (Sum.inl i))) + algebraMap K L (w (some (Sum.inr i))) * θ) /
      algebraMap K L (w none) * (g i * ((algebraMap K L (w (some (Sum.inl i))) +
        algebraMap K L (w (some (Sum.inr i))) * -θ) / algebraMap K L (w none))) =
      (g i * algebraMap K L (w (some (Sum.inl i))) ^ 2 +
        -(θ * θ) * g i * algebraMap K L (w (some (Sum.inr i))) ^ 2) /
          algebraMap K L (w none) ^ 2 := by
    intro i
    field_simp
    ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [div_eq_iff (pow_ne_zero 2 hw2)]
  linear_combination hw1

theorem congr_diagonal_of_five (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : L, c t = t ↔ ∃ s : K, algebraMap K L s = t) {θ : L} (hθ0 : θ ≠ 0) (hθ : c θ = -θ)
    (r : ℕ) : ∀ g g' : Fin r → L,
    (∀ i, c (g i) = g i) → (∀ i, c (g' i) = g' i) → (∀ i, g i ≠ 0) → (∀ i, g' i ≠ 0) →
    (∃ x : L, ∏ i, g i = x * c x * ∏ i, g' i) →
    Congr c (Matrix.diagonal g) (Matrix.diagonal g') := by
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).2 h2
  induction r with
  | zero =>
    intro g g' _ _ _ _ _
    exact ⟨1, by simp, Subsingleton.elim _ _⟩
  | succ r ih =>
    intro g g' hg hg' h0 h0' ⟨x, hx⟩
    obtain ⟨z, hz⟩ : ∃ z : Fin (r + 1) → L, z ⬝ᵥ Matrix.diagonal g *ᵥ (c ∘ z) = g' 0 := by
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          exact h0 0 (by simpa using hx)
        have hx1 : c x ≠ 0 := (map_ne_zero c).2 hx0
        refine ⟨fun _ => x⁻¹, ?_⟩
        simp only [dotProduct, Matrix.mulVec_diagonal, Function.comp_apply, map_inv₀,
          Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, hx]
        field_simp
      · exact exists_represent_of_five h2 H hF hθ0 hθ (by omega) hg h0 (hg' 0) (h0' 0)
    have hG : ∀ a b, c (Matrix.diagonal g a b) = Matrix.diagonal g b a := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simpa using hg a
      · simp [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab)]
    obtain ⟨P, k, hP, hPk, hk, hk0, -, hk1⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal_col_eq h2L hc hG (x := z) (hz ▸ h0' 0) 0
    have hp : ∏ i, g i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => h0 i
    have hk0 := hk0 (by rwa [Matrix.det_diagonal])
    have hcg : Congr c (Matrix.diagonal g) (Matrix.diagonal k) := ⟨P, hP, hPk.symm⟩
    have hk2 : k 0 = g' 0 := hk1.trans hz
    refine hcg.trans (congr_diagonal_of_tail hk2 (ih _ _ (fun i => hk _) (fun i => hg' _)
      (fun i => hk0 _) (fun i => h0' _) ?_))
    obtain ⟨y, -, hy⟩ := hcg.det
    rw [Matrix.det_diagonal, Matrix.det_diagonal, hx, Fin.prod_univ_succ, Fin.prod_univ_succ,
      hk2] at hy
    refine ⟨y * x, mul_left_cancel₀ (h0' 0) ?_⟩
    rw [hy, map_mul]
    ring

theorem congr_iff_of_five (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).2 h2
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    refine le_antisymm ?_ ?_
    · rw [← Algebra.IsQuadraticExtension.finrank_eq_two K L]
      simpa using AlgEquiv.card_le (F := K) (K := L)
    · have : Nontrivial (L ≃ₐ[K] L) := ⟨σ, 1, hσ⟩
      exact Finite.one_lt_card
  have : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L
    (hcard.trans (Algebra.IsQuadraticExtension.finrank_eq_two K L).symm)
  obtain ⟨τ, -, hτ⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hcard
  have hall : ∀ ρ : L ≃ₐ[K] L, ρ = 1 ∨ ρ = σ := fun ρ => by
    by_cases h : ρ = 1
    · exact Or.inl h
    · exact Or.inr ((hτ ρ h).trans (hτ σ hσ).symm)
  have hc : ∀ t, (σ : L →+* L) ((σ : L →+* L) t) = t := fun t => by
    rcases hall (σ * σ) with h | h
    · exact DFunLike.congr_fun h t
    · exact absurd (by simpa using h) hσ
  have hF : ∀ t : L, (σ : L →+* L) t = t ↔ ∃ s : K, algebraMap K L s = t := fun t => by
    constructor
    · intro h
      refine (IsGalois.mem_range_algebraMap_iff_fixed t).2 fun ρ => ?_
      rcases hall ρ with rfl | rfl
      · rfl
      · exact h
    · rintro ⟨s, rfl⟩
      exact σ.commutes s
  obtain ⟨u, hu⟩ : ∃ u : L, σ u ≠ u := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  have hθ : (σ : L →+* L) (u - σ u) = -(u - σ u) := by
    rw [map_sub, show (σ : L →+* L) (σ u) = u from hc u, neg_sub]
    rfl
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := (show Congr (σ : L →+* L) G G' from h).symm.det
    exact ⟨x, by rw [hx, mul_div_cancel_right₀ _ hd']; rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨P, g, hP, hPg, hg, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2L hc (G := G) hG
    obtain ⟨P', g', hP', hPg', hg', hg0'⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2L hc (G := G') hG'
    have h1 : Congr (σ : L →+* L) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
    have h1' : Congr (σ : L →+* L) G' (Matrix.diagonal g') := ⟨P', hP', hPg'.symm⟩
    refine (h1.trans (congr_diagonal_of_five h2 H hc hF (sub_ne_zero.2 hu.symm) hθ r g g' hg hg'
      (hg0 hd) (hg0' hd') ?_)).trans h1'.symm
    obtain ⟨y, -, hy⟩ := h1.det
    obtain ⟨y', -, hy'⟩ := h1'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [map_mul, RingHom.coe_coe]
    ring

end Abstract

open ValuativeRel in

theorem isotropic_five_of_localField (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (h2 : (2 : K) ≠ 0) (a : Fin 5 → K) :
    ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let w : Valuation K ℤᵐ⁰ := (valuation K).map e.toMonoidWithZeroHom e.strictMono.monotone
  have hw : ∀ x, w x = e (valuation K x) := fun _ => rfl
  have hlt : ∀ x y, w x < w y ↔ valuation K x < valuation K y := fun x y => by
    rw [hw, hw]; exact e.strictMono.lt_iff_lt
  have hlt1 : ∀ x, w x < 1 ↔ valuation K x < 1 := fun x => by simpa using hlt x 1
  have hle1 : ∀ x, w x ≤ 1 ↔ valuation K x ≤ 1 := fun x => by
    have := (hlt 1 x).not
    simpa using this
  have hmax : ∀ y : 𝒪[K], y ∈ 𝓂[K] ↔ valuation K (y : K) < 1 := fun y => by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one
  refine exists_zero_five_of_valuation h2 w (fun γ => ?_) (fun x hx => ?_) (fun c hc => ?_) a
  · obtain ⟨x, hx⟩ := valuation_surjective (e.symm γ)
    exact ⟨x, by rw [hw, hx]; simp⟩
  · letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    have h4 : (4 : K) ≠ 0 := by
      rw [show (4 : K) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    have hu : valuation K ((x - 1) / 4) < 1 := by
      rw [map_div₀, div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h4))]
      exact (hlt _ _).1 hx
    let u : 𝒪[K] := ⟨(x - 1) / 4, hu.le⟩
    have hum : u ∈ 𝓂[K] := (hmax u).2 hu
    obtain ⟨ρ, hρ, -⟩ := HenselianRing.is_henselian (I := 𝓂[K])
      (Polynomial.X ^ 2 + (Polynomial.X - Polynomial.C u))
      (by monicity!) 0
      (by simpa using hum) (by simp)
    have h1 : ρ ^ 2 + (ρ - u) = 0 := by simpa using hρ
    have h3 : (ρ : K) ^ 2 + (ρ - (x - 1) / 4) = 0 := by
      simpa [u] using congrArg (Subtype.val : 𝒪[K] → K) h1
    refine ⟨1 + 2 * ρ, ?_⟩
    have : x - 1 = 4 * ((ρ : K) ^ 2 + ρ) := by
      rw [show (ρ : K) ^ 2 + ρ = (x - 1) / 4 by linear_combination h3]
      field_simp
    linear_combination this
  · let r : Fin 3 → Fin 3 → 𝒪[K] := fun i j => ⟨c i j, (hle1 _).1 (hc i j)⟩
    obtain ⟨x, hx0, hx⟩ := TernaryResidue.exists_ne_zero_sum_eq_zero
      (k := 𝓀[K]) fun i j => IsLocalRing.residue 𝒪[K] (r i j)
    choose y hy using fun i => IsLocalRing.residue_surjective (x i)
    refine ⟨fun i => y i, fun i => (hle1 _).2 (y i).2, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
      refine ⟨i, le_antisymm ((hle1 _).2 (y i).2) (not_lt.1 fun h => hi ?_)⟩
      rw [← hy i]
      exact (IsLocalRing.residue_eq_zero_iff _).2 ((hmax _).2 ((hlt1 _).1 h))
    · have hmem : (∑ i, ∑ j, r i j * y i * y j) ∈ 𝓂[K] := by
        rw [← IsLocalRing.residue_eq_zero_iff, ← hx]
        simp only [map_sum, map_mul, hy]
      rw [hlt1]
      simpa [r] using (hmax _).1 hmem

theorem congr_iff_adicCompletion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (L : Type*) [Field L] [Algebra (v.adicCompletion F) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion F) L] (σ : L ≃ₐ[v.adicCompletion F] L)
    (hσ : σ ≠ 1) {r : ℕ} {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  exact congr_iff_of_five two_ne_zero (isotropic_adicCompletion_of_five_le F v (by simp)) σ hσ
    hG hG' hd hd'

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev ccBase (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Type*)
    [CommRing A] [Algebra (maximalRealSubfield E) A] :
    A ⊗[maximalRealSubfield E] E →ₐ[A] A ⊗[maximalRealSubfield E] E :=
  Algebra.TensorProduct.map (AlgHom.id A A) (IsCMField.complexConj E).toAlgHom

def CongrOver (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
    (G G' : Matrix (Fin r) (Fin r) E) : Prop :=
  ∃ P : Matrix (Fin r) (Fin r) (A ⊗[maximalRealSubfield E] E), IsUnit P.det ∧
    G'.map (fun x => (1 : A) ⊗ₜ[maximalRealSubfield E] x) =
      Pᵀ * G.map (fun x => (1 : A) ⊗ₜ[maximalRealSubfield E] x) * P.map (ccBase E A)

variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}

theorem CongrOver.of_congr
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) :
    CongrOver A G G' := by
  obtain ⟨P, hP, rfl⟩ := h
  let ι : E →+* A ⊗[maximalRealSubfield E] E := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨P.map ι, ?_, ?_⟩
  · rw [show (P.map ι).det = ι P.det from (RingHom.map_det ι P).symm]
    exact hP.isUnit.map ι
  · change (Pᵀ * G * P.map cc).map ι = (P.map ι)ᵀ * G.map ι * _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rfl

theorem CongrOver.det_norm (hd' : G'.det ≠ 0) (h : CongrOver A G G') :
    ∃ z : A ⊗[maximalRealSubfield E] E,
      (1 : A) ⊗ₜ[maximalRealSubfield E] (G.det / G'.det) = z * ccBase E A z := by
  obtain ⟨P, ⟨p, hp⟩, h⟩ := h
  let ι : E →+* A ⊗[maximalRealSubfield E] E := Algebra.TensorProduct.includeRight.toRingHom
  have h1 : ι G'.det = p * ι G.det * ccBase E A p := by
    rw [RingHom.map_det, RingHom.map_det, hp, AlgHom.map_det, ← Matrix.det_transpose P,
      ← Matrix.det_mul, ← Matrix.det_mul]
    exact congrArg Matrix.det h
  have h2 : ι (G.det / G'.det) * ι G'.det = ι G.det := by rw [← map_mul, div_mul_cancel₀ _ hd']
  have h3 : ccBase E A p * ccBase E A (p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ) = 1 := by
    rw [← map_mul, p.mul_inv, map_one]
  refine ⟨(p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ), ?_⟩
  change ι (G.det / G'.det) = _
  refine ((hd'.isUnit.map ι).mul_left_inj).1 ?_
  rw [h2, h1]
  linear_combination (-ι G.det) * p.mul_inv - (p * (p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ) * ι G.det) * h3

theorem congr_of_local (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (hf : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E)) G G')
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by
  refine landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E r G G' hG hG' hd hd' hs ?_
  have hm : G.det / G'.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')
  let a : maximalRealSubfield E := ⟨_, hm⟩
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  obtain ⟨b, hb0, hb1⟩ := GlobalTheory.Published.exists_basis_one_imaginary h0 hθ
  obtain ⟨d, hdθ⟩ := GlobalTheory.Published.exists_sq_real hθ
  have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))
  have ha0 : a ≠ 0 := fun h => div_ne_zero hd hd' (congrArg Subtype.val h)
  obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0
    (fun ρ => by
      let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
      have h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a :=
        ComplexEmbedding.lift_algebraMap_apply E _ a
      have h2 : 0 < (τ (a : E)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd τ (hs τ)
      rw [h1] at h2
      exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
    (fun v => by
      obtain ⟨z, hz⟩ := (hf v).det_norm hd'
      let B := Algebra.TensorProduct.basis (v.adicCompletion (maximalRealSubfield E)) b
      have hzB : z = B.repr z 0 ⊗ₜ[maximalRealSubfield E] (1 : E) +
          B.repr z 1 ⊗ₜ[maximalRealSubfield E] θ := by
        conv_lhs => rw [← B.sum_repr z, Fin.sum_univ_two]
        simp only [B, Algebra.TensorProduct.basis_apply, hb0, hb1, TensorProduct.smul_tmul',
          smul_eq_mul, mul_one]
      refine ⟨B.repr z 0, B.repr z 1, ?_⟩
      rw [← GlobalTheory.Published.norm_tmul_add_tmul _ h0 hθ hdθ, ← hzB]
      refine (algebraMap _
        (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).injective ?_
      rw [GlobalTheory.Published.algebraMap_norm_tensor, ← hz, ← IsScalarTower.algebraMap_apply]
      exact Algebra.TensorProduct.algebraMap_apply' a)
  refine ⟨x + y * θ, ?_⟩
  have h1 := congrArg (Subtype.val : maximalRealSubfield E → E) hxy
  have h2 : IsCMField.complexConj E θ = -θ := hθ
  simp [a, hdθ] at h1
  simp only [cc, map_add, map_mul, IsCMField.complexConj_apply_eq_self, h2, h1]
  ring

end Global

theorem exists_orthonormal_of_unimodular (R : Type) [CommRing R] (σ : R ≃+* R)
    (hσ : ∀ x, σ (σ x) = x) (R₀ : Subring R) (hR₀ : ∀ x, x ∈ R₀ ↔ σ x = x)
    [HenselianLocalRing R₀] [Finite (IsLocalRing.ResidueField R₀)]
    (hθ : ∃ θ : R, IsUnit (θ - σ θ)) {n : ℕ} {A : Matrix (Fin n) (Fin n) R}
    (hA : ∀ a b, σ (A a b) = A b a) (hd : IsUnit A.det) :
    ∃ P : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ Pᵀ * A * P.map σ = 1 := by
  obtain ⟨g, hg, h⟩ := Formalism.HermitianLatticesTheory.unimodUnramUnique R σ hσ R₀ hR₀ hθ n A
    (by ext a b; exact hA b a) hd
  refine ⟨g.map σ, ?_, ?_⟩
  · rw [show (g.map σ).det = σ g.det from (RingHom.map_det (σ : R →+* R) g).symm]
    exact hg.map σ
  · rwa [show (g.map σ).map σ = g by ext a b; exact hσ _]

end GlobalTheory.HermLocal

namespace GlobalTheory.Published

open GlobalTheory.HermLocal

def HermitianLocalGlobal : Prop :=
  (∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K],
    (2 : K) ≠ 0 →
    ∀ (L : Type) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L), σ ≠ 1 →
    ∀ (r : ℕ) (G G' : Matrix (Fin r) (Fin r) L),
      (∀ a b, σ (G a b) = G b a) → (∀ a b, σ (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
      ((∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
        ∃ x : L, G.det / G'.det = x * σ x)) ∧
  (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G G' : Matrix (Fin r) (Fin r) E),
    (∀ a b, cc (G a b) = G b a) → (∀ a b, cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      CongrOver (v.adicCompletion (maximalRealSubfield E)) G G') →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      G'.map τ = Qᵀ * G.map τ * Q.map conj) →
    ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc)

theorem hermitianLocalGlobal_holds : HermitianLocalGlobal :=
  ⟨fun K _ _ _ _ h2 _ _ _ _ σ hσ _ _ _ hG hG' hd hd' =>
      congr_iff_of_five h2 (isotropic_five_of_localField K h2) σ hσ hG hG' hd hd',
    fun _ _ _ _ _ _ _ hG hG' hd hd' hf hs => congr_of_local hG hG' hd hd' hf hs⟩

end GlobalTheory.Published
