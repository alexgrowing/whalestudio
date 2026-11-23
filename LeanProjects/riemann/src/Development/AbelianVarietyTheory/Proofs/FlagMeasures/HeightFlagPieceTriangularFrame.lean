import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroForallNormLeOfCovolumeLe
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.PieceCov

theorem det_gram_cols {n j r : Type} [Fintype n] [Fintype j] [Fintype r] [DecidableEq j] [DecidableEq r]
    (A : Matrix n j ℂ) (B U : Matrix n r ℂ) (C : Matrix j r ℂ) (hU : Uᴴ * U = 1) (hA : Uᴴ * A = 0)
    (hB : B = A * C + U * (Uᴴ * B)) :
    ((fromCols A B)ᴴ * fromCols A B).det.re = (Aᴴ * A).det.re * ‖(Uᴴ * B).det‖ ^ 2 := by
  have h1 : fromCols A B = fromCols A U * fromBlocks 1 C 0 (Uᴴ * B) := by
    rw [fromCols_mul_fromBlocks, ← hB]
    simp
  have hA' : Aᴴ * U = 0 := by
    have := congrArg conjTranspose hA
    simpa using this
  have h2 : (fromCols A U)ᴴ * fromCols A U = fromBlocks (Aᴴ * A) 0 0 1 := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hA, hA', hU]
  have h3 : (fromBlocks (1 : Matrix j j ℂ) C 0 (Uᴴ * B)).det = (Uᴴ * B).det := by
    rw [det_fromBlocks_zero₂₁]; simp
  rw [h1, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (fromCols A U)ᴴ, h2, det_mul, det_mul,
    det_conjTranspose, h3, det_fromBlocks_zero₂₁, det_one, mul_one]
  have h4 : star (Uᴴ * B).det * ((Aᴴ * A).det * (Uᴴ * B).det) =
      (Aᴴ * A).det * ((‖(Uᴴ * B).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [h4, Complex.re_mul_ofReal]

theorem relIndex_split {R V W : Type} [CommRing R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (p : V →ₗ[R] W) (s : W →ₗ[R] V) (hps : ∀ w, p (s w) = w) {F₀ F₁ S₀ : Submodule R V} {Λ S : Submodule R W}
    (h01 : F₀ ≤ F₁) (h0 : ∀ y ∈ F₀, p y = 0) (h1 : ∀ y ∈ F₁, p y ∈ Λ ∧ y - s (p y) ∈ F₀)
    (hs : ∀ w ∈ Λ, s w ∈ F₁) (hS₀ : S₀ ≤ F₀) (hS : S ≤ Λ) :
    (S₀ ⊔ S.map s).toAddSubgroup.relIndex F₁.toAddSubgroup =
      S₀.toAddSubgroup.relIndex F₀.toAddSubgroup * S.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  let q : V →ₗ[R] V := LinearMap.id - s ∘ₗ p
  have hq : ∀ y, q y = y - s (p y) := fun y => rfl
  let M : AddSubgroup V := S.toAddSubgroup.comap p.toAddMonoidHom ⊓ F₁.toAddSubgroup
  have hM : ∀ y, y ∈ M ↔ p y ∈ S ∧ y ∈ F₁ := fun y => Iff.rfl
  have e1 : (S₀ ⊔ S.map s).toAddSubgroup = S₀.toAddSubgroup.comap q.toAddMonoidHom ⊓ M := by
    ext y
    change y ∈ S₀ ⊔ S.map s ↔ q y ∈ S₀ ∧ y ∈ M
    rw [hM, hq, Submodule.mem_sup]
    constructor
    · rintro ⟨a, ha, _, ⟨w, hw, rfl⟩, rfl⟩
      have : p (a + s w) = w := by rw [map_add, h0 a (hS₀ ha), hps, zero_add]
      rw [this]
      exact ⟨by simpa using ha, hw, add_mem (h01 (hS₀ ha)) (hs w (hS hw))⟩
    · rintro ⟨ha, hb, -⟩
      exact ⟨_, ha, _, ⟨_, hb, rfl⟩, by simp⟩
  have e2 : M.map q.toAddMonoidHom = F₀.toAddSubgroup := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h1 x ((hM x).1 hx).2).2
    · intro hy
      refine ⟨y, (hM y).2 ⟨by rw [h0 y hy]; exact S.zero_mem, h01 hy⟩, ?_⟩
      change q y = y
      rw [hq, h0 y hy]; simp
  have e3 : F₁.toAddSubgroup.map p.toAddMonoidHom = Λ.toAddSubgroup := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h1 x hx).1
    · intro hw
      exact ⟨s w, hs w hw, hps w⟩
  rw [← AddSubgroup.relIndex_mul_relIndex (K := M) _ _ (e1 ▸ inf_le_right) inf_le_right]
  congr 1
  · rw [e1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, e2]
  · rw [AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, e3]

section Field

variable {E : Type} [Field E] [NumberField E]

def cm {n : ℕ} {κ : Type} (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (e : κ → Fin n → E) :
    Matrix (Fin n) κ ℂ := P⁻¹ * (Matrix.of e)ᵀ.map φ

omit [NumberField E] in
theorem cm_conj {n : ℕ} {κ : Type} (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (e : κ → Fin n → E) :
    cm ((starRingEnd ℂ).comp φ) (P.map (starRingEnd ℂ)) e = (cm φ P e).map (starRingEnd ℂ) := by
  have h : (P.map (starRingEnd ℂ))⁻¹ = P⁻¹.map (starRingEnd ℂ) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
    simp
  rw [cm, cm, h, Matrix.map_mul]
  rfl

theorem gramPl_eq [StarRing E] {n j : ℕ} (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace E)
    (e : Fin j → Fin n → E) :
    Formalism.HN.gramPl (Pi.basisFun E (Fin n)) X w e = (cm w.embedding (X w) e)ᴴ * cm w.embedding (X w) e := by
  ext a c
  simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, cm, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, mul_comm]

theorem unit_X {ι : Type} {n : ℕ} {φ : ι → E →+* ℂ} {P : ι → Matrix (Fin n) (Fin n) ℂ}
    {X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ} (h : PlaceMatch φ P X) (hP : ∀ v, IsUnit (P v)) (w) :
    IsUnit (X w).det := by
  obtain ⟨v, rfl⟩ := h.1.2 w
  have := (Matrix.isUnit_iff_isUnit_det _).1 (hP v)
  rcases h.2 v with ⟨-, h2⟩ | ⟨-, h2⟩
  · simp only [h2, this]
  · simp only [h2]
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact this.map _

theorem ht_index [StarRing E] [IsTotallyComplex E] {ι : Type} [Fintype ι] {n : ℕ} {φ : ι → E →+* ℂ}
    {P : ι → Matrix (Fin n) (Fin n) ℂ} {X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ}
    (h : PlaceMatch φ P X) (hP : ∀ v, IsUnit (P v)) {κ : Type} [Fintype κ] [DecidableEq κ]
    (e : κ → Fin n → E) (he : LinearIndependent E e) (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG)
    (hle : ∀ a, e a ∈ L) (hsp : Submodule.span E (L : Set (Fin n → E)) = Submodule.span E (Set.range e)) :
    Formalism.HN.ht (Pi.basisFun E (Fin n)) X L *
              ((Submodule.span (𝓞 E) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ v, ((cm (φ v) (P v) e)ᴴ * cm (φ v) (P v) e).det.re ∧
    (Submodule.span (𝓞 E) (Set.range e)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
  let σ := (Fintype.equivFin κ).symm
  have hr : Set.range (e ∘ σ) = Set.range e := σ.surjective.range_comp e
  obtain ⟨h1, h2⟩ := Formalism.HN.htGram E _ _ (Pi.basisFun E (Fin n)) X (unit_X h hP) _ (e ∘ σ)
    (he.comp _ σ.injective)
  rw [hr] at h1 h2
  have h3 := h2 L hL (Submodule.span_le.2 (Set.range_subset_iff.2 hle))
    (by rw [Formalism.HN.rkK, hsp, finrank_span_eq_card he])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [h3, h1]
    refine (Fintype.prod_bijective _ h.1 _ _ fun v => ?_).symm
    have h4 : ∀ ψ Q, ((cm ψ Q (e ∘ σ))ᴴ * cm ψ Q (e ∘ σ)).det = ((cm ψ Q e)ᴴ * cm ψ Q e).det := by
      intro ψ Q
      rw [← Matrix.det_submatrix_equiv_self σ ((cm ψ Q e)ᴴ * cm ψ Q e)]
      rfl
    rw [gramPl_eq, h4]
    rcases h.2 v with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · rw [h5, h6]
    · rw [h5, h6, cm_conj _ _ (hP v), ← Matrix.conjTranspose_map (starRingEnd ℂ) (fun _ => rfl), ← Matrix.map_mul,
        ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_re]
  · rw [h0] at h3
    have := (Formalism.HN.plLat E _ _ (Pi.basisFun E (Fin n)) X (unit_X h hP) (Submodule.span (𝓞 E) (Set.range e))
      (Submodule.fg_span (Set.finite_range e))).2.2
    rw [← h3] at this
    simp at this

theorem latAt_one {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E)) :
    (latAt E j Λ fun _ a b => if a = b then 1 else 0).toAddSubgroup =
      Λ.toAddSubgroup.map (GlobalTheory.LatFacts.emb E j) := by
  have h1 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
  have h2 : (latAt E j Λ fun _ a b => if a = b then 1 else 0) =
      Submodule.span ℤ ((Λ.toAddSubgroup.map (GlobalTheory.LatFacts.emb E j)).toIntSubmodule : Set _) := by
    simp only [latAt, h1, inv_one, Matrix.one_mulVec]
    rfl
  rw [h2, Submodule.span_eq]
  rfl

theorem emb_injective (j : ℕ) : Function.Injective (GlobalTheory.LatFacts.emb E j) := by
  intro x y h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  funext a
  exact w.embedding.injective (congrFun (congrFun h w) a)

theorem covStd_index [IsTotallyComplex E] {ι : Type} [Fintype ι] {n : ℕ} {φ : ι → E →+* ℂ}
    {P : ι → Matrix (Fin n) (Fin n) ℂ} {X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ}
    (h : PlaceMatch φ P X) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ)
    (g : Fin j → Fin j → E) (hg : LinearIndependent E g) (hsp : Submodule.span E (Set.range g) = ⊤)
    (hle : ∀ a, g a ∈ Λ) :
    covStd j Λ * ((Submodule.span (𝓞 E) (Set.range g)).toAddSubgroup.relIndex Λ.toAddSubgroup : ℝ) =
      Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * j) * ∏ v, ‖((Matrix.of g)ᵀ.map (φ v)).det‖ ^ 2 := by
  obtain ⟨hall, hstd⟩ := GlobalTheory.LatFacts.lattice_facts E ‹_› j
  have h1 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
  have hd1 : detNorm E j (fun _ a b => if a = b then 1 else 0) = 1 := by
    simp only [detNorm, h1]; simp
  have hlat : ∀ g : Fin j → Fin j → E, Submodule.span E (Set.range g) = ⊤ →
      Submodule.IsLattice E (Submodule.span (𝓞 E) (Set.range g)) := fun g hsp =>
    ⟨Submodule.fg_span (Set.finite_range g), by rw [Submodule.span_span_of_tower, hsp]⟩
  obtain ⟨κ, -, hκ⟩ := hall Λ hΛ
  obtain ⟨⟨i1, i2⟩, -⟩ := hκ _ (hd1 ▸ one_pos)
  obtain ⟨κ', -, hκ'⟩ := hall _ (hlat g hsp)
  obtain ⟨⟨i3, i4⟩, -⟩ := hκ' _ (hd1 ▸ one_pos)
  have hsub : Submodule.span (𝓞 E) (Set.range g) ≤ Λ := Submodule.span_le.2 (Set.range_subset_iff.2 hle)
  have hc := GlobalTheory.covolume_eq_relIndex_mul_of_haar volume
    (latAt E j (Submodule.span (𝓞 E) (Set.range g)) fun _ a b => if a = b then 1 else 0)
    (latAt E j Λ fun _ a b => if a = b then 1 else 0) (Submodule.span_mono (Set.image_mono hsub))
  rw [latAt_one, latAt_one, AddSubgroup.relIndex_map_map_of_injective _ _ (emb_injective j)] at hc
  rw [mul_comm]
  refine hc.symm.trans ?_
  obtain ⟨κ₀, -, hκ₀⟩ := hall _ (hlat (fun a => (Pi.single a 1 : Fin j → E)) (by
    simpa [← Pi.basisFun_apply] using (Pi.basisFun E (Fin j)).span_eq))
  have h0 := (hκ₀ _ (hd1 ▸ one_pos)).2.1
  rw [hstd, hd1, div_one] at h0
  set M : Matrix (Fin j) (Fin j) E := (Matrix.of g)ᵀ with hM
  have hMu : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hg)).ne_zero
  have hMw : ∀ ψ : E →+* ℂ, (M.map ψ).det ≠ 0 := fun ψ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero ψ).2 hMu
  let γ : MatInf E j := fun w => Matrix.of.symm (M.map w.embedding)⁻¹
  have hγ : ∀ w, Matrix.of (γ w) = (M.map w.embedding)⁻¹ := fun w => Matrix.of.apply_symm_apply _
  have hdγ : detNorm E j γ = (∏ v, ‖(M.map (φ v)).det‖ ^ 2)⁻¹ := by
    rw [detNorm, ← Finset.prod_inv_distrib]
    refine (Fintype.prod_bijective _ h.1 _ _ fun v => ?_).symm
    rw [hγ, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow]
    rcases h.2 v with ⟨h5, -⟩ | ⟨h5, -⟩
    · rw [h5]
    · rw [h5, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      simp
  have hpos : 0 < ∏ v, ‖(M.map (φ v)).det‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hMw _)) 2
  have h2 := (hκ₀ γ (hdγ ▸ inv_pos.2 hpos)).2.1
  rw [hdγ, ← h0, div_inv_eq_mul] at h2
  rw [← h2]
  have h3 : Submodule.span (𝓞 E) (Set.range g) = (Submodule.span (𝓞 E)
      (Set.range fun a => (Pi.single a 1 : Fin j → E))).map (M.mulVecLin.restrictScalars (𝓞 E)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext a
    simp [hM]
  unfold covAt latAt
  rw [h3, Submodule.map_coe, Set.image_image]
  congr 3
  funext y w
  rw [h1, inv_one, Matrix.one_mulVec, hγ, Matrix.nonsing_inv_nonsing_inv _ (hMw _).isUnit]
  funext a
  exact RingHom.map_mulVec w.embedding M y a

omit [NumberField E] in
theorem cm_mulVec {n : ℕ} {κ : Type} [Fintype κ] (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (e : κ → Fin n → E) (c : κ → E) :
    cm φ P e *ᵥ (fun i => φ (c i)) = P⁻¹ *ᵥ fun l => φ ((∑ i, c i • e i) l) := by
  rw [cm, ← Matrix.mulVec_mulVec]
  congr 1
  funext l
  simp [Matrix.mulVec, dotProduct, mul_comm]

theorem col_mem {n : ℕ} {κ : Type} (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (k : ℕ) (e : κ → Fin n → E) (a : κ) (ha : e a ∈ F k) :
    (fun l => cm φ P e l a) ∈ locFlag φ P F k :=
  Submodule.subset_span ⟨e a, ha, rfl⟩

theorem gram_step {n m j : ℕ} (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) {r : ℕ → ℕ} (U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ)
    (hU : Biorth r m U (fun b => (U b)ᴴ)) (hF : ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0)
    (b : ℕ) (e : Fin j → Fin n → E) (he : ∀ a, e a ∈ F b)
    (hsp : Submodule.span E (Set.range e) = Submodule.span E (F b : Set (Fin n → E)))
    (t : Fin (r b) → Fin n → E) (ht : ∀ a, t a ∈ F (b + 1)) :
    ((cm φ P (Sum.elim e t))ᴴ * cm φ P (Sum.elim e t)).det.re =
      ((cm φ P e)ᴴ * cm φ P e).det.re * ‖((U b)ᴴ * cm φ P t).det‖ ^ 2 := by
  have h1 : cm φ P (Sum.elim e t) = fromCols (cm φ P e) (cm φ P t) := by
    ext l a
    rcases a with a | a <;> rfl
  have hrange : locFlag φ P F b ≤ LinearMap.range (cm φ P e).mulVecLin := by
    rw [locFlag, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ Submodule.span E (Set.range e) := hsp ▸ Submodule.subset_span hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 this
    exact ⟨_, cm_mulVec φ P e c⟩
  have hC : ∀ a, ∃ c, cm φ P e *ᵥ c = fun l => (cm φ P t - U b * ((U b)ᴴ * cm φ P t)) l a := by
    intro a
    refine hrange ((hF b _).2 fun b' hb' => ?_)
    change (fun l => ((U b')ᴴ * (cm φ P t - U b * ((U b)ᴴ * cm φ P t))) l a) = 0
    rw [Matrix.mul_sub, ← Matrix.mul_assoc]
    rcases hb'.eq_or_lt with rfl | hlt
    · rw [hU.1 b, Matrix.one_mul, sub_self]; rfl
    · rw [hU.2.1 b' b hlt.ne', Matrix.zero_mul, sub_zero]
      exact (hF _ _).1 (col_mem φ P F _ t a (ht a)) b' hlt
  choose C hC using hC
  rw [h1]
  refine det_gram_cols _ _ (U b) (Matrix.of C)ᵀ (hU.1 b) ?_ ?_
  · ext l a
    exact congrFun ((hF _ _).1 (col_mem φ P F _ e a (he a)) b le_rfl) l
  · rw [← sub_eq_iff_eq_add]
    ext l a
    exact (congrFun (hC a) l).symm

end Field

theorem main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (n m : ℕ) (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ) (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ), PlaceMatch φ P X → (∀ v, IsUnit (P v)) → ∀ (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → ∀ U : ι → ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, (∀ v, Biorth r m (U v) (fun b => (U v b)ᴴ)) → (∀ v k y, y ∈ locFlag (φ v) (P v) F k ↔ ∀ b, k ≤ b → (U v b)ᴴ *ᵥ y = 0) → ∀ b, covStd (r b) (Λ b) * ∏ v, ‖((U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v))).det‖ ^ 2 = Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * r b) * pieceHt X F b := by
  intro E _ _ _ hE ι _ n m φ P X hm hP F r T T' Λ hT hΛ hF U hU hloc b
  have hfg : ∀ k, (F k).FG := by
    intro k
    refine Submodule.FG.of_le (Submodule.fg_finset_sup (Finset.range m)
      (fun s => (Λ s).map ((T s).mulVecLin.restrictScalars (𝓞 E))) fun s _ => (hΛ s).fg.map _) fun y hy => ?_
    have h1 : y = ∑ s ∈ Finset.range m, T s *ᵥ (T' s *ᵥ y) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.sum_mulVec, hT.2.2, Matrix.one_mulVec]
    rw [h1]
    refine Submodule.sum_mem _ fun s hs => ?_
    exact Finset.le_sup (f := fun s => (Λ s).map ((T s).mulVecLin.restrictScalars (𝓞 E))) hs
      ⟨_, ((hF k y).1 hy s).1, rfl⟩
  have hTT : ∀ w, T' b *ᵥ (T b *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hT.1 b, Matrix.one_mulVec]
  have hT0 : ∀ b', b' ≠ b → ∀ w, T' b' *ᵥ (T b *ᵥ w) = 0 := fun b' h w => by
    rw [Matrix.mulVec_mulVec, hT.2.1 b' b h, Matrix.zero_mulVec]
  have h01 : F b ≤ F (b + 1) := fun y hy =>
    (hF _ _).2 fun s => ⟨((hF _ _).1 hy s).1, fun h => ((hF _ _).1 hy s).2 (by omega)⟩
  have h0 : ∀ y ∈ F b, T' b *ᵥ y = 0 := fun y hy => ((hF _ _).1 hy b).2 le_rfl
  have h1 : ∀ y ∈ F (b + 1), T' b *ᵥ y ∈ Λ b ∧ y - T b *ᵥ (T' b *ᵥ y) ∈ F b := by
    intro y hy
    refine ⟨((hF _ _).1 hy b).1, (hF _ _).2 fun s => ?_⟩
    rw [Matrix.mulVec_sub]
    by_cases hs : s = b
    · subst hs
      rw [hTT, sub_self]
      exact ⟨zero_mem _, fun _ => rfl⟩
    · rw [hT0 s hs, sub_zero]
      exact ⟨((hF _ _).1 hy s).1, fun h => ((hF _ _).1 hy s).2 (by omega)⟩
  have hs : ∀ w ∈ Λ b, T b *ᵥ w ∈ F (b + 1) := by
    intro w hw
    refine (hF _ _).2 fun s => ?_
    by_cases hs : s = b
    · subst hs
      rw [hTT]
      exact ⟨hw, fun h => by omega⟩
    · rw [hT0 s hs]
      exact ⟨zero_mem _, fun _ => rfl⟩
  obtain ⟨e, he, hesp, heli⟩ := Submodule.exists_fun_fin_finrank_span_eq E (F b : Set (Fin n → E))
  obtain ⟨g, hg, hgsp, hgli⟩ : ∃ g : Fin (r b) → Fin (r b) → E, (∀ a, g a ∈ Λ b) ∧
      Submodule.span E (Set.range g) = ⊤ ∧ LinearIndependent E g := by
    have h := Submodule.exists_fun_fin_finrank_span_eq E (Λ b : Set (Fin (r b) → E))
    rw [(hΛ b).span_eq_top, finrank_top, Module.finrank_fin_fun] at h
    exact h
  set t : Fin (r b) → Fin n → E := fun a => T b *ᵥ g a with ht
  have htm : ∀ a, t a ∈ F (b + 1) := fun a => hs _ (hg a)
  have hli : LinearIndependent E (Sum.elim e t) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [Sum.elim_inl, Sum.elim_inr] at hc
    have h2 := congrArg (fun y => T' b *ᵥ y) hc
    simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, ht, hTT, h0 _ (he _), smul_zero,
      Finset.sum_const_zero, zero_add, Matrix.mulVec_zero] at h2
    have h3 := Fintype.linearIndependent_iff.1 hgli _ h2
    simp only [h3, zero_smul, Finset.sum_const_zero, add_zero] at hc
    have h4 := Fintype.linearIndependent_iff.1 heli _ hc
    rintro (a | a)
    exacts [h4 a, h3 a]
  have hsp : Submodule.span E (F (b + 1) : Set (Fin n → E)) = Submodule.span E (Set.range (Sum.elim e t)) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.Sum.elim_range, Submodule.span_union, hesp]
      intro y hy
      have h2 : T b *ᵥ (T' b *ᵥ y) ∈ Submodule.span E (Set.range t) := by
        have h3 : T' b *ᵥ y ∈ Submodule.span E (Set.range g) := hgsp ▸ Submodule.mem_top
        have h4 := Submodule.mem_map_of_mem (f := (T b).mulVecLin) h3
        rwa [Submodule.map_span, ← Set.range_comp] at h4
      exact Submodule.mem_sup.2 ⟨_, Submodule.subset_span (h1 y hy).2, _, h2, sub_add_cancel _ _⟩
    · refine Submodule.span_mono ?_
      rintro _ ⟨a | a, rfl⟩
      exacts [h01 (he a), htm a]
  have hidx := relIndex_split ((T' b).mulVecLin.restrictScalars (𝓞 E)) ((T b).mulVecLin.restrictScalars (𝓞 E))
    hTT h01 h0 h1 hs (S₀ := Submodule.span (𝓞 E) (Set.range e)) (S := Submodule.span (𝓞 E) (Set.range g))
    (Submodule.span_le.2 (Set.range_subset_iff.2 he)) (Submodule.span_le.2 (Set.range_subset_iff.2 hg))
  have hsp' : Submodule.span (𝓞 E) (Set.range (Sum.elim e t)) = Submodule.span (𝓞 E) (Set.range e) ⊔
      (Submodule.span (𝓞 E) (Set.range g)).map ((T b).mulVecLin.restrictScalars (𝓞 E)) := by
    rw [Set.Sum.elim_range, Submodule.span_union, Submodule.map_span, ← Set.range_comp]
    rfl
  obtain ⟨a1, a2⟩ := ht_index hm hP e heli (F b) (hfg b) he hesp.symm
  obtain ⟨b1, b2⟩ := ht_index hm hP (Sum.elim e t) hli (F (b + 1)) (hfg _)
    (by rintro (a | a); exacts [h01 (he a), htm a]) hsp
  have c1 := covStd_index hm (Λ b) (hΛ b) g hgli hgsp hg
  rw [hsp', hidx] at b1 b2
  have hcm : ∀ v, ‖((U v b)ᴴ * cm (φ v) (P v) t).det‖ ^ 2 =
      ‖((U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v))).det‖ ^ 2 * ‖((Matrix.of g)ᵀ.map (φ v)).det‖ ^ 2 := by
    intro v
    have : (Matrix.of t)ᵀ = T b * (Matrix.of g)ᵀ := rfl
    rw [cm, this, Matrix.map_mul, ← Matrix.mul_assoc (P v)⁻¹, ← Matrix.mul_assoc, Matrix.det_mul, norm_mul,
      mul_pow]
  simp only [fun v => gram_step (φ v) (P v) F (U v) (hU v) (hloc v) b e he hesp t htm, hcm,
    Finset.prod_mul_distrib] at b1
  rw [← a1] at b1
  have hp := (Formalism.HN.plLat E _ _ (Pi.basisFun E (Fin n)) X (unit_X hm hP) (F b) (hfg b)).2.2
  have a2' : ((Submodule.span (𝓞 E) (Set.range e)).toAddSubgroup.relIndex (F b).toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast a2
  have b2' : ((Submodule.span (𝓞 E) (Set.range g)).toAddSubgroup.relIndex (Λ b).toAddSubgroup : ℝ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero_iff.1 b2).2
  push_cast at b1
  rw [pieceHt, ← mul_div_assoc, eq_div_iff hp.ne']
  refine mul_right_cancel₀ (mul_ne_zero a2' b2') ?_
  rw [mul_assoc (Formalism.HermitianLatticesTheory.vInv E ^ _), b1]
  linear_combination (∏ v, ‖((U v b)ᴴ * ((P v)⁻¹ * (T b).map (φ v))).det‖ ^ 2) *
    Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b) *
    ((Submodule.span (𝓞 E) (Set.range e)).toAddSubgroup.relIndex (F b).toAddSubgroup : ℝ) * c1

end GlobalTheory.PieceCov
