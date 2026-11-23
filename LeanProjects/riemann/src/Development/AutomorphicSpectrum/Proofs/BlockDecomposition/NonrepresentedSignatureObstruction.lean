import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongrOfSignatureOfAdelicNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSignatureFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAuxiliaryHyperbolicVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignCompatibleNumberingOfWittTowerLower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseRangeRealEmbeddings
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse
open Matrix NumberField

theorem hasSignature_map_conj {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (J.map (starRingEnd ℂ)) p q := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  refine GlobalTheory.FrameComplement.hasSignature_of_frame c (Q.map (starRingEnd ℂ)) ?_
  have e1 : (Q.map (starRingEnd ℂ))ᴴ * J.map (starRingEnd ℂ) * Q.map (starRingEnd ℂ) =
      (Qᴴ * J * Q).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ)]
    congr 2
  rw [e1, hQ]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.one_apply, apply_ite (starRingEnd ℂ)]

theorem hasSignature_diagonal {n P N : ℕ} (c : Fin n → ℝ) (h : P + N = n)
    (hc : ∀ i : Fin n, ((i : ℕ) < P → 0 < c i) ∧ (P ≤ (i : ℕ) → c i < 0)) :
    Formalism.UG.HasSignature (Matrix.diagonal fun i => (c i : ℂ)) P N := by
  let e : Fin P ⊕ Fin N ≃ Fin n := finSumFinEquiv.trans (finCongr h)
  let s : Fin n → ℝ := fun i => (√|c i|)⁻¹
  have hs : ∀ i, s i * c i * s i = if (i : ℕ) < P then 1 else -1 := fun i => by
    have h0 : c i ≠ 0 := by
      rcases lt_or_ge (i : ℕ) P with h | h
      · exact ((hc i).1 h).ne'
      · exact ((hc i).2 h).ne
    have hp : 0 < |c i| := abs_pos.2 h0
    have hq : √|c i| * √|c i| = |c i| := Real.mul_self_sqrt hp.le
    have hq0 : √|c i| ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    split_ifs with hi
    · have hh := (hc i).1 hi
      rw [abs_of_pos hh] at hq hq0
      simp only [s, abs_of_pos hh]
      field_simp
      linarith
    · have hh := (hc i).2 (not_lt.1 hi)
      rw [abs_of_neg hh] at hq hq0
      simp only [s, abs_of_neg hh]
      field_simp
      linarith
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by simp [h])
    ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e) ?_
  have e1 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
      (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e =
      (Matrix.diagonal fun i : Fin n => (((if (i : ℕ) < P then 1 else -1 : ℝ)) : ℂ)).submatrix e e := by
    have e2 : ((Matrix.diagonal fun i => (s i : ℂ)).submatrix id e)ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
        (Matrix.diagonal fun i => (s i : ℂ)).submatrix id e =
        ((Matrix.diagonal fun i => (s i : ℂ))ᴴ * (Matrix.diagonal fun i => (c i : ℂ)) *
        (Matrix.diagonal fun i => (s i : ℂ))).submatrix e e := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [e2, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    funext i
    rw [← hs i]
    simp
  rw [e1]
  have hl : ∀ a : Fin P, ((e (Sum.inl a) : Fin n) : ℕ) = a := fun a => by simp [e]
  have hr : ∀ a : Fin N, ((e (Sum.inr a) : Fin n) : ℕ) = P + a := fun a => by simp [e]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply, hl, hr, Fin.ext_iff] <;>
    split_ifs <;> simp

theorem exists_signs (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (n : ℕ) (P : (F →+* ℝ) → ℕ) :
    ∃ a : Fin n → F, ∀ (σ : F →+* ℝ) (i : Fin n),
      ((i : ℕ) < P σ → 0 < σ (a i)) ∧ (P σ ≤ (i : ℕ) → σ (a i) < 0) := by
  haveI : Finite (F →+* ℝ) := Finite.of_injective (fun σ => Complex.ofRealHom.comp σ) (fun σ τ h => by
    ext x
    have := congrArg (fun g : F →+* ℂ => g x) h
    simpa using this)
  have hd := GlobalTheory.Shintani.denseRange_realEmbeddings F
  have key : ∀ i : Fin n, ∃ x : F, ∀ σ : F →+* ℝ, ((i : ℕ) < P σ → 0 < σ x) ∧ (P σ ≤ (i : ℕ) → σ x < 0) := by
    intro i
    let U : (F →+* ℝ) → Set ℝ := fun σ => if (i : ℕ) < P σ then Set.Ioi 0 else Set.Iio 0
    have hU : IsOpen (Set.pi Set.univ U) := isOpen_set_pi Set.finite_univ fun σ _ => by
      simp only [U]
      split_ifs
      · exact isOpen_Ioi
      · exact isOpen_Iio
    have hne : (Set.pi Set.univ U).Nonempty := ⟨fun σ => if (i : ℕ) < P σ then 1 else -1, fun σ _ => by
      simp only [U]
      split_ifs <;> simp⟩
    obtain ⟨x, hx⟩ := hd.exists_mem_open hU hne
    refine ⟨x, fun σ => ?_⟩
    have := hx σ (Set.mem_univ _)
    simp only [U] at this
    constructor
    · intro h
      simpa [h] using this
    · intro h
      simpa [not_lt.2 h] using this
  choose a ha using key
  exact ⟨a, fun σ i => ha i σ⟩

theorem exists_real_restrict {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (τ : E →+* ℂ) :
    ∃ σ : F →+* ℝ, ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ) := by
  haveI := cm.totReal
  have hr : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  exact ⟨hr.embedding, fun x => (hr.coe_embedding_apply x).symm⟩

theorem eq_or_conj_of_restrict {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (τ τ' : E →+* ℂ)
    (h : ∀ x : F, τ' (algebraMap F E x) = τ (algebraMap F E x)) :
    τ' = τ ∨ τ' = (starRingEnd ℂ).comp τ := by
  haveI := cm.totReal
  haveI := cm.cmUnram.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hst : ∀ (φ : E →+* ℂ) x, φ (star x) = starRingEnd ℂ (φ x) := cm.cmUnram.2.1
  have hcc : ∀ x : E, ReciprocityTheory.ChartRestriction.G.FD.cc x = star x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective ((GlobalTheory.Published.embedding_cc τ x).trans (hst τ x).symm)
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  rw [hcc] at hθ
  have hfix : ∀ x : E, star x = x → τ' x = τ x := fun x hx => by
    obtain ⟨a, rfl⟩ := (cm.fixed x).1 hx
    exact h a
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have hdec : ∀ x : E, ∃ u v : E, star u = u ∧ star v = v ∧ x = u + v * θ := fun x => by
    refine ⟨(x + star x) / 2, (x - star x) / (2 * θ), ?_, ?_, ?_⟩
    · simp [star_div₀, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', hθ]
      simp only [star_ofNat]
      field_simp
      ring
    · field_simp
      ring
  have hsq : τ' θ * τ' θ = τ θ * τ θ := by
    have : star (θ * θ) = θ * θ := by rw [star_mul', hθ]; ring
    have := hfix _ this
    simpa using this
  have hf : (τ' θ - τ θ) * (τ' θ + τ θ) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hf with h3 | h3
  · left
    ext x
    obtain ⟨u, v, hu, hv, rfl⟩ := hdec x
    simp only [map_add, map_mul, hfix u hu, hfix v hv, sub_eq_zero.1 h3]
  · right
    have hθ' : τ' θ = starRingEnd ℂ (τ θ) := by
      rw [← hst, hθ, map_neg]
      linear_combination h3
    have hc : ∀ w : E, star w = w → starRingEnd ℂ (τ w) = τ w := fun w hw => by rw [← hst, hw]
    ext x
    obtain ⟨u, v, hu, hv, rfl⟩ := hdec x
    simp only [RingHom.comp_apply, map_add, map_mul, hfix u hu, hfix v hv, hc u hu, hc v hv, hθ']

theorem frame_of_congr {E : Type} [Field E] [StarRing E] {m t k n : ℕ} (G P : Matrix (Fin m) (Fin m) E)
    (hP : P.det ≠ 0) (e : Fin m ≃ Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) (B : Matrix (Fin t) (Fin t) E)
    (A : Matrix (Fin n) (Fin n) E)
    (h : Pᴴ * G * P = (fromBlocks B 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0 A)).submatrix e e) :
    ∃ x : Matrix (Fin m) (Fin t ⊕ Fin k) E, x.rank = t + k ∧ xᴴ * G * x = fromBlocks B 0 0 0 := by
  let g : Fin t ⊕ Fin k → Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n) :=
    Sum.elim Sum.inl (fun j => Sum.inr (Sum.inl (Sum.inl j)))
  have hg : Function.Injective g := by
    rintro (a | a) (b | b) hab <;> simp_all [g]
  let c : Fin t ⊕ Fin k → Fin m := fun i => e.symm (g i)
  refine ⟨P.submatrix id c, le_antisymm ?_ ?_, ?_⟩
  · simpa using Matrix.rank_le_card_width (P.submatrix id c)
  · have hu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
    have h1 : (P⁻¹).submatrix c id * P.submatrix id c = 1 := by
      have : (P⁻¹).submatrix c id * P.submatrix id c = (P⁻¹ * P).submatrix c c := by
        refine Matrix.ext fun i j => ?_
        simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
      rw [this, Matrix.nonsing_inv_mul _ hu]
      refine Matrix.ext fun i j => ?_
      have hc : Function.Injective c := e.symm.injective.comp hg
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply, hij, hc.ne hij]
    have h2 := Matrix.rank_mul_le_right ((P⁻¹).submatrix c id) (P.submatrix id c)
    rw [h1, Matrix.rank_one] at h2
    simpa using h2
  · have : (P.submatrix id c)ᴴ * G * P.submatrix id c = (Pᴴ * G * P).submatrix c c := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [this, h]
    refine Matrix.ext fun i j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [c, g]

theorem block_submatrix {E : Type} [Field E] {r t : ℕ} (ht : t < r) (β : Matrix (Fin r) (Fin r) E)
    (hz : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → β i j = 0) (htk : t + (r - t) = r) :
    (fromBlocks (β.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) 0 0 0 :
      Matrix (Fin t ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) E).submatrix
        (finSumFinEquiv.trans (finCongr htk)).symm (finSumFinEquiv.trans (finCongr htk)).symm = β := by
  set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf
  have h1 : ∀ a : Fin t, f (Sum.inl a) = Fin.castLE ht.le a := fun a => by
    apply Fin.ext; simp [hf]
  have h2 : ∀ a : Fin (r - t), t ≤ (f (Sum.inr a)).1 := fun a => by
    simp [hf]
  refine Matrix.ext fun a b => ?_
  obtain ⟨a, rfl⟩ := f.surjective a
  obtain ⟨b, rfl⟩ := f.surjective b
  rw [Matrix.submatrix_apply, f.symm_apply_apply, f.symm_apply_apply]
  rcases a with a | a <;> rcases b with b | b
  · simp [h1]
  · simp [hz _ _ (Or.inr (h2 b))]
  · simp [hz _ _ (Or.inl (h2 a))]
  · simp [hz _ _ (Or.inl (h2 a))]

theorem exists_nonnegOn {r t : ℕ} (ht : t < r) (Z : Matrix (Fin r) (Fin r) ℂ)
    (hZ : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → Z i j = 0) {p q : ℕ}
    (hs : Formalism.UG.HasSignature (Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) p q) :
    ∃ S : Submodule ℂ (Fin r → ℂ), NonnegOn 1 Z S ∧ Module.finrank ℂ S = p + (r - t) := by
  have htk : t + (r - t) = r := by omega
  have hZe := block_submatrix ht Z hZ htk
  set f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk) with hf
  set Zs := Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hZs
  obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ hs
  let Q₁ : Matrix (Fin t) (Fin p) ℂ := Q.submatrix id Sum.inl
  have hQ1 : Q₁ᴴ * Zs * Q₁ = 1 := by
    have h1 : Q₁ᴴ * Zs * Q₁ = (Qᴴ * Zs * Q).submatrix Sum.inl Sum.inl := by
      refine Matrix.ext fun i j => ?_
      simp only [Q₁, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [h1, hQ]
    refine Matrix.ext fun i j => ?_
    simp [Formalism.UG.Jpq]
  let C : Matrix (Fin t ⊕ Fin (r - t)) (Fin p ⊕ Fin (r - t)) ℂ := fromBlocks Q₁ 0 0 1
  let A : Matrix (Fin r) (Fin p ⊕ Fin (r - t)) ℂ := C.submatrix f.symm id
  let Lm : Matrix (Fin p ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ := fromBlocks (Q₁ᴴ * Zs) 0 0 1
  have hLC : Lm * C = 1 := by
    simp [Lm, C, fromBlocks_multiply, hQ1]
  have hLA : Lm.submatrix id f.symm * A = 1 := by
    rw [show A = C.submatrix f.symm id from rfl, Matrix.submatrix_mul_equiv, hLC, Matrix.submatrix_id_id]
  have hA : Aᴴ * Z * A = fromBlocks 1 0 0 0 := by
    have h1 : Aᴴ * Z * A = Cᴴ * (fromBlocks Zs 0 0 0 : Matrix (Fin t ⊕ Fin (r - t)) (Fin t ⊕ Fin (r - t)) ℂ) * C := by
      rw [← hZe]
      simp only [A]
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_id_id]
    rw [h1]
    simp [C, fromBlocks_conjTranspose, fromBlocks_multiply, hQ1]
  have hinj : Function.Injective A.mulVecLin := fun v w hvw => by
    have h1 : A *ᵥ v = A *ᵥ w := hvw
    have := congrArg (fun u => (Lm.submatrix id f.symm) *ᵥ u) h1
    simpa [Matrix.mulVec_mulVec, hLA] using this
  refine ⟨LinearMap.range A.mulVecLin, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    have e1 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = star v ⬝ᵥ ((Aᴴ * Z * A) *ᵥ v) := by
      rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]
    have e2 : star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v)) = ∑ i, star (v (Sum.inl i)) * v (Sum.inl i) := by
      rw [e1, hA]
      simp [fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
    show 0 ≤ 1 * (star (A *ᵥ v) ⬝ᵥ (Z *ᵥ (A *ᵥ v))).re
    rw [e2, one_mul, Complex.re_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have hc : star (v (Sum.inl i)) * v (Sum.inl i) = ((Complex.normSq (v (Sum.inl i)) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hc, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  · rw [LinearMap.finrank_range_of_inj hinj]
    simp

theorem finrank_le_of_posOn {m p q : ℕ} (G : Matrix (Fin m) (Fin m) ℂ) (hs : Formalism.UG.HasSignature G p q)
    (T : Submodule ℂ (Fin m → ℂ)) (hT : PosOn 1 G T) : Module.finrank ℂ T ≤ p := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ hs
  simp only [Fintype.card_fin] at c
  let N : Matrix (Fin m) (Fin q) ℂ := Q.submatrix id Sum.inr
  have hN : Nᴴ * G * N = -1 := by
    have h1 : Nᴴ * G * N = (Qᴴ * G * Q).submatrix Sum.inr Sum.inr := by
      refine Matrix.ext fun i j => ?_
      simp only [N, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]
    rw [h1, hQ]
    refine Matrix.ext fun i j => ?_
    simp [Formalism.UG.Jpq]
  have hL : (-(Nᴴ * G)) * N = 1 := by
    rw [Matrix.neg_mul, hN, neg_neg]
  have hinj : Function.Injective N.mulVecLin := fun v w hvw => by
    have h1 : N *ᵥ v = N *ᵥ w := hvw
    have := congrArg (fun u => (-(Nᴴ * G)) *ᵥ u) h1
    simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
  have hdis : Disjoint T (LinearMap.range N.mulVecLin) := by
    rw [Submodule.disjoint_def]
    rintro x hx ⟨v, rfl⟩
    by_contra h0
    have h1 := hT _ hx h0
    have e1 : star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v)) = star v ⬝ᵥ ((Nᴴ * G * N) *ᵥ v) := by
      rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]
    have h2 : 0 < 1 * (star (N *ᵥ v) ⬝ᵥ (G *ᵥ (N *ᵥ v))).re := h1
    rw [e1, hN, one_mul] at h2
    simp only [Matrix.neg_mulVec, Matrix.one_mulVec, dotProduct_neg, Complex.neg_re] at h2
    have h3 : 0 ≤ (star v ⬝ᵥ v).re := by
      rw [dotProduct, Complex.re_sum]
      refine Finset.sum_nonneg fun i _ => ?_
      have hc : star (v i) * v i = ((Complex.normSq (v i) : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]; rfl
      simp only [Pi.star_apply]
      rw [hc, Complex.ofReal_re]
      exact Complex.normSq_nonneg _
    linarith
  have h1 := Submodule.finrank_add_finrank_le_of_disjoint hdis
  rw [LinearMap.finrank_range_of_inj hinj] at h1
  simp at h1
  omega

theorem hasSig_neg {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨c, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ h
  let s := Equiv.sumComm (Fin q) (Fin p)
  refine GlobalTheory.FrameComplement.hasSignature_of_frame (by omega) (Q.submatrix id s) ?_
  have e1 : (Q.submatrix id s)ᴴ * (-J) * Q.submatrix id s = -((Qᴴ * J * Q).submatrix s s) := by
    ext a b
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e1, hQ]
  ext (a | a) (b | b) <;> simp [Formalism.UG.Jpq, s, Matrix.one_apply]

theorem sig_bound {m r t : ℕ} (ht : t < r) (Z : Matrix (Fin r) (Fin r) ℂ)
    (hZ : ∀ i j : Fin r, (t ≤ i.1 ∨ t ≤ j.1) → Z i j = 0) (G : Matrix (Fin m) (Fin m) ℂ) {p₁ q₁ p q : ℕ}
    (hB : Formalism.UG.HasSignature (Z.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le)) p₁ q₁)
    (hG : Formalism.UG.HasSignature G p q)
    (hno : ∀ (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) → NonnegOn ε Z S →
      ∃ T : Submodule ℂ (Fin m → ℂ), PosOn ε G T ∧ Module.finrank ℂ S ≤ Module.finrank ℂ T) :
    p₁ + (r - t) ≤ p ∧ q₁ + (r - t) ≤ q := by
  constructor
  · obtain ⟨S, hS, hd⟩ := exists_nonnegOn ht Z hZ hB
    obtain ⟨T, hT, hle⟩ := hno 1 S (Or.inl rfl) hS
    have := finrank_le_of_posOn G hG T hT
    omega
  · obtain ⟨S, hS, hd⟩ := exists_nonnegOn ht (-Z) (fun i j h => by simp [hZ i j h])
      (q := p₁) (p := q₁) (hasSig_neg hB)
    have hS' : NonnegOn (-1) Z S := fun w hw => by
      have := hS w hw
      simpa [Matrix.neg_mulVec] using this
    obtain ⟨T, hT, hle⟩ := hno (-1) S (Or.inr rfl) hS'
    have hT' : PosOn 1 (-G) T := fun w hw h0 => by
      have := hT w hw h0
      simpa [Matrix.neg_mulVec] using this
    have := finrank_le_of_posOn (-G) (hasSig_neg hG) T hT'
    omega

def blockM {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) : Matrix (Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) (Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) E :=
  fromBlocks B 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0 (diagonal fun i => algebraMap F E (a i)))

theorem blockM_map {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) (τ : E →+* ℂ) (σ : F →+* ℝ) (hσ : ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ)) :
    (blockM (k := k) B a).map τ = fromBlocks (B.map τ) 0 0 (fromBlocks (fromBlocks 0 1 1 0) 0 0
      (diagonal fun i => ((σ (a i) : ℝ) : ℂ))) := by
  ext (i | (i | i) | i) (j | (j | j) | j) <;>
    simp [blockM, Matrix.one_apply, Matrix.diagonal_apply, apply_ite τ, hσ]

theorem blockM_det {F E : Type} [Field F] [Field E] [Algebra F E] {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E)
    (a : Fin n → F) : (blockM (k := k) B a).det =
      B.det * (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E).det * ∏ i, algebraMap F E (a i) := by
  rw [blockM, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_diagonal, mul_assoc]

theorem hyp_det_ne {E : Type} [Field E] (k : ℕ) :
    (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E).det ≠ 0 := by
  have : (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) *
      (fromBlocks 0 1 1 0 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) E) = 1 := by
    simp [fromBlocks_multiply]
  exact (Matrix.isUnit_det_of_right_inverse this).ne_zero

theorem blockM_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (cm : CMData F E) {t k n : ℕ} (B : Matrix (Fin t) (Fin t) E) (hB : Bᴴ = B) (a : Fin n → F) :
    (blockM (k := k) B a)ᴴ = blockM B a := by
  have hf : ∀ z : F, star (algebraMap F E z) = algebraMap F E z := fun z => (cm.fixed _).2 ⟨z, rfl⟩
  simp [blockM, fromBlocks_conjTranspose, hB, Matrix.diagonal_conjTranspose]
  exact fun i => hf _

theorem map_isHerm {E : Type} [Field E] [StarRing E] {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : Gᴴ = G)
    (τ : E →+* ℂ) (hτ : ∀ x, τ (star x) = starRingEnd ℂ (τ x)) : Formalism.UG.IsHerm (starRingEnd ℂ) (G.map τ) := by
  unfold Formalism.UG.IsHerm
  rw [Formalism.UG.P.cT_conj_eq]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
  have : G i j = star (G j i) := by
    conv_lhs => rw [← hG]
    rfl
  rw [this, hτ]
  rfl

theorem map_isUnit_det {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : G.det ≠ 0)
    (τ : E →+* ℂ) : IsUnit (G.map τ).det := by
  rw [show (G.map τ).det = τ G.det from (RingHom.map_det τ G).symm]
  exact (isUnit_iff_ne_zero.2 hG).map _

theorem gram_submatrix {E : Type} [Field E] [StarRing E] {m a b : Type} [Fintype m] [Fintype a] [Fintype b] [DecidableEq a]
    (G : Matrix m m E) (x : Matrix m a E) (f : b ≃ a) :
    (x.submatrix id f)ᴴ * G * x.submatrix id f = (xᴴ * G * x).submatrix f f := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, id]

theorem exists_lift {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) (σ : F →+* ℝ) : ∃ τ : E →+* ℂ, ∀ x : F, τ (algebraMap F E x) = (σ x : ℂ) := by
  haveI : Algebra.IsQuadraticExtension F E := ⟨cm.deg2⟩
  exact ⟨ComplexEmbedding.lift E (Complex.ofRealHom.comp σ), fun x => ComplexEmbedding.lift_algebraMap_apply E _ x⟩

theorem exists_frame_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (cm : CMData F E) {m t k : ℕ} (G : Matrix (Fin m) (Fin m) E) (B : Matrix (Fin t) (Fin t) E)
    (hG : Gᴴ = G) (hB : Bᴴ = B) (hGd : G.det ≠ 0) (hBd : B.det ≠ 0) (hm : t + 2 * k < m)
    (hs : ∀ τ : E →+* ℂ, ∃ p₁ q₁ p q : ℕ, Formalism.UG.HasSignature (B.map τ) p₁ q₁ ∧
      Formalism.UG.HasSignature (G.map τ) p q ∧ p₁ + k ≤ p ∧ q₁ + k ≤ q) :
    ∃ x : Matrix (Fin m) (Fin t ⊕ Fin k) E, x.rank = t + k ∧ xᴴ * G * x = fromBlocks B 0 0 0 := by
  classical
  haveI := cm.totReal
  obtain ⟨n, hn⟩ : ∃ n, n = m - t - 2 * k := ⟨_, rfl⟩
  have hn0 : 0 < n := by omega
  choose L hL using exists_lift cm
  choose p₁ q₁ p q h1 h2 h3 h4 using fun σ => hs (L σ)
  have c1 : ∀ σ, t = p₁ σ + q₁ σ := fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h1 σ)).1
  have c2 : ∀ σ, m = p σ + q σ := fun σ => by simpa using (Formalism.UG.P.sig_data _ _ _ (h2 σ)).1
  let P : (F →+* ℝ) → ℕ := fun σ => p σ - p₁ σ - k
  have sigM : ∀ a : Fin n → F, (∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a i)) ∧ (P σ ≤ (i : ℕ) → σ (a i) < 0)) →
      ∀ τ : E →+* ℂ, ∃ u v : ℕ, Formalism.UG.HasSignature (G.map τ) u v ∧
        Formalism.UG.HasSignature ((blockM (k := k) B a).map τ) u v := by
    intro a ha τ
    obtain ⟨σ, hσ⟩ := exists_real_restrict cm τ
    have key : Formalism.UG.HasSignature ((blockM (k := k) B a).map (L σ)) (p σ) (q σ) := by
      have hc1 := c1 σ
      have hc2 := c2 σ
      have h3' := h3 σ
      have h4' := h4 σ
      have d := hasSignature_diagonal (P := P σ) (N := q σ - q₁ σ - k) (fun i => σ (a i))
        (by simp only [P]; omega) (ha σ)
      have := GlobalTheory.FrameComplement.hasSignature_fromBlocks (h1 σ)
        (GlobalTheory.FrameComplement.hasSignature_fromBlocks (GlobalTheory.WittSign.hasSignature_hyperbolic k) d)
      rw [blockM_map B a (L σ) σ (hL σ)]
      rwa [show p₁ σ + (k + P σ) = p σ by simp only [P]; omega,
        show q₁ σ + (k + (q σ - q₁ σ - k)) = q σ by omega] at this
    rcases eq_or_conj_of_restrict cm (L σ) τ (fun x => by rw [hσ, hL]) with rfl | rfl
    · exact ⟨_, _, h2 σ, key⟩
    · refine ⟨p σ, q σ, ?_, ?_⟩
      · have := hasSignature_map_conj (h2 σ)
        rwa [Matrix.map_map] at this
      · have := hasSignature_map_conj key
        rwa [Matrix.map_map] at this
  obtain ⟨a, ha⟩ := exists_signs F n P
  obtain ⟨e⟩ : Nonempty (Fin m ≃ Fin t ⊕ ((Fin k ⊕ Fin k) ⊕ Fin n)) :=
    Fintype.card_eq.1 (by simp; omega)
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨σ₀, -⟩ := exists_real_restrict cm τ₀
  have ha0 : ∀ i, a i ≠ 0 := fun i h0 => by
    have := ha σ₀ i
    rw [h0, map_zero] at this
    rcases lt_or_ge (i : ℕ) (P σ₀) with h | h
    · exact lt_irrefl _ (this.1 h)
    · exact lt_irrefl _ (this.2 h)
  have hMd : ∀ b : Fin n → F, (∀ i, b i ≠ 0) → ((blockM (k := k) B b).submatrix e e).det ≠ 0 := fun b hb => by
    rw [det_submatrix_equiv_self, blockM_det]
    refine mul_ne_zero (mul_ne_zero hBd (hyp_det_ne k)) (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    exact (map_ne_zero _).2 (hb i)
  have hMh : ∀ b : Fin n → F, ((blockM (k := k) B b).submatrix e e)ᴴ = (blockM (k := k) B b).submatrix e e :=
    fun b => by rw [conjTranspose_submatrix, blockM_herm cm B hB]
  have hsub : ∀ (b : Fin n → F) (τ : E →+* ℂ), ((blockM (k := k) B b).submatrix e e).map τ =
      ((blockM (k := k) B b).map τ).submatrix e e := fun _ _ => rfl
  obtain ⟨c, hc⟩ := (cm.fixed (G.det / ((blockM (k := k) B a).submatrix e e).det)).1 (by
    rw [star_div₀, ← Matrix.det_conjTranspose, ← Matrix.det_conjTranspose, hG, hMh])
  have hcpos : ∀ σ : F →+* ℝ, 0 < σ c := fun σ => by
    obtain ⟨u, v, hu, hv⟩ := sigM a ha (L σ)
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.HermAdelicNorm.congr_of_hasSignature hu
      (GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e)
    have := GlobalTheory.Published.Landherr.re_det_div_pos (G' := (blockM (k := k) B a).submatrix e e) hGd (L σ) ⟨Q, hQ, hQe⟩
    rw [← hc, hL] at this
    simpa using this
  have hc0 : c ≠ 0 := fun h => by
    have := hcpos σ₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  let i₀ : Fin n := ⟨0, hn0⟩
  let a' : Fin n → F := fun i => a i * (if i = i₀ then c else 1)
  have ha'0 : ∀ i, a' i ≠ 0 := fun i => mul_ne_zero (ha0 i) (by split_ifs <;> simp [hc0])
  have ha' : ∀ (σ : F →+* ℝ) (i : Fin n), ((i : ℕ) < P σ → 0 < σ (a' i)) ∧ (P σ ≤ (i : ℕ) → σ (a' i) < 0) := by
    intro σ i
    have hp : 0 < σ (if i = i₀ then c else 1) := by
      split_ifs
      · exact hcpos σ
      · simp
    simp only [a', map_mul]
    exact ⟨fun h => mul_pos ((ha σ i).1 h) hp, fun h => mul_neg_of_neg_of_pos ((ha σ i).2 h) hp⟩
  have hdet : ((blockM (k := k) B a').submatrix e e).det = G.det := by
    have h5 := hMd a ha0
    rw [det_submatrix_equiv_self] at h5 ⊢
    have h6 : ∏ i, algebraMap F E (a' i) = (∏ i, algebraMap F E (a i)) * algebraMap F E c := by
      simp only [a', map_mul, Finset.prod_mul_distrib, apply_ite (algebraMap F E), map_one,
        Finset.prod_ite_eq', Finset.mem_univ, if_true]
    rw [hc, det_submatrix_equiv_self] at *
    rw [blockM_det, h6, ← mul_assoc, ← blockM_det, mul_div_cancel₀ _ h5]
  obtain ⟨R, hR, hRe⟩ := GlobalTheory.HermAdelicNorm.congr_of_signature_of_adelic_norm F E cm m G
    ((blockM (k := k) B a').submatrix e e) hG (hMh a') hGd (hMd a' ha'0)
    (fun τ => by
      obtain ⟨u, v, hu, hv⟩ := sigM a' ha' τ
      exact ⟨u, v, hu, GlobalTheory.StandardGramVectors.hasSignature_submatrix hv e⟩)
    ⟨1, by rw [hdet, div_self hGd]; simp⟩
  exact frame_of_congr G R hR e B _ hRe

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse

open GlobalTheory.CompanionTheory.WeilSiegel.NoFrame GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Hasse in

theorem GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.exists_obstruction : ∀ (D : D7) (r : ℕ) (V : HSp D), 2 * r < V.rank → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (¬ ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → ∃ (ρ : D.what₂.Tau) (ε : ℝ) (S : Submodule ℂ (Fin r → ℂ)), (ε = 1 ∨ ε = -1) ∧ GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.NonnegOn ε (β.1.map (tauE D ρ)) S ∧ ∀ T : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.PosOn ε (gramAt D V ρ) T → Module.finrank ℂ T < Module.finrank ℂ S := by
  intro D r V h2r t β hNF hno
  by_contra hcon
  push_neg at hcon
  obtain ⟨ht, hz, hdet⟩ := hNF
  apply hno
  have hstar : ∀ x : D.host.E, D.sp.cm.sig x = star x := fun _ => rfl
  have hβ : ∀ i j, star (β.1 j i) = β.1 i j := fun i j => by
    have := congrFun (congrFun β.2 i) j
    simpa [hstar] using this
  set B : Matrix (Fin t) (Fin t) D.host.E := β.1.submatrix (Fin.castLE ht.le) (Fin.castLE ht.le) with hBdef
  have hBh : Bᴴ = B := Matrix.ext fun i j => hβ _ _
  have hGh : V.gramᴴ = V.gram := Matrix.ext fun a b => V.herm.eq _ _
  have hGd : V.gram.det ≠ 0 := GlobalTheory.FrameComplement.gram_det_ne V
  have hplace : ∀ ρ : D.what₂.Tau, ∃ p₁ q₁ p q : ℕ, Formalism.UG.HasSignature (B.map (tauE D ρ)) p₁ q₁ ∧
      Formalism.UG.HasSignature (V.gram.map (tauE D ρ)) p q ∧ p₁ + (r - t) ≤ p ∧ q₁ + (r - t) ≤ q := by
    intro ρ
    have hτ : ∀ x, tauE D ρ (star x) = starRingEnd ℂ (tauE D ρ x) := fun x => D.sp.cm.cmUnram.2.1 _ x
    obtain ⟨p₁, q₁, hB⟩ := Formalism.UG.P.signature_exists _ (B.map (tauE D ρ))
      (map_isHerm B hBh _ hτ) (map_isUnit_det B hdet _)
    obtain ⟨p, q, hG⟩ := Formalism.UG.P.signature_exists _ (V.gram.map (tauE D ρ))
      (map_isHerm _ hGh _ hτ) (map_isUnit_det _ hGd _)
    obtain ⟨h1, h2⟩ := sig_bound ht (β.1.map (tauE D ρ)) (fun i j h => by simp [hz i j h])
      (V.gram.map (tauE D ρ)) (p₁ := p₁) (q₁ := q₁) hB hG (fun ε S hε hS => by
        obtain ⟨T, hT, hle⟩ := hcon ρ ε S hε hS
        exact ⟨T, hT, hle⟩)
    exact ⟨p₁, q₁, p, q, hB, hG, h1, h2⟩
  obtain ⟨x, hx1, hx2⟩ := exists_frame_of_sig D.sp.cm (k := r - t) V.gram B hGh hBh hGd hdet (by omega)
    (fun τ => by
      obtain ⟨ρ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D τ
      · exact hplace ρ
      · obtain ⟨p₁, q₁, p, q, h1, h2, h3, h4⟩ := hplace ρ
        refine ⟨p₁, q₁, p, q, ?_, ?_, h3, h4⟩
        · have := hasSignature_map_conj h1
          rwa [Matrix.map_map] at this
        · have := hasSignature_map_conj h2
          rwa [Matrix.map_map] at this)
  have htk : t + (r - t) = r := by omega
  let f : Fin t ⊕ Fin (r - t) ≃ Fin r := finSumFinEquiv.trans (finCongr htk)
  refine ⟨x.submatrix id f.symm, ?_, ?_⟩
  · have := Matrix.rank_submatrix x (Equiv.refl _) f.symm
    rw [hx1, htk] at this
    exact this
  · have e1 : gramQ V (x.submatrix id f.symm) = (x.submatrix id f.symm)ᴴ * V.gram * x.submatrix id f.symm := by
      unfold gramQ
      rw [Matrix.mul_assoc]
      rfl
    rw [e1, gram_submatrix, hx2]
    exact block_submatrix ht β.1 hz htk
