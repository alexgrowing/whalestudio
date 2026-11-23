import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings

theorem det_mul_cols {R : Type} [CommRing R] {N d : ℕ} (M : Matrix (Fin d) (Fin N) R)
    (B : Matrix (Fin N) (Fin N) R) (C : Finset (Fin N)) (hC : C.card = d) :
    (M * B.submatrix id (C.orderEmbOfFin hC)).det =
      ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C := by
  rw [GroundTheory.PAdicHodge.det_mul_eq_sum_minors]
  have h1 : ∑ I : Finset (Fin N), (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) *
        minorIJ B I C =
      ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin N) => I.card = d),
        (if e : I.card = d then (M.submatrix id (I.orderEmbOfFin e)).det else 0) * minorIJ B I C := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun s _ hs => ?_
    have hc : s.card ≠ d := fun hc => hs (by simp [hc])
    rw [dif_neg hc, zero_mul]
  rw [h1, Finset.sum_subtype (Finset.univ.filter fun I : Finset (Fin N) => I.card = d)
    (p := fun s : Finset (Fin N) => s.card = d) (fun s => by simp)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dif_pos s.2, MinorCalc.minorIJ_eq_det B s.1 C d s.2 hC]
  rfl

variable {Ψ : Type} {p q : ℕ}

theorem blockEquiv_symm_omEmb (a : Fin q) : (blockEquiv p q).symm (omEmb p q a) = Sum.inl a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, omEmb]

theorem blockEquiv_symm_wEmb (a : Fin p) : (blockEquiv p q).symm (wEmb p q a) = Sum.inr a := by
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp [blockEquiv, wEmb]
  omega

theorem blocks_wEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin p) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (wEmb p q a) (wEmb p q b) =
      Y a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_wEmb, blockEquiv_symm_wEmb, Matrix.fromBlocks_apply₂₂]

theorem blocks_omEmb {R : Type} [Zero R] (X : Matrix (Fin q) (Fin q) R) (Y : Matrix (Fin p) (Fin p) R) (a b : Fin q) :
    (Matrix.fromBlocks X 0 0 Y).submatrix (blockEquiv p q).symm (blockEquiv p q).symm (omEmb p q a) (omEmb p q b) =
      X a b := by
  rw [Matrix.submatrix_apply, blockEquiv_symm_omEmb, blockEquiv_symm_omEmb, Matrix.fromBlocks_apply₁₁]

theorem gMat_posOf (Ω : Type) [Field Ω] (τ : Ψ) (s : Ψ ⊕ Ψ) (hs : s = .inl τ ∨ s = .inr τ)
    (l l' : Fin (rk Ψ p q s)) :
    gMat p q Ω τ (posOf p q s l) (posOf p q s l') = genU Ω (rk Ψ p q) s l l' := by
  rcases hs with rfl | rfl
  · exact blocks_wEmb _ _ l l'
  · exact blocks_omEmb _ _ l l'

theorem posOf_strictMono (s : Ψ ⊕ Ψ) : StrictMono (posOf p q s) := by
  rcases s with τ | τ
  · exact wEmb_strictMono p q
  · exact omEmb_strictMono p q

theorem sum_aExt_mul {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {L : Type} [Field L] (f : Ω →+* L) (s : Ψ ⊕ Ψ) (j : Fin (n s)) (G : Fin (p + q) → L) :
    ∑ a, f (aExt A s j a) * G a = ∑ l, f (A s j l) * G (posOf p q s l) := by
  simp only [aExt, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single (posOf p q s l)]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem stepOf_fst (r : Ψ × Fin (p + q)) :
    (stepOf Ψ p q r).1 = .inl r.1 ∨ (stepOf Ψ p q r).1 = .inr r.1 := by
  unfold stepOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem mem_stepCols_iff (r : Ψ × Fin (p + q)) (a : Fin (p + q)) :
    a ∈ stepCols (p + q) p r.2 ↔
      ∃ y : Fin (((stepOf Ψ p q r).2 : ℕ) + 1),
        posOf p q (stepOf Ψ p q r).1 (Fin.castLE (stepOf Ψ p q r).2.2 y) = a := by
  have hr := r.2.2
  by_cases h : (r.2 : ℕ) < p
  · have e : stepOf Ψ p q r = ⟨.inl r.1, ⟨r.2, h⟩⟩ := dif_pos h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_pos (by omega)]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨a - q, ?_⟩, Fin.ext ?_⟩
      · show (a : ℕ) - q < (r.2 : ℕ) + 1
        omega
      · show q + ((a : ℕ) - q) = a
        omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) + 1 := y.2
      show p + q - p ≤ q + (y : ℕ) ∧ q + (y : ℕ) < p + q - p + ((r.2 : ℕ) + 1)
      omega
  · have e : stepOf Ψ p q r = ⟨.inr r.1, ⟨r.2 - p, by show _ < q; omega⟩⟩ := dif_neg h
    rw [e]
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [if_neg (by omega)]
    constructor
    · intro h1
      refine ⟨⟨a, ?_⟩, Fin.ext rfl⟩
      show (a : ℕ) < (r.2 : ℕ) - p + 1
      omega
    · rintro ⟨y, rfl⟩
      have hy : (y : ℕ) < (r.2 : ℕ) - p + 1 := y.2
      show (y : ℕ) < (r.2 : ℕ) + 1 - p
      omega

theorem det_fMat_eq {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ} (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω)
    {K₀ : Type} {J₀ : K₀ → Type} (τ : Ψ) (t : StepIx Ψ p q) (hs : t.1 = .inl τ ∨ t.1 = .inr τ)
    (C : Finset (Fin (p + q)))
    (hC : ∀ a, a ∈ C ↔ ∃ y : Fin ((t.2 : ℕ) + 1), posOf p q t.1 (Fin.castLE t.2.2 y) = a)
    (J : Fin ((t.2 : ℕ) + 1) → Fin (n t.1)) :
    ((fMat A t.1).submatrix J (Fin.castLE t.2.2)).det =
      ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q))
        (coefF (K₀ := K₀) (J₀ := J₀) A ⟨.inr t, J⟩ I) * minorIJ (gMat p q Ω τ) I C := by
  have hf : StrictMono fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) :=
    (posOf_strictMono t.1).comp (Fin.strictMono_castLE _)
  have hCe : C = Finset.univ.image fun y : Fin ((t.2 : ℕ) + 1) => posOf p q t.1 (Fin.castLE t.2.2 y) := by
    ext a
    simp [hC]
  have hcard : C.card = (t.2 : ℕ) + 1 := by
    rw [hCe, Finset.card_image_of_injective _ hf.injective]
    simp
  have henum : ∀ y, C.orderEmbOfFin hcard y = posOf p q t.1 (Fin.castLE t.2.2 y) := fun y =>
    congrFun (Finset.orderEmbOfFin_unique hcard (fun x => (hC _).2 ⟨x, rfl⟩) hf).symm y
  have hmat : (fMat A t.1).submatrix J (Fin.castLE t.2.2) =
      ((aExt A t.1).map (algebraMap Ω (GenField Ω (rk Ψ p q)))).submatrix J id *
        (gMat p q Ω τ).submatrix id (C.orderEmbOfFin hcard) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply, id, fMat]
    rw [sum_aExt_mul A _ t.1 (J x) fun a => gMat p q Ω τ a (C.orderEmbOfFin hcard y)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [henum, gMat_posOf Ω τ t.1 hs]
  rw [hmat, det_mul_cols _ _ C hcard]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  by_cases e : I.card = (t.2 : ℕ) + 1
  · rw [dif_pos e]
    simp only [coefF]
    rw [dif_pos e, RingHom.map_det]
    rfl
  · rw [dif_neg e]
    simp [coefF, e]

theorem yv_step : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k, yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) * minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk with hp
  obtain rfl := Option.some.inj hk
  exact det_fMat_eq A r.1 (stepOf Ψ p q r) (stepOf_fst r) _ (mem_stepCols_iff r) i

end GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings
