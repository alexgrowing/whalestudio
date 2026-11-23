import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagMultiHomog

section Kernel

theorem ker_map_le_span {F E : Type} [Field F] [Field E] (τ : F →+* E) {t N1 n : ℕ}
    (M : Matrix (Fin t) (Fin N1) F) (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B)
    (hK : Submodule.span F (Set.range B) = LinearMap.ker M.mulVecLin) :
    LinearMap.ker (M.map τ).mulVecLin ≤ Submodule.span E (Set.range (B.map τ)) := by
  let _ : Algebra F E := τ.toAlgebra
  have : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 τ.injective
  have hBE : LinearIndependent E (B.map τ) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := E) (v := B)).2 hB
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F M.col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hliE : LinearIndependent E ((M.map τ).col ∘ a) :=
    (linearIndependent_algebraMap_comp_iff (R := F) (S := E) (v := M.col ∘ a)).2 hli
  have hr : Module.finrank F (LinearMap.range M.mulVecLin) ≤
      Module.finrank E (LinearMap.range (M.map τ).mulVecLin) := by
    rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, ← hsp, finrank_span_eq_card hli,
      ← finrank_span_eq_card hliE]
    exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range _ _))
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker (M.map τ).mulVecLin
  rw [← hK, finrank_span_eq_card hB, Module.finrank_fin_fun] at h1
  rw [Module.finrank_fin_fun] at h2
  have hle : Submodule.span E (Set.range (B.map τ)) ≤ LinearMap.ker (M.map τ).mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have h0 : B a ∈ LinearMap.ker M.mulVecLin := hK ▸ Submodule.subset_span ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h0
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    show Matrix.mulVec (M.map τ) (τ ∘ B a) i = 0
    rw [← RingHom.map_mulVec, h0, Pi.zero_apply, map_zero]
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).ge
  rw [finrank_span_eq_card hBE]
  simp only [Fintype.card_fin] at h1 ⊢
  omega

end Kernel

section Scale

variable {L : Type} [DecidableEq L] {κ : L → Type} {R : Type} [CommRing R]

def scaleHom (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) : MvPolynomial (Σ b, κ b) ℤ →+* MvPolynomial L R :=
  eval₂Hom (Int.castRingHom _) fun q => C (φ (X q)) * X q.1

omit [DecidableEq L] in

theorem eval_one_scaleHom (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) (f : MvPolynomial (Σ b, κ b) ℤ) :
    eval (fun _ => 1) (scaleHom (L := L) φ f) = φ f := by
  have h : (eval fun _ : L => (1 : R)).comp (scaleHom φ) = φ :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun q => by simp [scaleHom]
  exact RingHom.congr_fun h f

theorem scaleHom_component (φ : MvPolynomial (Σ b, κ b) ℤ →+* R) (b : L → ℕ)
    (f : MvPolynomial (Σ b, κ b) ℤ) :
    scaleHom φ (weightedHomogeneousComponent (NumbersDVR.blockWeight κ) b f) =
      weightedHomogeneousComponent (fun c : L => (Pi.single c 1 : L → ℕ)) b (scaleHom φ f) := by
  set ω : L → L → ℕ := fun c => Pi.single c 1
  have he : ∀ q : Σ b, κ b, IsWeightedHomogeneous ω (C (φ (X q)) * X q.1 : MvPolynomial L R)
      (NumbersDVR.blockWeight κ q) := fun q => by
    have := (isWeightedHomogeneous_C ω (φ (X q))).mul (isWeightedHomogeneous_X R ω q.1)
    rwa [zero_add] at this
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    have hmon : IsWeightedHomogeneous ω (scaleHom φ (monomial d c))
        (Finsupp.weight (NumbersDVR.blockWeight κ) d) := by
      rw [scaleHom, coe_eval₂Hom, eval₂_monomial, Finsupp.weight_apply, eq_intCast,
        ← map_intCast (C : R →+* MvPolynomial L R)]
      have := (isWeightedHomogeneous_C ω (c : R)).mul (IsWeightedHomogeneous.prod d.support
        (fun q => (C (φ (X q)) * X q.1 : MvPolynomial L R) ^ d q)
        (fun q => d q • NumbersDVR.blockWeight κ q) (fun q _ => (he q).pow (d q)))
      rw [zero_add] at this
      exact this
    by_cases hdm : Finsupp.weight (NumbersDVR.blockWeight κ) d = b
    · have hmon' : IsWeightedHomogeneous ω (scaleHom φ (monomial d c)) b := hdm ▸ hmon
      rw [(isWeightedHomogeneous_monomial _ d c hdm).weightedHomogeneousComponent_same,
        hmon'.weightedHomogeneousComponent_same]
    · rw [(isWeightedHomogeneous_monomial (NumbersDVR.blockWeight κ) d c
        (m := Finsupp.weight (NumbersDVR.blockWeight κ) d) rfl).weightedHomogeneousComponent_ne b
        (Ne.symm hdm), hmon.weightedHomogeneousComponent_ne b (Ne.symm hdm), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

end Scale

section Flag

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}

abbrev TRing (P : Ideal (MRing ι)) (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) (FnField P)

abbrev LRing (P : Ideal (MRing ι)) (n : ℕ) : Type := MvPolynomial (K ⊕ Fin (n - 1)) (TRing P n)

abbrev OmegaF (P : Ideal (MRing ι)) (n : ℕ) : Type := FractionRing (LRing P n)

def iota (P : Ideal (MRing ι)) (n : ℕ) : FnField P →+* OmegaF P n :=
  (algebraMap (LRing P n) (OmegaF P n)).comp (C.comp C)

def lam (P : Ideal (MRing ι)) (n : ℕ) (b : K ⊕ Fin (n - 1)) : OmegaF P n :=
  algebraMap (LRing P n) (OmegaF P n) (X b)

theorem lam_ne_zero (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (b : K ⊕ Fin (n - 1)) : lam P n b ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (LRing P n) (OmegaF P n))).2 (X_ne_zero b)

def zScale (P : Ideal (MRing ι)) (n : ℕ) : MRing ι →+* LRing P n :=
  eval₂Hom (Int.castRingHom (LRing P n)) fun p => C (C (genPt P p)) * X (Sum.inl p.1)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem eval₂_genPt (P : Ideal (MRing ι)) {S : Type} [CommRing S] (φ : FnField P →+* S) (f : MRing ι) :
    eval₂ (Int.castRingHom S) (fun p => φ (genPt P p)) f =
      φ (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P f)) := by
  have h : eval₂Hom (Int.castRingHom S) (fun p => φ (genPt P p)) =
      φ.comp ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp [genPt]
  exact RingHom.congr_fun h f

omit [DecidableEq K] in

theorem ker_zScale (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsMultiHomogIdeal P) (n : ℕ) :
    RingHom.ker (zScale P n) = P := by
  refine le_antisymm (fun f hf => ?_) ?_
  · have h1 : (eval fun _ => (1 : TRing P n)).comp (zScale P n) =
        C.comp ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp [zScale, genPt]
    have h2 := RingHom.congr_fun h1 f
    rw [RingHom.comp_apply, RingHom.mem_ker.1 hf, map_zero] at h2
    rw [← ker_algebraMap_comp_mk P, RingHom.mem_ker]
    exact C_injective _ _ (h2.symm.trans C_0.symm)
  · obtain ⟨S, hS, hSP⟩ := hP
    refine hSP.le.trans (Ideal.span_le.2 fun s hs => ?_)
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ P := by rw [hSP]; exact Ideal.subset_span hs
    rw [SetLike.mem_coe, RingHom.mem_ker, zScale, coe_eval₂Hom]
    have h3 := HeightsSet.CurveComplexPoint.eval₂_smul_homog s a ha
      (fun k => (X (Sum.inl k) : LRing P n)) (fun p => ((C : TRing P n →+* LRing P n).comp C) (genPt P p))
    have h4 := eval₂_genPt (S := LRing P n) P ((C : TRing P n →+* LRing P n).comp C) s
    simp only [RingHom.comp_apply] at h3 h4
    rw [show (fun p : Σ k, ι k => (C (C (genPt P p)) * X (Sum.inl p.1) : LRing P n)) =
        fun p => X (Sum.inl p.1) * C (C (genPt P p)) from funext fun _ => mul_comm _ _, h3, h4,
      Ideal.Quotient.eq_zero_iff_mem.2 hsP, map_zero, map_zero, map_zero, mul_zero]

omit [DecidableEq K] in

theorem exists_sigma (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsMultiHomogIdeal P) (n : ℕ) :
    ∃ σ : FnField P →+* OmegaF P n, ∀ p : Σ k, ι k,
      σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1) := by
  have hker := ker_zScale P hP n
  let g : MRing ι ⧸ P →+* LRing P n := Ideal.Quotient.lift P (zScale P n) fun f hf => by
    rw [← RingHom.mem_ker, hker]; exact hf
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker, RingHom.mem_ker]
    simpa [g] using ha
  have hg' : Function.Injective ((algebraMap (LRing P n) (OmegaF P n)).comp g) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective (LRing P n) (OmegaF P n)).comp hg
  refine ⟨IsFractionRing.lift hg', fun p => ?_⟩
  rw [genPt, IsFractionRing.lift_algebraMap]
  simp [g, zScale, iota, lam, genPt]

omit [DecidableEq K] in

theorem sigma_evalAt (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    σ (evalAt (genPt P) f) = (∏ k, lam P n (Sum.inl k) ^ a k) * iota P n (evalAt (genPt P) f) := by
  have key : ∀ φ : FnField P →+* OmegaF P n,
      φ (evalAt (genPt P) f) = eval₂ (Int.castRingHom _) (fun p => φ (genPt P p)) f := by
    intro φ
    rw [evalAt, eval_map, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [key σ, key (iota P n)]
  simp only [hσ]
  rw [show (fun p : Σ k, ι k => iota P n (genPt P p) * lam P n (Sum.inl p.1)) =
      fun p => lam P n (Sum.inl p.1) * iota P n (genPt P p) from funext fun _ => mul_comm _ _]
  exact HeightsSet.CurveComplexPoint.eval₂_smul_homog f a hf (fun k => lam P n (Sum.inl k))
    (fun p => iota P n (genPt P p))

omit [DecidableEq K] in

theorem exists_h (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B)
    (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1)) :
    ∃ h : Matrix (Fin n) (Fin n) (OmegaF P n), h * B.map σ = B.map (iota P n) := by
  set M : Matrix (Fin t) (Fin N1) (FnField P) := Matrix.of fun a j => evalAt (genPt P) (c a j)
  have hmem : ∀ a, (B.map (iota P n)) a ∈ Submodule.span (OmegaF P n) (Set.range (B.map σ)) := by
    intro a
    apply ker_map_le_span σ M B hB.1 hB.2
    have h0 : B a ∈ LinearMap.ker M.mulVecLin := hB.2 ▸ Submodule.subset_span ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h0
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext i
    have h1 := congrFun h0 i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, M, Matrix.of_apply, Pi.zero_apply] at h1 ⊢
    simp only [sigma_evalAt P n σ hσ (hc _ _), mul_assoc, ← Finset.mul_sum, ← map_mul, ← map_sum, h1,
      map_zero, mul_zero]
  choose h hh using fun a => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem a)
  refine ⟨Matrix.of h, ?_⟩
  ext a j
  rw [Matrix.mul_apply, ← hh a]
  simp [Finset.sum_apply]

end Flag

section Minor

theorem map_flagMinor {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n N1 : ℕ}
    (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    φ (flagMinor M j T) = flagMinor (M.map φ) j T :=
  RingHom.map_det φ _

theorem flagMinor_diagonal_mul {R : Type} [CommRing R] {n N1 : ℕ} (d : Fin n → R)
    (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    flagMinor (Matrix.diagonal d * M) j T =
      (∏ a : Fin (j.1 + 1), d ⟨a.1, by have := j.2; omega⟩) * flagMinor M j T := by
  unfold flagMinor
  rw [show (Matrix.diagonal d * M).submatrix (Fin.castLE (by have := j.2; omega)) (T.1.orderEmbOfFin T.2) =
      Matrix.diagonal (fun a : Fin (j.1 + 1) => d ⟨a.1, by have := j.2; omega⟩) *
        M.submatrix (Fin.castLE (by have := j.2; omega)) (T.1.orderEmbOfFin T.2) from by
    ext a b; simp [Matrix.diagonal_mul]; rfl, Matrix.det_mul, Matrix.det_diagonal]

theorem minor_scale {R S : Type} [CommRing R] [CommRing S] {n N1 : ℕ} (θ j0 : R →+* S)
    (G : Matrix (Fin n) (Fin n) R) (Bc : Matrix (Fin n) (Fin N1) R) (d : Fin n → S)
    (h : Matrix (Fin n) (Fin n) S) (Bs : Matrix (Fin n) (Fin N1) S)
    (hG : G.map θ = Matrix.diagonal d * G.map j0 * h) (hBs : Bc.map θ = Bs) (hh : h * Bs = Bc.map j0)
    (j : Fin (n - 1)) (T : PluckerBlocks N1 n j) :
    θ (flagMinor (G * Bc) j T) =
      (∏ a : Fin (j.1 + 1), d ⟨a.1, by have := j.2; omega⟩) * j0 (flagMinor (G * Bc) j T) := by
  rw [map_flagMinor, map_flagMinor, Matrix.map_mul, Matrix.map_mul, hG, hBs,
    Matrix.mul_assoc (Matrix.diagonal d * G.map j0), hh, Matrix.mul_assoc, flagMinor_diagonal_mul]

end Minor

section Flag2

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}

def lamN (P : Ideal (MRing ι)) (n : ℕ) (i : ℕ) : OmegaF P n :=
  if h : i + 1 < n then lam P n (Sum.inr ⟨i, by omega⟩) else 1

theorem lamN_ne_zero (P : Ideal (MRing ι)) [P.IsPrime] (n i : ℕ) : lamN P n i ≠ 0 := by
  unfold lamN
  split_ifs
  exacts [lam_ne_zero P n _, one_ne_zero]

def diagE (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (i : ℕ) : OmegaF P n :=
  lamN P n i / (if i = 0 then 1 else lamN P n (i - 1))

theorem prod_diagE (P : Ideal (MRing ι)) [P.IsPrime] (n m : ℕ) :
    ∏ i ∈ Finset.range (m + 1), diagE P n i = lamN P n m := by
  induction m with
  | zero => simp [diagE]
  | succ m ih =>
    have := lamN_ne_zero P n m
    rw [Finset.prod_range_succ, ih, diagE, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]
    field_simp

theorem exists_theta (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsMultiHomogIdeal P)
    (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B) :
    ∃ θ : TRing P n →+* OmegaF P n, θ.comp (flagMap P B) =
      (algebraMap (LRing P n) (OmegaF P n)).comp (scaleHom (flagMap P B)) := by
  obtain ⟨σ, hσ⟩ := exists_sigma P hP n
  obtain ⟨h, hh⟩ := exists_h P c m B hc hB σ hσ
  let TΩ : Matrix (Fin n) (Fin n) (OmegaF P n) :=
    (genMat (FnField P) n).map ((algebraMap (LRing P n) (OmegaF P n)).comp C)
  let D : Matrix (Fin n) (Fin n) (OmegaF P n) := Matrix.diagonal fun a => diagE P n a.1
  let θ : TRing P n →+* OmegaF P n := eval₂Hom σ fun ab => (D * TΩ * h) ab.1 ab.2
  refine ⟨θ, MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) ?_⟩
  rintro ⟨k | j, i⟩
  · simp [θ, flagMap, scaleHom, hσ, iota, lam]
  · have e1 : (genMat (FnField P) n).map θ = D * TΩ * h := by
      ext a b
      simp [θ, genMat]
    have e2 : (B.map C).map θ = B.map σ := by
      ext a b
      simp [θ]
    have e3 : (B.map C).map ((algebraMap (LRing P n) (OmegaF P n)).comp C) = B.map (iota P n) := by
      ext a b
      simp [iota]
    have e4 : ∏ a : Fin (j.1 + 1), diagE P n a.1 = lam P n (Sum.inr j) := by
      rw [Fin.prod_univ_eq_prod_range (fun i => diagE P n i), prod_diagE, lamN, dif_pos (by omega)]
    simp only [RingHom.comp_apply, scaleHom, coe_eval₂Hom, eval₂_X, map_mul, flagMap]
    refine (minor_scale θ ((algebraMap (LRing P n) (OmegaF P n)).comp C) (genMat (FnField P) n) (B.map C)
      (fun a => diagE P n a.1) h (B.map σ) e1 e2 (hh.trans e3.symm) j i).trans ?_
    rw [mul_comm]
    congr 1

theorem component_mem (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι)
    (m : K → ℕ) (B : Matrix (Fin n) (Fin N1) (FnField P)) (hP : IsMultiHomogIdeal P)
    (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B) (f : MRing (FlagBundleBlocks ι N1 n))
    (hf : f ∈ flagIdeal P B) (b : K ⊕ Fin (n - 1) → ℕ) :
    weightedHomogeneousComponent (NumbersDVR.blockWeight (FlagBundleBlocks ι N1 n)) b f ∈ flagIdeal P B := by
  obtain ⟨θ, hθ⟩ := exists_theta P c m B hP hc hB
  have h0 : scaleHom (L := K ⊕ Fin (n - 1)) (flagMap P B) f = 0 := by
    apply IsFractionRing.injective (LRing P n) (OmegaF P n)
    rw [map_zero, ← RingHom.comp_apply, ← hθ, RingHom.comp_apply, RingHom.mem_ker.1 hf, map_zero]
  rw [flagIdeal, RingHom.mem_ker, ← eval_one_scaleHom (L := K ⊕ Fin (n - 1)) (flagMap P B),
    scaleHom_component, h0, map_zero, map_zero]

end Flag2

theorem proof : Statement := by
  intro K _ ι _ N1 t n P c m B hp hP hc hB
  classical
  have := hp
  exact (NumbersDVR.Objects.isMultiHomogIdeal_iff (flagIdeal P B)).1 fun f hf b =>
    component_mem P c m B hP hc hB f hf b

end FlagMultiHomog

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
