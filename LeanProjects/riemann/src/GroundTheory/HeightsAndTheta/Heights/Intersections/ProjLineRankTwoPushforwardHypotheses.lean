import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Pull

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

def pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) (A : HermLine ι) :
    HermLine ι' where
  a := pullDeg κ A.a
  h z := A.h fun p => z (v p)
  pos z hz := A.pos _ fun k => by
    obtain ⟨i', hi'⟩ := hz (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, by rw [hp]; exact hi'⟩
  smul c z hc := by
    show A.h (fun p => c (v p).1 * z (v p)) = (∏ k', ‖c k'‖ ^ pullDeg κ A.a k') * A.h (fun p => z (v p))
    have e1 : (fun p => c (v p).1 * z (v p)) = fun p : Σ k, ι k => (fun k => c (κ k)) p.1 * z (v p) := by
      funext p
      rw [hv.2.2.1 p]
    rw [e1, A.smul _ _ fun k => hc (κ k)]
    congr 1
    refine Fintype.prod_of_injective κ hv.1 _ _ (fun k' hk' => ?_) (fun k => ?_)
    · rw [pullDeg, Function.extend_apply' _ _ _ (by simpa using hk')]
      simp
    · rw [pullDeg, hv.1.extend_apply]

omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem isPullHerm_pullHerm {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (A : HermLine ι) : IsPullHerm κ v A (pullHerm hv A) :=
  ⟨rfl, fun _ => rfl⟩

end Pull

section Bundles

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev FnField (P : Ideal (MRing ι)) : Type := FractionRing (MRing ι ⧸ P)

def genPt (P : Ideal (MRing ι)) : (Σ k, ι k) → FnField P :=
  fun p => algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (X p))

def evalAt {F : Type} [CommRing F] (x : (Σ k, ι k) → F) (f : MRing ι) : F :=
  eval x (map (Int.castRingHom F) f)

def IsPtOver {F : Type} [CommRing F] (P : Ideal (MRing ι)) (x : (Σ k, ι k) → F) : Prop :=
  (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, evalAt x f = 0

def IsQuotRows (P : Ideal (MRing ι)) {t N1 : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ) (n : ℕ) :
    Prop :=
  (∀ a j, IsMultiHomog (c a j) m) ∧
    ∀ (F : Type) [Field F] (x : (Σ k, ι k) → F), IsPtOver P x →
      (Matrix.of fun a j => evalAt x (c a j)).rank + n = N1

def IsKerBasis (P : Ideal (MRing ι)) {t N1 n : ℕ} (c : Fin t → Fin N1 → MRing ι)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) : Prop :=
  LinearIndependent (FnField P) B ∧
    Submodule.span (FnField P) (Set.range B) =
      LinearMap.ker (Matrix.mulVecLin (Matrix.of fun a j => evalAt (genPt P) (c a j)))

abbrev PBlk (ι : K → Type) (N1 : ℕ) : K ⊕ Unit → Type := Sum.elim ι fun _ => Fin N1

def projBundleMap (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    MRing (PBlk ι N1) →+* MvPolynomial (Fin n) (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ a, C (B a j) * X a

def projBundleIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    Ideal (MRing (PBlk ι N1)) :=
  RingHom.ker (projBundleMap P B)

abbrev PluckerBlocks (N1 n : ℕ) : Fin (n - 1) → Type := fun j => {S : Finset (Fin N1) // S.card = j + 1}

abbrev FlagBundleBlocks (ι : K → Type) (N1 n : ℕ) : K ⊕ Fin (n - 1) → Type := Sum.elim ι (PluckerBlocks N1 n)

def flagMinor {R : Type} [CommRing R] {n N1 : ℕ} (M : Matrix (Fin n) (Fin N1) R) (j : Fin (n - 1))
    (S : PluckerBlocks N1 n j) : R :=
  (M.submatrix (Fin.castLE (by have := j.2; omega)) (S.1.orderEmbOfFin S.2)).det

def genMat (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun a b => X (a, b)

def flagMap (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    MRing (FlagBundleBlocks ι N1 n) →+* MvPolynomial (Fin n × Fin n) (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr j, S⟩ => flagMinor (genMat (FnField P) n * B.map C) j S

def flagIdeal (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    Ideal (MRing (FlagBundleBlocks ι N1 n)) :=
  RingHom.ker (flagMap P B)

def flagIdealQ (n : ℕ) : Ideal (MRingOver ℚ (PluckerBlocks n n)) :=
  RingHom.ker (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat ℚ n) q.1 q.2) :
    MRingOver ℚ (PluckerBlocks n n) →ₐ[ℚ] MvPolynomial (Fin n × Fin n) ℚ)

def flagDim (n : ℕ) : ℕ := n * (n - 1) / 2

def chartProd (i : ∀ k, ι k) : MRing ι := ∏ k, X ⟨k, i k⟩

def IsSecOf (P : Ideal (MRing ι)) (a : K → ℤ) (f : FnField P) : Prop :=
  ∀ i : ∀ k, ι k, (∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) →
    ∃ (N : ℕ) (h : MRing ι) (α : K → ℕ), IsMultiHomog h α ∧ (∀ k, (α k : ℤ) = a k + N) ∧
      f * algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (chartProd i)) ^ N =
        algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P h)

def secGroup (P : Ideal (MRing ι)) (a : K → ℤ) : AddSubgroup (FnField P) :=
  AddSubgroup.closure {f | IsSecOf P a f}

def quotCard (P : Ideal (MRing ι)) (a : K → ℤ) (s : MRing ι) : ℕ :=
  Nat.card (secGroup P a ⧸ ((secGroup P 0).map (AddMonoidHom.mulLeft
    (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P s)))).addSubgroupOf (secGroup P a))

def orbitOf (z : (Σ k, ι k) → ℂ) : Set ((Σ k, ι k) → ℂ) :=
  {z' | ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = fun p => c p.1 * z p}

def cPts (P : Ideal (MRing ι)) : Set (Set ((Σ k, ι k) → ℂ)) :=
  {O | ∃ z ∈ mcPts P, O = orbitOf z}

def sumPts (P : Ideal (MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∑ᶠ O ∈ cPts P, g (Classical.epsilon (· ∈ O))

end Bundles

def PushforwardProjectivePoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (I' : Family ι') (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')),
    IsFamily I' → IsBlockMap κ v →
    ∀ (P' : Ideal (MRing ι')) (d' : ℕ) (P : Ideal (MRing ι)) (d : ℕ),
      IsArithVar P' d' → IsArithVar P d → P ≤ imageZ v P' →
      ringKrullDim (MRing ι ⧸ imageZ v P') < ((d' + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ∀ (L : Fin d' → HermLine ι) (L' : Fin d' → HermLine ι'),
        AllSmooth L → (∀ j, IsPullHerm κ v (L j) (L' j)) → I' P' d' L' = 0

def PushforwardArithIntersection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (I : Family ι) (I' : Family ι') (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')),
    IsFamily I → IsFamily I' → IsBlockMap κ v →
    ∀ (P' : Ideal (MRing ι')) (P : Ideal (MRing ι)) (d : ℕ),
      IsArithVar P' d → IsArithVar P d → imageZ v P' = P →
      ∀ (G : GenFibre v P') (i : ∀ k : FibreBlock κ, fibreIdx ι' κ k), IsChart (fibreIdeal κ G) i →
      ∀ (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
        AllSmooth L → (∀ j, IsPullHerm κ v (L j) (L' j)) →
        I' P' d L' = (ptDeg (fibreIdeal κ G) i : ℝ) * I P d L

def PushforwardProjLineRankTwo.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t : ℕ)
    (I : Family ι) (I' : Family (PBlk ι N1)), IsFamily I → IsFamily I' →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
      (B : Matrix (Fin 2) (Fin N1) (FnField P)),
      IsArithVar P d → IsQuotRows P c m 2 → IsKerBasis P c B →
      ∀ (L : Fin d → HermLine ι) (L' : Fin d → HermLine (PBlk ι N1)) (N : HermLine (PBlk ι N1)),
        AllSmooth L → (∀ j, IsPullHerm Sum.inl (inlV (ι₂ := fun _ : Unit => Fin N1)) (L j) (L' j)) →
        IsSmoothHerm N →
        I' (projBundleIdeal P B) (d + 1) (Fin.cons (α := fun _ => HermLine (PBlk ι N1)) N L') =
          (N.a (Sum.inr ()) : ℝ) * I P d L

def PushforwardProjLineFlag.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (N1 t n : ℕ)
    (I : Family ι) (I' : Family (FlagBundleBlocks ι N1 n)), IsFamily I → IsFamily I' →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
      (B : Matrix (Fin n) (Fin N1) (FnField P)),
      IsArithVar P d → IsQuotRows P c m n → IsKerBasis P c B →
      ∀ (L : Fin d → HermLine ι) (L' : Fin d → HermLine (FlagBundleBlocks ι N1 n))
        (N : Fin (flagDim n) → HermLine (FlagBundleBlocks ι N1 n)),
        AllSmooth L → (∀ j, IsPullHerm Sum.inl (inlV (ι₂ := PluckerBlocks N1 n)) (L j) (L' j)) →
        AllSmooth N →
        ∀ J : IFamily ℚ (PluckerBlocks n n), IsFieldIntersection J →
          I' (flagIdeal P B) (flagDim n + d) (Fin.append N L') =
            (J (flagIdealQ n) (flagDim n) (fun i j => (N i).a (Sum.inr j)) : ℝ) * I P d L

def SpecIntHeightFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Family ι) (P : Ideal (MRing ι))
    (A : HermLine ι) (s : MRing ι), IsArithVar P 1 → IsSmoothHerm A → IsSec P A s →
    rhsR I P ![] A s = Real.log (quotCard P A.a s) - sumPts P (logNorm A s)

section Inhabitants

abbrev ProjLineSquareBlocks : Fin 2 → Type := fun _ => Fin 2

theorem isArithVar_bot_sq : IsArithVar (⊥ : Ideal (MRing ProjLineSquareBlocks)) 3 := by
  refine ⟨⟨0⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [Nat.card_eq_fintype_card]
    rfl

theorem imageZ_blkV_bot : imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks)) = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ (isBlockMap_blkV (Fin 2) 0).2.1)

theorem projPoint_pushforward_hypotheses :
    IsBlockMap (blkOf 0) (blkV (Fin 2) 0) ∧ IsArithVar (⊥ : Ideal (MRing ProjLineSquareBlocks)) 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    (⊥ : Ideal (MRing (GlobalTheory 2))) ≤ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks)) ∧
    ringKrullDim (MRing (GlobalTheory 2) ⧸ imageZ (blkV (Fin 2) 0) (⊥ : Ideal (MRing ProjLineSquareBlocks))) <
      ((3 + Fintype.card Unit : ℕ) : WithBot ℕ∞) ∧
    AllSmooth (fun _ : Fin 3 => fsO1 2) ∧
    ∀ _ : Fin 3, IsPullHerm (blkOf 0) (blkV (Fin 2) 0) (fsO1 2)
      (pullHerm (isBlockMap_blkV (Fin 2) 0) (fsO1 2)) := by
  refine ⟨isBlockMap_blkV (Fin 2) 0, isArithVar_bot_sq, isArithVar_bot 1, bot_le, ?_,
    fun _ => isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _⟩
  rw [imageZ_blkV_bot, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  simp [Nat.card_eq_fintype_card]
  decide

theorem aeval_algebraMap_X {Φ : Type} [Field Φ] [Algebra (MRing (GlobalTheory 2)) Φ] (f : MRing (GlobalTheory 2)) :
    aeval (R := ℤ) (fun p => algebraMap (MRing (GlobalTheory 2)) Φ (X p)) f = algebraMap (MRing (GlobalTheory 2)) Φ f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, eq_intCast (algebraMap ℤ Φ) a]
    exact (eq_intCast ((algebraMap (MRing (GlobalTheory 2)) Φ).comp C) a).symm
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p n hp => rw [map_mul, map_mul, hp, aeval_X]

theorem imageZ_id_bot : imageZ (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id ⊥ = ⊥ :=
  Ideal.comap_bot_of_injective _ (rename_injective _ Function.injective_id)

def genFibreId : GenFibre (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id ⊥ where
  Φ := FractionRing (MRing (GlobalTheory 2))
  Φ' := FractionRing (MRing (GlobalTheory 2))
  x p := algebraMap (MRing (GlobalTheory 2)) (FractionRing (MRing (GlobalTheory 2))) (X p)
  x' p := algebraMap (MRing (GlobalTheory 2)) (FractionRing (MRing (GlobalTheory 2))) (X p)
  ker_x := by
    rw [imageZ_id_bot]
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing (GlobalTheory 2)) (FractionRing (MRing (GlobalTheory 2))))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X f
  gen c := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := MRing (GlobalTheory 2)) c
    refine ⟨a, b, ?_, ?_⟩
    · convert IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (K := FractionRing (MRing (GlobalTheory 2))) hb using 2
      exact aeval_algebraMap_X b
    · exact (congrArg₂ (· / ·) (aeval_algebraMap_X a) (aeval_algebraMap_X b)).symm
  genericFibre_ker_target := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_bot]
    convert map_eq_zero_iff (algebraMap (MRing (GlobalTheory 2)) (FractionRing (MRing (GlobalTheory 2))))
      (IsFractionRing.injective _ _) using 2
    exact aeval_algebraMap_X f
  compat _ := rfl

def chartId : ∀ k : FibreBlock (id : Unit → Unit), fibreIdx (GlobalTheory 2) id k := fun k => (k.2 ⟨k.1, rfl⟩).elim

theorem pfAI3_hyps :
    IsBlockMap (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id id ∧ IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧
    imageZ (ι := GlobalTheory 2) (ι' := GlobalTheory 2) id ⊥ = ⊥ ∧ IsChart (fibreIdeal id genFibreId) chartId ∧
    AllSmooth ![fsO1 2, fsO1 2] ∧
    ∀ j, IsPullHerm id id (![fsO1 2, fsO1 2] j) (pullHerm isBlockMap_id (![fsO1 2, fsO1 2] j)) :=
  ⟨isBlockMap_id, isArithVar_bot 1, imageZ_id_bot, fun k => (k.2 ⟨k.1, rfl⟩).elim,
    fun j => by fin_cases j <;> exact isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _⟩

def noRows (n : ℕ) : Fin 0 → Fin n → MRing (GlobalTheory 2) := fun a => a.elim0

def idRows (n : ℕ) : Matrix (Fin n) (Fin n) (FnField (⊥ : Ideal (MRing (GlobalTheory 2)))) :=
  ⇑(Pi.basisFun (FnField (⊥ : Ideal (MRing (GlobalTheory 2)))) (Fin n))

theorem isQuotRows_noRows (n : ℕ) : IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows n) 0 n := by
  refine ⟨fun a => a.elim0, fun F _ x _ => ?_⟩
  rw [Subsingleton.elim (Matrix.of fun a j => evalAt x (noRows n a j)) 0, Matrix.rank_zero, zero_add]

theorem isKerBasis_idRows (n : ℕ) : IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows n) (idRows n) := by
  refine ⟨(Pi.basisFun _ _).linearIndependent, ?_⟩
  rw [idRows, (Pi.basisFun _ _).span_eq]
  symm
  rw [LinearMap.ker_eq_top]
  exact LinearMap.ext fun _ => Subsingleton.elim _ _

def fibreFubiniStudyO1 : HermLine (PBlk (GlobalTheory 2) 2) := HermLine.sqMetric (Sum.elim (fun _ => 0) fun _ => 1)

theorem projLineRankTwo_pushforward_hypotheses :
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧ IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 2) 0 2 ∧
    IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 2) (idRows 2) ∧ AllSmooth ![fsO1 2, fsO1 2] ∧
    (∀ j, IsPullHerm Sum.inl (inlV (ι := GlobalTheory 2) (ι₂ := fun _ : Unit => Fin 2)) (![fsO1 2, fsO1 2] j)
      (pullHerm isBlockMap_inl (![fsO1 2, fsO1 2] j))) ∧
    IsSmoothHerm fibreFubiniStudyO1 ∧ fibreFubiniStudyO1.a (Sum.inr ()) = 1 :=
  ⟨isArithVar_bot 1, isQuotRows_noRows 2, isKerBasis_idRows 2,
    fun j => by fin_cases j <;> exact isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _,
    isSmoothHerm_sqMetric _, rfl⟩

def pluckerFubiniStudyO1 : HermLine (FlagBundleBlocks (GlobalTheory 2) 3 3) := HermLine.sqMetric (Sum.elim (fun _ => 0) fun _ => 1)

theorem projLineFlag_pushforward_hypotheses :
    flagDim 3 = 3 ∧
    IsArithVar (⊥ : Ideal (MRing (GlobalTheory 2))) 2 ∧ IsQuotRows (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) 0 3 ∧
    IsKerBasis (⊥ : Ideal (MRing (GlobalTheory 2))) (noRows 3) (idRows 3) ∧ AllSmooth ![fsO1 2, fsO1 2] ∧
    (∀ j, IsPullHerm Sum.inl (inlV (ι := GlobalTheory 2) (ι₂ := PluckerBlocks 3 3)) (![fsO1 2, fsO1 2] j)
      (pullHerm isBlockMap_inl (![fsO1 2, fsO1 2] j))) ∧
    AllSmooth (fun _ : Fin (flagDim 3) => pluckerFubiniStudyO1) :=
  ⟨rfl, isArithVar_bot 1, isQuotRows_noRows 3, isKerBasis_idRows 3,
    fun j => by fin_cases j <;> exact isSmoothHerm_fubiniStudyO1 2, fun _ => isPullHerm_pullHerm _ _,
    fun _ => isSmoothHerm_sqMetric _⟩

theorem specIntHeightFormula_hypotheses : IsArithVar (⊥ : Ideal (MRing (GlobalTheory 1))) 1 ∧ IsSmoothHerm (fsO1 1) ∧
    IsSec (⊥ : Ideal (MRing (GlobalTheory 1))) (fsO1 1) (Xb 1 0) :=
  specInt_hypotheses_hold

theorem isSecOf_X : IsSecOf (⊥ : Ideal (MRing (GlobalTheory 1))) (fun _ => 1) (genPt ⊥ ⟨(), 0⟩) := fun _ _ =>
  ⟨0, Xb 1 0, fun _ => 1, isMultiHomog_Xb 1 0, fun _ => by simp, by simp [genPt]⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
