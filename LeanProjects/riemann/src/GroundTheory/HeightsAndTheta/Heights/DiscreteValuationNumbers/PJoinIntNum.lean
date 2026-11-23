import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinIntNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)

namespace JoinIntNum

noncomputable section

theorem isWeightedHomogeneous_algHom {R : Type*} [CommRing R] {σ τ M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : τ → N) (L : M →+ N)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ s, IsWeightedHomogeneous w' (φ (X s)) (L (w s)))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (φ f) (L m) := by
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have hw : Finsupp.weight w d = m := hf (mem_support_iff.mp hd)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, map_finsuppProd]
  have h1 : IsWeightedHomogeneous w' (d.prod fun s e => φ (X s ^ e)) (L m) := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    unfold Finsupp.prod
    refine IsWeightedHomogeneous.prod _ _ _ fun s _ => ?_
    show IsWeightedHomogeneous w' (φ (X s ^ d s)) (L (d s • w s))
    rw [map_pow, map_nsmul]
    exact (hφ s).pow _
  exact h1.C_mul _

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

def newVar : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) := ⟨.inr (), (0 : Fin 1)⟩

variable (F) in

def dropPt : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) → MRing ι F
  | ⟨.inl k, i⟩ => X ⟨k, i⟩
  | ⟨.inr _, _⟩ => 1

theorem dropPt_rename (f : MRing ι F) :
    aeval (dropPt F) (rename (liftVar (ι := ι) ptIdx) f) = f := by
  rw [aeval_rename]
  have : (dropPt F ∘ liftVar (ι := ι) ptIdx) = X := by
    funext p
    rfl
  rw [this, aeval_X_left_apply]

theorem mul_pow_mem_map_iff (V : Ideal (MRing ι F)) (f : MRing ι F) (t : ℕ) :
    rename (liftVar (ι := ι) ptIdx) f * X newVar ^ t ∈ V.map (rename (liftVar (ι := ι) ptIdx)) ↔
      f ∈ V := by
  constructor
  · intro h
    have hle : V.map (rename (liftVar (ι := ι) ptIdx)) ≤ V.comap (aeval (dropPt F)) :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => by
        rw [Ideal.mem_comap, Ideal.mem_comap, dropPt_rename]
        exact hx
    have h2 := hle h
    rw [Ideal.mem_comap, map_mul, map_pow, dropPt_rename, aeval_X] at h2
    simpa [newVar, dropPt] using h2
  · intro h
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)

theorem weight_newBlock (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι ptIdx)) d (.inr ()) = d newVar := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  rw [Finset.sum_eq_single newVar]
  · simp [blockWeight, newVar]
  · rintro ⟨k | u, i⟩ _ hne
    · simp [blockWeight]
    · exfalso
      apply hne
      cases u
      obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      rfl
  · intro h
    simp [Finsupp.notMem_support_iff.mp h]

theorem rename_dropPt_monomial (d : (Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) →₀ ℕ) (c : F) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (monomial d c)) * X newVar ^ (d newVar) =
      monomial d c := by
  induction d using Finsupp.induction generalizing c with
  | zero =>
    rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero, mul_one, ← C_apply, aeval_C, algebraMap_eq,
      rename_C]
  | single_add a b f _ _ ih =>
    have hsplit : monomial (Finsupp.single a b + f) c = X a ^ b * monomial f c := by
      rw [X_pow_eq_monomial, monomial_mul, one_mul]
    have key : rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (X a ^ b : MRing (Sum.elim ι ptIdx) F)) *
        X newVar ^ (Finsupp.single a b newVar) = X a ^ b := by
      rcases a with ⟨k | u, i⟩
      · have hne : (⟨.inl k, i⟩ : Σ k : K ⊕ Unit, Sum.elim ι ptIdx k) ≠ newVar := by
          intro h
          exact Sum.inl_ne_inr (congrArg Sigma.fst h)
        rw [Finsupp.single_eq_of_ne hne.symm]
        simp only [map_pow, aeval_X, pow_zero, mul_one]
        show (rename (liftVar (ι := ι) ptIdx) (X ⟨k, i⟩ : MRing ι F)) ^ b = _
        rw [rename_X]
        rfl
      · cases u
        obtain rfl : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
        show _ * X newVar ^ (Finsupp.single newVar b newVar) = X newVar ^ b
        simp [dropPt, newVar]
    rw [hsplit, map_mul, map_mul, Finsupp.add_apply, pow_add]
    calc _ = (rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (X a ^ b : MRing (Sum.elim ι ptIdx) F)) *
          X newVar ^ (Finsupp.single a b newVar)) *
          (rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) (monomial f c)) *
          X newVar ^ (f newVar)) := by ring
      _ = _ := by rw [key, ih]

theorem rename_dropPt_of_homog {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    rename (liftVar (ι := ι) ptIdx) (aeval (dropPt F) g) * X newVar ^ (M (.inr ())) = g := by
  conv_rhs => rw [g.as_sum]
  conv_lhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWeight (Sum.elim ι ptIdx)) d = M := hg (mem_support_iff.mp hd)
  have ht : M (.inr ()) = d newVar := by rw [← hw, weight_newBlock]
  rw [ht, rename_dropPt_monomial]

def extendZero : (K → ℕ) →+ (K ⊕ Unit → ℕ) where
  toFun a := Sum.elim a 0
  map_zero' := by
    funext x
    cases x <;> rfl
  map_add' a b := by
    funext x
    cases x <;> simp

def restrictFirst : (K ⊕ Unit → ℕ) →+ (K → ℕ) where
  toFun a k := a (.inl k)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem rename_homog {f : MRing ι F} {m : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f m) :
    IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx))
      (rename (liftVar (ι := ι) ptIdx) f) (extendZero m) := by
  refine isWeightedHomogeneous_algHom _ _ extendZero _ (fun s => ?_) hf
  rw [rename_X]
  have e : extendZero (blockWeight ι s) = blockWeight (Sum.elim ι ptIdx) (liftVar (ι := ι) ptIdx s) := by
    funext x
    rcases x with k | u
    · simp [extendZero, blockWeight, liftVar, Pi.single_apply]
    · simp [extendZero, blockWeight, liftVar]
  rw [e]
  exact isWeightedHomogeneous_X F _ _

theorem dropPt_homog {g : MRing (Sum.elim ι ptIdx) F} {M : K ⊕ Unit → ℕ}
    (hg : IsWeightedHomogeneous (blockWeight (Sum.elim ι ptIdx)) g M) :
    IsWeightedHomogeneous (blockWeight ι) (aeval (dropPt F) g) (restrictFirst M) := by
  refine isWeightedHomogeneous_algHom _ _ restrictFirst _ (fun s => ?_) hg
  rw [aeval_X]
  rcases s with ⟨k | u, i⟩
  · have e : restrictFirst (blockWeight (Sum.elim ι ptIdx) ⟨.inl k, i⟩) =
        blockWeight ι (⟨k, i⟩ : Σ k, ι k) := by
      funext k'
      simp [restrictFirst, blockWeight, Pi.single_apply]
    rw [e]
    exact isWeightedHomogeneous_X F _ _
  · have e : restrictFirst (blockWeight (Sum.elim ι ptIdx) ⟨.inr u, i⟩) = 0 := by
      funext k'
      simp [restrictFirst, blockWeight]
    rw [e]
    exact isWeightedHomogeneous_one F _

theorem homogSubmodule_eq_map (M : K ⊕ Unit → ℕ) :
    weightedHomogeneousSubmodule F (blockWeight (Sum.elim ι ptIdx)) M =
      (weightedHomogeneousSubmodule F (blockWeight ι) (restrictFirst M)).map
        ((LinearMap.mulRight F (X newVar ^ M (.inr ()))).comp
          (rename (liftVar (ι := ι) ptIdx)).toLinearMap) := by
  ext g
  rw [mem_weightedHomogeneousSubmodule]
  constructor
  · intro hg
    refine ⟨aeval (dropPt F) g, ?_, ?_⟩
    · exact dropPt_homog hg
    · exact rename_dropPt_of_homog hg
  · rintro ⟨f, hf, rfl⟩
    have hf' : IsWeightedHomogeneous (blockWeight ι) f (restrictFirst M) := hf
    have h := (rename_homog hf').mul
      ((isWeightedHomogeneous_X F (blockWeight (Sum.elim ι ptIdx)) newVar).pow (M (.inr ())))
    have e : extendZero (restrictFirst M) +
        M (.inr ()) • blockWeight (Sum.elim ι ptIdx) newVar = M := by
      funext x
      rcases x with k | u
      · simp [extendZero, restrictFirst, blockWeight, newVar]
      · cases u
        simp [extendZero, restrictFirst, blockWeight, newVar]
    rw [e] at h
    exact h

theorem finrank_gradedPiece (V : Ideal (MRing ι F)) (M : K ⊕ Unit → ℕ) :
    Module.finrank F (gradedPiece (V.map (rename (liftVar (ι := ι) ptIdx))) M) =
      Module.finrank F (gradedPiece V (restrictFirst M)) := by
  set ψ := (LinearMap.mulRight F (X newVar ^ M (.inr ()))).comp
    (rename (liftVar (ι := ι) ptIdx)).toLinearMap with hψ
  set H := weightedHomogeneousSubmodule F (blockWeight ι) (restrictFirst M)
  set A := (Ideal.Quotient.mkₐ F (V.map (rename (liftVar (ι := ι) ptIdx)))).toLinearMap ∘ₗ ψ
  set B := (Ideal.Quotient.mkₐ F V).toLinearMap
  have hker : LinearMap.ker A = LinearMap.ker B := by
    ext f
    simp only [LinearMap.mem_ker, A, B, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hψ, LinearMap.mulRight_apply]
    exact mul_pow_mem_map_iff V f _
  have hA : gradedPiece (V.map (rename (liftVar (ι := ι) ptIdx))) M = H.map A := by
    unfold gradedPiece
    rw [homogSubmodule_eq_map, ← Submodule.map_comp]
  have hB : gradedPiece V (restrictFirst M) = H.map B := rfl
  have e : ∀ {N : Type} [AddCommGroup N] [Module F N] (C : MRing ι F →ₗ[F] N),
      H.map C = LinearMap.range (C ∘ₗ H.subtype) := by
    intro N _ _ C
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk2 : LinearMap.ker (A ∘ₗ H.subtype) = LinearMap.ker (B ∘ₗ H.subtype) := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    rw [← LinearMap.mem_ker, hker, LinearMap.mem_ker]
  rw [hA, hB, e, e, ← (LinearMap.quotKerEquivRange _).finrank_eq,
    ← (LinearMap.quotKerEquivRange _).finrank_eq, hk2]

theorem hilbFn_map (V : Ideal (MRing ι F)) (m' : K ⊕ Unit → ℤ) :
    hilbFn (V.map (rename (liftVar (ι := ι) ptIdx))) m' =
      if 0 ≤ m' (.inr ()) then hilbFn V (fun k => m' (.inl k)) else 0 := by
  unfold hilbFn
  by_cases ht : 0 ≤ m' (.inr ())
  · rw [if_pos ht]
    by_cases hk : ∀ k, 0 ≤ m' (.inl k)
    · have hall : ∀ x, 0 ≤ m' x := by
        rintro (k | u)
        · exact hk k
        · cases u
          exact ht
      rw [if_pos hall, if_pos hk, finrank_gradedPiece]
      rfl
    · have hall : ¬ ∀ x, 0 ≤ m' x := fun h => hk fun k => h _
      rw [if_neg hall, if_neg hk]
  · rw [if_neg ht, if_neg (fun h => ht (h _))]

theorem foldr_diffStep_pullDeg (L : List (K → ℤ)) (h : (K → ℤ) → ℤ)
    (h' : (K ⊕ Unit → ℤ) → ℤ)
    (hh : ∀ m', h' m' = if 0 ≤ m' (.inr ()) then h (fun k => m' (.inl k)) else 0)
    (m' : K ⊕ Unit → ℤ) :
    (L.map (pullDeg (K' := Unit))).foldr diffStep h' m' =
      if 0 ≤ m' (.inr ()) then L.foldr diffStep h (fun k => m' (.inl k)) else 0 := by
  induction L generalizing m' with
  | nil => exact hh m'
  | cons b L ih =>
    simp only [List.map_cons, List.foldr_cons, diffStep]
    rw [ih, ih]
    have h1 : (m' - pullDeg (K' := Unit) b) (.inr ()) = m' (.inr ()) := by
      simp [pullDeg, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]
    have h2 : (fun k => (m' - pullDeg (K' := Unit) b) (.inl k)) =
        (fun k => m' (.inl k)) - b := by
      funext k
      simp [pullDeg, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]
    rw [h1, h2]
    split_ifs <;> simp

theorem mixedDiff_map (V : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) (m' : K ⊕ Unit → ℤ) :
    mixedDiff (fun j => pullDeg (K' := Unit) (bs j))
        (hilbFn (V.map (rename (liftVar (ι := ι) ptIdx)))) m' =
      if 0 ≤ m' (.inr ()) then mixedDiff bs (hilbFn V) (fun k => m' (.inl k)) else 0 := by
  unfold mixedDiff
  have hl : List.ofFn (fun j => pullDeg (K' := Unit) (bs j)) =
      (List.ofFn bs).map (pullDeg (K' := Unit)) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  exact foldr_diffStep_pullDeg _ _ _ (hilbFn_map V) m'

end

theorem proof : JoinIntNum.Statement := by
  intro F _ K _ _ ι _ V n bs
  unfold intNum
  rw [funext (mixedDiff_map V bs)]
  set f := mixedDiff bs (hilbFn V)
  by_cases hc : ∃ c, ∀ᶠ m in Filter.atTop, f m = c
  · obtain ⟨c, hc⟩ := hc
    rw [(EventualValueFacts.proof K f c 0).1 hc]
    apply (EventualValueFacts.proof _ _ c 0).1
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc
    refine Filter.eventually_atTop.mpr ⟨Sum.elim N 0, fun m' hm' => ?_⟩
    have ht : 0 ≤ m' (.inr ()) := by simpa using hm' (.inr ())
    rw [if_pos ht]
    exact hN _ (fun k => by simpa using hm' (.inl k))
  · have hc' : ¬ ∃ c, ∀ᶠ m' in Filter.atTop,
        (fun m' : K ⊕ Unit → ℤ => if 0 ≤ m' (.inr ()) then f (fun k => m' (.inl k)) else 0) m' =
          c := by
      rintro ⟨c, hc'⟩
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hc'
      refine hc ⟨c, Filter.eventually_atTop.mpr ⟨fun k => N (.inl k), fun m hm => ?_⟩⟩
      have h := hN (Sum.elim m (fun _ => |N (.inr ())|)) ?_
      · simpa using h
      · rintro (k | u)
        · exact hm k
        · exact le_abs_self _
    rw [eventualValue, eventualValue, dif_neg hc, dif_neg hc']

end JoinIntNum

end GroundTheory.Heights₂.Heights.NumbersDVR
