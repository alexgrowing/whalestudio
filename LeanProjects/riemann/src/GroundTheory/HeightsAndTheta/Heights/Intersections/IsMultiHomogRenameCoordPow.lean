import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace PushforwardArithIntersection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

open Classical in

def blkW : (Σ k, ι k) → K → ℕ := fun p => Pi.single p.1 1

open Classical in

theorem isMultiHomog_of_wh {s : MRing ι} {a : K → ℕ} (h : IsWeightedHomogeneous (blkW (ι := ι)) s a) :
    IsMultiHomog s a := by
  intro m hm k
  rw [← h (mem_support_iff.mp hm), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [blkW]
  · intro b _ hb
    simp [blkW, Ne.symm hb]
  · simp

omit [Fintype K] in
open Classical in

theorem sum_single_eq_extend {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by
  funext k'
  rw [Finset.sum_apply]
  by_cases h : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [hκ.extend_apply, Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hκ.ne hb]
    · simp
  · rw [Function.extend_apply' _ _ _ h]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : k' ≠ κ k := fun e => h ⟨k, e.symm⟩
    simp [hk]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem wh_prod_X_pow {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) :=
  IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℤ _ (q k)).pow (α k)

theorem isMultiHomog_coordPow (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) α := by
  have h := wh_prod_X_pow (ι := ι) (fun k => ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι) ⟨k, i k⟩) = α := by
    funext k
    simp only [blkW, Finset.sum_apply]
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [e] at h
  exact isMultiHomog_of_wh h

omit [∀ k, Fintype (ι k)] in

theorem isMultiHomog_rename_coordPow {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    (i : ∀ k, ι k) (α : K → ℕ) :
    IsMultiHomog (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)) (Function.extend κ α 0) := by
  have h := wh_prod_X_pow (ι := ι') (fun k => v ⟨k, i k⟩) α
  have e : (∑ k, α k • blkW (ι := ι') (v ⟨k, i k⟩)) = Function.extend κ α 0 := by
    simp only [blkW, hv.2.2.1]
    exact sum_single_eq_extend κ hv.1 α
  rw [e] at h
  simp only [map_prod, map_pow, rename_X]
  exact isMultiHomog_of_wh h

omit [∀ k, Fintype (ι k)] in

theorem coordPow_not_mem {V : Ideal (MRing ι)} (hV : V.IsPrime) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ V) (α : K → ℕ) : (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hi k (hV.mem_of_pow_mem _ hk)

theorem isSmoothHerm_pull {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {A : HermLine ι} {A' : HermLine ι'} (hA : IsSmoothHerm A) (h : IsPullHerm κ v A A') :
    IsSmoothHerm A' := by
  have e : A'.h = A.h ∘ fun z' p => z' (v p) := funext h.2
  unfold IsSmoothHerm
  rw [e]
  refine hA.comp (contDiff_pi.2 fun p => contDiff_apply ℝ ℂ (v p)).contDiffOn ?_
  intro z' hz'
  simp only [Set.mem_ofPred_eq] at hz' ⊢
  intro k
  obtain ⟨i', hi'⟩ := hz' (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem genDegAt_zero (h0 : ArithVarZeroStatement) (I : AllFam) : GenDegAt I 0 := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' _ hP'
  exact absurd hP' (h0 K' ι' P')

theorem genDegAt_succ (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement)
    (I : AllFam) (hI : I.IsFamily) (n : ℕ) (ih : GenDegAt I n) : GenDegAt I (n + 1) := by
  intro K _ ι _ K' _ ι' _ κ v P' G J L L' hv hP' hP hJ hL hLL'
  have hrel := hP.2.1.2.2
  choose i hi using hrel
  have hPp : (imageZ v P').IsPrime := hP.2.1.1
  let α : K → ℕ := fun k => ((L (Fin.last n)).a k).toNat
  let β : K → ℕ := fun k => (-(L (Fin.last n)).a k).toNat
  have hfP := coordPow_not_mem hPp i hi α
  have hgP := coordPow_not_mem hPp i hi β
  have hfP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k) ∉ P' := fun h => hfP (Ideal.mem_comap.mpr h)
  have hgP' : rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) ∉ P' := fun h => hgP (Ideal.mem_comap.mpr h)
  have hsec : IsRatSectionOn (imageZ v P') (L (Fin.last n)) (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k)
      (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k) :=
    ⟨α, β, isMultiHomog_coordPow i α, isMultiHomog_coordPow i β, hfP, hgP,
      fun k => Int.toNat_sub_toNat_neg _⟩
  have hsec' : IsRatSectionOn P' (L' (Fin.last n)) (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ α k))
      (rename v (∏ k, (X ⟨k, i k⟩ : MRing ι) ^ β k)) := by
    refine ⟨_, _, isMultiHomog_rename_coordPow hv i α, isMultiHomog_rename_coordPow hv i β, hfP', hgP',
      fun k' => ?_⟩
    rw [(hLL' (Fin.last n)).1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hv.1.extend_apply]
      exact Int.toNat_sub_toNat_neg _
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => isSmoothHerm_pull hv (hL j) (hLL' j)
  have e1 := hRat K' ι' (I K' ι') (hI K' ι') P' n (Fin.init L') (L' (Fin.last n)) _ _ hP'
    (fun j => hL' _) (hL' _) hsec'
  have e2 := hRat K ι (I K ι) (hI K ι) (imageZ v P') n (Fin.init L) (L (Fin.last n)) _ _ hP
    (fun j => hL _) (hL _) hsec
  rw [Fin.snoc_init_self] at e1 e2
  rw [e1, e2, recRRat, recRRat,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ α hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i α) hfP,
    hCyc I hI n ih K ι K' ι' κ v P' G J (Fin.init L) (Fin.init L') _ β hv hP' hP hJ (fun j => hL _)
      (fun j => hLL' _) (isMultiHomog_coordPow i β) hgP,
    hInt K ι K' ι' κ v P' n G J (Fin.init L) (Fin.init L') (L (Fin.last n)) (L' (Fin.last n)) _ _ hv hP' hP
      hJ (fun j => hL _) (fun j => hLL' _) (hL _) (hLL' _) hsec]
  ring

end PushforwardArithIntersection

theorem PushforwardArithIntersection.proof (h0 : ArithVarZeroStatement) (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement)
    (hInt : ArithmeticIntersectionIntegral.Statement) : PushforwardArithIntersection.Statement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement
  intro I hI K _ ι _ K' _ ι' _ κ v P' d G J L L' hv hP' hP hJ hL hLL'
  have key : ∀ n, GenDegAt I n := fun n =>
    Nat.rec (PushforwardArithIntersection.genDegAt_zero h0 I) (fun n ih => PushforwardArithIntersection.genDegAt_succ hRat hCyc hInt I hI n ih) n
  exact key d K ι K' ι' κ v P' G J L L' hv hP' hP hJ hL hLL'

end GroundTheory.Heights₂.Heights.Inter
