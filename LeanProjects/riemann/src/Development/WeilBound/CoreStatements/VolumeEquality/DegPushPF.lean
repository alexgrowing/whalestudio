import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPFc
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum pointConeMap)
open GlobalTheory.CompanionTheory.Ar

namespace PF

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

theorem pointIdeal_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] (y : (Σ b, ι b) → Ω) :
    pointIdeal ℚ y = (mCoordIdeal y).map (map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

def cst (ι : K → Type) [∀ b, Fintype (ι b)] : HermLine ι := HermLine.ofWeight (fun _ => 1) fun _ _ _ => rfl

theorem cst_smooth : IsSmoothHerm (cst ι) := contDiffOn_const

theorem ii_cst (hI : PB.Inputs) {II : IntersectionSystem} (hII : IsIntersectionSystem II) {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {y : (Σ b, ι b) → Ω} {e : ℕ} (ha : IsArithVar (mCoordIdeal y) (e + 1)) (a : Fin e → K → ℤ) :
    II K ι (mCoordIdeal y) (e + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun j => fsHerm ι (a j)) (cst ι)) = -inum ℚ y a := by
  classical
  have hs : ∀ j, IsSmoothHerm (fsHerm ι (a j)) := fun j => FsInvPow.isSmoothHerm_fsHerm _
  have h1 := (hII K ι).2.2 _ e (fun j => fsHerm ι (a j)) (cst ι) 1 (fun _ => 0) ha hs cst_smooth (fun _ => rfl)
    Geo.isMultiHomog_one ((Ideal.ne_top_iff_one _).1 ha.2.1.1.ne_top)
  have h3 : logNorm (cst ι) 1 = fun _ => 1 := by
    funext z
    simp [logNorm, cst, HermLine.ofWeight]
  have h2 := Giv.degreeGeneric_of_degree hI.2.1.2.1 K ι _ e (fun j => fsHerm ι (a j)) ha hs
  refine h1.trans ?_
  rw [recR, Geo.divSupp_one, finsum_mem_empty, zero_sub, arInt, h3, inum, pointIdeal_rat]
  exact congrArg _ h2

theorem ii_cast {II : IntersectionSystem} (hII : IsIntersectionSystem II) {P : Ideal (MRing ι)} {d d' : ℕ} (σ : Fin d ≃ Fin d')
    (hP : IsArithVar P d') (L : Fin d' → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) : II K ι P d (L ∘ σ) = II K ι P d' L := by
  obtain rfl : d = d' := Fin.equiv_iff_eq.1 ⟨σ⟩
  exact (hII K ι).1 P d L σ hP hL

theorem pull_inl (a : K → ℤ) : AI.I1.pullDeg (Sum.inl : K → K ⊕ K') a = Sum.elim a 0 := by
  funext k
  rcases k with k | k
  · exact Sum.inl_injective.extend_apply _ _ k
  · exact Function.extend_apply' _ _ _ (by simp)

theorem pull_fs (a : K → ℤ) : IsPullHerm Sum.inl inlV (fsHerm ι a) (fsHerm (Sum.elim ι ι') (Sum.elim a 0)) := by
  refine ⟨(pull_inl a).symm, fun z => ?_⟩
  simp only [fsHerm_h, refNorm, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply]
  simp
  rfl

theorem pull_cst : IsPullHerm Sum.inl inlV (cst ι) (cst (Sum.elim ι ι')) := by
  refine ⟨?_, fun z => rfl⟩
  show (0 : K ⊕ K' → ℤ) = AI.I1.pullDeg Sum.inl 0
  rw [pull_inl]
  funext k
  rcases k with k | k <;> rfl

def factorAction (n r : ℕ) : Fin (n + 1 + r) ≃ Fin (n + r + 1) where
  toFun j := ⟨if (j : ℕ) < n then j else if (j : ℕ) = n then n + r else j - 1, by have := j.2; split_ifs <;> omega⟩
  invFun j := ⟨if (j : ℕ) < n then j else if (j : ℕ) = n + r then n else j + 1, by have := j.2; split_ifs <;> omega⟩
  left_inv j := by
    have := j.2
    ext
    dsimp only
    split_ifs <;> omega
  right_inv j := by
    have := j.2
    ext
    dsimp only
    split_ifs <;> omega

theorem position_eq {α : Type} {n r : ℕ} (A : Fin n → α) (c : α) (B : Fin r → α) :
    Fin.snoc (α := fun _ => α) (Fin.append A B) c ∘ factorAction n r = Fin.append (Fin.snoc (α := fun _ => α) A c) B := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · have : factorAction n r (Fin.castAdd r (Fin.last n)) = Fin.last _ := by simp [factorAction, Fin.ext_iff]
      simp [this]
    · have : factorAction n r (Fin.castAdd r j.castSucc) = (Fin.castAdd r j).castSucc := by simp [factorAction, Fin.ext_iff]
      simp [this]
  · have : factorAction n r (Fin.natAdd (n + 1) j) = (Fin.natAdd n j).castSucc := by
      have h1 : ¬ n + 1 + j < n := by omega
      have h2 : ¬ n + 1 + j = n := by omega
      simp only [factorAction, Equiv.coe_fn_mk, Fin.val_natAdd, h1, h2, ite_false, Fin.ext_iff, Fin.val_castSucc]
      omega
    rw [Function.comp_apply, this, Fin.snoc_castSucc, Fin.append_right, Fin.append_right]

end PF

open PF in
theorem geoPF : PtDim → GeoPF := by
  intro _ hI II hII Ω₁ _ _ Ω _ _ _ K _ ι _ K' _ ι' _ y y' n r a N hb ha hy'
  classical
  have hne := ne_of_arith ha
  have hP := isPt_join hb ha hy'
  refine ⟨hP, ?_⟩
  have : Nonempty K := ha.1
  have hA := arith_of_isPt hP
  obtain ⟨G, hG⟩ := exists_genFibre y' hb hne
  have hsm : ∀ {m : ℕ} {α : Type} [Fintype α] {κ : α → Type} [∀ b, Fintype (κ b)] (b : Fin m → α → ℤ) (j : Fin (m + 1)),
      IsSmoothHerm (Fin.snoc (α := fun _ => HermLine κ) (fun j => fsHerm κ (b j)) (cst κ) j) := by
    intro m α _ κ _ b j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa using cst_smooth
    · simpa using FsInvPow.isSmoothHerm_fsHerm _
  have h := hI.2.2.2.1.1 II hII.1 K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl inlV _ (n + 1) r G (fun V _ L => intNum G.Φ V L)
    (Fin.snoc (α := fun _ => HermLine ι) (fun j => fsHerm ι (a j)) (cst ι))
    (Fin.snoc (α := fun _ => HermLine (Sum.elim ι ι')) (fun j => fsHerm (Sum.elim ι ι') (Sum.elim (a j) 0)) (cst _))
    (fun j => fsHerm (Sum.elim ι ι') (Sum.elim 0 (N j))) isBlockMap_inl (by rwa [Nat.add_right_comm])
    (by rwa [image_join]) (NumbersDVR.IntNumIsFieldIntersection.full _ _ _) (hsm a)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using pull_cst
      · simpa using pull_fs _)
    fun j => FsInvPow.isSmoothHerm_fsHerm _
  rw [image_join, ii_cst hI hII.1 ha, ← position_eq] at h
  have e : (Fin.append (fun j => fsHerm (Sum.elim ι ι') (Sum.elim (a j) 0)) fun j => fsHerm (Sum.elim ι ι') (Sum.elim 0 (N j))) =
      fun j => fsHerm (Sum.elim ι ι')
        (Fin.append (fun j => Sum.elim (a j) (0 : K' → ℤ)) (fun j => Sum.elim (0 : K → ℤ) (N j)) j) := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  rw [e, ii_cast hII.1 _ hA _ (hsm _), ii_cst hI hII.1 hA] at h
  have h' := hG r N
  rw [mul_neg, neg_inj] at h
  rw [num, num, finrank_join y' hb hne, mul_assoc, ← h']
  congr 1
  exact_mod_cast h

end SheetDecomposition
