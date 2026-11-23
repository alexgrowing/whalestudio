import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace AddBlockDimension

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
  (D : AddBlockData P)

abbrev plusMap : MvPolynomial (Coord D.extSizes) ℤ →+* MvPolynomial (Option ι) P.FunField := D.extMap

def oldMap : MvPolynomial (Coord n) ℤ →+* MvPolynomial (Option ι) P.FunField :=
  (plusMap D).comp (D.liftOld : MvPolynomial (Coord n) ℤ →+* MvPolynomial (Coord D.extSizes) ℤ)

theorem ker_plusMap : RingHom.ker (plusMap D) = D.extIdeal := rfl

theorem plusMap_X_old (v : Coord n) :
    plusMap D (X (D.oldCoord v)) = C (P.mkF (X v)) * X (some v.1) := by
  simp [plusMap, AddBlockData.extMap, AddBlockData.oldCoord, AddBlockData.extVal]

theorem plusMap_X_new (j : Fin (D.size + 1)) :
    plusMap D (X (D.newCoord j)) = C (D.elt j) * X none := by
  simp [plusMap, AddBlockData.extMap, AddBlockData.newCoord, AddBlockData.extVal]

theorem oldMap_X (v : Coord n) : oldMap D (X v) = plusMap D (X (D.oldCoord v)) := by
  simp [oldMap, AddBlockData.liftOld]

theorem oldMap_of_homog {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    oldMap D f = (∏ k, (X (some k) : MvPolynomial (Option ι) P.FunField) ^ δ k) * C (P.mkF f) := by
  have h1 : oldMap D = eval₂Hom (Int.castRingHom _)
      (fun v : Coord n ↦ (X (some v.1) : MvPolynomial (Option ι) P.FunField) * C (P.mkF (X v))) := by
    refine MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ ?_)
    rw [oldMap_X, plusMap_X_old, eval₂Hom_X', mul_comm]
  have h2 : (C : P.FunField →+* MvPolynomial (Option ι) P.FunField).comp P.mkF =
      eval₂Hom (Int.castRingHom _)
        (fun v : Coord n ↦ (C (P.mkF (X v)) : MvPolynomial (Option ι) P.FunField)) :=
    MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ by simp)
  rw [h1, coe_eval₂Hom]
  refine (eval₂_scale_of_isWeightedHomogeneous (fun k ↦ (X (some k) : MvPolynomial (Option ι) P.FunField))
    (fun v ↦ C (P.mkF (X v))) hf).trans ?_
  congr 1
  exact (congrArg (fun φ : MvPolynomial (Coord n) ℤ →+* _ ↦ φ f) h2).symm

theorem ker_oldMap : RingHom.ker (oldMap D) = P.ideal := by
  ext f
  rw [RingHom.mem_ker]
  constructor
  · intro hf

    let ev : MvPolynomial (Option ι) P.FunField →+* P.FunField :=
      (aeval (R := P.FunField) fun _ : Option ι ↦ (1 : P.FunField)).toRingHom
    have hev : ev.comp (oldMap D) = P.mkF :=
      MvPolynomial.ringHom_ext (fun m ↦ by simp) (fun v ↦ by
        simp [ev, oldMap_X, plusMap_X_old])
    have := congrArg (fun φ : MvPolynomial (Coord n) ℤ →+* P.FunField ↦ φ f) hev
    simp only [RingHom.comp_apply, hf, map_zero] at this
    exact (P.mkF_eq_zero_iff f).mp this.symm
  · intro hf
    rw [← sum_weightedHomogeneousComponent (coordDeg n) f,
      map_finsum _ (weightedHomogeneousComponent_finsupp f)]
    refine finsum_eq_zero_of_forall_eq_zero fun m ↦ ?_
    rw [oldMap_of_homog D (weightedHomogeneousComponent_isWeightedHomogeneous m f),
      (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, mul_zero]

theorem isAlgebraic_new [CharZero P.FunField] {j : Fin (D.size + 1)} (hj : D.elt j ≠ 0)
    (i : Fin (D.size + 1)) :
    IsAlgebraic (Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
      (Set.range fun v ↦ oldMap D (X v)))) (plusMap D (X (D.newCoord i))) := by
  set S := Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
      (Set.range fun v ↦ oldMap D (X v)))
  obtain ⟨fi, gi, δfi, δgi, hfi, hgi, hdi, hgiP, hxi⟩ := D.elt_deg i
  obtain ⟨fj, gj, δfj, δgj, hfj, hgj, hdj, hgjP, hxj⟩ := D.elt_deg j
  have hgi0 : P.mkF gi ≠ 0 := fun h ↦ hgiP ((P.mkF_eq_zero_iff gi).mp h)
  have hgj0 : P.mkF gj ≠ 0 := fun h ↦ hgjP ((P.mkF_eq_zero_iff gj).mp h)
  have hfj0 : P.mkF fj ≠ 0 := fun h ↦ hj (by rw [hxj, h, zero_div])
  have hδ : δgi + δfj = δfi + δgj := by
    funext k
    have h1 := hdi k
    have h2 := hdj k
    simp only [Pi.add_apply]
    omega
  have hH2 := oldMap_of_homog D (hgi.mul hfj)
  have hH1 := oldMap_of_homog D (hfi.mul hgj)
  rw [← hδ] at hH1
  set T := ∏ k, (X (some k) : MvPolynomial (Option ι) P.FunField) ^ (δgi + δfj) k
  have hT : T ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (X_ne_zero _)
  have key : P.mkF gi * P.mkF fj * D.elt i = P.mkF fi * P.mkF gj * D.elt j := by
    rw [hxi, hxj]
    field_simp
  have hrel : oldMap D (gi * fj) * plusMap D (X (D.newCoord i)) =
      oldMap D (fi * gj) * plusMap D (X (D.newCoord j)) := by
    rw [hH2, hH1, plusMap_X_new, plusMap_X_new]
    have e1 : T * C (P.mkF (gi * fj)) * (C (D.elt i) * X none) =
        T * C (P.mkF gi * P.mkF fj * D.elt i) * X none := by
      simp only [map_mul]
      ring
    have e2 : T * C (P.mkF (fi * gj)) * (C (D.elt j) * X none) =
        T * C (P.mkF fi * P.mkF gj * D.elt j) * X none := by
      simp only [map_mul]
      ring
    rw [e1, e2, key]
  have hmemY : ∀ g, oldMap D g ∈ S := fun g ↦
    Algebra.adjoin_mono (Set.subset_insert _ _) (TrdegAdjoin.map_mem_adjoin (oldMap D) g)
  have hmemE : plusMap D (X (D.newCoord j)) ∈ S := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hne : oldMap D (gi * fj) ≠ 0 := by
    rw [hH2, map_mul]
    refine mul_ne_zero hT ?_
    rw [Ne, MvPolynomial.C_eq_zero]
    exact mul_ne_zero hgi0 hfj0
  refine IsAlgebraic.of_mul (y := oldMap D (gi * fj)) (mem_nonZeroDivisors_of_ne_zero hne)
    (isAlgebraic_algebraMap (⟨_, hmemY _⟩ : S)) ?_
  rw [hrel]
  exact isAlgebraic_algebraMap (⟨_, mul_mem (hmemY _) hmemE⟩ : S)

end AddBlockDimension

open AddBlockDimension in

theorem ExtensionDimension.proof : ExtensionDimension.Statement := by
  intro ι _ _ n P D
  have : CharZero P.FunField :=
    charZero_of_injective_ringHom (IsFractionRing.injective P.CoordRing P.FunField)
  obtain ⟨s₀, htr₀, hdim₀⟩ := TrdegAdjoin.ringKrullDim_quotient_ker (oldMap D)
  obtain ⟨s₁, htr₁, hdim₁⟩ := TrdegAdjoin.ringKrullDim_quotient_ker (plusMap D)
  rw [ker_oldMap] at hdim₀
  rw [ker_plusMap] at hdim₁

  obtain ⟨j, hj⟩ : ∃ j, D.elt j ≠ 0 := by
    obtain ⟨c, hc⟩ := P.exists_chart
    obtain ⟨u, -, hu⟩ := D.generating c hc
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    simp [h] at hu
  have hYZ : (Set.range fun v ↦ oldMap D (X v)) ⊆ Set.range fun w ↦ plusMap D (X w) := by
    rintro _ ⟨v, rfl⟩
    exact ⟨D.oldCoord v, (oldMap_X D v).symm⟩
  have hC : ∀ r ∈ Algebra.adjoin ℚ (Set.range fun v ↦ oldMap D (X v)), ∃ a, r = rename some a :=
    fun r hr ↦ TrdegAdjoin.exists_rename_of_mem_adjoin (by
      rintro _ ⟨v, rfl⟩
      refine ⟨C (P.mkF (X v)) * X v.1, ?_⟩
      show oldMap D (X v) = _
      rw [oldMap_X, plusMap_X_old, map_mul, rename_C, rename_X]) hr
  have he : Transcendental (Algebra.adjoin ℚ (Set.range fun v ↦ oldMap D (X v)))
      (plusMap D (X (D.newCoord j))) := by
    rw [plusMap_X_new]
    exact TrdegAdjoin.transcendental_C_mul_X_none _ hC hj
  have halg : ∀ z ∈ Set.range fun w ↦ plusMap D (X w),
      IsAlgebraic (Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
        (Set.range fun v ↦ oldMap D (X v)))) z := by
    rintro _ ⟨⟨_ | k, i⟩, rfl⟩
    · exact isAlgebraic_new D hj i
    · have hmem : plusMap D (X ⟨some k, i⟩) ∈ Algebra.adjoin ℚ (insert (plusMap D (X (D.newCoord j)))
          (Set.range fun v ↦ oldMap D (X v))) :=
        Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨⟨k, i⟩, oldMap_X D _⟩)
      exact isAlgebraic_algebraMap (⟨_, hmem⟩ : Algebra.adjoin ℚ _)
  have htr := TrdegAdjoin.trdeg_adjoin_eq_add_one hYZ ⟨D.newCoord j, rfl⟩ he halg htr₀
  rw [htr₁] at htr
  have hs : s₁ = s₀ + 1 := by exact_mod_cast htr
  rw [hdim₁]
  change _ = ringKrullDim (MvPolynomial (Coord n) ℤ ⧸ P.ideal) + 1
  rw [hdim₀, hs]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
