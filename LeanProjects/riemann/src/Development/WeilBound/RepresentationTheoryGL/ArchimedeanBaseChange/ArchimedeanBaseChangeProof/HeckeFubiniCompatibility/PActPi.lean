import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.Rg.BcB.CG

section Split

variable {ι : Type} [DecidableEq ι] {X : Type}

def splitY (w : ι) (t : X) (z : {v // v ≠ w} → X) : ι → X := fun v => if h : v = w then t else z ⟨v, h⟩

theorem splitY_self (w : ι) (t : X) (z : {v // v ≠ w} → X) : splitY w t z w = t := dif_pos rfl

theorem splitY_ne (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) : splitY w t z v = z v := by
  simp [splitY, v.2]

theorem update_splitY_self (w : ι) (t t' : X) (z : {v // v ≠ w} → X) :
    Function.update (splitY w t z) w t' = splitY w t' z := by
  funext v
  simp only [Function.update_apply, splitY]
  by_cases h : v = w
  · rw [if_pos h, dif_pos h]
  · rw [if_neg h]; simp [h]

theorem update_splitY_ne (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) (s : X) :
    Function.update (splitY w t z) v s = splitY w t (Function.update z v s) := by
  funext x
  simp only [Function.update_apply, splitY]
  by_cases h : x = w
  · have h' : x ≠ (v : ι) := fun e => v.2 (e ▸ h)
    rw [if_neg h', dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    by_cases h' : x = v
    · have : (⟨x, h⟩ : {v // v ≠ w}) = v := Subtype.ext h'
      rw [if_pos h', if_pos this]
    · have : (⟨x, h⟩ : {v // v ≠ w}) ≠ v := fun e => h' (congrArg Subtype.val e)
      rw [if_neg h', if_neg this]

theorem splitY_one [One X] (w : ι) : splitY w (1 : X) (1 : {v // v ≠ w} → X) = 1 := by
  funext v
  by_cases h : v = w <;> simp [splitY, h]

theorem continuous_splitY_left [TopologicalSpace X] (w : ι) (z : {v // v ≠ w} → X) :
    Continuous fun t : X => splitY w t z :=
  continuous_pi fun v => by
    by_cases h : v = w
    · simp only [splitY, dif_pos h]; exact continuous_id
    · simp only [splitY, dif_neg h]; exact continuous_const

theorem continuous_splitY_right [TopologicalSpace X] (w : ι) (t : X) :
    Continuous fun z : {v // v ≠ w} → X => splitY w t z :=
  continuous_pi fun v => by
    by_cases h : v = w
    · simp only [splitY, dif_pos h]; exact continuous_const
    · simp only [splitY, dif_neg h]; exact continuous_apply _

variable {Idx : ι → Type}

theorem psa_apply (w : ι) (J : ∀ v, Idx v) : Equiv.piSplitAt w Idx J = (J w, fun v : {v // v ≠ w} => J v) := rfl

theorem psa_symm_self (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    (Equiv.piSplitAt w Idx).symm (j, J') w = j :=
  congrArg Prod.fst ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))

theorem psa_symm_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) :
    (Equiv.piSplitAt w Idx).symm (j, J') v = J' v :=
  congrFun (congrArg Prod.snd ((Equiv.piSplitAt w Idx).apply_symm_apply (j, J'))) v

theorem psa_symm_apply_self (w : ι) (J : ∀ v, Idx v) : (Equiv.piSplitAt w Idx).symm (J w, fun v : {v // v ≠ w} => J v) = J :=
  (Equiv.piSplitAt w Idx).symm_apply_apply J

theorem update_psa_self (w : ι) (j j' : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) w j' = (Equiv.piSplitAt w Idx).symm (j', J') := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · exact Function.update_self _ _ _
  · funext v
    show Function.update _ w j' (v : ι) = J' v
    rw [Function.update_of_ne v.2, psa_symm_ne]

theorem update_psa_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) (x : Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) (v : ι) x =
      (Equiv.piSplitAt w Idx).symm (j, Function.update J' v x) := by
  apply (Equiv.piSplitAt w Idx).injective
  rw [Equiv.apply_symm_apply, psa_apply]
  refine Prod.ext ?_ ?_
  · show Function.update _ (v : ι) x w = j
    rw [Function.update_of_ne (Ne.symm v.2), psa_symm_self]
  · funext v'
    show Function.update _ (v : ι) x (v' : ι) = Function.update J' v x v'
    by_cases h : v' = v
    · subst h; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne (fun e => h (Subtype.ext e)), Function.update_of_ne h, psa_symm_ne]

def splitM [MeasurableSpace X] (w : ι) : (ι → X) ≃ᵐ X × ({v // v ≠ w} → X) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (· = w)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique fun _ : {v // v = w} => X) (MeasurableEquiv.refl _))

theorem splitM_apply [MeasurableSpace X] (w : ι) (y : ι → X) : splitM w y = (y w, fun v : {v // v ≠ w} => y v) := rfl

theorem splitM_symm [MeasurableSpace X] (w : ι) (t : X) (z : {v // v ≠ w} → X) :
    (splitM w).symm (t, z) = splitY w t z := by
  rw [MeasurableEquiv.symm_apply_eq, splitM_apply]
  refine Prod.ext (splitY_self w t z).symm ?_
  funext v
  exact (splitY_ne w t z v).symm

theorem splitM_mp [MeasurableSpace X] [Fintype ι] (μ : Measure X) [SigmaFinite μ] (w : ι) :
    MeasurePreserving (splitM w) (Measure.pi fun _ : ι => μ) (μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
  ((@measurePreserving_piUnique {v // v = w} (Subtype.fintype _) (fun _ => X) _ _ (fun _ => μ)).prod (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (· = w))

end Split

section Iter

variable {X : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem pi_cont_supp {ι : Type} [Fintype ι] [DecidableEq ι] {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Continuous (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ∧
      HasCompactSupport (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) := by
  refine ⟨continuous_finsetSum _ fun J _ => Continuous.mul ?_ (hu J), ?_⟩
  · exact continuous_finsetProd (f := fun v (y : ι → X) => e v (y v) (I v) (J v)) _
      fun v _ => (he v (I v) (J v)).1.comp (continuous_apply v)
  let K : ι → Set X := fun v => ⋃ a, ⋃ b, tsupport (fun t => e v t a b)
  have hK : ∀ v, IsCompact (K v) := fun v => isCompact_iUnion fun a => isCompact_iUnion fun b => (he v a b).2
  refine HasCompactSupport.intro (isCompact_univ_pi hK) fun y hy => ?_
  rw [Set.mem_univ_pi] at hy
  push_neg at hy
  obtain ⟨v, hv⟩ := hy
  refine Finset.sum_eq_zero fun J _ => ?_
  have h0 : e v (y v) (I v) (J v) = 0 := image_eq_zero_of_notMem_tsupport (f := fun t => e v t (I v) (J v)) fun h =>
    hv (Set.mem_iUnion.2 ⟨I v, Set.mem_iUnion.2 ⟨J v, h⟩⟩)
  rw [Finset.prod_eq_zero (Finset.mem_univ v) h0, zero_mul]

theorem pi_integrable (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    {Idx : ι → Type} [∀ v, Fintype (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J)) :
    Integrable (fun y : ι → X => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) (Measure.pi fun _ => μ) :=
  (pi_cont_supp e u I he hu).1.integrable_of_hasCompactSupport (pi_cont_supp e u I he hu).2

variable [One X]

theorem pi_iterated_integral_continuous (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
      (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v),
      Fintype.card ι = n →
      (∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b)) → (∀ J, Continuous (u J)) →
      (∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
        val v * u J (Function.update y v 1)) →
      ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 := by
  induction n with
  | zero =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hn
    rw [Measure.pi_of_empty (fun _ : ι => μ) (1 : ι → X), integral_dirac, Fintype.sum_unique,
      Subsingleton.elim (default : ∀ v, Idx v) I]
    simp
  | succ n ih =>
    intro ι _ _ Idx _ _ e val u I hn he hu hloc
    obtain ⟨w⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    have hn' : Fintype.card {v // v ≠ w} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
    have hmp := splitM_mp μ w
    have hF := pi_integrable μ e u I he hu

    have hsplit : ∀ (t : X) (z : {v // v ≠ w} → X),
        (∑ J, (∏ v, e v (splitY w t z v) (I v) (J v)) * u J (splitY w t z)) =
          ∑ j, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) := by
      intro t z
      rw [← Fintype.sum_equiv (Equiv.piSplitAt w Idx).symm
        (fun p => (∏ v, e v (splitY w t z v) (I v) ((Equiv.piSplitAt w Idx).symm p v)) *
          u ((Equiv.piSplitAt w Idx).symm p) (splitY w t z)) _ (fun _ => rfl), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J' _ => ?_
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ w, splitY_self, psa_symm_self]
      simp only [splitY_ne, psa_symm_ne]
      ring
    have hint : ∀ (z : {v // v ≠ w} → X) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v),
        Integrable (fun t => e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) μ :=
      fun z j J' => ((he w (I w) j).1.mul ((hu _).comp (continuous_splitY_left w z))).integrable_of_hasCompactSupport
        (HasCompactSupport.mul_right (he w (I w) j).2)
    let u' : (∀ v : {v // v ≠ w}, Idx v) → ({v // v ≠ w} → X) → ℂ :=
      fun J' z => val w * u ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
    have hinner : ∀ z : {v // v ≠ w} → X,
        ∫ t, (∑ J, (∏ v, e v ((splitM w).symm (t, z) v) (I v) (J v)) * u J ((splitM w).symm (t, z))) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z := by
      intro z
      simp only [splitM_symm, hsplit]
      rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun J' _ => (hint z j J').const_mul _]
      have hj : ∀ j : Idx w, ∫ t, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            (e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z)) ∂μ =
          ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) *
            ∫ t, e w t (I w) j * u ((Equiv.piSplitAt w Idx).symm (j, J')) (splitY w t z) ∂μ := fun j => by
        rw [integral_finset_sum _ fun J' _ => (hint z j J').const_mul _]
        simp only [integral_const_mul]
      rw [Finset.sum_congr rfl fun j _ => hj j]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J' _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      have h1 := hloc w ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_self] at h1
      simp only [update_psa_self, update_splitY_self] at h1
      exact h1
    have he' : ∀ (v : {v // v ≠ w}) a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b) :=
      fun v => he v
    have hu' : ∀ J', Continuous (u' J') :=
      fun J' => continuous_const.mul ((hu _).comp (continuous_splitY_right w 1))
    have hloc' : ∀ (v : {v // v ≠ w}) (J' : ∀ v : {v // v ≠ w}, Idx v) (z : {v // v ≠ w} → X),
        ∑ j, ∫ t, e v t (J' v) j * u' (Function.update J' v j) (Function.update z v t) ∂μ =
          val v * u' J' (Function.update z v 1) := by
      intro v J' z
      have h1 := hloc v ((Equiv.piSplitAt w Idx).symm (I w, J')) (splitY w 1 z)
      rw [psa_symm_ne] at h1
      simp only [update_psa_ne, update_splitY_ne] at h1
      simp only [u']
      calc _ = val w * ∑ j, ∫ t, e v t (J' v) j *
              u ((Equiv.piSplitAt w Idx).symm (I w, Function.update J' v j)) (splitY w 1 (Function.update z v t)) ∂μ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← integral_const_mul]
            congr 1
            funext t
            ring
        _ = _ := by rw [h1]; ring
    have hIH := ih {v // v ≠ w} (fun v => Idx v) (fun v => e v) (fun v => val v) u' (fun v => I v) hn' he' hu' hloc'
    calc ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ)
        = ∫ q, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm q)
            ∂(μ.prod (Measure.pi fun _ : {v // v ≠ w} => μ)) :=
          ((MeasurePreserving.symm _ hmp).integral_comp' _).symm
      _ = ∫ z, ∫ t, (fun y => ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y) ((splitM w).symm (t, z)) ∂μ
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_prod_symm _ (((MeasurePreserving.symm _ hmp).integrable_comp_emb
            (splitM w).symm.measurableEmbedding).2 hF)
      _ = ∫ z, ∑ J' : (∀ v : {v // v ≠ w}, Idx v), (∏ v : {v // v ≠ w}, e v (z v) (I v) (J' v)) * u' J' z
            ∂(Measure.pi fun _ : {v // v ≠ w} => μ) :=
          integral_congr_ae (ae_of_all _ hinner)
      _ = (∏ v : {v // v ≠ w}, val v) * u' (fun v => I v) 1 := hIH
      _ = (∏ v, val v) * u I 1 := by
          simp only [u', psa_symm_apply_self, splitY_one]
          rw [Fintype.prod_eq_mul_prod_subtype_ne _ w]
          ring

theorem pi_iter (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Idx : ι → Type) [∀ v, Fintype (Idx v)] [∀ v, DecidableEq (Idx v)]
    (e : ∀ v, X → Idx v → Idx v → ℂ) (val : ι → ℂ) (u : (∀ v, Idx v) → (ι → X) → ℂ) (I : ∀ v, Idx v)
    (he : ∀ v a b, Continuous (fun t => e v t a b) ∧ HasCompactSupport (fun t => e v t a b))
    (hu : ∀ J, Continuous (u J))
    (hloc : ∀ v J y, ∑ j, ∫ t, e v t (J v) j * u (Function.update J v j) (Function.update y v t) ∂μ =
      val v * u J (Function.update y v 1)) :
    ∫ y, ∑ J, (∏ v, e v (y v) (I v) (J v)) * u J y ∂(Measure.pi fun _ => μ) = (∏ v, val v) * u I 1 :=
  pi_iterated_integral_continuous μ _ ι Idx e val u I rfl he hu hloc

end Iter

end PositivityTheory.Rg.BcB.CG

end
