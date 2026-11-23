import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PExistsForm
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Pull

variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem extend_apply_self {M : Type*} [Zero M] (b : K → M) (k : K) :
    Function.extend j b 0 (j k) = b k :=
  j.injective.extend_apply b 0 k

theorem extend_apply_not {M : Type*} [Zero M] (b : K → M) (k' : K') (h : ¬ ∃ k, j k = k') :
    Function.extend j b 0 k' = 0 := by
  rw [Function.extend_apply' _ _ _ h]
  rfl

theorem extend_inj {M : Type*} [Zero M] {b₁ b₂ : K → M} :
    Function.extend j b₁ 0 = Function.extend j b₂ 0 ↔ b₁ = b₂ := by
  refine ⟨fun h => funext fun k => ?_, fun h => h ▸ rfl⟩
  have := congrFun h (j k)
  rwa [extend_apply_self, extend_apply_self] at this

theorem weight_apply_eval {σ : Type*} (w : σ → K' → ℕ) (d : σ →₀ ℕ) (k' : K') :
    Finsupp.weight w d k' = Finsupp.weight (fun v => w v k') d := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

variable [DecidableEq K] [DecidableEq K']

omit [DecidableEq K] [DecidableEq K'] in

theorem weight_mapDomain {σ τ M : Type*} [AddCommMonoid M] (w : τ → M) (g : σ → τ)
    (d : σ →₀ ℕ) : Finsupp.weight w (Finsupp.mapDomain g d) = Finsupp.weight (w ∘ g) d := by
  simp only [Finsupp.weight_apply]
  rw [Finsupp.sum_mapDomain_index (h := fun i c => c • w i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  rfl

theorem weight_blockIncl (d : (Σ k, ι' (j k)) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain (blockIncl j ι') d) =
      Function.extend j (Finsupp.weight (blockWeight (fun k => ι' (j k))) d) 0 := by
  rw [weight_mapDomain]
  funext k'
  rw [weight_apply_eval]
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    rw [extend_apply_self, weight_apply_eval]
    have e : (fun v => (blockWeight ι' ∘ blockIncl j ι') v (j k)) =
        fun v => blockWeight (fun k => ι' (j k)) v k := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) (j k) = (Pi.single v.1 1 : K → ℕ) k
      simp only [Pi.single_apply, j.injective.eq_iff]
    rw [e]
  · rw [extend_apply_not j _ k' h]
    have h0 : (fun v => (blockWeight ι' ∘ blockIncl j ι') v k') = 0 := by
      funext v
      show (Pi.single (j v.1) 1 : K' → ℕ) k' = 0
      rw [Pi.single_apply, if_neg (fun hv => h ⟨v.1, hv.symm⟩)]
    rw [h0]
    simp [Finsupp.weight_apply]

variable {F : Type u} [Field F]

theorem isMultiHomog_rename {a : MRing (fun k => ι' (j k)) F} {c : K → ℕ} (ha : IsMultiHomog a c) :
    IsMultiHomog (rename (blockIncl j ι') a) (Function.extend j c 0) := by
  classical
  have ha' : IsWeightedHomogeneous (blockWeight (fun k => ι' (j k))) a c := ha
  show IsWeightedHomogeneous _ _ _
  intro d' hd'
  have hmem : d' ∈ (rename (blockIncl j ι') a).support := mem_support_iff.mpr hd'
  rw [support_rename_of_injective (blockIncl_injective j ι')] at hmem
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hmem
  rw [weight_blockIncl, ha' (mem_support_iff.mp hd)]

theorem rename_component (a : MRing (fun k => ι' (j k)) F) (b : K → ℕ) :
    rename (blockIncl j ι') (weightedHomogeneousComponent (blockWeight (fun k => ι' (j k))) b a) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0)
        (rename (blockIncl j ι') a) := by
  classical
  ext d'
  rw [coeff_weightedHomogeneousComponent]
  by_cases hd : ∃ d, Finsupp.mapDomain (blockIncl j ι') d = d'
  · obtain ⟨d, rfl⟩ := hd
    rw [coeff_rename_mapDomain _ (blockIncl_injective j ι'),
      coeff_rename_mapDomain _ (blockIncl_injective j ι'), coeff_weightedHomogeneousComponent,
      weight_blockIncl]
    by_cases hw : Finsupp.weight (blockWeight (fun k => ι' (j k))) d = b
    · rw [if_pos hw, if_pos (by rw [hw])]
    · rw [if_neg hw, if_neg (fun h => hw ((extend_inj j).mp h))]
  · push Not at hd
    rw [coeff_rename_eq_zero _ _ d' (fun u hu => absurd hu (hd u)),
      coeff_rename_eq_zero _ a d' (fun u hu => absurd hu (hd u))]
    simp

theorem isMultiProjPrime_contractPrime {P' : Ideal (MRing ι' F)} (hP' : IsMultiProjPrime P') :
    IsMultiProjPrime (contractPrime j P') where
  isPrime := by
    have := hP'.isPrime
    exact contractPrime.isPrime j P'
  multiHomog := by
    intro f hf b
    show rename (blockIncl j ι') _ ∈ P'
    rw [rename_component]
    exact hP'.multiHomog _ hf _
  relevant := by
    intro k
    obtain ⟨i, hi⟩ := hP'.relevant (j k)
    refine ⟨i, ?_⟩
    show rename (blockIncl j ι') (X ⟨k, i⟩) ∉ P'
    rw [rename_X]
    exact hi

omit [DecidableEq K] [DecidableEq K'] in

theorem contractFracMap_algebraMap (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (a : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') a)) =
      algebraMap _ (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') a)) := by
  unfold contractFracMap
  exact IsFractionRing.lift_algebraMap
    (g := ((IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P')).toRingHom)
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      Ideal.quotientMap_injective) _

theorem map_homFracDegZero_le (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' := by
  unfold homFracDegZero
  rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, rfl⟩, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_⟩
  rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]

omit [DecidableEq K] [DecidableEq K'] in

theorem pullDeg_sub (bf bg : K → ℕ) :
    pullDeg j (fun k => (bf k : ℤ) - bg k) =
      fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ) := by
  funext k'
  by_cases h : ∃ k, j k = k'
  · obtain ⟨k, rfl⟩ := h
    simp only [pullDeg, extend_apply_self]
  · simp only [pullDeg, extend_apply_not j _ k' h]
    simp

end Pull

theorem ProjectionFormulaDegree.proof (h1 : CutRational.Statement.{u})
    (h2 : IntNumBase.Statement.{u}) (h3 : ProjectionFormulaContracted.Statement.{u})
    (h4 : DivPushForward.Statement.{u}) : ProjectionFormulaDegree.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n
  induction n generalizing P' with
  | zero =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    have e1 : (fun i : Fin 0 => pullDeg j (bs i)) = ![] := Subsingleton.elim _ _
    have e2 : bs = ![] := Subsingleton.elim _ _
    rw [e1, e2, (h2 F K' ι' P' hP' hdim).2, (h2 F K _ _ hP hdimP).2,
      ← IntermediateField.finrank_bot_mul_relfinrank (map_homFracDegZero_le j ι' P'),
      ← (IntermediateField.equivMap _ (contractFracMap j P')).toLinearEquiv.finrank_eq]
    unfold relDeg
    push_cast
    ring
  | succ n ih =>
    intro hdim hdimP bs
    have := hP'.isPrime
    refine ⟨map_homFracDegZero_le j ι' P', ?_⟩
    have hP := isMultiProjPrime_contractPrime j ι' hP'
    obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hb⟩ :=
      ExistsForm.proof F K (fun k => ι' (j k)) (contractPrime j P') hP (bs (Fin.last n))
    have hbs : bs = Fin.snoc (α := fun _ => K → ℤ) (Fin.init bs) (fun k => (bf k : ℤ) - bg k) := by
      rw [hb, Fin.snoc_init_self]
    have hpull : (fun i => pullDeg j (bs i)) = Fin.snoc (α := fun _ => K' → ℤ)
        (fun i => pullDeg j (Fin.init bs i))
        (fun k' => ((Function.extend j bf 0 k' : ℕ) : ℤ) - ((Function.extend j bg 0 k' : ℕ) : ℤ)) := by
      rw [← pullDeg_sub, hb]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc, Fin.init]
    have hcutP : intNum F (contractPrime j P') bs =
        cycEval (fun W => intNum F W (Fin.init bs)) (ratDiv (contractPrime j P') f g) := by
      conv_lhs => rw [hbs]
      exact h1 F K _ _ hP n hdimP bf bg f g hf hg hfP hgP (Fin.init bs)
    have hcutP' := h1 F K' ι' P' hP' n hdim _ _ (rename (blockIncl j ι') f)
      (rename (blockIncl j ι') g) (isMultiHomog_rename j ι' hf) (isMultiHomog_rename j ι' hg)
      hfP hgP (fun i => pullDeg j (Fin.init bs i))
    have hyp1 : ∀ W' (hW' : IsMultiProjPrime W'), relDim W' = (n : ℕ) →
        relDim (contractPrime j W') = (n : ℕ) →
        haveI := hW'.isPrime
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) =
          relDeg j W' * intNum F (contractPrime j W') (Fin.init bs) :=
      fun W' hW' hd hc => (ih W' hW' hd hc (Fin.init bs)).2
    have hyp2 : ∀ W', IsMultiProjPrime W' → relDim W' = (n : ℕ) →
        relDim (contractPrime j W') < (n : ℕ) →
        intNum F W' (fun i => pullDeg j (Fin.init bs i)) = 0 :=
      fun W' hW' hd hlt => h3 F K K' j ι' W' hW' n hd hlt (Fin.init bs)
    have hpf := h4 F K K' j ι' P' hP' n hdim hdimP bf f hf hfP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    have hpg := h4 F K K' j ι' P' hP' n hdim hdimP bg g hg hgP (fun W' => intNum F W' (fun i => pullDeg j (Fin.init bs i)))
      (fun W => intNum F W (Fin.init bs)) hyp1 hyp2
    rw [hpull, hcutP', hcutP, cycEval_ratDiv, cycEval_ratDiv, mul_sub, hpf, hpg]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
