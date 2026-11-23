import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriBlocks.SimpleIn
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks
open GlobalTheory.PRep GlobalTheory.SmGL Formalism.BasicNotions GlobalTheory.CuspRep
open scoped TensorProduct Classical

private theorem pi_hom_ext {r : ℕ} {N : Fin r → Type} [∀ i, Monoid (N i)] {M : Type} [Monoid M]
    (f g : (∀ i, N i) →* M) (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) : f = g := by
  apply (MonoidHom.noncommPiCoprodEquiv (ι := Fin r) (N := N) (M := M)).symm.injective
  apply Subtype.ext
  funext i
  exact MonoidHom.ext fun x => h i x

private noncomputable def cfH {K : Type} [Field K] [NumberField K] {n : ℕ} (v : Pl K) : FA K n →* Gw n v where
  toFun := GM.cf v
  map_one' := by simp only [GM.cf]; rw [map_one, finAt_one]
  map_mul' a b := by simp only [GM.cf]; rw [map_mul, finAt_mul]

private theorem cf_ext {K : Type} [Field K] [NumberField K] {n : ℕ} {a b : FA K n}
    (h : ∀ v : Pl K, GM.cf v a = GM.cf v b) : a = b := by
  apply (AdelicGLn.finiteRestrictedEquiv K n).injective
  ext v : 1
  exact h v

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.IwahoriBlocks.embEx :
    ∀ {K : Type} [Field K] [NumberField K] (n : ℕ) {r : ℕ} (w : Fin r → Pl K), Function.Injective w → (∃ ι, IsEmb (n := n) w ι) ∧ ∀ ι : GS n w →* FA K n, IsEmb w ι →
      Continuous ι ∧ (∀ g i, GM.cf (w i) (ι g) = g i) ∧ (∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1) ∧
      (∀ h : FA K n, ∃ g h', h = ι g * h' ∧ ∀ i, GM.cf (w i) h' = 1) ∧ (∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h') ∧
      ∀ (U : ∀ v : Pl K, Subgroup (Gw n v)) (h : FA K n), h ∈ levOn (im w) U ↔
        ∃ g h', h = ι g * h' ∧ (∀ i, g i ∈ U (w i)) ∧ (∀ i, GM.cf (w i) h' = 1) ∧ ∀ v, GM.cf v h' ∈ GLnLocal.integralGL (v.adicCompletion K) n := by
  intro K _ _ n r w hw
  have L := fun v : Pl K => UpperTheory.ConvolutionTheory.Tf.locEmb K n v
  refine ⟨?_, ?_⟩
  · refine ⟨MonoidHom.noncommPiCoprod (fun i => AdelicGLn.localEmbedding (w i)) ?_, ?_⟩
    · intro i j hij x y
      exact (L (w i)).2.2.2.1 (w j) (fun e => hij (hw e).symm) x y
    · intro i g
      exact MonoidHom.noncommPiCoprod_mulSingle (N := fun i => Gw n (w i)) (fun i => AdelicGLn.localEmbedding (w i)) i g
  intro ι hι
  have hmul : ∀ (v : Pl K) (a b : FA K n), GM.cf v (a * b) = GM.cf v a * GM.cf v b :=
    fun v a b => map_mul (cfH v) a b
  have hinv : ∀ (v : Pl K) (a : FA K n), GM.cf v a⁻¹ = (GM.cf v a)⁻¹ :=
    fun v a => map_inv (cfH v) a
  have hone : ∀ v : Pl K, GM.cf v (1 : FA K n) = 1 := fun v => map_one (cfH v)
  have hcf : ∀ g i, GM.cf (w i) (ι g) = g i := by
    intro g i
    have e : (cfH (w i)).comp ι = Pi.evalMonoidHom (fun j => Gw n (w j)) i := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf (w i) (ι (Pi.mulSingle j x)) = (Pi.mulSingle j x : GS n w) i
      rw [hι j x]
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact (L (w j)).2.1 x
      · rw [Pi.mulSingle_eq_of_ne (Ne.symm h)]
        exact (L (w j)).2.2.1 (w i) (fun e => h (hw e).symm) x
    exact DFunLike.congr_fun e g
  have hoff : ∀ g, ∀ v ∉ im w, GM.cf v (ι g) = 1 := by
    intro g v hv
    have e : (cfH v).comp ι = 1 := by
      refine pi_hom_ext _ _ fun j x => ?_
      change GM.cf v (ι (Pi.mulSingle j x)) = 1
      rw [hι j x]
      exact (L (w j)).2.2.1 v (fun e => hv (e ▸ Finset.mem_image_of_mem w (Finset.mem_univ j))) x
    exact DFunLike.congr_fun e g
  have hcomm : ∀ g (h' : FA K n), (∀ i, GM.cf (w i) h' = 1) → Commute (ι g) h' := by
    intro g h' hh
    refine cf_ext fun v => ?_
    rw [hmul, hmul]
    by_cases hv : v ∈ im w
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
      rw [hh i, one_mul, mul_one]
    · rw [hoff g v hv, one_mul, mul_one]
  have hsplit : ∀ h : FA K n, ∀ i, GM.cf (w i) ((ι fun j => GM.cf (w j) h)⁻¹ * h) = 1 := by
    intro h i
    rw [hmul, hinv, hcf, inv_mul_cancel]
  have hcont : Continuous ι := by
    let tr : Finset (Fin r) → GS n w → GS n w := fun s g i => if i ∈ s then g i else 1
    have hc : ∀ s : Finset (Fin r), Continuous fun g => ι (tr s g) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        have e : (fun g => ι (tr ∅ g)) = fun _ => 1 := by
          funext g
          have : tr ∅ g = 1 := by funext i; simp [tr]
          rw [this, map_one]
        rw [e]
        exact continuous_const
      | insert a s ha ih =>
        have e : (fun g => ι (tr (insert a s) g)) =
            fun g => ι (tr s g) * AdelicGLn.localEmbedding (w a) (g a) := by
          funext g
          rw [← hι a (g a), ← map_mul]
          congr 1
          funext i
          by_cases h : i = a
          · subst h
            simp [tr, ha]
          · simp [tr, h, Pi.mulSingle_eq_of_ne h]
        rw [e]
        exact ih.mul ((L (w a)).1.comp (continuous_apply a))
    have e : (fun g => ι (tr Finset.univ g)) = ι := by
      funext g
      congr 1
      funext i
      simp [tr]
    rw [← e]
    exact hc Finset.univ
  refine ⟨hcont, hcf, hoff, ?_, hcomm, ?_⟩
  · intro h
    exact ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, hsplit h⟩
  · intro U h
    constructor
    · intro hh
      have hh' : ∀ v, GM.cf v h ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := hh
      refine ⟨fun j => GM.cf (w j) h, _, (mul_inv_cancel_left _ _).symm, fun i => ?_, hsplit h, fun v => ?_⟩
      · have := hh' (w i)
        rwa [if_pos (Finset.mem_image_of_mem w (Finset.mem_univ i))] at this
      · by_cases hv : v ∈ im w
        · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hsplit h i]
          exact one_mem _
        · have := hh' v
          rw [if_neg hv] at this
          rw [hmul, hinv, hoff _ v hv, inv_one, one_mul]
          exact this
    · rintro ⟨g, h', rfl, hg, h1, hint⟩
      have hh' : ∀ v, GM.cf v (ι g * h') ∈ (if v ∈ im w then U v else GLnLocal.integralGL (v.adicCompletion K) n) := by
        intro v
        rw [hmul]
        by_cases hv : v ∈ im w
        · rw [if_pos hv]
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
          rw [hcf, h1 i, mul_one]
          exact hg i
        · rw [if_neg hv, hoff g v hv, one_mul]
          exact hint v
      exact hh'
