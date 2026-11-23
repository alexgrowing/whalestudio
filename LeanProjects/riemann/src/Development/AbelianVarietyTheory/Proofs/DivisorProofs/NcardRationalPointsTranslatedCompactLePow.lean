import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NormInfSubmultiplicativeLeAdelicHeight
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryAdelicHeightCosetLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmTypeRestrictRealSubfieldInfinitePlaceBijective

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RatCount

theorem exists_nat_den {E : Type} [Field E] [NumberField E] {κ : Type} [Finite κ] (A : κ → E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * A i) := by
  classical
  haveI := Fintype.ofFinite κ
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image A)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (A i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [zsmul_eq_mul] at h1
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  rcases abs_choice y with e | e <;> rw [e]
  · exact h1
  · rw [Int.cast_neg, neg_mul]; exact h1.neg

theorem exists_den_of_isCompact {F : Type} [Field F] [NumberField F] {K : Set (FiniteAdeleRing (𝓞 F) F)}
    (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ K → IsIntegral ℤ ((m : F) * a) := by
  classical
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  let U : FiniteAdeleRing (𝓞 F) F → Set (FiniteAdeleRing (𝓞 F) F) := fun z =>
    (fun w => w - z) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun z => hV.preimage (continuous_id.sub continuous_const))
    fun z _ => Set.mem_iUnion.2 ⟨z, fun v => by
      show (z - z) v ∈ _
      rw [sub_self]; exact zero_mem _⟩
  let A : t → F := fun z =>
    if h : ∃ a : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U z then h.choose else 0
  obtain ⟨m, hm, h⟩ := exists_nat_den A
  refine ⟨m, hm, fun a ha => ?_⟩
  obtain ⟨z, hz, haz⟩ := Set.mem_iUnion₂.1 (ht ha)
  have hex : ∃ a : F, algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U z := ⟨a, haz⟩
  have hA : algebraMap F (FiniteAdeleRing (𝓞 F) F) (A ⟨z, hz⟩) ∈ U z := by
    simp only [A, dif_pos hex]; exact hex.choose_spec
  obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (a - A ⟨z, hz⟩) fun v => by
    have h1 := sub_mem (haz v) (hA v)
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a - z) v -
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (A ⟨z, hz⟩) - z) v =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (a - A ⟨z, hz⟩) v := by
      rw [map_sub, ← sub_sub_sub_cancel_right (algebraMap F (FiniteAdeleRing (𝓞 F) F) a)
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) (A ⟨z, hz⟩)) z]
      rfl
    rw [e] at h1
    have h2 : ((a - A ⟨z, hz⟩ : F) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
    exact h2
  have e : (m : F) * a = m * algebraMap (𝓞 F) F c + m * A ⟨z, hz⟩ := by rw [hc]; ring
  rw [e]
  exact ((isIntegral_natCast m).mul c.2).add (h _)

theorem exists_den_of_isCompact_tensor {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {K : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)} (hK : IsCompact K) :
    ∃ m : ℕ, 0 < m ∧ ∀ a : E, (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] a ∈ K → IsIntegral ℤ ((m : E) * a) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) b
  have hc : ∀ k, Continuous (B.coord k) := fun k => IsModuleTopology.continuous_of_linearMap _
  obtain ⟨m, hm, h⟩ := exists_den_of_isCompact (isCompact_iUnion fun k => hK.image (hc k))
  obtain ⟨m', hm', h'⟩ := exists_nat_den b
  refine ⟨m * m', by positivity, fun a ha => ?_⟩
  have h1 : ∀ k, IsIntegral ℤ ((m : F) * b.repr a k) := fun k => h _ <| Set.mem_iUnion.2 ⟨k, _, ha, by
    show B.repr ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] a) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp⟩
  have e : ((m * m' : ℕ) : E) * a = ∑ k, algebraMap F E ((m : F) * b.repr a k) * ((m' : E) * b k) := by
    conv_lhs => rw [← b.sum_repr a]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e]
  exact IsIntegral.sum _ fun k _ => ((h1 k).map (algebraMap F E).toIntAlgHom).mul (h' k)

theorem exists_repr_le_house (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem count_matrices (E : Type) [Field E] [NumberField E] (n : ℕ) :
    ∃ N : ℕ, ∀ m : ℕ, 0 < m → ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      {A : Matrix (Fin n) (Fin n) E | ∀ i j, IsIntegral ℤ ((m : E) * A i j) ∧ house (A i j) ≤ R}.Finite ∧
      (({A : Matrix (Fin n) (Fin n) E | ∀ i j, IsIntegral ℤ ((m : E) * A i j) ∧ house (A i j) ≤ R}.ncard : ℕ) : ℝ) ≤
        C * R ^ N := by
  classical
  obtain ⟨c, hc, hb⟩ := exists_repr_le_house E
  let ι := Fin n × Fin n × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  refine ⟨Fintype.card ι, fun m hm => ⟨(2 * (c * m) + 3) ^ Fintype.card ι, by positivity, fun R hR => ?_⟩⟩
  set T := {A : Matrix (Fin n) (Fin n) E | ∀ i j, IsIntegral ℤ ((m : E) * A i j) ∧ house (A i j) ≤ R}
  let M : ℕ := ⌈c * m * R⌉₊
  let s : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(M : ℤ)) M
  let f : T → s := fun A => ⟨fun q => (RingOfIntegers.basis E).repr ⟨_, (A.2 q.1 q.2.1).1⟩ q.2.2, by
    refine Fintype.mem_piFinset.2 fun q => Finset.mem_Icc.2 (abs_le.1 ?_)
    have h1 := hb ⟨_, (A.2 q.1 q.2.1).1⟩ q.2.2
    have h2 : c * house ((m : E) * A.1 q.1 q.2.1) ≤ (M : ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [house_nat_mul, mul_assoc]
      gcongr
      exact (A.2 _ _).2
    have h3 := h1.trans h2
    exact_mod_cast h3⟩
  have hf : Function.Injective f := by
    intro A A' h
    ext a b
    have : (⟨_, (A.2 a b).1⟩ : 𝓞 E) = ⟨_, (A'.2 a b).1⟩ :=
      (RingOfIntegers.basis E).ext_elem fun j => congrFun (congrArg Subtype.val h) (a, b, j)
    have h2 : (m : E) * A.1 a b = m * A'.1 a b := congrArg Subtype.val this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hm.ne') h2
  refine ⟨Set.finite_coe_iff.1 (Finite.of_injective f hf), ?_⟩
  have h1 : T.ncard ≤ (2 * M + 1) ^ Fintype.card ι := by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_piFinset] at this
    refine this.trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ, Int.card_Icc]
    congr 1
    omega
  have h2 : (M : ℝ) ≤ c * m * R + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  rw [← mul_pow]
  refine (Nat.cast_le.2 h1).trans ?_
  push_cast
  gcongr
  linarith

variable {D : D7}

theorem normInf_inv (θ : InfFam D) (V : HSp D) (g : GA D V) : normInf θ V g⁻¹ = normInf θ V g := by
  unfold normInf
  rw [inv_inv]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => add_comm _ _

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf; positivity

theorem continuous_normInf {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) : Continuous (normInf θ V) := by
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have h := fun τ => GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ τ)
  refine continuous_finset_sum _ fun τ _ => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((h τ).matrix_elem i j).norm.add (((h τ).comp continuous_inv).matrix_elem i j).norm

theorem one_le_normInf (θ : InfFam D) {V : HSp D} (hV : 0 < V.rank) (g : GA D V) : 1 ≤ normInf θ V g :=
  le_trans (by exact_mod_cast le_max_left _ _)
    (GlobalTheory.SmoothForms.HeightCoset.infHt_le_normInf θ V hV (D.eTau.symm 1) g)

theorem house_le_normInf {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V)
    (A : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hA : (matHom V g).1 = A.map (incA D)) (i j : Fin V.rank) :
    house (A i j) ≤ normInf θ V g := by
  refine (pi_norm_le_iff_of_nonneg (normInf_nonneg θ V g)).2 fun φ => ?_
  change ‖φ (A i j)‖ ≤ _
  obtain ⟨τ, hτ⟩ := (GlobalTheory.CMTypePlaces.mk_tauE_bijective D).2 (InfinitePlace.mk φ)
  have e1 : ‖φ (A i j)‖ = ‖tauE D τ (A i j)‖ := by
    rw [← InfinitePlace.apply, ← InfinitePlace.apply, ← hτ]
  have e2 : infMat D.sp.cm.sig V.gram (θ τ) g i j = tauE D τ (A i j) := by
    rw [← (hθ τ).1]
    show θ τ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V g).1 i j)) = _
    rw [hA]
    rfl
  rw [e1, ← e2]
  unfold normInf
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ τ))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j))
  exact le_add_of_nonneg_right (norm_nonneg _)

theorem ncard_rational_le : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (Ω : Set (GA D V)), IsCompact Ω → ∃ N : ℕ, ∀ x : GA D V, ∃ C : ℝ, ∀ u ∈ GinfC V, ∀ y : GA D V, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.Finite ∧ (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}.ncard : ℕ) : ℝ) ≤ C * normInf θ V u ^ N := by
  intro D θ V hθ Ω hΩ
  have hinj : Function.Injective fun g : GA D V => (matHom V g).1 := fun g h e =>
    Subtype.ext (Units.ext e)
  rcases Nat.eq_zero_or_pos V.rank with hV | hV
  · haveI : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
    haveI : Subsingleton (GA D V) := hinj.subsingleton
    refine ⟨0, fun x => ⟨1, fun u _ y => ⟨Set.toFinite _, ?_⟩⟩⟩
    rw [pow_zero, mul_one]
    exact_mod_cast (Set.ncard_le_one (Set.toFinite _)).2 fun a _ b _ => Subsingleton.elim a b
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨N, hN⟩ := count_matrices D.host.E V.rank
  refine ⟨2 * N, fun x => ?_⟩
  have hW : IsCompact ((fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω)) :=
    (hΩ.prod hΩ).image (continuous_fst.mul continuous_snd.inv)
  obtain ⟨B, hB⟩ := (hW.image (continuous_normInf hθ V)).bddAbove
  have hc : ∀ i j, Continuous fun g : GA D V => finMat D.sp.cm.sig V.gram (x * g * x⁻¹) i j := fun i j =>
    ((GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).comp
      ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem i j
  obtain ⟨m, hm, hden⟩ := exists_den_of_isCompact_tensor
    (isCompact_iUnion fun i => isCompact_iUnion fun j => hW.image (hc i j))
  obtain ⟨C, hC, hT⟩ := hN m hm
  set c : ℝ := normInf θ V x ^ 2 * |B| + 1 with hcd
  have hc1 : 1 ≤ c := le_add_of_nonneg_left (by positivity)
  refine ⟨C * c ^ N, fun u hu y => ?_⟩
  have hu1 := one_le_normInf θ hV u
  obtain ⟨hT1, hT2⟩ := hT (c * normInf θ V u ^ 2) (one_le_mul_of_one_le_of_one_le hc1 (one_le_pow₀ hu1))
  set S := {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = x * u * o}
  rcases S.eq_empty_or_nonempty with hS | ⟨γ₀, hγ₀, o₀, ho₀, e₀⟩
  · rw [hS]
    refine ⟨Set.finite_empty, ?_⟩
    rw [Set.ncard_empty, Nat.cast_zero]
    positivity
  have hψ : Function.Injective fun g : GA D V => (matHom V (g * γ₀⁻¹)).1 := fun g h e =>
    mul_right_cancel (hinj e)
  have hsub : (fun g : GA D V => (matHom V (g * γ₀⁻¹)).1) '' S ⊆ (fun A => A.map (incA D)) ''
      {A : Matrix (Fin V.rank) (Fin V.rank) D.host.E |
        ∀ i j, IsIntegral ℤ ((m : D.host.E) * A i j) ∧ house (A i j) ≤ c * normInf θ V u ^ 2} := by
    rintro _ ⟨γ, ⟨hγ, o, ho, e⟩, rfl⟩
    obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 (mul_mem hγ (inv_mem hγ₀)))
    have hA : (matHom V (γ * γ₀⁻¹)).1 = δ.1.map (incA D) := (congrArg Units.val hδ).symm
    have e1 : γ * γ₀⁻¹ = x * u * (o * o₀⁻¹) * u⁻¹ * x⁻¹ := by
      rw [eq_mul_inv_of_mul_eq e, eq_mul_inv_of_mul_eq e₀]; group
    have hw : o * o₀⁻¹ ∈ (fun p : GA D V × GA D V => p.1 * p.2⁻¹) '' (Ω ×ˢ Ω) := ⟨(o, o₀), ⟨ho, ho₀⟩, rfl⟩
    refine ⟨δ.1, fun i j => ⟨hden _ (Set.mem_iUnion₂.2 ⟨i, j, _, hw, ?_⟩), ?_⟩, hA.symm⟩
    · have h0 : finHom V u = 1 := hu
      have h1 : finHom V (x * (o * o₀⁻¹) * x⁻¹) = finHom V (γ * γ₀⁻¹) := by
        rw [e1]
        simp only [map_mul, map_inv, h0, mul_one, inv_one]
      show (finHom V (x * (o * o₀⁻¹) * x⁻¹)).1 i j = _
      rw [h1]
      show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V (γ * γ₀⁻¹)).1 i j) = _
      rw [hA]
      rfl
    · refine (house_le_normInf hθ V _ _ hA i j).trans ?_
      have hmul := (GlobalTheory.SmoothForms.normInf_mul_le_and_le_height D θ V).1
      have h0 := normInf_nonneg θ V
      have hb : normInf θ V (o * o₀⁻¹) ≤ |B| := (hB ⟨_, hw, rfl⟩).trans (le_abs_self B)
      rw [e1]
      calc _ ≤ normInf θ V x * normInf θ V u * |B| * normInf θ V u * normInf θ V x := by
            refine (hmul _ _).trans (mul_le_mul ?_ (normInf_inv θ V x).le (h0 _) ?_)
            · refine (hmul _ _).trans (mul_le_mul ?_ (normInf_inv θ V u).le (h0 _) ?_)
              · exact (hmul _ _).trans (mul_le_mul (hmul _ _) hb (h0 _) (mul_nonneg (h0 _) (h0 _)))
              · have := h0 x; positivity
            · have := h0 x; positivity
        _ ≤ _ := by rw [hcd]; nlinarith [sq_nonneg (normInf θ V u)]
  have hfin := (hT1.image _).subset hsub
  refine ⟨Set.Finite.of_finite_image hfin hψ.injOn, ?_⟩
  rw [← Set.ncard_image_of_injective S hψ, pow_mul, mul_assoc, ← mul_pow]
  refine le_trans ?_ hT2
  exact_mod_cast (Set.ncard_le_ncard hsub (hT1.image _)).trans (Set.ncard_image_le hT1)

end GlobalTheory.RatCount

end
