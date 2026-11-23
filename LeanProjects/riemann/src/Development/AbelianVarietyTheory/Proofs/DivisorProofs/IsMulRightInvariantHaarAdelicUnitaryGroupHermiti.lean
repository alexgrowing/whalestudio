import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.DataExtra

open MeasureTheory NumberField IsDedekindDomain Matrix Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicUnimod
open Formalism.UG (UJ cT intAd)
open scoped TensorProduct NNReal ENNReal Pointwise RestrictedProduct

noncomputable section

namespace GlobalTheory.AdelicPointsUnimod

theorem modular_of_mem_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (hc : IsCompact (K : Set G)) {k : G} (hk : k ∈ K) : Measure.modularCharacter k = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨U, hU, h1⟩ := exists_compact_mem_nhds (1 : G)
  have hW : IsCompact (U * (K : Set G)) := hU.mul hc
  have hW1 : U * (K : Set G) ∈ 𝓝 (1 : G) := mem_of_superset h1 (Set.subset_mul_left _ K.one_mem)
  have h2 := congrArg (fun m : Measure G => m (U * (K : Set G))) (map_mul_right_eq μ k)
  simp only [Measure.coe_nnreal_smul_apply] at h2
  have he : (fun x => x * k) ⁻¹' (U * (K : Set G)) = U * (K : Set G) := by
    ext x
    constructor
    · rintro ⟨u, hu, y, hy, h⟩
      refine ⟨u, hu, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), ?_⟩
      show u * (y * k⁻¹) = x
      rw [← mul_assoc, show u * y = x * k from h, mul_inv_cancel_right]
    · rintro ⟨u, hu, y, hy, rfl⟩
      exact ⟨u, hu, y * k, K.mul_mem hy hk, (mul_assoc _ _ _).symm⟩
  rw [Measure.map_apply (measurable_mul_const _) hW.isClosed.measurableSet, he] at h2
  have h3 : (Measure.modularCharacter k : ℝ≥0∞) = 1 :=
    (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ hW1).ne' hW.measure_lt_top.ne).1
      (by rw [one_mul]; exact h2.symm)
  exact_mod_cast h3

section Congruence

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_sub_one_mem (C : NonUnitalSubring A) {X Y : Matrix n n A} (hX : ∀ i j, (X - 1) i j ∈ C)
    (hY : ∀ i j, (Y - 1) i j ∈ C) (i j : n) : (X * Y - 1) i j ∈ C := by
  have : X * Y - 1 = (X - 1) * (Y - 1) + (X - 1) + (Y - 1) := by noncomm_ring
  rw [this, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
  exact add_mem (add_mem (sum_mem fun l _ => mul_mem (hX i l) (hY l j)) (hX i j)) (hY i j)

def congSub (σ : A →+* A) (J : Matrix n n A) (C : NonUnitalSubring A) : Subgroup (UJ σ J) where
  carrier := {k | (∀ i j, (mat k - 1) i j ∈ C) ∧ ∀ i j, (mat k⁻¹ - 1) i j ∈ C}
  one_mem' := by
    have : mat (1 : UJ σ J) = 1 := rfl
    simp [this]
  mul_mem' := fun {a b} ha hb => ⟨mul_sub_one_mem C ha.1 hb.1, by
    rw [_root_.mul_inv_rev]
    exact mul_sub_one_mem C hb.2 ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem isCompact_congSub [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {σ : A →+* A} (hσ : Continuous σ)
    (J : Matrix n n A) (C : NonUnitalSubring A) (hC : IsCompact (C : Set A)) :
    IsCompact (congSub σ J C : Set (UJ σ J)) := by
  have hc : IsClosed (UJ σ J : Set (GL n A)) := by
    have hv : Continuous fun g : GL n A => (g : Matrix n n A) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hv)
      continuous_const
  have h1 : IsCompact {X : Matrix n n A | ∀ i j, X i j ∈ C} := by
    have := isCompact_univ_pi fun _ : n => isCompact_univ_pi fun _ : n => hC
    have e : {X : n → n → A | ∀ i j, X i j ∈ C} = Set.univ.pi fun _ : n => Set.univ.pi fun _ : n => (C : Set A) := by
      ext X
      simp [Set.mem_pi]
    rw [← e] at this
    exact this
  have h2 : IsCompact {X : Matrix n n A | ∀ i j, (X - 1) i j ∈ C} :=
    (Homeomorph.subRight (1 : Matrix n n A)).isCompact_preimage.2 h1
  have h3 := (MulOpposite.opHomeomorph (M := Matrix n n A)).symm.isCompact_preimage.2 h2
  exact (Units.isClosedEmbedding_embedProduct.comp hc.isClosedEmbedding_subtypeVal).isCompact_preimage (h2.prod h3)

end Congruence

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_intAd : IsCompact (intAd F : Set (Af F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

def intFin : NonUnitalSubring (AF F) where
  carrier := {a | a.1 = 0 ∧ a.2 ∈ intAd F}
  add_mem' := fun {a b} ha hb => ⟨by show a.1 + b.1 = 0; rw [ha.1, hb.1, add_zero], add_mem ha.2 hb.2⟩
  zero_mem' := ⟨rfl, zero_mem _⟩
  mul_mem' := fun {a b} ha hb => ⟨by show a.1 * b.1 = 0; rw [ha.1, zero_mul], mul_mem ha.2 hb.2⟩
  neg_mem' := fun {a} ha => ⟨by show -a.1 = 0; rw [ha.1, neg_zero], neg_mem ha.2⟩

theorem isCompact_intFin : IsCompact (intFin F : Set (AF F)) :=
  (isCompact_singleton (x := (0 : Ainf F))).prod (isCompact_intAd F)

variable {F}

theorem exists_split_adele {κ : Type} [Finite κ] (a : κ → AF F) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra F R) (p : AF F →ₐ[F] R) (e : AF F),
    IsArtinianRing R ∧ Function.Surjective p ∧ p e = 1 ∧ (∀ x, p x = 0 → e * x = 0) ∧
      ∀ k, (1 - e) * a k ∈ intFin F := by
  classical
  let S := ⋃ k, {v : HeightOneSpectrum (𝓞 F) | (a k).2 v ∉ v.adicCompletionIntegers F}
  have hS : S.Finite := Set.finite_iUnion fun k => Filter.eventually_cofinite.1 (a k).2.2
  haveI : Finite S := hS.to_subtype
  let p : AF F →ₐ[F] (Ainf F × ∀ v : S, v.1.adicCompletion F) :=
    { toFun := fun x => (x.1, fun v => x.2 v.1)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let s : (∀ v : S, v.1.adicCompletion F) → Af F := fun y =>
    ⟨fun v => if h : v ∈ S then y ⟨v, h⟩ else 0, by
      filter_upwards [hS.compl_mem_cofinite] with v hv
      rw [dif_neg hv]
      exact zero_mem _⟩
  have hs : ∀ x y, p ((x, s y) : Ainf F × Af F) = (x, y) := fun x y => Prod.ext rfl (funext fun v => dif_pos v.2)
  have hs1 : ∀ v, s 1 v = if v ∈ S then 1 else 0 := fun v => by
    show dite _ _ _ = _
    split_ifs <;> rfl
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing (∀ v : InfinitePlace F, v.Completion))
  refine ⟨_, inferInstance, inferInstance, p, ((1, s 1) : Ainf F × Af F), inferInstance, fun y => ⟨_, hs y.1 y.2⟩,
    hs 1 1, fun x hx => Prod.ext ?_ ?_, fun k => ⟨?_, fun v => ?_⟩⟩
  · show 1 * x.1 = 0
    rw [one_mul]
    exact congrArg Prod.fst hx
  · refine FiniteAdeleRing.ext _ fun v => ?_
    show s 1 v * x.2 v = 0
    rw [hs1]
    split_ifs with h
    · rw [one_mul]
      exact congrFun (congrArg Prod.snd hx) ⟨v, h⟩
    · exact zero_mul _
  · show (1 - 1) * (a k).1 = 0
    rw [sub_self, zero_mul]
  · show (1 - s 1 v) * (a k).2 v ∈ _
    rw [hs1]
    split_ifs with h
    · rw [sub_self, zero_mul]
      exact zero_mem _
    · rw [sub_zero, one_mul]
      exact not_not.1 fun h' => h (Set.mem_iUnion.2 ⟨k, h'⟩)

end Adeles

section Tensor

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {R : Type} [CommRing R] [Algebra F R]

theorem exists_sum_tmul (x : R ⊗[F] E) :
    ∃ a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R, x = ∑ i, a i ⊗ₜ[F] (RingOfIntegers.basis E i : E) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨fun i => algebraMap ℚ F ((integralBasis E).repr y i) • r, ?_⟩
    conv_lhs => rw [← (integralBasis E).sum_repr y, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul, algebraMap_smul, integralBasis_apply]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

theorem exists_compact_subring [TopologicalSpace R] [IsTopologicalRing R] (R₀ : NonUnitalSubring R)
    (hc : IsCompact (R₀ : Set R)) : ∃ C : NonUnitalSubring (R ⊗[F] E), IsCompact (C : Set (R ⊗[F] E)) ∧
      ∀ r ∈ R₀, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let f : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R) →ₗ[R] R ⊗[F] E :=
    Fintype.linearCombination R fun i => (1 : R) ⊗ₜ[F] (RingOfIntegers.basis E i : E)
  have hf : ∀ a, f a = ∑ i, a i ⊗ₜ[F] (RingOfIntegers.basis E i : E) := fun a => by
    simp [f, Fintype.linearCombination_apply, TensorProduct.smul_tmul']
  let C₀ : AddSubgroup (R ⊗[F] E) := (AddSubgroup.pi Set.univ fun _ => R₀.toAddSubgroup).map f.toAddMonoidHom
  have h1 : ∀ r ∈ R₀, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C₀ := fun r hr β => by
    refine ⟨fun i => (RingOfIntegers.basis E).repr β i • r, fun i _ => zsmul_mem hr _, ?_⟩
    show f _ = _
    rw [hf]
    show ∑ i, _ ⊗ₜ[F] algebraMap (𝓞 E) E _ = r ⊗ₜ[F] algebraMap (𝓞 E) E β
    conv_rhs => rw [← (RingOfIntegers.basis E).sum_repr β, map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, TensorProduct.smul_tmul]
  refine ⟨{ C₀ with mul_mem' := ?_ }, ?_, h1⟩
  · rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    show f a * f b ∈ C₀
    rw [hf, hf, Finset.sum_mul_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    exact h1 _ (R₀.mul_mem (ha i trivial) (hb j trivial)) (RingOfIntegers.basis E i * RingOfIntegers.basis E j)
  · exact (isCompact_univ_pi fun _ => hc).image (IsModuleTopology.continuous_of_linearMap f)

theorem sigR_sigR {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_split_tensor (σ : E →ₐ[F] E) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ) {κ : Type} [Finite κ]
    (C : NonUnitalSubring (AF F ⊗[F] E)) (hC : ∀ r ∈ intFin F, ∀ β : 𝓞 E, r ⊗ₜ[F] (β : E) ∈ C)
    (x : κ → AF F ⊗[F] E) : ∃ (B : Type) (_ : CommRing B) (σ' : B →+* B) (π : AF F ⊗[F] E →+* B)
      (e : AF F ⊗[F] E), (∀ x, π (sigR (AF F) σ x) = σ' (π x)) ∧ Function.Surjective π ∧ π e = 1 ∧
      (∀ x, π x = 0 → e * x = 0) ∧ sigR (AF F) σ e = e ∧ Generic σ' ∧ ∀ k, (1 - e) * x k ∈ C := by
  classical
  choose a ha using fun k => exists_sum_tmul (x k)
  obtain ⟨R, _, _, p, e, hR, hp, hpe, hker, hint⟩ :=
    exists_split_adele (κ := κ × _) fun q => a q.1 q.2
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsArtinianRing (R ⊗[F] E) := IsArtinianRing.of_finite R _
  letI : Algebra ℚ (R ⊗[F] E) := ((inclR (F := F) R).comp (algebraMap ℚ E)).toAlgebra
  refine ⟨R ⊗[F] E, inferInstance, sigR R σ, (Algebra.TensorProduct.map p (AlgHom.id F E)).toRingHom,
    e ⊗ₜ 1, fun y => ?_, Algebra.TensorProduct.map_surjective _ _ hp Function.surjective_id, ?_, fun y hy => ?_, ?_,
    generic_of_semilocal (δ := inclR R δ) (hδ.isUnit.map _) ?_, fun k => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  · simp [hpe, Algebra.TensorProduct.one_def]
  · have hy' : y ∈ RingHom.ker (Algebra.TensorProduct.map p (AlgHom.id F E)) := hy
    rw [Algebra.TensorProduct.rTensor_ker _ hp] at hy'
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simp [hker z hz]
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
  · simp [sigR]
  · simp [sigR, inclR, hσδ, TensorProduct.tmul_neg]
  · rw [ha k, Finset.mul_sum, Algebra.TensorProduct.one_def, ← TensorProduct.sub_tmul]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact hC _ (hint (k, i)) _

theorem isMulRightInvariant_adelic (σ : E →ₐ[F] E) (hss : ∀ x, σ (σ x) = x) {δ : E} (hδ : δ ≠ 0) (hσδ : σ δ = -δ)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨h⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AF F ⊗[F] E) := h.isEmbedding.t2Space
  obtain ⟨_, _, _⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ n J
  haveI : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  have hσ := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  obtain ⟨C, hCc, hC⟩ := exists_compact_subring (F := F) (E := E) (intFin F) (isCompact_intFin F)
  obtain ⟨M, hM⟩ := exists_framed (σ := (σ : E →+* E)) hss (J := J) (by ext i j; exact hJ.1 i j) hJ.2
  have hF : Framed (sigR (AF F) σ) (JR (AF F) J) (M.map (inclR (AF F))) :=
    hM.map fun x => by simp [sigR, inclR]
  obtain ⟨T, hTc, hT, hT'⟩ := exists_involution hσ (sigR_sigR hss) hF
  refine ⟨fun g => ?_⟩
  obtain ⟨B, _, σ', π, e, h1, h2, h3, h4, h5, h6, h7⟩ := exists_split_tensor σ hδ hσδ
    (κ := Bool × Fin n × Fin n) C hC fun p =>
      (mat (σ := sigR (AF F) σ) (J := JR (AF F) J) (bif p.1 then g else g⁻¹) - 1) p.2.1 p.2.2
  let χ : HA (AF F) σ J →* ℝ≥0 := Measure.modularCharacter
  have hχ := modular_involution (G := HA (AF F) σ J) T hTc hT
  obtain ⟨k, hk, hk', hkg⟩ := exists_char_eq h1 h2 h3 h4 h5 (sigR_sigR hss) hF h6 χ
    (fun x x' h => by
      rw [hT' x x' h]
      exact hχ x) g
  have hkK : k ∈ congSub (sigR (AF F) σ) (JR (AF F) J) C :=
    ⟨fun i j => by rw [hk]; exact h7 (true, i, j), fun i j => by rw [hk']; exact h7 (false, i, j)⟩
  let K : Subgroup (HA (AF F) σ J) := congSub (sigR (AF F) σ) (JR (AF F) J) C
  have hKc : IsCompact (K : Set (HA (AF F) σ J)) := isCompact_congSub hσ _ C hCc
  have h8 := modular_of_mem_compact K hKc (k := k) hkK
  rw [map_mul_right_eq, show Measure.modularCharacter g = 1 from hkg.symm.trans h8, one_smul]

end Tensor

end GlobalTheory.AdelicPointsUnimod

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure :
    ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant := by
  intro D V μ hμ
  obtain ⟨δ, hδ, hσδ⟩ : ∃ δ : D.host.E, δ ≠ 0 ∧ D.sp.cm.sig δ = -δ := by
    by_contra! h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun a => (D.sp.cm.fixed a).1 (by
      by_contra hne
      exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
    have := (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
      ⟨(algebraMap D.host.F D.host.E).injective, hs⟩).finrank_eq
    rw [D.sp.cm.deg2, Module.finrank_self] at this
    omega
  exact isMulRightInvariant_adelic D.sp.cm.sig (fun x => star_star x) hδ hσδ
    ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) μ
