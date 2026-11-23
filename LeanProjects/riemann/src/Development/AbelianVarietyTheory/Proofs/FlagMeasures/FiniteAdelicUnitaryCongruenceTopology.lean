import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
open Matrix Topology Filter IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongTop

section Abstract

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
  {S : Type} [CommRing S] [Algebra S A]

def cong (Λ : Submodule S (n → A)) (a : A) : Subgroup (GL n A) where
  carrier := {x | x ∈ Formalism.UG.stabGL Λ ∧
    ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix n n A) - 1) *ᵥ y = a • z}
  one_mem' := ⟨one_mem _, fun y _ => ⟨0, zero_mem _, by simp⟩⟩
  mul_mem' := by
    rintro x w ⟨hx, hx'⟩ ⟨hw, hw'⟩
    refine ⟨mul_mem hx hw, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ ((hw y).1 hy)
    obtain ⟨z', hz', e'⟩ := hw' y hy
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [smul_add, ← e, ← e', Units.val_mul]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul]
    abel
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨inv_mem hx, fun y hy => ?_⟩
    obtain ⟨z, hz, e⟩ := hx' _ ((inv_mem hx y).1 hy)
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [smul_neg, ← e]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, sub_mul, one_mul, Units.mul_inv]
    abel

theorem conj_mem_cong {Λ : Submodule S (n → A)} {a : A} {k x : GL n A}
    (hk : k ∈ Formalism.UG.stabGL Λ) (hx : x ∈ cong Λ a) : k * x * k⁻¹ ∈ cong Λ a := by
  refine ⟨mul_mem (mul_mem hk hx.1) (inv_mem hk), fun y hy => ?_⟩
  obtain ⟨z, hz, e⟩ := hx.2 _ ((inv_mem hk y).1 hy)
  refine ⟨(k : Matrix n n A) *ᵥ z, (hk z).1 hz, ?_⟩
  rw [← Matrix.mulVec_smul, ← e]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_sub,
    Units.val_mul, Units.mul_inv, mul_assoc, sub_mul, one_mul, mul_sub]

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem eventually_sub_one_mulVec {C V : Set (n → A)} (hC : IsCompact C) (hV : V ∈ 𝓝 (0 : n → A)) :
    ∀ᶠ m : Matrix n n A in 𝓝 1, ∀ y ∈ C, (m - 1) *ᵥ y ∈ V := by
  refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
  have hc : Continuous fun p : Matrix n n A × (n → A) => (p.1 - 1) *ᵥ p.2 :=
    (continuous_fst.sub continuous_const).matrix_mulVec continuous_snd
  refine hc.continuousAt.preimage_mem_nhds ?_
  simpa using hV

theorem smul_mem_nhds {Λ : Submodule S (n → A)} (ho : IsOpen (Λ : Set (n → A))) {a : A}
    (ha : IsUnit a) : {w | ∃ z ∈ Λ, w = a • z} ∈ 𝓝 (0 : n → A) := by
  obtain ⟨u, rfl⟩ := ha
  have hc : Continuous fun w : n → A => ((u⁻¹ : Aˣ) : A) • w := continuous_const_smul _
  refine mem_of_superset ((ho.preimage hc).mem_nhds (by simp)) fun w hw => ⟨_, hw, ?_⟩
  rw [smul_smul, Units.mul_inv, one_smul]

theorem isOpen_cong {Λ : Submodule S (n → A)} (ho : IsOpen (Λ : Set (n → A)))
    (hc : IsCompact (Λ : Set (n → A))) {a : A} (ha : IsUnit a) :
    IsOpen (cong Λ a : Set (GL n A)) := by
  have h0 : (Λ : Set (n → A)) ∈ 𝓝 (0 : n → A) := ho.mem_nhds (zero_mem _)
  have t1 : Tendsto (fun x : GL n A => (x : Matrix n n A)) (𝓝 1) (𝓝 1) :=
    Units.continuous_val.tendsto' _ _ rfl
  have t2 : Tendsto (fun x : GL n A => ((x⁻¹ : GL n A) : Matrix n n A)) (𝓝 1) (𝓝 1) :=
    Units.continuous_coe_inv.tendsto' _ _ (by simp)
  refine (cong Λ a).isOpen_of_mem_nhds (g := 1) ?_
  filter_upwards [t1.eventually (eventually_sub_one_mulVec hc h0),
    t2.eventually (eventually_sub_one_mulVec hc h0),
    t1.eventually (eventually_sub_one_mulVec hc (smul_mem_nhds ho ha))] with x h1 h2 h3
  refine ⟨fun y => ⟨fun hy => ?_, fun hy => ?_⟩, h3⟩
  · have := add_mem (h1 y hy) hy
    simpa [Matrix.sub_mulVec] using this
  · have := add_mem (h2 _ hy) hy
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel, Matrix.mulVec_mulVec, Units.inv_mul,
      Matrix.one_mulVec] at this

theorem isOpen_stab {Λ : Submodule S (n → A)} (ho : IsOpen (Λ : Set (n → A)))
    (hc : IsCompact (Λ : Set (n → A))) : IsOpen (Formalism.UG.stabGL Λ : Set (GL n A)) :=
  Subgroup.isOpen_mono (H₁ := cong Λ 1) (fun _ h => h.1) (isOpen_cong ho hc isUnit_one)

omit [Fintype n] in

theorem isCompact_cols {C : Set (n → A)} (hC : IsCompact C) (u : Aˣ) :
    IsCompact {m : Matrix n n A | ∀ j, (fun i => (u : A) * m i j) ∈ C} := by
  have hc : Continuous fun p : n → n → A => (Matrix.of fun i j => ((u⁻¹ : Aˣ) : A) * p j i) :=
    continuous_matrix fun i j => continuous_const.mul (continuous_apply_apply j i)
  convert (isCompact_univ_pi fun _ : n => hC).image hc using 1
  ext m
  constructor
  · intro h
    exact ⟨fun j i => u * m i j, fun j _ => h j, by ext i j; simp⟩
  · rintro ⟨p, hp, rfl⟩ j
    simpa using hp j trivial

theorem isCompact_stab [T2Space A] {Λ : Submodule S (n → A)} (ho : IsOpen (Λ : Set (n → A)))
    (hc : IsCompact (Λ : Set (n → A))) (u : Aˣ) (hu : ∀ j, (Pi.single j (u : A) : n → A) ∈ Λ) :
    IsCompact (Formalism.UG.stabGL Λ : Set (GL n A)) := by
  have h := isCompact_cols hc u
  have h2 := (Units.isClosedEmbedding_embedProduct (α := Matrix n n A)).isCompact_preimage
    (h.prod (h.image MulOpposite.continuous_op))
  have key : ∀ x ∈ Formalism.UG.stabGL Λ, ∀ j, (fun i => (u : A) * (x : Matrix n n A) i j) ∈ Λ := by
    intro x hx j
    convert (hx _).1 (hu j) using 1
    funext i
    simp [mul_comm]
  refine h2.of_isClosed_subset ((Formalism.UG.stabGL Λ).isClosed_of_isOpen (isOpen_stab ho hc)) ?_
  intro x hx
  exact ⟨key x hx, _, key _ (inv_mem hx), rfl⟩

theorem eventually_cong_subset {Λ : Submodule S (n → A)}
    (hc : IsCompact (Λ : Set (n → A))) (u : Aˣ) (hu : ∀ j, (Pi.single j (u : A) : n → A) ∈ Λ)
    {W : Set (GL n A)} (hW : W ∈ 𝓝 1) : ∀ᶠ a : A in 𝓝 0, (cong Λ a : Set (GL n A)) ⊆ W := by
  rw [(Units.isEmbedding_embedProduct (M := Matrix n n A)).isInducing.nhds_eq_comap, mem_comap] at hW
  obtain ⟨T, hT, hTW⟩ := hW
  rw [show Units.embedProduct (Matrix n n A) 1 = (1, MulOpposite.op 1) from rfl, mem_nhds_prod_iff] at hT
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := hT
  have hV₃ : V₁ ∩ MulOpposite.op ⁻¹' V₂ ∈ 𝓝 (1 : Matrix n n A) :=
    inter_mem hV₁ (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hV₂)
  have h : ∀ᶠ a : A in 𝓝 0, ∀ m ∈ {m : Matrix n n A | ∀ j, (fun i => (u : A) * m i j) ∈ (Λ : Set _)},
      1 + a • m ∈ V₁ ∩ MulOpposite.op ⁻¹' V₂ := by
    refine (isCompact_cols hc u).eventually_forall_of_forall_eventually fun m _ => ?_
    have hc : Continuous fun p : A × Matrix n n A => 1 + p.1 • p.2 :=
      continuous_const.add (continuous_fst.smul continuous_snd)
    refine hc.continuousAt.preimage_mem_nhds ?_
    simpa using hV₃
  filter_upwards [h] with a ha
  have key : ∀ x ∈ cong Λ a, (x : Matrix n n A) ∈ V₁ ∩ MulOpposite.op ⁻¹' V₂ := by
    intro x hx
    choose z hz e using fun j => hx.2 _ (hu j)
    have := ha (Matrix.of fun i j => ((u⁻¹ : Aˣ) : A) * z j i) fun j => by simpa using hz j
    convert this using 1
    rw [← sub_eq_iff_eq_add']
    ext i j
    have e1 := congrFun (e j) i
    simp only [Matrix.mulVec_single, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, Matrix.col_apply] at e1
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_left_comm, ← e1, mul_comm, Units.mul_inv_cancel_right]
  intro x hx
  exact hTW (hV ⟨(key x hx).1, (key _ (inv_mem hx)).2⟩)

theorem top_eq {Λ : Submodule S (n → A)} (ho : IsOpen (Λ : Set (n → A)))
    (hc : IsCompact (Λ : Set (n → A))) (u : Aˣ) (hu : ∀ j, (Pi.single j (u : A) : n → A) ∈ Λ)
    (hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : A)) (h0 : ∀ W ∈ 𝓝 (0 : A), ∃ g : ℕ, 1 ≤ g ∧ (g : A) ∈ W)
    (U : Subgroup (GL n A)) (t : TopologicalSpace U) (ht : @IsTopologicalGroup U t _)
    (h1 : ∀ g : ℕ, 1 ≤ g → IsOpen[t] {x : U | (x : GL n A) ∈ cong Λ g})
    (h2 : ∀ W ∈ @nhds U t 1, ∃ g : ℕ, 1 ≤ g ∧ {x : U | (x : GL n A) ∈ cong Λ g} ⊆ W) :
    t = instTopologicalSpaceSubtype := by
  refine @IsTopologicalGroup.ext U _ t instTopologicalSpaceSubtype ht
    (Subgroup.instIsTopologicalGroupSubtypeMem U) (le_antisymm ?_ ?_)
  · intro W hW
    obtain ⟨V, hV, hVW⟩ := (mem_nhds_subtype _ _ _).1 hW
    obtain ⟨g, hg, hgV⟩ := h0 _ (eventually_cong_subset hc u hu hV)
    exact mem_of_superset (@IsOpen.mem_nhds _ t _ _ (h1 g hg) (one_mem (cong Λ g))) fun x hx => hVW (hgV hx)
  · intro W hW
    obtain ⟨g, hg, hgW⟩ := h2 W hW
    exact (mem_nhds_subtype _ _ _).2 ⟨_, (isOpen_cong ho hc (hun g hg)).mem_nhds (one_mem (cong Λ g)), hgW⟩

theorem isOpen_isCompact_of_bounds (R : Subring A) (ho : IsOpen (R : Set A)) (hc : IsCompact (R : Set A))
    (Λ : Submodule S (n → A)) (u v : Aˣ)
    (hu : ∀ w : n → A, (∀ i, w i ∈ R) → (fun i => (u : A) * w i) ∈ Λ)
    (hv : ∀ w ∈ Λ, ∀ i, (v : A) * w i ∈ R) :
    IsOpen (Λ : Set (n → A)) ∧ IsCompact (Λ : Set (n → A)) := by
  have c : ∀ a : A, Continuous fun w : n → A => fun i => a * w i := fun a =>
    continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have h1 : IsOpen (Λ : Set (n → A)) := by
    have hp : IsOpen (Set.pi Set.univ fun _ : n => (R : Set A)) :=
      isOpen_set_pi Set.finite_univ fun _ _ => ho
    refine Λ.toAddSubgroup.isOpen_of_mem_nhds (g := 0) (mem_of_superset
      ((hp.preimage (c ((u⁻¹ : Aˣ) : A))).mem_nhds fun i _ => by simp) fun w hw => ?_)
    simpa using hu _ fun i => hw i trivial
  refine ⟨h1, ((isCompact_univ_pi fun _ : n => hc).image (c ((v⁻¹ : Aˣ) : A))).of_isClosed_subset
    (Λ.toAddSubgroup.isClosed_of_isOpen h1) fun w hw => ⟨_, fun i _ => hv w hw i, by simp⟩⟩

theorem properties [T2Space A] [SecondCountableTopology A]
    (R : Subring A) (ho : IsOpen (R : Set A)) (hc : IsCompact (R : Set A))
    (Λ : Submodule S (n → A)) (u v : A) (hu' : IsUnit u) (hv' : IsUnit v)
    (hu : ∀ w : n → A, (∀ i, w i ∈ R) → (fun i => u * w i) ∈ Λ)
    (hv : ∀ w ∈ Λ, ∀ i, v * w i ∈ R)
    (hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : A)) (h0 : ∀ W ∈ 𝓝 (0 : A), ∃ g : ℕ, 1 ≤ g ∧ (g : A) ∈ W)
    (σ : A →+* A) (hσ : Continuous σ) (J : Matrix n n A)
    [t : TopologicalSpace (Formalism.UG.UJ σ J)] [ht : IsTopologicalGroup (Formalism.UG.UJ σ J)]
    (h1 : ∀ g : ℕ, 1 ≤ g → IsOpen {x : Formalism.UG.UJ σ J | (x : GL n A) ∈ cong Λ g})
    (h2 : ∀ W ∈ 𝓝 (1 : Formalism.UG.UJ σ J), ∃ g : ℕ, 1 ≤ g ∧ {x : Formalism.UG.UJ σ J | (x : GL n A) ∈ cong Λ g} ⊆ W) :
    T2Space (Formalism.UG.UJ σ J) ∧ LocallyCompactSpace (Formalism.UG.UJ σ J) ∧ SecondCountableTopology (Formalism.UG.UJ σ J) ∧
      IsCompact {x : Formalism.UG.UJ σ J | (x : GL n A) ∈ Formalism.UG.stabGL Λ} ∧
      IsOpen {x : Formalism.UG.UJ σ J | (x : GL n A) ∈ Formalism.UG.stabGL Λ} := by
  obtain ⟨u, rfl⟩ := hu'
  obtain ⟨v, rfl⟩ := hv'
  obtain ⟨hΛo, hΛc⟩ := isOpen_isCompact_of_bounds R ho hc Λ u v hu hv
  have hsing : ∀ j, (Pi.single j (u : A) : n → A) ∈ Λ := fun j => by
    convert hu (Pi.single j 1) fun i => ?_ using 1
    · funext i
      by_cases h : i = j <;> simp [h]
    · rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
  have htop := top_eq hΛo hΛc u hsing hun h0 _ t ht h1 h2
  subst htop
  have hcl : IsClosed (Formalism.UG.UJ σ J : Set (GL n A)) := by
    have hv : Continuous fun g : GL n A => (g : Matrix n n A) := Units.continuous_val
    exact isClosed_eq (((hv.matrix_map hσ).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hemb : IsClosedEmbedding (Subtype.val : Formalism.UG.UJ σ J → GL n A) := hcl.isClosedEmbedding_subtypeVal
  haveI : SecondCountableTopology (Matrix n n A) := inferInstanceAs (SecondCountableTopology (n → n → A))
  haveI : SecondCountableTopology (Matrix n n A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL n A) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL n A) := Units.isEmbedding_embedProduct.t2Space
  have hKc := hemb.isCompact_preimage (isCompact_stab hΛo hΛc u hsing)
  have hKo := (isOpen_stab hΛo hΛc).preimage hemb.continuous
  exact ⟨hemb.isEmbedding.t2Space,
    hKc.locallyCompactSpace_of_mem_nhds_of_group (hKo.mem_nhds (x := 1) (one_mem (Formalism.UG.stabGL Λ))),
    hemb.isEmbedding.secondCountableTopology, hKc, hKo⟩

end Abstract

section Adeles

open Formalism.UG Formalism.UG.P

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mem_nhds (W : Set (Af F)) (hW : W ∈ 𝓝 (0 : Af F)) : ∃ g : ℕ, 1 ≤ g ∧ (g : Af F) ∈ W := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have hC := GlobalTheory.AdeleCocompact.isCompact_integral F
  obtain ⟨V, hVW, hV, h0⟩ := mem_nhds_iff.1 hW
  let T : ℕ → Set (Af F) := fun k => (fun a => k.factorial • a) ''
    {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hT : ∀ k, IsCompact (T k) := fun k => hC.image (continuous_const_smul _)
  have hdvd : ∀ N k : ℕ, N ∣ k.factorial → ∀ y ∈ T k, ∃ a : Af F,
      (∀ v, a v ∈ v.adicCompletionIntegers F) ∧ y = N • a := by
    rintro N k ⟨c, hc⟩ _ ⟨a, ha, rfl⟩
    exact ⟨c • a, nsmul_mem (S := intAd F) ha c, by simp only [hc, mul_smul]⟩
  have hanti : Antitone T := fun k l hkl y hy => by
    obtain ⟨a, ha, e⟩ := hdvd _ l (Nat.factorial_dvd_factorial hkl) y hy
    exact ⟨a, ha, e.symm⟩
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact' (V := T) hanti.directed_ge hT
    (fun k => (hT k).isClosed) (U := V) (by
      refine fun y hy => hV.mem_nhds ?_
      have := (GlobalTheory.AdLat.integral_finiteAdele_complete_separated F).1 y fun N hN =>
        hdvd N N (Nat.dvd_factorial hN le_rfl) y (Set.mem_iInter.1 hy N)
      rwa [this])
  exact ⟨k.factorial, k.factorial_pos, hVW (hk ⟨1, one_mem (intAd F), by simp⟩)⟩

theorem exists_topology (σ : E →ₐ[F] E) : ∃ t : TopologicalSpace (E ⊗[F] Af F),
    IsTopologicalRing (E ⊗[F] Af F) ∧ T2Space (E ⊗[F] Af F) ∧ SecondCountableTopology (E ⊗[F] Af F) ∧
    IsOpen (IntAf F E : Set (E ⊗[F] Af F)) ∧ IsCompact (IntAf F E : Set (E ⊗[F] Af F)) ∧
    Continuous (sigR σ (Af F)) ∧
    ∀ W ∈ 𝓝 (0 : E ⊗[F] Af F), ∃ g : ℕ, 1 ≤ g ∧ (g : E ⊗[F] Af F) ∈ W := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  letI : Algebra (Af F) (E ⊗[F] Af F) := Algebra.TensorProduct.rightAlgebra
  let e : (Fin (Module.finrank F E) → Af F) ≃ₗ[Af F] E ⊗[F] Af F :=
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun.symm.trans
      (Algebra.TensorProduct.commRight F (Af F) E).toLinearEquiv
  haveI : Module.Finite (Af F) (E ⊗[F] Af F) := Module.Finite.equiv e
  letI t : TopologicalSpace (E ⊗[F] Af F) := moduleTopology (Af F) (E ⊗[F] Af F)
  haveI : IsModuleTopology (Af F) (E ⊗[F] Af F) := ⟨rfl⟩
  haveI : IsTopologicalRing (E ⊗[F] Af F) := IsModuleTopology.isTopologicalRing (Af F) _
  let h : (E ⊗[F] Af F) ≃ₜ (Fin (Module.finrank F E) → Af F) :=
    { e.symm.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap }
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  let φ : (Fin m → Af F) →ₗ[Af F] E ⊗[F] Af F :=
    Fintype.linearCombination (Af F) fun j => algebraMap (𝓞 E) E (b j) ⊗ₜ[F] (1 : Af F)
  have hsm : ∀ (r : Af F) (x : E ⊗[F] Af F), r • x = ((1 : E) ⊗ₜ[F] r) * x := fun r x => rfl
  have hφ : ∀ r, φ r = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j := fun r => by
    simp [φ, Fintype.linearCombination_apply, hsm]
  have him : (IntAf F E : Set (E ⊗[F] Af F)) = φ '' Set.pi Set.univ fun _ => (intAd F : Set (Af F)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨r, hr, e⟩ := levelaf_decomp b hb hs
      exact ⟨r, fun j _ => hr j, (hφ r).trans e.symm⟩
    · rintro ⟨r, hr, rfl⟩
      rw [hφ]
      exact sum_mem fun j _ => levelaf_tmul_mem _ (hr j trivial)
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨d, hd, hx⟩ := levelaf_denom x
    have hx' : levelafC E d * x ∈ (IntAf F E : Set (E ⊗[F] Af F)) := hx
    rw [him] at hx'
    obtain ⟨r, -, hr⟩ := hx'
    refine ⟨algebraMap F (Af F) (algebraMap (𝓞 F) F d)⁻¹ • r, ?_⟩
    have hd' : algebraMap (𝓞 F) F d ≠ 0 := by simpa using hd
    rw [map_smul, hr, hsm, levelafC, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      IsScalarTower.algebraMap_apply (𝓞 F) F (Af F), ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  have hio : IsOpen (intAd F : Set (Af F)) :=
    RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      fun _ => Valued.isOpen_valuationSubring _
  refine ⟨t, inferInstance, h.isEmbedding.t2Space, h.secondCountableTopology, ?_, ?_, ?_, fun W hW => ?_⟩
  · rw [him]
    exact IsModuleTopology.isOpenMap_of_surjective hsurj _ (isOpen_set_pi Set.finite_univ fun _ _ => hio)
  · rw [him]
    exact (isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F).image
      (IsModuleTopology.continuous_of_linearMap φ)
  · let s : E ⊗[F] Af F →ₗ[Af F] E ⊗[F] Af F :=
      { toFun := sigR σ (Af F)
        map_add' := map_add _
        map_smul' := fun r x => by
          rw [RingHom.id_apply, hsm, hsm, map_mul]
          congr 1
          simp [sigR] }
    exact IsModuleTopology.continuous_of_linearMap s
  · have hc : Continuous (algebraMap (Af F) (E ⊗[F] Af F)) :=
      IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Af F) (E ⊗[F] Af F))
    obtain ⟨g, hg, hgW⟩ := exists_nat_mem_nhds F _ (hc.continuousAt.preimage_mem_nhds (by rwa [map_zero]))
    exact ⟨g, hg, by simpa using hgW⟩

theorem isUnit_levelafC {d : 𝓞 F} (hd : d ≠ 0) : IsUnit (levelafC (F := F) E d) := by
  have hd' : algebraMap (𝓞 F) E d ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F E]
    simpa using hd
  rw [← adelstab_incl_C]
  exact hd'.isUnit.map _

end Adeles

theorem adelic_topology : ∀ I : AutInst, T2Space I.Gf ∧ LocallyCompactSpace I.Gf ∧ SecondCountableTopology I.Gf ∧ IsCompact I.Kset ∧ IsOpen I.Kset ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kset) ∧ ∀ g : ℕ, 1 ≤ g → IsOpen (I.Kg g) ∧ (∃ K : Subgroup I.Gf, (K : Set I.Gf) = I.Kg g) ∧ ∀ k ∈ I.Kset, ∀ x ∈ I.Kg g, k * x * k⁻¹ ∈ I.Kg g := by
  intro I
  obtain ⟨t, hr, h2, hsc, ho, hc, hσ, h0⟩ := exists_topology I.F I.E I.cm.sig
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  obtain ⟨c, hc0, hlow⟩ := Formalism.UG.P.adelstabL_lower (F := I.F) I.L I.L_span
  obtain ⟨d, hd0, hup⟩ := Formalism.UG.P.adelstabL_upper (F := I.F) I.L (Module.Finite.iff_fg.2 I.L_fg)
  rw [← hL] at hlow hup
  have hun : ∀ g : ℕ, 1 ≤ g → IsUnit (g : I.E ⊗[I.F] Af I.F) := fun g hg => by
    have : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have := this.isUnit.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rwa [map_natCast] at this
  obtain ⟨a1, a2, a3, a4, a5⟩ := properties (IntAf I.F I.E) ho hc I.Lf _ _ (isUnit_levelafC I.F I.E hc0)
    (isUnit_levelafC I.F I.E hd0) hlow hup hun h0 _ hσ (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (t := I.topf) (ht := I.topf_group) I.topf_open I.topf_basis
  exact ⟨a1, a2, a3, a4, a5, ⟨(Formalism.UG.stabGL I.Lf).subgroupOf _, rfl⟩, fun g hg => ⟨I.topf_open g hg,
      ⟨(cong I.Lf (g : I.E ⊗[I.F] Af I.F)).subgroupOf _, rfl⟩, fun k hk x hx =>
      conj_mem_cong (Λ := I.Lf) (a := (g : I.E ⊗[I.F] Af I.F)) hk hx⟩⟩

end GlobalTheory.CongTop
