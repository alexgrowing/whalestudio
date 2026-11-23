import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.LeftInvOfJac
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem fss_scalar {k E M : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [AddCommGroup M]
    [Module k M] [Module E M] [IsScalarTower k E M] [IsSimpleModule E M]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ aeval x p = 0) (φ : Module.End E M) : ∃ c : k, ∀ v, φ v = c • v := by
  haveI := IsSimpleModule.nontrivial E M
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  obtain ⟨r, hr⟩ := IsSimpleModule.toSpanSingleton_surjective E hv (φ v)
  replace hr : r • v = φ v := hr
  obtain ⟨p, hp, hp0⟩ := h r
  by_contra hne
  push Not at hne
  have key : ∀ s : Multiset k, aeval r (s.map fun a => X - C a).prod • v ≠ 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simpa using hv
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul, mul_smul]
      set q := aeval r (s.map fun a => X - C a).prod
      let ψ : Module.End E M := φ - a • (1 : Module.End E M)
      have h1 : aeval r (X - C a) • v = ψ v := by simp [ψ, sub_smul, hr]
      rw [h1, ← map_smul]
      rcases LinearMap.bijective_or_eq_zero ψ with hb | hb
      · exact fun h0 => ih (hb.1 (h0.trans (map_zero ψ).symm))
      · obtain ⟨w, hw⟩ := hne a
        have := LinearMap.congr_fun hb w
        simp only [ψ, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, LinearMap.zero_apply] at this
        exact absurd (sub_eq_zero.1 this) hw
  have := key p.roots
  rw [← (IsAlgClosed.splits p).eq_prod_roots_of_monic hp, hp0, zero_smul] at this
  exact this rfl

private theorem fss_fin {n : ℕ} {k E M : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] [AddCommGroup M]
    [Module k M] [Module E M] [IsScalarTower k E M] [IsSimpleModule E M]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) : Module.Finite k M := by
  classical
  let b := Module.Basis.ofVectorSpace k M
  rcases finite_or_infinite (Module.Basis.ofVectorSpaceIndex k M) with hf | hf
  · exact Module.Finite.of_basis b
  exfalso
  let e := Infinite.natEmbedding (Module.Basis.ofVectorSpaceIndex k M)
  let f : M →ₗ[k] M := b.constr k fun i => b (e (Function.invFun e i + 1))
  have hfe : ∀ i, f (b (e i)) = b (e (i + 1)) := fun i => by
    simp only [f, Module.Basis.constr_basis]
    rw [Function.leftInverse_invFun e.injective i]
  let F : Module.End (Module.End E M) M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := fss_scalar (k := k) (fun x => (h x).imp fun p hp => ⟨hp.1, hp.2.2⟩) φ
        simp [hc] }
  obtain ⟨r, hr⟩ := jacobson_density F ((Finset.range n).image fun i => b (e i))
  have hr' : ∀ i ≤ n, r ^ i • b (e 0) = b (e i) := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', mul_smul, ih (by omega), ← hfe]
      exact (hr _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))).symm
  obtain ⟨p, hp, hpn, hp0⟩ := h r
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • b (e i) = 0 := by
    have := congrArg (· • b (e 0)) hp0
    simp only [aeval_eq_sum_range, zero_smul, Finset.sum_smul, smul_assoc] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hr' i (by have := Finset.mem_range.1 hi; omega)]
  have h2 := linearIndependent_iff'.1 (b.linearIndependent.comp e e.injective) _ _ h1 p.natDegree (by simp)
  rw [hp.coeff_natDegree] at h2
  exact one_ne_zero h2

private theorem fss_count {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) (m : ℕ → Ideal E)
    (hm : ∀ i, IsCoatom (m i)) (hinj : Function.Injective fun i => Module.annihilator E (E ⧸ m i)) : False := by
  classical
  haveI : ∀ i, IsSimpleModule E (E ⧸ m i) := fun i => isSimpleModule_iff_isCoatom.2 (hm i)
  let a : ℕ ↪ k := Infinite.natEmbedding k
  let M := ∀ i : Fin (n + 1), E ⧸ m i
  have hz : ∀ (φ : Module.End E M) (i j : Fin (n + 1)) (x : E ⧸ m i), i ≠ j → φ (Pi.single i x) j = 0 := by
    intro φ i j x hij
    rcases LinearMap.bijective_or_eq_zero ((LinearMap.proj j).comp (φ.comp
      (LinearMap.single E (fun i : Fin (n + 1) => E ⧸ m i) i))) with hb | hb
    · exact absurd (Fin.ext (hinj (LinearEquiv.ofBijective _ hb).annihilator_eq)) hij
    · exact LinearMap.congr_fun hb x
  let F : Module.End (Module.End E M) M :=
    { toFun := fun v j => algebraMap k E (a j) • v j
      map_add' := fun v w => funext fun j => smul_add _ _ _
      map_smul' := fun φ v => funext fun j => by
        have h1 : ∀ w : M, φ w j = φ (Pi.single j (w j)) j := fun w => by
          conv_lhs => rw [← Finset.univ_sum_single w, map_sum, Finset.sum_apply]
          exact Finset.sum_eq_single j (fun i _ hi => hz φ i j _ hi) (by simp)
        change algebraMap k E (a j) • φ v j = φ (fun j => algebraMap k E (a j) • v j) j
        rw [h1 v, h1 (fun j => algebraMap k E (a j) • v j), Pi.single_smul, map_smul]
        rfl }
  obtain ⟨r, hr⟩ := jacobson_density F {fun i => Submodule.Quotient.mk 1}
  replace hr := hr _ (Finset.mem_singleton_self _)
  obtain ⟨p, hp, hpn, hp0⟩ := h r
  have hroot : ∀ j : Fin (n + 1), p.eval (a j) = 0 := by
    intro j
    set v : E ⧸ m j := Submodule.Quotient.mk 1 with hv
    have h1 : r • v = a j • v := by
      rw [← algebraMap_smul E (a j) v]
      exact (congrFun hr j).symm
    have h2 : ∀ i : ℕ, r ^ i • v = a j ^ i • v := by
      intro i
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ, mul_smul, h1, smul_comm, ih, smul_smul, pow_succ']
    have h3 : aeval r p • v = p.eval (a j) • v := by
      simp only [aeval_eq_sum_range, eval_eq_sum_range, Finset.sum_smul, smul_assoc, h2, mul_smul]
    rw [hp0, zero_smul] at h3
    refine (smul_eq_zero.1 h3.symm).resolve_right fun h0 => (hm j).1 ?_
    exact (Ideal.eq_top_iff_one _).2 ((Submodule.Quotient.mk_eq_zero _).1 h0)
  refine hp.ne_zero (eq_zero_of_natDegree_lt_card_of_eval_eq_zero p (f := fun j : Fin (n + 1) => a j)
    (fun i j hij => Fin.ext (a.injective hij)) hroot ?_)
  simp only [Fintype.card_fin]
  omega

private theorem fss_alg {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E]
    (h : ∀ x : E, ∃ p : k[X], p.Monic ∧ p.natDegree ≤ n ∧ aeval x p = 0) (hj : Ring.jacobson E = ⊥) :
    Module.Finite k E := by
  let S : Set (Ideal E) := {P | ∃ m : Ideal E, IsCoatom m ∧ Module.annihilator E (E ⧸ m) = P}
  have hS : ∀ P : S, ∃ m : Ideal E, IsCoatom m ∧ Module.annihilator E (E ⧸ m) = P := fun P => P.2
  choose m hm hm' using hS
  haveI : Finite S := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    let e := Infinite.natEmbedding S
    refine fss_count h (fun i => m (e i)) (fun i => hm _) fun i j hij => e.injective (Subtype.ext ?_)
    rw [← hm', ← hm']
    exact hij
  haveI : ∀ P, IsSimpleModule E (E ⧸ m P) := fun i => isSimpleModule_iff_isCoatom.2 (hm i)
  haveI : ∀ P, Module.Finite k (E ⧸ m P) := fun i => fss_fin h
  let f : E →ₗ[k] ∀ P : S, Module.End k (E ⧸ m P) :=
    LinearMap.pi fun P => (Algebra.lsmul k k (E ⧸ m P) (A := E)).toLinearMap
  refine Module.Finite.of_injective f ((injective_iff_map_eq_zero f).2 fun x hx => ?_)
  rw [← Ideal.mem_bot, ← hj]
  refine Submodule.mem_sInf.2 fun I hI => ?_
  have h1 : x ∈ Module.annihilator E (E ⧸ m ⟨_, I, hI, rfl⟩) :=
    Module.mem_annihilator.2 fun v => LinearMap.congr_fun (congrFun hx ⟨_, I, hI, rfl⟩) v
  rw [hm'] at h1
  have h2 := Module.mem_annihilator.1 h1 (Submodule.Quotient.mk 1)
  rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at h2
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem UpperTheory.V.CA.d_faithful_ss :
    ∀ {n : ℕ} {k E : Type} [Field k] [IsAlgClosed k] [Ring E] [Algebra k E] (D : Det n k E), D.ker = ⊥ → Module.Finite k E ∧ IsSemisimpleRing E := by
  intro n k E _ _ _ _ D hD
  have hCH : D.IsCH := le_bot_iff.1 (hD ▸ d_ch_ker D)
  have hj : Ring.jacobson E = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have h1 := (d_ker _ _).1.1 ((d_rad D hCH x).2 hx)
    have h2 : D.Kills x := by
      intro S _ _ y
      letI : Algebra (ResidueField k) S :=
        (Ideal.Quotient.lift (maximalIdeal k) (algebraMap k S) fun a ha => by
          rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha
          rw [ha, map_zero]).toAlgebra
      haveI : IsScalarTower k (ResidueField k) S := .of_algebraMap_eq fun _ => rfl
      obtain ⟨z, rfl⟩ : ∃ z, Det.cancel k E (ResidueField k) S z = y := by
        induction y with
        | zero => exact ⟨0, map_zero _⟩
        | tmul s e => exact ⟨s ⊗ₜ (1 ⊗ₜ e), by simp [Det.cancel_tmul]⟩
        | add a b ha hb =>
          obtain ⟨a, rfl⟩ := ha
          obtain ⟨b, rfl⟩ := hb
          exact ⟨a + b, map_add _ _ _⟩
      have h3 := h1 S z
      rw [(d_bc D (ResidueField k)).1] at h3
      simpa [Det.cancel_tmul] using h3
    have h4 := (d_ker D x).1.2 h2
    rw [hD] at h4
    simpa using h4
  haveI := fss_alg (n := n) (k := k) (E := E)
    (fun x => ⟨D.chi x, (d_chi D x).2.2.2.2.1, (d_chi D x).2.2.2.2.2.1, ((d_chS D k).2.2 hCH).2 x⟩) hj
  haveI : IsArtinianRing E := IsArtinianRing.of_finite k E
  exact ⟨inferInstance, IsArtinianRing.isSemisimpleRing_iff_jacobson.2 hj⟩
