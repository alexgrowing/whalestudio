import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring

noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.TypesInhab

section Tensor

variable {I : Type} [Fintype I] {Γ : I → Type} [∀ i, Group (Γ i)] [∀ i, Finite (Γ i)]

def ten (x : ∀ i, MonoidAlgebra ℂ (Γ i)) : MonoidAlgebra ℂ (∀ i, Γ i) :=
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g => ∏ i, (x i).coeff (g i)

theorem coeff_ten (x : ∀ i, MonoidAlgebra ℂ (Γ i)) (g : ∀ i, Γ i) :
    (ten x).coeff g = ∏ i, (x i).coeff (g i) := rfl

theorem coeff_mul_sum {Δ : Type} [Group Δ] [Fintype Δ] (x y : MonoidAlgebra ℂ Δ) (g : Δ) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  simp

theorem ten_mul (x y : ∀ i, MonoidAlgebra ℂ (Γ i)) : ten x * ten y = ten fun i => x i * y i := by
  classical
  haveI := fun i => Fintype.ofFinite (Γ i)
  ext g
  simp only [coeff_mul_sum, coeff_ten]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.prod_mul_distrib]
  rfl

theorem ten_single (g : ∀ i, Γ i) :
    ten (fun i => MonoidAlgebra.single (g i) (1 : ℂ)) = MonoidAlgebra.single g 1 := by
  classical
  ext h
  rw [coeff_ten]
  by_cases hh : g = h
  · subst hh; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hh
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
    simp [hh]

theorem ten_central (x : ∀ i, MonoidAlgebra ℂ (Γ i)) (hx : ∀ i a, x i * a = a * x i) :
    ten x ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, Γ i)) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of g => simp only [MonoidAlgebra.of_apply, ← ten_single, ten_mul, hx]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]
  | smul c a ha => rw [smul_mul_assoc, mul_smul_comm, ha]

theorem ten_eq_zero {x : ∀ i, MonoidAlgebra ℂ (Γ i)} {i : I} (h : x i = 0) : ten x = 0 := by
  ext g
  rw [coeff_ten, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])]
  simp

theorem ten_ne_zero {x : ∀ i, MonoidAlgebra ℂ (Γ i)} (h : ∀ i, x i ≠ 0) : ten x ≠ 0 := by
  have h1 : ∀ i, ∃ g, (x i).coeff g ≠ 0 := by
    intro i
    by_contra hh
    push Not at hh
    exact h i (by ext g; simp [hh g])
  choose g hg using h1
  intro h0
  have h2 := coeff_ten x g
  rw [h0] at h2
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hg i) (by simpa using h2.symm)

end Tensor

theorem exists_char {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] (z : Subalgebra.center ℂ A) {t : A}
    (ht : t ≠ 0) (h : (z : A) * t = 0) : ∃ ω : Subalgebra.center ℂ A →ₐ[ℂ] ℂ, ω z = 0 := by
  have hz : Ideal.span {z} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨u, hu⟩ := hu.exists_left_inv
    have h1 : (u : A) * z = 1 := congrArg Subtype.val hu
    apply ht
    rw [← one_mul t, ← h1, mul_assoc, h, mul_zero]
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hz
  letI := Ideal.Quotient.field M
  haveI : Module.Finite ℂ (Subalgebra.center ℂ A) :=
    Module.Finite.of_injective (Subalgebra.center ℂ A).val.toLinearMap Subtype.val_injective
  haveI : Module.Finite ℂ (Subalgebra.center ℂ A ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℂ M).toLinearMap (Ideal.Quotient.mkₐ_surjective ℂ M)
  let l : (Subalgebra.center ℂ A ⧸ M) →ₐ[ℂ] ℂ := IsAlgClosed.lift
  refine ⟨l.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  exact (congrArg l (Ideal.Quotient.eq_zero_iff_mem.2 (hle (Ideal.mem_span_singleton_self z)))).trans (map_zero l)

def twoChar {Z A : Type} [Ring Z] [Algebra ℂ Z] [Ring A] [Algebra ℂ A] (ω₁ ω₀ : Z →ₐ[ℂ] ℂ) (e : A)
    (he : e * e = e) : Z →ₐ[ℂ] A where
  toFun z := ω₁ z • e + ω₀ z • (1 - e)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, add_mul, mul_add, smul_mul_smul_comm, mul_sub, sub_mul, mul_one, one_mul, he, sub_self,
      smul_zero, add_zero, zero_add, sub_zero]
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add, add_smul]
    abel
  commutes' c := by
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, ← smul_add, add_sub_cancel,
      Algebra.algebraMap_eq_smul_one]

theorem twoChar_apply {Z A : Type} [Ring Z] [Algebra ℂ Z] [Ring A] [Algebra ℂ A] (ω₁ ω₀ : Z →ₐ[ℂ] ℂ) (e : A)
    (he : e * e = e) (z : Z) : twoChar ω₁ ω₀ e he z = ω₁ z • e + ω₀ z • (1 - e) := rfl

open Classical in

theorem good_sum {I : Type} [Fintype I] {Γ : I → Type} [∀ i, Group (Γ i)] [∀ i, Finite (Γ i)]
    {P : I → Type} [∀ i, Finite (P i)] (E : ∀ i, P i → MonoidAlgebra ℂ (Γ i)) (good : (∀ i, P i) → Prop)
    (e : MonoidAlgebra ℂ (∀ i, Γ i))
    (he : ∀ g, e.coeff g = ∑ᶠ a, if good a then ∏ i, (E i (a i)).coeff (g i) else 0)
    (h1 : ∀ i p, E i p * E i p = E i p) (h2 : ∀ i p a, E i p * a = a * E i p)
    (h3 : ∀ i p q, p ≠ q → E i p * E i q = 0) :
    e ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ i, Γ i)) ∧
      ∀ a : ∀ i, P i, e * ten (fun i => E i (a i)) = if good a then ten (fun i => E i (a i)) else 0 := by
  haveI := Fintype.ofFinite (∀ i, P i)
  have h : e = ∑ a : ∀ i, P i, if good a then ten (fun i => E i (a i)) else 0 := by
    ext g
    rw [he, finsum_eq_sum_of_fintype, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs
    · rfl
    · rfl
  refine ⟨?_, fun a => ?_⟩
  · rw [h]
    refine sum_mem fun a _ => ?_
    split_ifs
    · exact ten_central _ fun i => h2 i _
    · exact zero_mem _
  · rw [h, Finset.sum_mul, Finset.sum_eq_single a]
    · split_ifs
      · simp only [ten_mul, h1]
      · rw [zero_mul]
    · intro b _ hb
      split_ifs
      · obtain ⟨i, hi⟩ := Function.ne_iff.1 hb
        rw [ten_mul]
        exact ten_eq_zero (i := i) (h3 i _ _ hi)
      · rw [zero_mul]
    · simp

section Types

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem goodTupleIdempotent_central_and_action (T : NTypes A) (hs : ∀ k f, f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0 → T.eSer k f ≠ 0) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) ∧
      ∀ f : ∀ k, N.PlG k → (ZMod (H.g k))[X], (∀ k v, (f k v).Monic ∧ (f k v).natDegree = R.r ∧ (f k v).coeff 0 ≠ 0) →
        ∃ t : MonoidAlgebra ℂ (G0g N), t ≠ 0 ∧ (T.goodTuple f → T.e0 * t = t) ∧ (¬ T.goodTuple f → T.e0 * t = 0) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (H.g k).Prime := fun k => ⟨H.g_prime k⟩
  obtain ⟨hc, hm⟩ := good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))
  refine ⟨hc, fun f hf => ?_⟩
  let a : ∀ kv : (Σ k : Fin 2, N.PlG k), Fin R.r → ZMod (H.g kv.1) := fun kv i => (f kv.1 kv.2).coeff i
  have ha : ∀ kv, Formalism.CyclotomicNorms.monicOf (a kv) = f kv.1 kv.2 := fun kv =>
    Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ (hf _ _).1 (hf _ _).2.1
  have ha' : (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) = f := by
    funext k v
    exact ha ⟨k, v⟩
  have := hm a
  rw [ha'] at this
  refine ⟨_, ten_ne_zero fun kv => ?_, fun h => this.trans (if_pos h), fun h => this.trans (if_neg h)⟩
  rw [ha]
  exact hs _ _ (hf _ _)

theorem not_good_unip (T : NTypes A) : ¬ T.goodTuple (fun _ _ => (X - 1) ^ R.r) := by
  intro h
  haveI : Fact (H.g 0).Prime := ⟨H.g_prime 0⟩
  have hne : Nonempty (N.PlG 0) := by
    rw [← Fintype.card_pos_iff, N.card_PlG]
    exact GaloisStage.f_pos R
  obtain ⟨v⟩ := hne
  have hf : Squarefree ((X - 1 : (ZMod (H.g 0))[X]) ^ R.r) := (h 0).1.2.1 v
  have h1 : IsUnit (X - 1 : (ZMod (H.g 0))[X]) :=
    hf _ (by rw [← sq]; exact pow_dvd_pow _ (GaloisStage.two_le_r R))
  have h2 := natDegree_eq_zero_of_isUnit h1
  have h3 := (GaloisStage.monic_unip (K := ZMod (H.g 0)) 1).2
  rw [pow_one] at h3
  omega

theorem exists_tie (T : NTypes A) (hs : ∀ k f, f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0 → T.eSer k f ≠ 0)
    (h : (∃ f, T.goodTuple f) ∨ ((∀ μ, what₂.eOp μ = 0) ∧ ∀ μ j, what₂.eMt μ j = 0)) :
    ∃ T' : NTypes A, T'.IdempotentMatchesAction ∧ T'.e0 = T.e0 := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (H.g k).Prime := fun k => ⟨H.g_prime k⟩
  obtain ⟨hc, hm⟩ := goodTupleIdempotent_central_and_action T hs
  obtain ⟨t, ht, -, ht0⟩ := hm (fun _ _ => (X - 1) ^ R.r) fun k _ =>
    ⟨(GaloisStage.monic_unip _).1, (GaloisStage.monic_unip _).2, GaloisStage.unip_coeff_zero _ _⟩
  obtain ⟨ω₀, h0⟩ := exists_char ⟨T.e0, hc⟩ ht (ht0 (not_good_unip T))
  obtain ⟨ω₁, h1, h2⟩ : ∃ ω₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] ℂ,
      (∀ μ, ω₁ ⟨T.e0, hc⟩ • what₂.eOp μ = what₂.eOp μ) ∧ ∀ μ j, ω₁ ⟨T.e0, hc⟩ • what₂.eMt μ j = what₂.eMt μ j := by
    rcases h with ⟨f, hf⟩ | ⟨h1, h2⟩
    · obtain ⟨s, hs0, hs1, -⟩ := hm f fun k v => (hf k).1.1 v
      obtain ⟨ω₁, h1⟩ := exists_char (1 - ⟨T.e0, hc⟩) hs0 (by
        change (1 - T.e0) * s = 0
        rw [sub_mul, one_mul, hs1 hf, sub_self])
      rw [map_sub, map_one, sub_eq_zero] at h1
      exact ⟨ω₁, fun μ => by rw [← h1, one_smul], fun μ j => by rw [← h1, one_smul]⟩
    · exact ⟨ω₀, fun μ => by rw [h1, smul_zero], fun μ j => by rw [h2, smul_zero]⟩
  let T' : NTypes A :=
    { T with
      cenAmb := fun μ => twoChar ω₁ ω₀ (what₂.eOp μ) (what₂.eOp_idem μ)
      cenMt := fun μ j => twoChar ω₁ ω₀ (what₂.eMt μ j) (what₂.eMt_idem μ j) }
  have he : T'.e0 = T.e0 := rfl
  refine ⟨T', ⟨fun μ => ?_, fun μ j => ?_⟩, he⟩
  · rw [he, NTypes.onAmb, dif_pos hc]
    change _ = twoChar ω₁ ω₀ (what₂.eOp μ) (what₂.eOp_idem μ) _
    rw [twoChar_apply, h0, zero_smul, add_zero]
    exact (h1 μ).symm
  · rw [he, NTypes.onMt, dif_pos hc]
    change _ = twoChar ω₁ ω₀ (what₂.eMt μ j) (what₂.eMt_idem μ j) _
    rw [twoChar_apply, h0, zero_smul, add_zero]
    exact (h2 μ j).symm

theorem goodTupleIdempotent_coeff_mem_subring (T : NTypes A) (S : Subring ℂ) (hS : ∀ k f x, (T.eSer k f).coeff x ∈ S) (x : G0g N) :
    T.e0.coeff x ∈ S := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  simp only [NTypes.e0, MonoidAlgebra.coeff_ofCoeff, Finsupp.coe_equivFunOnFinite_symm]
  refine finsum_induction (· ∈ S) (zero_mem S) (fun _ _ => add_mem) fun a => ?_
  split_ifs
  · exact prod_mem fun _ _ => hS _ _ _
  · exact zero_mem S

set_option synthInstance.maxHeartbeats 400000 in

def types0 [IsEmpty N.Loc] (hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p)
    (hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p)
    (hc : ∀ k, H.g k % (H.QS * H.q * H.d) = 1)
    (hB : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)))
    (tg : ∀ k, N.PlG k → G H.E N.Om) (htg : ∀ k v, TameGenAt (N.plOm.1 (A.plGw k v)) (tg k v))
    {n : ℕ} (e : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra ℂ (GL (Fin R.r) (ZMod (H.g k))))
    (he : ∀ k, IsSer R.r (H.g k) n (e k)) : NTypes A where
  Mray := H.K
  Mray_gal := inferInstance
  Mray_ab := fun σ τ => Subsingleton.elim _ _
  Mray_unr := fun p _ h => by
    rw [GaloisStage.discr_K, dvd_neg] at h
    exact Dvd.dvd.mul_left (by exact_mod_cast h) _
  g_Mray := fun k => GaloisStage.split_K H (H.g_prime k) (hc k)
  g_cond := hc
  BB_disj := hB
  bc := fun _ => {(R.r, 1)}
  bc_pos := fun _ p hp => by
    have := GaloisStage.two_le_r R
    rw [Multiset.mem_singleton.1 hp]
    exact ⟨by show 0 < R.r; omega, one_pos⟩
  bc_sum := fun _ => by simp
  rbar := fun _ _ => 1
  rbar_open := fun _ _ => by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  tg := tg
  tg_mem := fun k v => (htg k v).1
  tg_gen := htg
  iota := fun k _ w =>
    (@GaloisStage.exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose
  iota_inj := fun k _ w =>
    (@GaloisStage.exists_iota (H.g k) _ ⟨H.g_prime k⟩ ⟨what₂.places.resChar_prime w⟩).choose_spec
  teichC := fun k => (@GaloisStage.exists_teichC (H.g k) ⟨H.g_prime k⟩).choose
  teichC_inj := fun k => (@GaloisStage.exists_teichC (H.g k) ⟨H.g_prime k⟩).choose_spec
  inertiaCharpoly_type := fun k v L _ => by
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [hi, hl, GaloisStage.rootsBar_unip, Multiset.map_replicate, Multiset.prod_replicate, map_one, C_1]
  eSer := e
  eSer_idem := fun k => (he k).idem
  eSer_central := fun k => (he k).central
  eSer_orth := fun k => (he k).orth
  eSer_zero := fun k f => ((he k).zero f).2
  eSer_sum := fun k => (he k).sum
  cenAmb := fun _ => GaloisStage.cenTriv _ _
  cenMt := fun _ _ => GaloisStage.cenTriv _ _
  Par := Empty
  labPar := fun _ σ => σ.elim
  labPar_monic := fun _ σ => σ.elim
  locPar := fun σ => σ.elim
  locPar_dim := fun σ => σ.elim
  labPar_def := fun _ σ => σ.elim
  MtPar := fun _ _ σ => σ.elim
  AmbPar := fun _ σ => σ.elim
  heckeLoc_gamma_places := fun i => isEmptyElim i
  chiT_tg := fun i => isEmptyElim i

end Types

theorem isGood_comp {n g : ℕ} [Fact g.Prime] {P Q J : Type} (e : P ≃ Q) {f : Q → (ZMod g)[X]}
    {χ : Q → J → (ZMod g)ˣ} (h : Formalism.CyclotomicNorms.IsGood n g f χ) :
    Formalism.CyclotomicNorms.IsGood n g (fun v => f (e v)) (fun v => χ (e v)) := by
  obtain ⟨h1, h2, h3, h4, h5, v, h6⟩ := h
  refine ⟨fun v => h1 _, fun v => h2 _, fun l hl hb v => h3 l hl hb _, fun l hl hb v => h4 l hl hb _,
    fun a ha hb => ?_, e.symm v, by simpa using h6⟩
  obtain ⟨v, hv⟩ := h5 a ha hb
  exact ⟨e.symm v, by simpa using hv⟩

theorem adjoin_le (B : Base) : ∀ z ∈ IntermediateField.adjoin ℚ
    {Complex.exp (2 * Real.pi * Complex.I / (B.toPre.restRowsFiniteGroupCard : ℕ))}, z ∈ (B.LL0.toSubfield.map B.embLL).toSubring := by
  have h3 : IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (B.toPre.restRowsFiniteGroupCard : ℕ))} ≤
      (B.LL0.toSubfield.map B.embLL).toIntermediateField
        (fun q => by simpa using ratCast_mem (B.LL0.toSubfield.map B.embLL) q) := by
    rw [IntermediateField.adjoin_simple_le_iff]
    obtain ⟨z, hz, hz'⟩ := B.roots_Ks _ List.mem_cons_self
    exact ⟨z, B.Ks_le hz, hz'⟩
  exact fun z hz => h3 hz

theorem exists_goodTuple {B : Base} {C : Cols B} {W : RowsRest B C} {χ : Chi B.toPre}
    {nd : NData B.R B.host W.what₂} {A : NAut nd} (T : NTypes A) (hχ : HasChi nd χ) (hg : GoodChi B.toPre χ) :
    ∃ f, T.goodTuple f := by
  obtain ⟨f, hf⟩ := hg
  obtain ⟨ε, hε⟩ := hχ
  refine ⟨fun k v => f k (ε k v), fun k => ?_⟩
  haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
  have h : nd.chiT k = fun v => χ k (ε k v) := funext (hε k)
  have h1 := isGood_comp (ε k) (hf k).1
  have h2 := isGood_comp (ε k) (hf k).2
  rw [← h] at h1
  simp only [← hε] at h2
  exact ⟨h1, h2⟩

theorem exists_nTypes : ∀ (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre)
    (nd : NData B.R B.host W.what₂) (A : NAut nd), IsEmpty nd.Loc → HasChi nd χ →
    (∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p) →
    (∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p) →
    (GoodChi B.toPre χ ∨ ((∀ μ, W.eOp μ = 0) ∧ ∀ μ j, W.eMt μ j = 0)) →
    ∃ T : NTypes A, T.IdempotentMatchesAction ∧ ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := by
  intro B C W χ nd A hE hχ hl hi hg
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose e he using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T, hT⟩ : ∃ T : NTypes A, T.eSer = e := ⟨types0 hl hi B.g_cond B.BB_disj tg htg e he, rfl⟩
  subst hT
  obtain ⟨T', h1, h2⟩ := exists_tie T (fun k f hf h0 => ((he k).zero f).1 h0 hf)
    (hg.imp_left (exists_goodTuple T hχ))
  refine ⟨T', h1, fun x => ?_⟩
  obtain ⟨y, hy, hy'⟩ := goodTupleIdempotent_coeff_mem_subring T _ (fun k f x => adjoin_le B _ ((he k).rat f x)) x
  exact ⟨⟨y, hy⟩, by rw [h2]; exact hy'⟩

end GlobalTheory.MemN.TypesInhab
