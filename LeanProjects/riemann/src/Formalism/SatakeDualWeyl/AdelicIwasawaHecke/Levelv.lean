import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

theorem levelv_relIndex_ne_zero {G : Type*} [Group G] (H K : Subgroup G) {β : Type*} [Finite β]
    (f : G → β) (hf : ∀ a ∈ K, ∀ b ∈ K, f a = f b → a⁻¹ * b ∈ H) : H.relIndex K ≠ 0 := by
  classical
  have hfin : Finite (K ⧸ H.subgroupOf K) := by
    refine Finite.of_surjective
      (fun y : Set.range (fun k : K => f k) =>
        (QuotientGroup.mk (Set.mem_range.mp y.2).choose : K ⧸ H.subgroupOf K)) ?_
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨f k, k, rfl⟩, ?_⟩
    beta_reduce
    have hc := (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose_spec
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hf _ (Set.mem_range.mp (⟨k, rfl⟩ : f k ∈ Set.range (fun k : K => f k))).choose.2 _ k.2 hc
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem levelv_nat_denom {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (hfin : ∀ s : R, s ≠ 0 → Finite (R ⧸ Ideal.span {s})) (x : K) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ y : R, algebraMap R K y = N • x := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  haveI := hfin s hs0
  have hN : ringChar (R ⧸ Ideal.span {s}) ≠ 0 :=
    CharP.char_ne_zero_of_finite (R ⧸ Ideal.span {s}) (ringChar (R ⧸ Ideal.span {s}))
  have hmem : ((ringChar (R ⧸ Ideal.span {s}) : ℕ) : R) ∈ Ideal.span {s} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨ringChar (R ⧸ Ideal.span {s}), hN, t * a, ?_⟩
  have hs' : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  rw [nsmul_eq_mul, ← map_natCast (algebraMap R K), ← ht, map_mul, map_mul]
  field_simp <;> ring

section Local

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev lvS (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring

theorem levelv_tmul_mem (e : E) (he : e ∈ intOE E) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : e ⊗ₜ[F] x ∈ lvS F E v := by
  have h1 : e ⊗ₜ[F] (1 : v.adicCompletion F) ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩
  have h2 : (1 : E) ⊗ₜ[F] x ∈ lvS F E v := by
    apply Subring.subset_closure
    exact Set.mem_union_right _ ⟨⟨x, hx⟩, rfl⟩
  simpa using mul_mem h1 h2

def levelvPsi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) :
    (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      E ⊗[F] v.adicCompletion F :=
  AddMonoidHom.mk' (fun a => ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((a i : v.adicCompletionIntegers F) : v.adicCompletion F))
    (by intro a a'; simp [tmul_add, Finset.sum_add_distrib])

theorem levelv_tmul_mem_range (e : 𝓞 E) (x : v.adicCompletionIntegers F) :
    algebraMap (𝓞 E) E e ⊗ₜ[F] (x : v.adicCompletion F) ∈ (levelvPsi F E v).range := by
  classical
  let φ : 𝓞 E →+ E ⊗[F] v.adicCompletion F :=
    AddMonoidHom.mk' (fun y => algebraMap (𝓞 E) E y ⊗ₜ[F] (x : v.adicCompletion F))
      (by intro a b; simp [TensorProduct.add_tmul])
  have hb : ∀ i, φ (RingOfIntegers.basis E i) ∈ (levelvPsi F E v).range := by
    intro i
    refine AddMonoidHom.mem_range.mpr ⟨Pi.single i x, ?_⟩
    simp only [levelvPsi, AddMonoidHom.mk'_apply, φ]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  show φ e ∈ _
  rw [← (RingOfIntegers.basis E).sum_repr e, map_sum]
  exact sum_mem fun i _ => by rw [map_zsmul]; exact zsmul_mem (hb i) _

theorem levelv_mul_mem_range (y y' : E ⊗[F] v.adicCompletion F)
    (hy : y ∈ (levelvPsi F E v).range) (hy' : y' ∈ (levelvPsi F E v).range) :
    y * y' ∈ (levelvPsi F E v).range := by
  have hPsi : ∀ c, levelvPsi F E v c = ∑ i, algebraMap (𝓞 E) E (RingOfIntegers.basis E i) ⊗ₜ[F]
      ((c i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun c => rfl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hy
  obtain ⟨a', rfl⟩ := AddMonoidHom.mem_range.mp hy'
  rw [hPsi, hPsi]
  simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  first
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E i * RingOfIntegers.basis E j) (a i * a' j)
    | simpa using levelv_tmul_mem_range v (RingOfIntegers.basis E j * RingOfIntegers.basis E i) (a j * a' i)

def levelvT (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) where
  carrier := (levelvPsi F E v).range
  mul_mem' := levelv_mul_mem_range v _ _
  one_mem' := by
    have h1 : (1 : E ⊗[F] v.adicCompletion F) = algebraMap (𝓞 E) E 1 ⊗ₜ[F]
        ((1 : v.adicCompletionIntegers F) : v.adicCompletion F) := by rw [map_one]; rfl
    rw [h1]
    exact levelv_tmul_mem_range v 1 1
  add_mem' := add_mem
  zero_mem' := zero_mem _
  neg_mem' := neg_mem

theorem levelv_S_le_range (y : E ⊗[F] v.adicCompletion F) (hy : y ∈ lvS F E v) :
    y ∈ (levelvPsi F E v).range := by
  have hle : lvS F E v ≤ levelvT F E v := by
    apply Subring.closure_le.mpr
    rintro z (⟨⟨e, he⟩, rfl⟩ | ⟨⟨x, hx⟩, rfl⟩)
    · obtain ⟨e', rfl⟩ := RingHom.mem_range.mp he
      show algebraMap (𝓞 E) E e' ⊗ₜ[F] (1 : v.adicCompletion F) ∈ (levelvPsi F E v).range
      simpa using levelv_tmul_mem_range v e' 1
    · show (1 : E) ⊗ₜ[F] x ∈ (levelvPsi F E v).range
      have h := levelv_tmul_mem_range (E := E) v 1 ⟨x, hx⟩
      first
        | exact h
        | (rw [map_one] at h; exact h)
        | simpa using h
  exact hle hy

theorem levelv_range_le_S (a : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) :
    levelvPsi F E v a ∈ lvS F E v := by
  simp only [levelvPsi, AddMonoidHom.mk'_apply]
  exact sum_mem fun i _ => levelv_tmul_mem v _ (RingHom.mem_range.mpr ⟨_, rfl⟩) _ (a i).2

theorem levelv_denom (y : E ⊗[F] v.adicCompletion F) : ∃ N : ℕ, N ≠ 0 ∧ N • y ∈ lvS F E v := by
  classical
  have h1 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = (m • e) ⊗ₜ[F] x :=
    fun m e x => (map_nsmul ((TensorProduct.mk F E (v.adicCompletion F)).flip x) m e).symm
  have h2 : ∀ (m : ℕ) (e : E) (x : v.adicCompletion F), m • (e ⊗ₜ[F] x) = e ⊗ₜ[F] (m • x) :=
    fun m e x => (map_nsmul (TensorProduct.mk F E (v.adicCompletion F) e) m x).symm
  have hE : ∀ e : E, ∃ M : ℕ, M ≠ 0 ∧ M • e ∈ intOE E := by
    intro e
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
    refine ⟨Ideal.absNorm (Ideal.span {s}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hs0
    · refine RingHom.mem_range.mpr ⟨t * a, ?_⟩
      have hs' : algebraMap (𝓞 E) E s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
      rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 E) E), ← ht, map_mul, map_mul]
      field_simp <;> ring
  have hF : ∀ x : v.adicCompletion F, ∃ N : ℕ, N ≠ 0 ∧ N • x ∈ v.adicCompletionIntegers F := by
    intro x
    obtain ⟨b, hb, hbx⟩ :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hb0
    · have hcv : algebraMap (𝓞 F) (v.adicCompletion F) c ∈ v.adicCompletionIntegers F :=
        (algebraMap (𝓞 F) (v.adicCompletionIntegers F) c).2
      have key : Ideal.absNorm (Ideal.span {b}) • x = algebraMap (𝓞 F) (v.adicCompletion F) c *
          (x * algebraMap (𝓞 F) (v.adicCompletion F) b) := by
        rw [nsmul_eq_mul, ← map_natCast (algebraMap (𝓞 F) (v.adicCompletion F)), ← hc, map_mul]
        ring
      rw [key]
      exact mul_mem hcv hbx
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | tmul e x =>
    obtain ⟨M, hM0, hM⟩ := hE e
    obtain ⟨N, hN0, hN⟩ := hF x
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [mul_smul, h2, h1]
    exact levelv_tmul_mem v _ hM _ hN
  | add y z hy hz =>
    obtain ⟨M, hM0, hM⟩ := hy
    obtain ⟨N, hN0, hN⟩ := hz
    refine ⟨M * N, mul_ne_zero hM0 hN0, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact nsmul_mem hM _
    · rw [mul_smul]
      exact nsmul_mem hN _

theorem levelv_denom_family {ι : Type*} [Fintype ι] (a : ι → E ⊗[F] v.adicCompletion F) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i, N • a i ∈ lvS F E v := by
  classical
  choose M hM0 hM using fun i => levelv_denom v (a i)
  refine ⟨∏ i, M i, Finset.prod_ne_zero_iff.mpr fun i _ => hM0 i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ M (Finset.mem_univ i), mul_smul]
  exact nsmul_mem (hM i) _

end Local

section Lattice

open IsDedekindDomain NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]

theorem levelv_mem_lat (x : n → E ⊗[F] v.adicCompletion F) :
    x ∈ stdLat (n := n) ↥(lvS F E v) ↔ ∀ j, x j ∈ lvS F E v := by
  rw [stdLat, Submodule.mem_pi]
  refine ⟨fun h j => ?_, fun h j _ => ?_⟩
  · obtain ⟨s, hs⟩ := LinearMap.mem_range.mp (h j (Set.mem_univ j))
    rw [← hs]
    exact s.2
  · exact LinearMap.mem_range.mpr ⟨⟨x j, h j⟩, rfl⟩

theorem levelv_smul_mulVec_mem (N : ℕ) (M : Matrix n n (E ⊗[F] v.adicCompletion F))
    (hM : ∀ i j, N • M i j ∈ lvS F E v) (x : n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ stdLat (n := n) ↥(lvS F E v)) :
    N • (M *ᵥ x) ∈ stdLat (n := n) ↥(lvS F E v) := by
  rw [levelv_mem_lat] at hx ⊢
  intro i
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, Finset.smul_sum]
  refine sum_mem fun j _ => ?_
  rw [← smul_mul_assoc]
  exact mul_mem (hM i j) (hx j)

def levelvPhi (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n : Type) :
    (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →+
      (n → E ⊗[F] v.adicCompletion F) :=
  AddMonoidHom.mk' (fun α j => levelvPsi F E v (α j)) (by intro α β; ext j; simp)

theorem levelv_phi_mem (α : n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) :
    levelvPhi F E v n α ∈ stdLat (n := n) ↥(lvS F E v) := by
  rw [levelv_mem_lat]
  intro j
  exact levelv_range_le_S v (α j)

theorem levelv_lat_phi (x : n → E ⊗[F] v.adicCompletion F)
    (hx : x ∈ stdLat (n := n) ↥(lvS F E v)) : ∃ α, levelvPhi F E v n α = x := by
  rw [levelv_mem_lat] at hx
  choose α hα using fun j => AddMonoidHom.mem_range.mp (levelv_S_le_range v (x j) (hx j))
  exact ⟨α, funext fun j => hα j⟩

theorem levelv_nsmul_inj {N : ℕ} (hN : N ≠ 0) (y y' : n → E ⊗[F] v.adicCompletion F)
    (h : N • y = N • y') : y = y' := by
  funext j
  have hj := congr_fun h j
  simp only [Pi.smul_apply] at hj
  have hu : IsUnit ((N : E ⊗[F] v.adicCompletion F)) := by
    have h0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) N]
    exact (IsUnit.mk0 _ h0).map _
  rw [nsmul_eq_mul, nsmul_eq_mul] at hj
  exact hu.mul_left_cancel hj

end Lattice

section GLact

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem levelv_mulVec_mul (k l : GL n R) (x : n → R) :
    ((k * l : GL n R) : Matrix n n R) *ᵥ x = (k : Matrix n n R) *ᵥ ((l : Matrix n n R) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem levelv_inv_mulVec (k : GL n R) (x : n → R) :
    ((k⁻¹ : GL n R) : Matrix n n R) *ᵥ ((k : Matrix n n R) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem levelv_mulVec_inv (k : GL n R) (x : n → R) :
    (k : Matrix n n R) *ᵥ (((k⁻¹ : GL n R) : Matrix n n R) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

end GLact

theorem levelv_stab_of_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (Λ : Set (n → R)) (N : ℕ) (hinj : ∀ y y' : n → R, N • y = N • y' → y = y') (ga a b : GL n R)
    (hZ : (fun x => N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ =
      (fun x => N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ) (x : n → R) :
    x ∈ Λ ↔ ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x ∈ Λ := by
  have hk : ∀ y, ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ y =
      ((ga⁻¹ : GL n R) : Matrix n n R) *ᵥ (((a⁻¹ : GL n R) : Matrix n n R) *ᵥ
        ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ y))) := by
    intro y
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  constructor
  · intro hx
    have hmem : N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x)) ∈
        (fun x => N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ := by
      rw [hZ]
      exact ⟨x, hx, rfl⟩
    obtain ⟨x', hx', he⟩ := hmem
    have he' := hinj _ _ he
    have hxx : x' = ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x := by
      rw [hk, ← he', levelv_inv_mulVec, levelv_inv_mulVec]
    rw [← hxx]
    exact hx'
  · intro hx
    have hmem : N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ
        (((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x))) ∈
        (fun x => N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ := by
      rw [← hZ]
      exact ⟨_, hx, rfl⟩
    obtain ⟨x', hx', he⟩ := hmem
    have he' := hinj _ _ he
    rw [hk, levelv_mulVec_inv, levelv_mulVec_inv] at he'
    have hxx : x' = x := by
      have h1 := congrArg (fun y => ((ga⁻¹ : GL n R) : Matrix n n R) *ᵥ
        (((b⁻¹ : GL n R) : Matrix n n R) *ᵥ y)) he'
      simpa only [levelv_inv_mulVec] using h1
    rw [← hxx]
    exact hx'

open IsDedekindDomain NumberField in
theorem level_subgroup_commute : Formalism.UG.LevelVComm := by
  intro F E _ _ _ _ _ n _ _ σ J v g
  classical
  have hlev : ∀ k : UPts σ J (v.adicCompletion F),
      k ∈ (levelV σ J v).subgroupOf (UPts σ J (v.adicCompletion F)) ↔
        (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    simp only [levelV, level, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  obtain ⟨N, hN0, hN⟩ := levelv_denom_family (E := E) v (fun p : (n × n) ⊕ (n × n) =>
    Sum.elim (fun q : n × n => ((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) q.1 q.2)
      (fun q : n × n => (((g : GL n (E ⊗[F] v.adicCompletion F))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) q.1 q.2) p)
  have hg : ∀ i j, N • ((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈ lvS F E v :=
    fun i j => hN (.inl (i, j))
  have hg' : ∀ i j, N • (((g : GL n (E ⊗[F] v.adicCompletion F))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j ∈
      lvS F E v :=
    fun i j => hN (.inr (i, j))
  obtain ⟨c, hcdef⟩ : ∃ c : v.adicCompletionIntegers F, c = ((N * N : ℕ) : v.adicCompletionIntegers F) :=
    ⟨_, rfl⟩
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    rw [hcdef] at h1
    simp [hN0] at h1
  have : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    glint_finite_quotient_of_dvr (glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let Z : UPts σ J (v.adicCompletion F) → Set (n → E ⊗[F] v.adicCompletion F) := fun k =>
    (fun x => N • (((k : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
      (((g : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ x))) ''
      (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) : Set (n → E ⊗[F] v.adicCompletion F))
  have hZ1 : ∀ k : UPts σ J (v.adicCompletion F),
      (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
        Z k ⊆ (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) : Set (n → E ⊗[F] v.adicCompletion F)) := by
    rintro k hk _ ⟨x, hx, rfl⟩
    simp only
    rw [← Matrix.mulVec_smul]
    exact (hk _).1 (levelv_smul_mulVec_mem v N _ hg x hx)
  have hZ2 : ∀ k : UPts σ J (v.adicCompletion F),
      (k : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
        ∀ z ∈ stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v), (N * N) • z ∈ Z k := by
    intro k hk z hz
    have hw : ((((k : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v) := ((inv_mem hk) z).1 hz
    refine ⟨N • ((((g : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ
      (((((k : GL n (E ⊗[F] v.adicCompletion F)))⁻¹ : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ z),
      levelv_smul_mulVec_mem v N _ hg' _ hw, ?_⟩
    simp only
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, levelv_mulVec_inv, levelv_mulVec_inv, mul_smul]
  have hZ3 : ∀ k : UPts σ J (v.adicCompletion F), ∀ y ∈ Z k, ∀ y' ∈ Z k, y + y' ∈ Z k := by
    rintro k _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    exact ⟨x + x', add_mem hx hx', by simp only [Matrix.mulVec_add, smul_add]⟩
  let π : (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F) →
      (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    fun α j i => Ideal.Quotient.mk _ (α j i)
  let f : UPts σ J (v.adicCompletion F) →
      Set (n → Module.Free.ChooseBasisIndex ℤ (𝓞 E) → v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    fun k => π '' ((levelvPhi F E v n) ⁻¹' Z k)
  have hsub : ∀ a b : UPts σ J (v.adicCompletion F),
      (a : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) →
      (b : GL n (E ⊗[F] v.adicCompletion F)) ∈ stabGL (stdLat (n := n) (A := E ⊗[F] v.adicCompletion F) ↥(lvS F E v)) → f a = f b → Z a ⊆ Z b := by
    intro a b ha hb hab y hy
    obtain ⟨α, hα⟩ := levelv_lat_phi v y (hZ1 a ha hy)
    have hmem : π α ∈ f b := by
      rw [← hab]
      exact ⟨α, by rw [Set.mem_preimage, hα]; exact hy, rfl⟩
    obtain ⟨α', hα'Z, hπ⟩ := hmem
    have hdiff : ∀ j i, α j i - α' j i ∈ Ideal.span {c} := by
      intro j i
      have := congrFun (congrFun hπ j) i
      exact Ideal.Quotient.eq.1 this.symm
    choose β hβ using fun j i => Ideal.mem_span_singleton'.1 (hdiff j i)
    have hαβ : α = α' + (N * N) • β := by
      funext j i
      have := hβ j i
      rw [hcdef] at this
      simp only [Pi.add_apply, Pi.smul_apply]
      rw [nsmul_eq_mul]
      push_cast at this ⊢
      linear_combination -this
    rw [← hα, hαβ, map_add, map_nsmul]
    exact hZ3 b _ hα'Z _ (hZ2 b hb _ (levelv_phi_mem v β))
  refine levelv_relIndex_ne_zero _ _ f ?_
  intro a ha b hb hab
  have ha' := (hlev a).1 ha
  have hb' := (hlev b).1 hb
  have hZ : Z a = Z b := (hsub a b ha' hb' hab).antisymm (hsub b a hb' ha' hab.symm)
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, hlev]
  intro x
  exact levelv_stab_of_eq _ N (levelv_nsmul_inj v hN0) _ _ _ hZ x

end Formalism.UG.P
