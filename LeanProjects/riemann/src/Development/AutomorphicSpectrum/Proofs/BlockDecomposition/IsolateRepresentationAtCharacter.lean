import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HkMemFixed
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmulEqOnFinset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleHomFixedVectorsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

noncomputable section

namespace GlobalTheory.CompanionTheory.Isolate

open GlobalTheory.CompanionTheory.HeckeMul

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_finset {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (he : IsHk K e) :
    ∃ A : Finset (GL ι F ⧸ K), ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A :=
  ⟨(finite_out_mem K he.1 he.2.2.1).toFinset, fun q hq => by
    simpa using subset_tsupport _ (Function.mem_support.2 hq)⟩

section Ops

variable {K : Subgroup (GL ι F)} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL ι F) V)

theorem hk_add_right {e : GL ι F → ℂ} (he : IsHk K e) (v w : V) :
    hk ρ K e (v + w) = hk ρ K e v + hk ρ K e w := by
  obtain ⟨A, hA⟩ := exists_finset he
  simp only [hk_eq_sum ρ K e _ A hA, map_add, smul_add, Finset.sum_add_distrib]

theorem hk_smul_right {e : GL ι F → ℂ} (he : IsHk K e) (c : ℂ) (v : V) :
    hk ρ K e (c • v) = c • hk ρ K e v := by
  obtain ⟨A, hA⟩ := exists_finset he
  simp only [hk_eq_sum ρ K e _ A hA, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm _ _ _

theorem hk_zero_right (e : GL ι F → ℂ) : hk ρ K e (0 : V) = 0 := by
  simp [hk]

theorem hk_add_left {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) (v : V) :
    hk ρ K (e₁ + e₂) v = hk ρ K e₁ v + hk ρ K e₂ v := by
  classical
  obtain ⟨A₁, hA₁⟩ := exists_finset h₁
  obtain ⟨A₂, hA₂⟩ := exists_finset h₂
  have m₁ : ∀ q : GL ι F ⧸ K, e₁ q.out ≠ 0 → q ∈ A₁ ∪ A₂ :=
    fun q hq => Finset.mem_union_left _ (hA₁ q hq)
  have m₂ : ∀ q : GL ι F ⧸ K, e₂ q.out ≠ 0 → q ∈ A₁ ∪ A₂ :=
    fun q hq => Finset.mem_union_right _ (hA₂ q hq)
  have m : ∀ q : GL ι F ⧸ K, (e₁ + e₂) q.out ≠ 0 → q ∈ A₁ ∪ A₂ := by
    intro q hq
    by_cases h : e₁ q.out = 0
    · refine m₂ q fun h' => hq ?_
      simp [h, h']
    · exact m₁ q h
  rw [hk_eq_sum ρ K _ v _ m, hk_eq_sum ρ K _ v _ m₁, hk_eq_sum ρ K _ v _ m₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp [add_smul]

theorem hk_smul_left {e : GL ι F → ℂ} (he : IsHk K e) (c : ℂ) (v : V) :
    hk ρ K (c • e) v = c • hk ρ K e v := by
  obtain ⟨A, hA⟩ := exists_finset he
  have m : ∀ q : GL ι F ⧸ K, (c • e) q.out ≠ 0 → q ∈ A := by
    intro q hq
    refine hA q fun h => hq ?_
    simp [h]
  rw [hk_eq_sum ρ K _ v _ m, hk_eq_sum ρ K _ v _ hA, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => by simp [mul_smul]

end Ops

theorem isHk_add {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (e₁ + e₂) :=
  ⟨h₁.1, h₁.2.1, HasCompactSupport.add h₁.2.2.1 h₂.2.2.1, fun k₁ hk₁ k₂ hk₂ g => by
    simp [h₁.2.2.2 k₁ hk₁ k₂ hk₂ g, h₂.2.2.2 k₁ hk₁ k₂ hk₂ g]⟩

theorem isHk_smul {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (c : ℂ) (h : IsHk K e) :
    IsHk K (c • e) :=
  ⟨h.1, h.2.1, HasCompactSupport.of_support_subset_isCompact h.2.2.1 (by
      intro x hx
      refine subset_tsupport _ fun h0 => hx ?_
      simp [h0]), fun k₁ hk₁ k₂ hk₂ g => by
    simp [h.2.2.2 k₁ hk₁ k₂ hk₂ g]⟩

open Classical in

def unitFn (K : Subgroup (GL ι F)) (g : GL ι F) : ℂ := if g ∈ K then 1 else 0

theorem isHk_unitFn {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) : IsHk K (unitFn K) := by
  refine ⟨hKo, hKc, HasCompactSupport.of_support_subset_isCompact hKc ?_, ?_⟩
  · intro x hx
    by_contra h
    exact hx (by simpa [unitFn] using h)
  · intro k₁ hk₁ k₂ hk₂ g
    have : k₁ * g * k₂ ∈ K ↔ g ∈ K := by
      rw [Subgroup.mul_mem_cancel_right K hk₂, Subgroup.mul_mem_cancel_left K hk₁]
    unfold unitFn
    by_cases h : g ∈ K
    · rw [if_pos h, if_pos (this.2 h)]
    · rw [if_neg h, if_neg fun h' => h (this.1 h')]

theorem hk_unitFn {K : Subgroup (GL ι F)} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) {v : V} (hv : v ∈ fixed ρ K) : hk ρ K (unitFn K) v = v := by
  classical
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have m : ∀ q : GL ι F ⧸ K, unitFn K q.out ≠ 0 → q ∈ ({(QuotientGroup.mk 1 : GL ι F ⧸ K)} : Finset _) := by
    intro q hq
    have h1 : q.out ∈ K := by
      by_contra h
      exact hq (by simp [unitFn, h])
    rw [Finset.mem_singleton, ← QuotientGroup.out_eq' q]
    exact (QuotientGroup.eq.2 (by simpa using h1))
  rw [hk_eq_sum ρ K _ v _ m, Finset.sum_singleton]
  have h1 : (QuotientGroup.mk 1 : GL ι F ⧸ K).out ∈ K := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk 1 : GL ι F ⧸ K))
    simpa using this
  simp [unitFn, h1, hvk _ h1]

theorem map_hk {K : Subgroup (GL ι F)} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (GL ι F) V} {σ : Representation ℂ (GL ι F) W}
    (T : ρ.Equiv σ) (e : GL ι F → ℂ) (v : V) :
    T.toLinearEquiv (hk ρ K e v) = hk σ K e (T.toLinearEquiv v) := by
  have hT : ∀ g x, T.toLinearEquiv (ρ g x) = σ g (T.toLinearEquiv x) := fun g x =>
    LinearMap.congr_fun (T.isIntertwining' g) x
  have h1 := AddMonoidHom.map_finsum_of_injective (T.toLinearEquiv : V →ₗ[ℂ] W).toAddMonoidHom
    T.toLinearEquiv.injective (fun q : GL ι F ⧸ K => e q.out • ρ q.out v)
  unfold hk
  refine h1.trans (finsum_congr fun q => ?_)
  show T.toLinearEquiv (e q.out • ρ q.out v) = e q.out • σ q.out (T.toLinearEquiv v)
  rw [map_smul, hT]

theorem unitFn_mul_right {K : Subgroup (GL ι F)} (y : GL ι F) {k : GL ι F} (hk' : k ∈ K) :
    unitFn K (y * k) = unitFn K y := by
  have : y * k ∈ K ↔ y ∈ K := Subgroup.mul_mem_cancel_right K hk'
  unfold unitFn
  by_cases h : y ∈ K
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg fun h' => h (this.1 h')]

theorem unitFn_mul_left {K : Subgroup (GL ι F)} (y : GL ι F) {k : GL ι F} (hk' : k ∈ K) :
    unitFn K (k * y) = unitFn K y := by
  have : k * y ∈ K ↔ y ∈ K := Subgroup.mul_mem_cancel_left K hk'
  unfold unitFn
  by_cases h : y ∈ K
  · rw [if_pos h, if_pos (this.2 h)]
  · rw [if_neg h, if_neg fun h' => h (this.1 h')]

theorem exists_hk_avg {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) (L : Subgroup K) [Fintype (K ⧸ L)] (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * ((l : K) : GL ι F) * g ∈ K)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {s : V}
    (hs : s ∈ fixed ρ K) :
    ∃ e, IsHk K e ∧ hk ρ K e s = ∑ q : K ⧸ L, ρ ((q.out : K) : GL ι F) (ρ g s) := by
  classical
  have hsk : ∀ k ∈ K, ρ k s = s := fun k hk' => by
    have := hs ⟨k, hk'⟩
    simpa using this
  let a : K ⧸ L → GL ι F := fun q => ((q.out : K) : GL ι F) * g
  have key : ∀ (k : K) (q : K ⧸ L), ∃ c ∈ K, (k : GL ι F) * a q = a (k • q) * c := by
    intro k q
    have hq : ((k * q.out : K) : K ⧸ L) = k • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hmem : ((k • q).out)⁻¹ * (k * q.out) ∈ L := by
      apply QuotientGroup.eq.1
      rw [hq, QuotientGroup.out_eq']
    refine ⟨_, hL _ hmem, ?_⟩
    simp only [a]
    push_cast
    group
  let e : GL ι F → ℂ := fun x => ∑ q, unitFn K ((a q)⁻¹ * x)
  have hright : ∀ x, ∀ k ∈ K, e (x * k) = e x := fun x k hk' =>
    Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, unitFn_mul_right _ hk']
  have hleft : ∀ x, ∀ k ∈ K, e (k * x) = e x := by
    intro x k hk'
    let k' : K := ⟨k⁻¹, K.inv_mem hk'⟩
    have h1 : ∀ q, unitFn K ((a q)⁻¹ * (k * x)) = unitFn K ((a (k' • q))⁻¹ * x) := by
      intro q
      obtain ⟨c, hc, h⟩ := key k' q
      have h2 : (a q)⁻¹ * (k * x) = c⁻¹ * ((a (k' • q))⁻¹ * x) := by
        have h3 : (a q)⁻¹ * k = c⁻¹ * (a (k' • q))⁻¹ := by
          rw [← mul_inv_rev, ← h]
          simp [k']
        rw [← mul_assoc, h3, mul_assoc]
      rw [h2, unitFn_mul_left _ (K.inv_mem hc)]
    simp only [e, h1]
    exact Fintype.sum_equiv (MulAction.toPerm k') _ _ (fun _ => rfl)
  have hsupp : ∀ x, e x ≠ 0 → ∃ q, (a q)⁻¹ * x ∈ K := by
    intro x hx
    obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    refine ⟨q, ?_⟩
    by_contra h
    exact hq (by simp [unitFn, h])
  have hE : IsHk K e := by
    refine ⟨hKo, hKc, ?_, ?_⟩
    · refine HasCompactSupport.of_support_subset_isCompact
        (K := ⋃ q, (fun y => a q * y) '' (K : Set (GL ι F)))
        (isCompact_iUnion fun q => hKc.image (continuous_mul_left _)) ?_
      intro x hx
      obtain ⟨q, hq⟩ := hsupp x hx
      exact Set.mem_iUnion.2 ⟨q, _, hq, by simp⟩
    · intro k₁ hk₁ k₂ hk₂ x
      rw [hright _ _ hk₂, hleft _ _ hk₁]
  refine ⟨e, hE, ?_⟩
  let B : Finset (GL ι F ⧸ K) := Finset.univ.image fun q => (QuotientGroup.mk (a q) : GL ι F ⧸ K)
  have hB : ∀ p : GL ι F ⧸ K, e p.out ≠ 0 → p ∈ B := by
    intro p hp
    obtain ⟨q, hq⟩ := hsupp _ hp
    refine Finset.mem_image.2 ⟨q, Finset.mem_univ _, ?_⟩
    rw [← QuotientGroup.out_eq' p]
    exact QuotientGroup.eq.2 hq
  rw [hk_eq_sum ρ K e s B hB]
  simp only [e, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_eq_single (QuotientGroup.mk (a q))]
  · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (a q)
    have h1 : unitFn K ((a q)⁻¹ * (a q * (c : GL ι F))) = 1 := by
      rw [inv_mul_cancel_left]
      simp [unitFn]
    rw [hc, h1, one_smul, map_mul, Module.End.mul_apply, hsk _ c.2, map_mul, Module.End.mul_apply]
  · intro p _ hp
    have h1 : unitFn K ((a q)⁻¹ * p.out) = 0 := by
      unfold unitFn
      rw [if_neg]
      intro h
      refine hp ?_
      rw [← QuotientGroup.out_eq' p]
      exact (QuotientGroup.eq.2 h).symm
    rw [h1, zero_smul]
  · intro h
    exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ q)) h

theorem stable_top {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F)))
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V)
    (hi : π.IsIrreducible) (S : Submodule ℂ V) (hS : S ≤ fixed π K) (h0 : S ≠ ⊥)
    (hst : ∀ e, IsHk K e → ∀ s ∈ S, hk π K e s ∈ S) : fixed π K ≤ S := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hfin : ∀ L : Subgroup K, IsOpen (L : Set K) → Finite (K ⧸ L) := fun L hL =>
    Subgroup.quotient_finite_of_isOpen L hL
  let gen : Set V := {x | ∃ g, ∃ s ∈ S, x = π g s}
  let U : Subrepresentation π := ⟨Submodule.span ℂ gen, by
    intro g v hv
    have : Submodule.span ℂ gen ≤ (Submodule.span ℂ gen).comap (π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g', s, hs, rfl⟩
      refine Submodule.subset_span ⟨g * g', s, hs, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    exact this hv⟩
  have hU : U = ⊤ := by
    rcases eq_bot_or_eq_top U with h | h
    · exfalso
      refine h0 ((Submodule.eq_bot_iff _).2 fun s hs => ?_)
      have h1 : s ∈ U.toSubmodule := Submodule.subset_span ⟨1, s, hs, by simp⟩
      rw [h] at h1
      exact (Submodule.mem_bot ℂ).1 h1
    · exact h
  have hall : ∀ w : V, w ∈ Submodule.span ℂ gen := by
    intro w
    have h1 : w ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← hU] at h1
    exact h1
  have hQ : ∀ w : V, ∃ L₀ : Subgroup K, IsOpen (L₀ : Set K) ∧ ∀ L : Subgroup K, IsOpen (L : Set K) → L ≤ L₀ →
      ∀ [Fintype (K ⧸ L)], ∑ q : K ⧸ L, π ((q.out : K) : GL ι F) w ∈ S := by
    intro w
    induction hall w using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, s, hs, rfl⟩ := hx
      let L₀ : Subgroup K := (K.comap (MulAut.conj g⁻¹).toMonoidHom).subgroupOf K
      refine ⟨L₀, ?_, ?_⟩
      · have hc : Continuous fun x : GL ι F => g⁻¹ * x * g := by fun_prop
        have := (hKo.preimage hc).preimage (continuous_subtype_val (p := (· ∈ K)))
        convert this using 1
        ext x
        simp [L₀, Subgroup.mem_subgroupOf]
      · intro L _ hLL _
        obtain ⟨e, he, h⟩ := exists_hk_avg hKo hKc L g (fun l hl => by
          have := hLL hl
          simpa [L₀, Subgroup.mem_subgroupOf] using this) π (hS hs)
        rw [← h]
        exact hst e he s hs
    | zero => exact ⟨⊤, by simp, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      obtain ⟨L₂, h₂, hy⟩ := hy
      refine ⟨L₁ ⊓ L₂, IsOpen.inter h₁ h₂, fun L hLo hL _ => ?_⟩
      simp only [map_add, Finset.sum_add_distrib]
      exact S.add_mem (hx L hLo (hL.trans inf_le_left)) (hy L hLo (hL.trans inf_le_right))
    | smul c x _ hx =>
      obtain ⟨L₁, h₁, hx⟩ := hx
      refine ⟨L₁, h₁, fun L hLo hL _ => ?_⟩
      simp only [map_smul, ← Finset.smul_sum]
      exact S.smul_mem c (hx L hLo hL)
  intro w hw
  have hwk : ∀ k ∈ K, π k w = w := fun k hk' => by
    have := hw ⟨k, hk'⟩
    simpa using this
  obtain ⟨L, hLo, hL⟩ := hQ w
  haveI := hfin L hLo
  letI : Fintype (K ⧸ L) := Fintype.ofFinite _
  have h1 := hL L hLo le_rfl
  simp only [fun q : K ⧸ L => hwk _ (q.out : K).2, Finset.sum_const, Finset.card_univ] at h1
  have hn : ((Fintype.card (K ⧸ L) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  have h2 := S.smul_mem ((Fintype.card (K ⧸ L) : ℕ) : ℂ)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hn, one_smul] at h2

theorem abstract_density {I : Type} [Fintype I] (M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)] [∀ i, Nontrivial (M i)]
    (A : Subalgebra ℂ (∀ i, Module.End ℂ (M i)))
    (hsimple : ∀ i (S : Submodule ℂ (M i)), (∀ a ∈ A, ∀ x ∈ S, a i x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hiso : ∀ i j (φ : M i ≃ₗ[ℂ] M j), (∀ a ∈ A, ∀ x, φ (a i x) = a j (φ x)) → i = j)
    (f : ∀ i, Module.End ℂ (M i)) : ∃ a ∈ A, ∀ i, a i = f i := by
  classical
  let ev : ∀ i, A →+* Module.End ℂ (M i) := fun i =>
    (Pi.evalRingHom (fun i => Module.End ℂ (M i)) i).comp A.val.toRingHom
  letI : ∀ i, Module A (M i) := fun i => Module.compHom _ (ev i)
  haveI : ∀ i, IsScalarTower ℂ A (M i) := fun i => ⟨fun c a x => rfl⟩
  haveI : ∀ i, IsSimpleModule A (M i) := by
    intro i
    refine (isSimpleModule_iff A (M i)).2 ⟨fun S => ?_⟩
    rcases hsimple i (S.restrictScalars ℂ) (fun a ha x hx => S.smul_mem ⟨a, ha⟩ hx) with h | h
    · left
      exact Submodule.restrictScalars_injective ℂ _ _ (by simpa using h)
    · right
      exact Submodule.restrictScalars_injective ℂ _ _ (by simpa using h)
  have hiso' : ∀ i j, Nonempty (M i ≃ₗ[A] M j) → i = j := by
    rintro i j ⟨φ⟩
    exact hiso i j (φ.restrictScalars ℂ) fun a ha x => φ.map_smul ⟨a, ha⟩ x
  obtain ⟨a, ha⟩ := GlobalTheory.CompanionTheory.SimpleDensity.exists_smul_eq_end A I M hiso' f
  exact ⟨a.1, a.2, fun i => LinearMap.ext fun x => ha i x⟩

section Alg

variable {K : Subgroup (GL ι F)} {I : Type} {Y : I → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
  (ρ : ∀ i, Representation ℂ (GL ι F) (Y i))

def hkFix {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL ι F) X)
    {e : GL ι F → ℂ} (he : IsHk K e) : Module.End ℂ (fixed σ K) where
  toFun v := ⟨hk σ K e v, (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e he X σ v v.2).1⟩
  map_add' v w := Subtype.ext (hk_add_right σ he v w)
  map_smul' c v := Subtype.ext (hk_smul_right σ he c v)

variable (K) in

def heckeAlg (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    Subalgebra ℂ (∀ i, Module.End ℂ (fixed (ρ i) K)) where
  carrier := {T | ∃ e, IsHk K e ∧ ∀ i (x : fixed (ρ i) K), ((T i x : fixed (ρ i) K) : Y i) = hk (ρ i) K e x}
  mul_mem' := by
    rintro a b ⟨e₁, h₁, ha⟩ ⟨e₂, h₂, hb⟩
    refine ⟨hconv K e₁ e₂, isHk_hconv h₁ h₂, fun i x => ?_⟩
    rw [hk_hconv h₁ h₂ (ρ i) x.2, ← hb i x, ← ha i]
    rfl
  add_mem' := by
    rintro a b ⟨e₁, h₁, ha⟩ ⟨e₂, h₂, hb⟩
    refine ⟨e₁ + e₂, isHk_add h₁ h₂, fun i x => ?_⟩
    rw [hk_add_left (ρ i) h₁ h₂, ← ha i, ← hb i]
    rfl
  algebraMap_mem' := by
    intro c
    refine ⟨c • unitFn K, isHk_smul c (isHk_unitFn hKo hKc), fun i x => ?_⟩
    rw [hk_smul_left (ρ i) (isHk_unitFn hKo hKc), hk_unitFn (ρ i) x.2]
    rfl

end Alg

theorem density_core {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) {I : Type} [Fintype I] {Y : I → Type}
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] (ρ : ∀ i, Representation ℂ (GL ι F) (Y i))
    (hs : ∀ i, IsSmooth (ρ i)) (hi : ∀ i, (ρ i).IsIrreducible)
    (h0 : ∀ i, ∃ v ∈ fixed (ρ i) K, v ≠ 0)
    (hne : ∀ i j, Nonempty ((ρ i).Equiv (ρ j)) → i = j)
    (f : ∀ i, Module.End ℂ (fixed (ρ i) K)) :
    ∃ e, IsHk K e ∧ ∀ i (x : fixed (ρ i) K), hk (ρ i) K e x = (f i x : Y i) := by
  classical
  haveI : ∀ i, FiniteDimensional ℂ (fixed (ρ i) K) := fun i =>
    (GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible F ι (Y i) (ρ i) (hs i) (hi i)).2 K hKo hKc
  haveI : ∀ i, Nontrivial (fixed (ρ i) K) := fun i => by
    obtain ⟨v, hv, hv0⟩ := h0 i
    exact ⟨⟨⟨v, hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  let A := heckeAlg K ρ hKo hKc
  have hop : ∀ e (he : IsHk K e), (fun i => hkFix (ρ i) he) ∈ A := fun e he => ⟨e, he, fun i x => rfl⟩
  have hS1 : ∀ i (S : Submodule ℂ (fixed (ρ i) K)), (∀ a ∈ A, ∀ x ∈ S, a i x ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro i S hS
    by_cases hb : S = ⊥
    · exact Or.inl hb
    right
    have h1 : fixed (ρ i) K ≤ S.map (fixed (ρ i) K).subtype := by
      refine stable_top hKo hKc (ρ i) (hi i) _ ?_ ?_ ?_
      · rintro _ ⟨x, _, rfl⟩
        exact x.2
      · intro hbot
        exact hb (Submodule.map_injective_of_injective (f := (fixed (ρ i) K).subtype) Subtype.val_injective
          (by rw [hbot, Submodule.map_bot]))
      · rintro e he _ ⟨x, hx, rfl⟩
        exact ⟨_, hS _ (hop e he) x hx, rfl⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hxy⟩ := h1 x.2
    have : y = x := Subtype.ext hxy
    exact this ▸ hy
  have hS2 : ∀ i j (φ : fixed (ρ i) K ≃ₗ[ℂ] fixed (ρ j) K),
      (∀ a ∈ A, ∀ x, φ (a i x) = a j (φ x)) → i = j := by
    intro i j φ hφ
    refine hne i j ?_
    obtain ⟨T, hT⟩ := LinearMap.exists_extend ((fixed (ρ j) K).subtype ∘ₗ φ.toLinearMap)
    have hTv : ∀ v (hv : v ∈ fixed (ρ i) K), T v = (φ ⟨v, hv⟩ : Y j) := fun v hv =>
      LinearMap.congr_fun hT ⟨v, hv⟩
    refine GlobalTheory.T.irreducible_hom_fixed_vectors F ι K hKo hKc (Y i) (Y j) (ρ i) (ρ j) (hs i) (hi i) (hs j) (hi j) (h0 i) T
      ?_ ?_ ?_ ?_
    · intro v hv
      rw [hTv v hv]
      exact (φ _).2
    · intro w hw
      refine ⟨(φ.symm ⟨w, hw⟩ : Y i), (φ.symm _).2, ?_⟩
      rw [hTv _ (φ.symm ⟨w, hw⟩).2]
      simp
    · intro v hv h
      rw [hTv v hv] at h
      have h2 : φ ⟨v, hv⟩ = 0 := Subtype.ext h
      have h3 := φ.map_eq_zero_iff.1 h2
      exact congrArg Subtype.val h3
    · intro e he v hv
      have hm := (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e he (Y i) (ρ i) v hv).1
      rw [hTv _ hm, hTv v hv]
      have := hφ _ (hop e he) ⟨v, hv⟩
      exact congrArg Subtype.val this
  obtain ⟨a, ⟨e, he, hh⟩, ha⟩ := abstract_density (fun i => fixed (ρ i) K) A hS1 hS2 f
  exact ⟨e, he, fun i x => by rw [← hh i x, ha i]⟩

structure BRep (F ι : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Fintype ι] [DecidableEq ι] where
  X : Type
  [g : AddCommGroup X]
  [m : Module ℂ X]
  ρ : Representation ℂ (GL ι F) X

attribute [instance] BRep.g BRep.m

theorem isolateAt : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], IsolateAt F ι := by
  intro F _ _ _ _ ι _ _ K hKo hKc V _ _ π hπ hπi ⟨v₀, hv₀, hv₀0⟩ J _ W _ _ τ hτ hτi hne
  classical
  let J' := {j // ∃ w ∈ fixed (τ j) K, w ≠ 0}
  let st : Setoid J' := ⟨fun a b => Nonempty ((τ a.1).Equiv (τ b.1)),
    ⟨fun a => ⟨Representation.Equiv.refl _⟩, fun ⟨T⟩ => ⟨T.symm⟩, fun ⟨S⟩ ⟨T⟩ => ⟨S.trans T⟩⟩⟩
  let R := Quotient st
  haveI : Fintype R := Fintype.ofFinite _
  let b : Option R → BRep F ι := fun o => o.elim ⟨V, π⟩ (fun r => ⟨W r.out.1, τ r.out.1⟩)
  obtain ⟨l, hl⟩ : ∃ l : V →ₗ[ℂ] ℂ, l v₀ = 1 := by
    have h : ¬ ∀ f : Module.Dual ℂ V, f v₀ = 0 := fun h =>
      hv₀0 ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).1 h)
    push_neg at h
    obtain ⟨f, hf⟩ := h
    exact ⟨(f v₀)⁻¹ • f, by simp [hf]⟩
  let P : Module.End ℂ (fixed π K) :=
    (LinearMap.toSpanSingleton ℂ _ ⟨v₀, hv₀⟩) ∘ₗ (l ∘ₗ (fixed π K).subtype)
  let f : ∀ o : Option R, Module.End ℂ (fixed (b o).ρ K) := fun o =>
    match o with
    | none => P
    | some _ => 0
  obtain ⟨e, he, hh⟩ := density_core hKo hKc (fun o => (b o).ρ)
    (fun o => match o with
      | none => hπ
      | some r => hτ _)
    (fun o => match o with
      | none => hπi
      | some r => hτi _)
    (fun o => match o with
      | none => ⟨v₀, hv₀, hv₀0⟩
      | some r => r.out.2)
    (by
      rintro (_ | r) (_ | r') ⟨T⟩
      · rfl
      · exact ((hne r'.out.1).false T.symm).elim
      · exact ((hne r.out.1).false T).elim
      · have : r = r' := by
          rw [← Quotient.out_eq r, ← Quotient.out_eq r']
          exact Quotient.sound (s := st) ⟨T⟩
        rw [this])
    f
  refine ⟨e, he, v₀, hv₀, l, hl, ?_, ?_⟩
  · intro v hv
    exact hh none ⟨v, hv⟩
  · intro j w hw
    by_cases hw0 : w = 0
    · rw [hw0]
      exact hk_zero_right _ _
    let r : R := Quotient.mk st ⟨j, w, hw, hw0⟩
    obtain ⟨T⟩ : Nonempty ((τ r.out.1).Equiv (τ j)) := Quotient.exact (s := st) (Quotient.out_eq r)
    have hT : ∀ g x, T.toLinearEquiv (τ r.out.1 g x) = τ j g (T.toLinearEquiv x) := fun g x =>
      LinearMap.congr_fun (T.isIntertwining' g) x
    have hw' : T.toLinearEquiv.symm w ∈ fixed (τ r.out.1) K := by
      intro k
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      apply T.toLinearEquiv.injective
      rw [hT, LinearEquiv.apply_symm_apply]
      simpa using hw k
    have h1 : hk (τ r.out.1) K e (T.toLinearEquiv.symm w) = 0 := hh (some r) ⟨_, hw'⟩
    have h2 := map_hk (K := K) T e (T.toLinearEquiv.symm w)
    rw [h1, map_zero, LinearEquiv.apply_symm_apply] at h2
    exact h2.symm

end GlobalTheory.CompanionTheory.Isolate
