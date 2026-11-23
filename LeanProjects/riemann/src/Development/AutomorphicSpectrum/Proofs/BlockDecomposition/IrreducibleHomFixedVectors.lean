import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.HeckeInj

section Generic

variable {G : Type} [Group G]

theorem fix_of_mem {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
    {v : V} (hv : v ∈ fixed ρ K) {c : G} (hc : c ∈ K) : ρ c v = v := by
  have := hv ⟨c, hc⟩
  simpa using this

theorem eq_top_of_inv {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : ρ.IsIrreducible) (N : Submodule ℂ V) (hN : ∀ g, ∀ v ∈ N, ρ g v ∈ N) {w : V} (hw : w ∈ N)
    (h0 : w ≠ 0) : N = ⊤ := by
  let S : Subrepresentation ρ := { toSubmodule := N, apply_mem_toSubmodule := fun g v hv => hN g v hv }
  rcases hρ.eq_bot_or_eq_top S with h | h
  · exfalso
    have h1 : w ∈ S.toSubmodule := hw
    rw [h] at h1
    exact h0 h1
  · exact congrArg Subrepresentation.toSubmodule h

def act {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) : (G →₀ M) →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun g => ρ g ∘ₗ A

theorem act_single {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) (g : G) (m : M) :
    act ρ A (Finsupp.single g m) = ρ g (A m) := by
  simp [act]

theorem act_translate {V M : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G V) (A : M →ₗ[ℂ] V) (h : G) (x : G →₀ M) :
    act ρ A (Finsupp.lmapDomain M ℂ (fun g => h * g) x) = ρ h (act ρ A x) := by
  have : act ρ A ∘ₗ Finsupp.lmapDomain M ℂ (fun g => h * g) = ρ h ∘ₗ act ρ A := by
    refine Finsupp.lhom_ext fun a b => ?_
    simp [act_single, Finsupp.mapDomain_single]
  exact LinearMap.congr_fun this x

def avg {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K L : Subgroup G)
    [Fintype (K ⧸ L.subgroupOf K)] : V →ₗ[ℂ] V :=
  ∑ q : K ⧸ L.subgroupOf K, ρ ((q.out : K) : G)

theorem avg_of_fixed {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K L : Subgroup G)
    [Fintype (K ⧸ L.subgroupOf K)] {v : V} (hv : v ∈ fixed ρ K) :
    avg ρ K L v = (Fintype.card (K ⧸ L.subgroupOf K) : ℂ) • v := by
  simp only [avg, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun q _ => fix_of_mem hv (q.out : K).2]
  simp [Nat.cast_smul_eq_nsmul]

def cosetFn (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g x : G) : ℂ :=
  open Classical in
  ∑ q : K ⧸ L.subgroupOf K,
    if (QuotientGroup.mk x : G ⧸ K) = QuotientGroup.mk (((q.out : K) : G) * g) then 1 else 0

theorem cosetFn_right (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (x * k) = cosetFn K L g x := by
  unfold cosetFn
  rw [QuotientGroup.mk_mul_of_mem x hk]

theorem cosetFn_left (K L : Subgroup G) [Fintype (K ⧸ L.subgroupOf K)] (g : G)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) (x : G) {k : G} (hk : k ∈ K) :
    cosetFn K L g (k * x) = cosetFn K L g x := by
  classical
  unfold cosetFn
  let kk : K := ⟨k, hk⟩
  refine Fintype.sum_equiv (MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) q =
      (QuotientGroup.mk (kk⁻¹ * q.out) : K ⧸ L.subgroupOf K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul (L.subgroupOf K) (kk⁻¹ * q.out)
  have hcL : ((c : K) : G) ∈ L := Subgroup.mem_subgroupOf.1 c.2
  have hmk : (QuotientGroup.mk (((((MulAction.toPerm kk⁻¹ : Equiv.Perm (K ⧸ L.subgroupOf K)) q).out : K) : G) * g) : G ⧸ K)
      = QuotientGroup.mk (k⁻¹ * (((q.out : K) : G) * g)) := by
    rw [hq, hc, QuotientGroup.eq]
    have := hL _ (L.inv_mem hcL)
    simpa [kk, mul_assoc] using this
  have hiff : ((QuotientGroup.mk (k * x) : G ⧸ K) = QuotientGroup.mk (((q.out : K) : G) * g)) ↔
      ((QuotientGroup.mk x : G ⧸ K) = QuotientGroup.mk (k⁻¹ * (((q.out : K) : G) * g))) := by
    rw [QuotientGroup.eq, QuotientGroup.eq]
    simp [mul_assoc]
  rw [hmk]
  simp only [hiff]

end Generic

section Hecke

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isHk_cosetFn {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)]
    (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) (g : GL ι F)
    (hL : ∀ l ∈ L, g⁻¹ * l * g ∈ K) : IsHk K (cosetFn K L g) := by
  classical
  refine ⟨hKo, hKc, ?_, fun k₁ h₁ k₂ h₂ x => ?_⟩
  · let C : Set (GL ι F) := ⋃ q : K ⧸ L.subgroupOf K, (fun y => (((q.out : K) : GL ι F) * g) * y) '' (K : Set (GL ι F))
    have hC : IsCompact C := isCompact_iUnion fun q => hKc.image (continuous_const.mul continuous_id)
    refine HasCompactSupport.of_support_subset_isCompact hC fun x hx => ?_
    obtain ⟨q, hq⟩ : ∃ q : K ⧸ L.subgroupOf K,
        (QuotientGroup.mk x : GL ι F ⧸ K) = QuotientGroup.mk (((q.out : K) : GL ι F) * g) := by
      by_contra h
      push_neg at h
      refine (Function.mem_support.1 hx) ?_
      unfold cosetFn
      exact Finset.sum_eq_zero fun q _ => if_neg (h q)
    refine Set.mem_iUnion.2 ⟨q, _, QuotientGroup.eq.1 hq.symm, ?_⟩
    group
  · rw [cosetFn_right K L g _ h₂, cosetFn_left K L g hL _ h₁]

theorem hk_cosetFn {K L : Subgroup (GL ι F)} [Fintype (K ⧸ L.subgroupOf K)] (g : GL ι F)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) {v : V} (hv : v ∈ fixed ρ K) :
    hk ρ K (cosetFn K L g) v = avg ρ K L (ρ g v) := by
  classical
  have step : ∀ p : GL ι F ⧸ K, cosetFn K L g p.out • ρ p.out v =
      ∑ q : K ⧸ L.subgroupOf K, if p = QuotientGroup.mk (((q.out : K) : GL ι F) * g)
        then ρ (((q.out : K) : GL ι F) * g) v else 0 := by
    intro p
    unfold cosetFn
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [QuotientGroup.out_eq']
    split_ifs with h
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K (((q.out : K) : GL ι F) * g)
      rw [one_smul, h, hc, map_mul, Module.End.mul_apply, fix_of_mem hv c.2]
    · rw [zero_smul]
  unfold hk
  rw [finsum_congr step, finsum_sum_comm]
  · simp only [avg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (((q.out : K) : GL ι F) * g))]
    · simp [map_mul, Module.End.mul_apply]
    · intro p hp
      exact if_neg hp
  · intro q _
    refine (Set.finite_singleton (QuotientGroup.mk (((q.out : K) : GL ι F) * g) : GL ι F ⧸ K)).subset ?_
    intro p hp
    by_contra h
    exact (Function.mem_support.1 hp) (if_neg h)

theorem exists_open_sub {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (s : Finset (GL ι F)) :
    ∃ L : Subgroup (GL ι F), IsOpen (L : Set (GL ι F)) ∧ L ≤ K ∧ ∀ g ∈ s, ∀ l ∈ L, g⁻¹ * l * g ∈ K := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K, hKo, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨L, hLo, hLK, hL⟩ := ih
    let C : Subgroup (GL ι F) := K.comap (MulAut.conj a⁻¹).toMonoidHom
    have hC : IsOpen (C : Set (GL ι F)) := by
      have hcont : Continuous fun l : GL ι F => a⁻¹ * l * a⁻¹⁻¹ :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hKo.preimage hcont
    refine ⟨L ⊓ C, hLo.inter hC, inf_le_left.trans hLK, fun g hg l hl => ?_⟩
    rcases Finset.mem_insert.1 hg with rfl | hg
    · have := hl.2
      simpa [C, Subgroup.mem_comap] using this
    · exact hL g hg l hl.1

theorem finite_quot {K L : Subgroup (GL ι F)} (hKc : IsCompact (K : Set (GL ι F)))
    (hLo : IsOpen (L : Set (GL ι F))) : Finite (K ⧸ L.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  exact Subgroup.quotient_finite_of_isOpen _ (hLo.preimage continuous_subtype_val)

theorem eq_zero_of_rel {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F)))
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W) (T : V →ₗ[ℂ] W)
    (hfix : ∀ v ∈ fixed π K, T v ∈ fixed τ K)
    (hT : ∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v))
    (x : GL ι F →₀ fixed π K) (ha : act π (fixed π K).subtype x = 0)
    (hb : act τ (T ∘ₗ (fixed π K).subtype) x ∈ fixed τ K) :
    act τ (T ∘ₗ (fixed π K).subtype) x = 0 := by
  classical
  obtain ⟨L, hLo, -, hL⟩ := exists_open_sub hKo x.support
  haveI := finite_quot hKc hLo
  letI : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hcard : (Fintype.card (K ⧸ L.subgroupOf K) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : avg τ K L (act τ (T ∘ₗ (fixed π K).subtype) x) = T (avg π K L (act π (fixed π K).subtype x)) := by
    simp only [act, Finsupp.coe_lsum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have h1 := hT _ (isHk_cosetFn hKo hKc g (hL g hg)) _ (x g).2
    rw [hk_cosetFn g π (x g).2, hk_cosetFn g τ (hfix _ (x g).2)] at h1
    simpa using h1.symm
  rw [ha, map_zero, map_zero, avg_of_fixed τ K L hb] at key
  exact (smul_eq_zero.1 key).resolve_left hcard

theorem hecke_determines : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι] (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) → ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL ι F) V) (τ : Representation ℂ (GL ι F) W), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → (∃ v ∈ fixed π K, v ≠ 0) → ∀ T : V →ₗ[ℂ] W, (∀ v ∈ fixed π K, T v ∈ fixed τ K) → (∀ w ∈ fixed τ K, ∃ v ∈ fixed π K, T v = w) → (∀ v ∈ fixed π K, T v = 0 → v = 0) → (∀ e, IsHk K e → ∀ v ∈ fixed π K, T (hk π K e v) = hk τ K e (T v)) → Nonempty (π.Equiv τ) := by
  intro F _ _ _ _ ι _ _ K hKo hKc V W _ _ _ _ π τ _ hπ _ hτ ⟨v₀, hv₀, hv₀0⟩ T hfix _ hinj hT
  classical
  set a := act π (fixed π K).subtype with ha_def
  set b := act τ (T ∘ₗ (fixed π K).subtype) with hb_def
  let tr : GL ι F → (GL ι F →₀ fixed π K) →ₗ[ℂ] (GL ι F →₀ fixed π K) :=
    fun h => Finsupp.lmapDomain (fixed π K) ℂ (fun g => h * g)
  have hatr : ∀ h x, a (tr h x) = π h (a x) := fun h x => act_translate π _ h x
  have hbtr : ∀ h x, b (tr h x) = τ h (b x) := fun h x => act_translate τ _ h x
  let x₀ : GL ι F →₀ fixed π K := Finsupp.single 1 ⟨v₀, hv₀⟩
  have hax₀ : a x₀ = v₀ := by simp [a, x₀, act_single]
  have hbx₀ : b x₀ = T v₀ := by simp [b, x₀, act_single]
  have hw₀ : T v₀ ≠ 0 := fun h => hv₀0 (hinj v₀ hv₀ h)
  have hsurj : Function.Surjective a := by
    refine LinearMap.range_eq_top.1 (eq_top_of_inv hπ (LinearMap.range a) ?_ ⟨x₀, hax₀⟩ hv₀0)
    rintro g _ ⟨x, rfl⟩
    exact ⟨tr g x, hatr g x⟩
  have hker : ∀ x, a x = 0 → b x = 0 := by
    intro y hy
    by_contra hne
    have htop : (LinearMap.ker a).map b = ⊤ := by
      refine eq_top_of_inv hτ _ ?_ (Submodule.mem_map_of_mem (LinearMap.mem_ker.2 hy)) hne
      rintro g _ ⟨x, hx, rfl⟩
      refine ⟨tr g x, ?_, hbtr g x⟩
      have hx' : a x = 0 := hx
      show a (tr g x) = 0
      rw [hatr, hx', map_zero]
    have hmem : T v₀ ∈ (LinearMap.ker a).map b := htop ▸ Submodule.mem_top
    obtain ⟨x, hx, hxe⟩ := hmem
    have hxe' : b x = T v₀ := hxe
    have := eq_zero_of_rel hKo hKc π τ T hfix hT x hx (by
      show b x ∈ fixed τ K
      rw [hxe']; exact hfix v₀ hv₀)
    exact hw₀ (hxe'.symm.trans this)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective a (LinearMap.range_eq_top.2 hsurj)
  have has : ∀ u, a (s u) = u := fun u => LinearMap.congr_fun hs u
  let S : V →ₗ[ℂ] W := b ∘ₗ s
  have hS : ∀ x, S (a x) = b x := by
    intro x
    have h0 : b (s (a x) - x) = 0 := hker _ (by rw [map_sub, has, sub_self])
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  have hint : ∀ g u, S (π g u) = τ g (S u) := by
    intro g u
    obtain ⟨x, rfl⟩ := hsurj u
    rw [← hatr, hS, hS, hbtr]
  let Φ : Representation.IntertwiningMap π τ :=
    { S with isIntertwining' := fun g => by ext u; exact hint g u }
  haveI := hπ
  haveI := hτ
  have hΦ : Φ ≠ 0 := by
    intro h0
    have h1 : Φ v₀ = 0 := by rw [h0]; rfl
    have h2 : Φ v₀ = T v₀ := by
      show S v₀ = T v₀
      rw [← hax₀, hS, hbx₀, hax₀]
    exact hw₀ (h2.symm.trans h1)
  exact ⟨Φ.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero Φ).resolve_right hΦ)⟩

end Hecke

end GlobalTheory.CompanionTheory.HeckeInj
