import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTraceIndicatorLevelLocalUnitary

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.TwTrLin PositivityTheory.Rg.BcB.F.Eig
open scoped Classical Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.LocHecke

section Generic

variable {G : Type} [Group G]

theorem finsum_left {M : Type} [AddCommMonoid M] (K' : Subgroup G) (F : G → M)
    (hr : ∀ k ∈ K', ∀ x, F (x * k) = F x) (g : G) :
    ∑ᶠ q : G ⧸ K', F (g * q.out) = ∑ᶠ q : G ⧸ K', F q.out := by
  have key : ∀ q : G ⧸ K', F (g * q.out) = F ((g • q : G ⧸ K').out) := by
    intro q
    have hq : (g • q : G ⧸ K') = ((g * q.out : G) : G ⧸ K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' (g * q.out)
    rw [hq, hh, hr _ h.2]
  have e : ∑ᶠ q : G ⧸ K', F ((g • q : G ⧸ K').out) = ∑ᶠ q : G ⧸ K', F q.out :=
    finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K')) (f := fun q => F q.out)
  rw [finsum_congr key, e]

theorem hint_eq (K K' : Subgroup G) (hle : K' ≤ K) (hidx : K'.relIndex K ≠ 0) (u : G → ℂ)
    (hr : ∀ k ∈ K', ∀ x, u (x * k) = u x) (hfin : {q : G ⧸ K' | u q.out ≠ 0}.Finite) :
    hint K u = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ K', u q.out := by
  set S : Subgroup G := rStab u ⊓ K with hS
  have hKS : K' ≤ S := fun k hk => Subgroup.mem_inf.mpr ⟨fun x => hr k hk x, hle hk⟩
  have hSK : S ≤ K := inf_le_right
  have hmul : K'.relIndex S * S.relIndex K = K'.relIndex K :=
    Subgroup.relIndex_mul_relIndex K' S K hKS hSK
  have h1 : K'.relIndex S ≠ 0 := fun h => hidx (by rw [← hmul, h, zero_mul])
  have h2 : S.relIndex K ≠ 0 := fun h => hidx (by rw [← hmul, h, mul_zero])
  have hrS : ∀ s ∈ S, ∀ x, u (x * s) = u x := fun s hs x => (Subgroup.mem_inf.mp hs).1 x
  let e := Subgroup.quotientEquivProdOfLE (α := G) hKS
  have he : ∀ q : G ⧸ K', u q.out = u ((e q).1).out := by
    intro q
    have hq : (e q).1 = ((q.out : G) : G ⧸ S) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq]
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S q.out
    rw [hs, hrS _ s.2]
  haveI : Finite (S ⧸ K'.subgroupOf S) := Nat.finite_of_card_ne_zero h1
  letI : Fintype (S ⧸ K'.subgroupOf S) := Fintype.ofFinite _
  have h3 : ∑ᶠ q : G ⧸ K', u ((e q).1).out =
      ∑ᶠ x : (G ⧸ S) × (S ⧸ K'.subgroupOf S), u x.1.out :=
    finsum_comp_equiv e (f := fun x => u x.1.out)
  have hfinP : (Function.support fun x : (G ⧸ S) × (S ⧸ K'.subgroupOf S) => u x.1.out).Finite := by
    refine (hfin.image e).subset ?_
    intro x hx
    refine ⟨e.symm x, ?_, by simp⟩
    show u (e.symm x).out ≠ 0
    rw [he, Equiv.apply_symm_apply]
    exact hx
  have hfinA : {p : G ⧸ S | u p.out ≠ 0}.Finite := by
    refine (hfinP.image Prod.fst).subset ?_
    intro p hp
    exact ⟨(p, ((1 : S) : S ⧸ K'.subgroupOf S)), hp, rfl⟩
  have hsub1 : (Function.support fun x : (G ⧸ S) × (S ⧸ K'.subgroupOf S) => u x.1.out) ⊆
      ↑(hfinA.toFinset ×ˢ (Finset.univ : Finset (S ⧸ K'.subgroupOf S))) := by
    intro x hx
    simp only [Finset.coe_product, Set.Finite.coe_toFinset, Finset.coe_univ, Set.mem_prod,
      Set.mem_univ, and_true, Set.mem_ofPred_eq]
    exact hx
  have hsub2 : (Function.support fun p : G ⧸ S => u p.out) ⊆ ↑hfinA.toFinset := by
    intro p hp
    rw [Set.Finite.coe_toFinset]
    exact hp
  have hsum : ∑ᶠ q : G ⧸ K', u q.out = ((K'.relIndex S : ℕ) : ℂ) * ∑ᶠ p : G ⧸ S, u p.out := by
    rw [finsum_congr he, h3, finsum_eq_sum_of_support_subset _ hsub1,
      finsum_eq_sum_of_support_subset _ hsub2, Finset.sum_product]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 2
    rw [Fintype.card_eq_nat_card]
    rfl
  have hdef : hint K u = ((S.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : G ⧸ S, u p.out := rfl
  have ha : ((K'.relIndex S : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h1
  rw [hdef, hsum, ← hmul, Nat.cast_mul, mul_inv, mul_comm ((K'.relIndex S : ℂ))⁻¹ _, mul_assoc,
    ← mul_assoc ((K'.relIndex S : ℂ))⁻¹, inv_mul_cancel₀ ha, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_apply (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite) (v : V) :
    levOp ρ K K' f LinearMap.id v = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ K', f q.out • ρ q.out v := by
  have hs := GlobalTheory.TwTrLin.term_fin ρ K' f LinearMap.id hfin
  have key : (∑ᶠ q : G ⧸ K', f q.out • ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V)) v =
      ∑ᶠ q : G ⧸ K', f q.out • ρ q.out v := by
    have := map_finsum (LinearMap.applyₗ (R := ℂ) (M := V) (M₂ := V) v) hs
    simpa using this
  simp only [levOp, LinearMap.smul_apply, key]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem fin_translate {K' : Subgroup G} (ho : IsOpen (K' : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) (g : G) :
    {q : G ⧸ K' | f (g * q.out) ≠ 0}.Finite := by
  have h' : HasCompactSupport (fun x => f (g * x)) := hf.comp_homeomorph (Homeomorph.mulLeft g)
  exact GlobalTheory.TwTrLin.finite_out_support ho h'

theorem isHecke_add {K' : Subgroup G} {f₁ f₂ : G → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) :
    IsHecke K' (f₁ + f₂) := by
  unfold GlobalTheory.BCT.IsHecke at *
  refine ⟨h₁.1.add h₂.1, fun k hk x => ?_⟩
  obtain ⟨a1, b1⟩ := h₁.2 k hk x
  obtain ⟨a2, b2⟩ := h₂.2 k hk x
  simp only [Pi.add_apply, a1, b1, a2, b2, and_self]

theorem isHecke_smul {K' : Subgroup G} {f : G → ℂ} (z : ℂ) (h : IsHecke K' f) : IsHecke K' (z • f) := by
  unfold GlobalTheory.BCT.IsHecke at *
  refine ⟨h.1.mono (Function.support_const_smul_subset z f), fun k hk x => ?_⟩
  obtain ⟨a, b⟩ := h.2 k hk x
  simp only [Pi.smul_apply, a, b, and_self]

end Generic

section Conv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem conv_formula {K K' : Subgroup G} (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) (hidx : K'.relIndex K ≠ 0)
    {f₁ f₂ : G → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) (y : G) :
    hint K (fun z => f₁ z * f₂ (z⁻¹ * y)) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * y) := by
  have fin1 := GlobalTheory.TwTrLin.finite_out_support ho h₁.1
  refine GlobalTheory.CompanionTheory.LocHecke.hint_eq K K' hle hidx _ ?_ (fin1.subset ?_)
  · intro k hk z
    try dsimp only
    rw [(h₁.2 k hk z).2, _root_.mul_inv_rev, mul_assoc, (h₂.2 k⁻¹ (K'.inv_mem hk) _).1]
  · intro q hq h0
    apply hq
    simp [h0]

theorem isHecke_conv {K K' : Subgroup G} (ho : IsOpen (K' : Set G)) (hle : K' ≤ K) (hidx : K'.relIndex K ≠ 0)
    {f₁ f₂ : G → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) :
    IsHecke K' (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) := by
  have hconv : ∀ y, hint K (fun z => f₁ z * f₂ (z⁻¹ * y)) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * y) :=
    fun y => GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx h₁ h₂ y
  have fin1 := GlobalTheory.TwTrLin.finite_out_support ho h₁.1
  unfold GlobalTheory.BCT.IsHecke at *
  refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
  · refine HasCompactSupport.intro
      (K := ⋃ q ∈ fin1.toFinset, (fun x => q.out * x) '' tsupport f₂)
      (fin1.toFinset.isCompact_biUnion fun q _ => IsCompact.image h₂.1 (by fun_prop)) ?_
    intro y hy
    try dsimp only
    rw [hconv, finsum_eq_zero_of_forall_eq_zero, mul_zero]
    intro q
    by_cases hq : f₁ q.out = 0
    · rw [hq, zero_mul]
    · have h0 : f₂ (q.out⁻¹ * y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        apply hy
        exact Set.mem_iUnion₂.mpr ⟨q, (Set.Finite.mem_toFinset fin1).mpr hq,
          ⟨q.out⁻¹ * y, hmem, by simp⟩⟩
      rw [h0, mul_zero]
  · dsimp only
    rw [hconv, hconv]
    congr 1
    have hΦ : ∀ k' ∈ K', ∀ z, f₁ (z * k') * f₂ ((z * k')⁻¹ * (k * x)) = f₁ z * f₂ (z⁻¹ * (k * x)) := by
      intro k' hk' z
      rw [(h₁.2 k' hk' z).2, _root_.mul_inv_rev, mul_assoc, (h₂.2 k'⁻¹ (K'.inv_mem hk') _).1]
    have hl : ∑ᶠ q : G ⧸ K', f₁ (k * q.out) * f₂ ((k * q.out)⁻¹ * (k * x)) =
        ∑ᶠ q : G ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * (k * x)) :=
      GlobalTheory.CompanionTheory.LocHecke.finsum_left K' (fun z => f₁ z * f₂ (z⁻¹ * (k * x))) hΦ k
    rw [← hl]
    apply finsum_congr
    intro q
    rw [(h₁.2 k hk q.out).1, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · dsimp only
    rw [hconv, hconv]
    congr 1
    apply finsum_congr
    intro q
    rw [← mul_assoc, (h₂.2 k hk _).2]

theorem isHecke_star {K' : Subgroup G} {f : G → ℂ} (h : IsHecke K' f) :
    IsHecke K' (fun y => starRingEnd ℂ (f y⁻¹)) := by
  unfold GlobalTheory.BCT.IsHecke at *
  obtain ⟨hc, hinv⟩ := h
  refine ⟨?_, fun k hk x => ?_⟩
  · exact (hc.comp_homeomorph (Homeomorph.inv G)).comp_left (g := starRingEnd ℂ) (map_zero _)
  · have hk' : k⁻¹ ∈ K' := K'.inv_mem hk
    refine ⟨?_, ?_⟩
    · dsimp only
      rw [_root_.mul_inv_rev, (hinv _ hk' _).2]
    · dsimp only
      rw [_root_.mul_inv_rev, (hinv _ hk' _).1]

theorem levOp_conv (ρ : Representation ℂ G V) {K K' : Subgroup G} (ho : IsOpen (K' : Set G)) (hle : K' ≤ K)
    (hidx : K'.relIndex K ≠ 0) {f₁ f₂ : G → ℂ} (h₁ : IsHecke K' f₁) (h₂ : IsHecke K' f₂) {v : V}
    (hv : v ∈ fixed ρ K') :
    levOp ρ K K' (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) LinearMap.id v =
      levOp ρ K K' f₁ LinearMap.id (levOp ρ K K' f₂ LinearMap.id v) := by
  have hF := GlobalTheory.CompanionTheory.LocHecke.isHecke_conv ho hle hidx h₁ h₂
  have fin1 := GlobalTheory.TwTrLin.finite_out_support ho h₁.1
  have fin2 := GlobalTheory.TwTrLin.finite_out_support ho h₂.1
  have finF := GlobalTheory.TwTrLin.finite_out_support ho hF.1
  have hfix : ∀ k ∈ K', ρ k v = v := (GlobalTheory.TwTrLin.mem_fixed_iff ρ K' v).mp hv
  have stepC : ∀ q : G ⧸ K', ∑ᶠ p : G ⧸ K', f₂ (q.out⁻¹ * p.out) • ρ p.out v =
      ρ q.out (∑ᶠ r : G ⧸ K', f₂ r.out • ρ r.out v) := by
    intro q
    have hsupp : (Function.support fun r : G ⧸ K' => f₂ r.out • ρ r.out v).Finite :=
      fin2.subset (fun r hr h0 => hr (by simp [h0]))
    rw [map_finsum (ρ q.out) hsupp]
    have hrΦ : ∀ k ∈ K', ∀ x : G, f₂ (q.out⁻¹ * (x * k)) • ρ (x * k) v = f₂ (q.out⁻¹ * x) • ρ x v := by
      intro k hk x
      rw [← mul_assoc, (h₂.2 k hk _).2, map_mul]
      show _ • ρ x (ρ k v) = _
      rw [hfix k hk]
    have hl : ∑ᶠ r : G ⧸ K', f₂ (q.out⁻¹ * (q.out * r.out)) • ρ (q.out * r.out) v =
        ∑ᶠ p : G ⧸ K', f₂ (q.out⁻¹ * p.out) • ρ p.out v :=
      GlobalTheory.CompanionTheory.LocHecke.finsum_left K' (fun x => f₂ (q.out⁻¹ * x) • ρ x v) hrΦ q.out
    rw [← hl]
    apply finsum_congr
    intro r
    rw [inv_mul_cancel_left, map_mul, map_smul]
    rfl
  have hconv : ∀ y, hint K (fun z => f₁ z * f₂ (z⁻¹ * y)) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : G ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * y) :=
    fun y => GlobalTheory.CompanionTheory.LocHecke.conv_formula ho hle hidx h₁ h₂ y
  rw [GlobalTheory.CompanionTheory.LocHecke.levOp_apply ρ K K' _ finF, GlobalTheory.CompanionTheory.LocHecke.levOp_apply ρ K K' _ fin2,
    GlobalTheory.CompanionTheory.LocHecke.levOp_apply ρ K K' _ fin1]
  simp_rw [hconv]
  generalize ((K'.relIndex K : ℕ) : ℂ)⁻¹ = c
  refine congrArg (c • ·) ?_
  set S₁ : Finset (G ⧸ K') := fin1.toFinset with hS₁
  set T : Finset (G ⧸ K') :=
    S₁.biUnion (fun q => (GlobalTheory.CompanionTheory.LocHecke.fin_translate ho h₂.1 q.out⁻¹).toFinset) with hT
  have memT : ∀ q ∈ S₁, ∀ p : G ⧸ K', f₂ (q.out⁻¹ * p.out) ≠ 0 → p ∈ T := by
    intro q hq p hp
    rw [hT, Finset.mem_biUnion]
    exact ⟨q, hq, (Set.Finite.mem_toFinset _).mpr hp⟩
  have hsub : ∀ p : G ⧸ K', (Function.support fun q : G ⧸ K' => f₁ q.out * f₂ (q.out⁻¹ * p.out)) ⊆ ↑S₁ := by
    intro p q hq
    rw [hS₁, Set.Finite.coe_toFinset]
    intro h0
    exact hq (by simp [h0])
  have hsubT : (Function.support fun p : G ⧸ K' =>
      (c * ∑ q ∈ S₁, f₁ q.out * f₂ (q.out⁻¹ * p.out)) • ρ p.out v) ⊆ ↑T := by
    intro p hp
    by_contra hpT
    apply hp
    have hz : ∑ q ∈ S₁, f₁ q.out * f₂ (q.out⁻¹ * p.out) = 0 := by
      refine Finset.sum_eq_zero fun q hq => ?_
      have hb : f₂ (q.out⁻¹ * p.out) = 0 := by
        by_contra hb
        exact hpT (memT q hq p hb)
      rw [hb, mul_zero]
    simp [hz]
  have hsubT' : ∀ q ∈ S₁, (Function.support fun p : G ⧸ K' => f₂ (q.out⁻¹ * p.out) • ρ p.out v) ⊆ ↑T := by
    intro q hq p hp
    by_contra hpT
    apply hp
    have hb : f₂ (q.out⁻¹ * p.out) = 0 := by
      by_contra hb
      exact hpT (memT q hq p hb)
    simp [hb]
  have hsubS : (Function.support fun q : G ⧸ K' =>
      f₁ q.out • ρ q.out (c • ∑ᶠ r : G ⧸ K', f₂ r.out • ρ r.out v)) ⊆ ↑S₁ := by
    intro q hq
    rw [hS₁, Set.Finite.coe_toFinset]
    intro h0
    exact hq (by simp [h0])
  calc ∑ᶠ p : G ⧸ K', (c * ∑ᶠ q : G ⧸ K', f₁ q.out * f₂ (q.out⁻¹ * p.out)) • ρ p.out v
      = ∑ᶠ p : G ⧸ K', (c * ∑ q ∈ S₁, f₁ q.out * f₂ (q.out⁻¹ * p.out)) • ρ p.out v := by
        apply finsum_congr
        intro p
        rw [finsum_eq_sum_of_support_subset _ (hsub p)]
    _ = ∑ p ∈ T, (c * ∑ q ∈ S₁, f₁ q.out * f₂ (q.out⁻¹ * p.out)) • ρ p.out v :=
        finsum_eq_sum_of_support_subset _ hsubT
    _ = ∑ q ∈ S₁, c • f₁ q.out • ∑ p ∈ T, f₂ (q.out⁻¹ * p.out) • ρ p.out v := by
        simp only [Finset.mul_sum, Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ q ∈ S₁, c • f₁ q.out • ρ q.out (∑ᶠ r : G ⧸ K', f₂ r.out • ρ r.out v) := by
        refine Finset.sum_congr rfl fun q hq => ?_
        rw [← finsum_eq_sum_of_support_subset _ (hsubT' q hq), stepC q]
    _ = ∑ q ∈ S₁, f₁ q.out • ρ q.out (c • ∑ᶠ r : G ⧸ K', f₂ r.out • ρ r.out v) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [map_smul, smul_comm]
    _ = ∑ᶠ q : G ⧸ K', f₁ q.out • ρ q.out (c • ∑ᶠ r : G ⧸ K', f₂ r.out • ρ r.out v) :=
        (finsum_eq_sum_of_support_subset _ hsubS).symm

end Conv

section Unitary

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E}

theorem locOp_mapsTo (σ : SmIrr (UL n w)) {K' : Subgroup (UL n w)} (ho : IsOpen (K' : Set (UL n w))) {f : UL n w → ℂ}
    (hf : IsHecke K' f) : ∀ v ∈ fixed σ.ρ K', levOp σ.ρ (KL n w) K' f LinearMap.id v ∈ fixed σ.ρ K' :=
  GlobalTheory.TwTrLin.levOp_mapsTo σ.ρ (KL n w) K' LinearMap.id f (GlobalTheory.TwTrLin.finite_out_support ho hf.1)
    (fun k hk x => (hf.2 k hk x).1) (fun k hk x => (hf.2 k hk x).2) (fun _ hv => hv)

theorem locOp_val (σ : SmIrr (UL n w)) {K' : Subgroup (UL n w)} (ho : IsOpen (K' : Set (UL n w))) {f : UL n w → ℂ}
    (hf : IsHecke K' f) (v : fixed σ.ρ K') : (locOp σ K' f v).1 = levOp σ.ρ (KL n w) K' f LinearMap.id v.1 := by
  unfold PositivityTheory.Rg.BcB.F.Eig.locOp
  rw [dif_pos (GlobalTheory.CompanionTheory.LocHecke.locOp_mapsTo σ ho hf)]
  rfl

end Unitary

theorem locAlg : LocAlg := by
  intro E iF iN iC n w σ K' hlev f₁ f₂ h₁ h₂
  have hunit := GlobalTheory.TwTrUnit.twTr_unit E n w K' hlev σ
  obtain ⟨ho, hle, -⟩ := hlev
  have hidx : K'.relIndex (KL n w) ≠ 0 := hunit.2.1
  have hc : IsHecke K' (lconv f₁ f₂) := GlobalTheory.CompanionTheory.LocHecke.isHecke_conv ho hle hidx h₁ h₂
  have hsum : ∀ z : ℂ, IsHecke K' (f₁ + z • f₂) := fun z =>
    GlobalTheory.CompanionTheory.LocHecke.isHecke_add h₁ (GlobalTheory.CompanionTheory.LocHecke.isHecke_smul z h₂)
  have hind : ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) =
      ((K'.relIndex (KL n w) : ℕ) : ℂ) • (K' : Set (UL n w)).indicator 1 := by
    funext x
    by_cases hx : x ∈ (K' : Set (UL n w))
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hI : IsHecke K' ((K' : Set (UL n w)).indicator fun _ => ((K'.relIndex (KL n w) : ℕ) : ℂ)) := by
    rw [hind]
    exact GlobalTheory.CompanionTheory.LocHecke.isHecke_smul _ hunit.1
  refine ⟨?_, fun v => GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho h₁ v, hc,
    GlobalTheory.CompanionTheory.LocHecke.isHecke_star h₁, ?_, ?_, hI, ?_⟩
  · unfold GlobalTheory.BCT.twTr PositivityTheory.Rg.BcB.F.Eig.locOp
    split_ifs with h
    · rfl
    · simp
  · refine LinearMap.ext fun v => Subtype.ext ?_
    show (locOp σ K' (lconv f₁ f₂) v).1 = (locOp σ K' f₁ (locOp σ K' f₂ v)).1
    rw [GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho hc, GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho h₁,
      GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho h₂]
    exact GlobalTheory.CompanionTheory.LocHecke.levOp_conv σ.ρ ho hle hidx h₁ h₂ v.2
  · intro z
    refine LinearMap.ext fun v => Subtype.ext ?_
    show (locOp σ K' (f₁ + z • f₂) v).1 = (locOp σ K' f₁ v).1 + z • (locOp σ K' f₂ v).1
    rw [GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho (hsum z), GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho h₁,
      GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho h₂,
      GlobalTheory.TwTrLin.levOp_add σ.ρ (KL n w) K' f₁ (z • f₂) LinearMap.id
        (GlobalTheory.TwTrLin.finite_out_support ho h₁.1)
        (GlobalTheory.TwTrLin.finite_out_support ho (GlobalTheory.CompanionTheory.LocHecke.isHecke_smul z h₂).1),
      GlobalTheory.TwTrLin.levOp_smul_fun]
    rfl
  · refine LinearMap.ext fun v => Subtype.ext ?_
    rw [GlobalTheory.CompanionTheory.LocHecke.locOp_val σ ho hI, hind, GlobalTheory.TwTrLin.levOp_smul_fun]
    obtain ⟨x₀, hx₀, hx⟩ := GlobalTheory.TwTrLin.levOp_unit σ.ρ (KL n w) K'
    rw [hx]
    have hv : σ.ρ x₀ v.1 = v.1 := (GlobalTheory.TwTrLin.mem_fixed_iff σ.ρ K' v.1).mp v.2 x₀ hx₀
    have hne : ((K'.relIndex (KL n w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hidx
    simp only [LinearMap.smul_apply, hv, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rfl

end GlobalTheory.CompanionTheory.LocHecke

end
