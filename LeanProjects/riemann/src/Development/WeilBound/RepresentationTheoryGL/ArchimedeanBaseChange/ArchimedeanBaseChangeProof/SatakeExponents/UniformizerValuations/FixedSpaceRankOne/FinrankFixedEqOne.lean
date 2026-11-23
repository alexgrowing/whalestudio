import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.Rg.BcB.F.EigA

section Sums

theorem finsum_refine {H M : Type} [Group H] [AddCommMonoid M] (A B : Subgroup H) (hAB : A ≤ B)
    [Finite (H ⧸ A)] (F : H → M) (hF : ∀ x, ∀ b ∈ B, F (x * b) = F x) :
    ∑ᶠ q : H ⧸ A, F q.out = (A.relIndex B) • ∑ᶠ q : H ⧸ B, F q.out := by
  classical
  let e := Subgroup.quotientEquivProdOfLE hAB
  haveI : Finite ((H ⧸ B) × (B ⧸ A.subgroupOf B)) := Finite.of_equiv _ e
  haveI : Finite (H ⧸ B) :=
    Finite.of_surjective Prod.fst (fun p =>
      ⟨(p, ((1 : B) : B ⧸ A.subgroupOf B)), rfl⟩)
  haveI : Finite (B ⧸ A.subgroupOf B) :=
    Finite.of_surjective Prod.snd (fun r => ⟨(((1 : H) : H ⧸ B), r), rfl⟩)
  letI := Fintype.ofFinite (H ⧸ A)
  letI := Fintype.ofFinite (H ⧸ B)
  letI := Fintype.ofFinite (B ⧸ A.subgroupOf B)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (p : H ⧸ B) (r : B ⧸ A.subgroupOf B), F (e.symm (p, r)).out = F p.out := by
    intro p r
    induction r using QuotientGroup.induction_on with
    | H b =>
      have h1 : e.symm (p, (b : B ⧸ A.subgroupOf B)) = ((p.out * (b : H) : H) : H ⧸ A) := rfl
      rw [h1]
      obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A (p.out * (b : H))
      rw [ha, hF _ _ (hAB a.2), hF _ _ b.2]
  simp only [key, Finset.sum_const, Finset.card_univ]
  rw [← Finset.smul_sum, Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

theorem out_mk_inv {H M : Type} [Group H] (A : Subgroup H) (F : H → M) (hF : ∀ x, ∀ a ∈ A, F (x * a) = F x)
    (y : H) : F ((y : H ⧸ A).out) = F y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A y
  rw [ha, hF _ _ a.2]

end Sums

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2

def stabK (K : Subgroup G) (g : G) : Subgroup K := (K.map (MulAut.conj g).toMonoidHom).subgroupOf K

theorem mem_stabK {K : Subgroup G} {g : G} {k : K} : k ∈ stabK K g ↔ g⁻¹ * (k : G) * g ∈ K := by
  rw [stabK, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, e⟩
    rw [← e]
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem finiteIndex_stabK {K : Subgroup G} {g : G} (h : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    (stabK K g).FiniteIndex := ⟨h⟩

def hop (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) : V →ₗ[ℂ] V :=
  ∑ᶠ q : K ⧸ stabK K g, ρ ((q.out : K) : G) ∘ₗ ρ g

theorem hop_apply (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) [Finite (K ⧸ stabK K g)] (v : V) :
    hop ρ K g v = ∑ᶠ q : K ⧸ stabK K g, ρ ((q.out : K) : G) (ρ g v) := by
  letI := Fintype.ofFinite (K ⧸ stabK K g)
  rw [hop, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  rfl

theorem term_inv {ρ : Representation ℂ G V} {K : Subgroup G} {g : G} {v : V} (hv : v ∈ fixed ρ K) :
    ∀ (x : K), ∀ h ∈ stabK K g, ρ (((x * h : K)) : G) (ρ g v) = ρ (x : G) (ρ g v) := by
  intro x h hh
  have h1 := (mem_fixed_iff.1 hv) _ (mem_stabK.1 hh)
  have e : ρ (h : G) (ρ g v) = ρ g v := by
    have : (h : G) * g = g * (g⁻¹ * (h : G) * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply, h1]
  rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, e]

theorem hop_mem_fixed {ρ : Representation ℂ G V} {K : Subgroup G} {g : G} [Finite (K ⧸ stabK K g)] {v : V}
    (hv : v ∈ fixed ρ K) : hop ρ K g v ∈ fixed ρ K := by
  letI := Fintype.ofFinite (K ⧸ stabK K g)
  rw [mem_fixed_iff]
  intro k hk
  rw [hop_apply, finsum_eq_sum_of_fintype, map_sum]
  let F : K → V := fun y => ρ (y : G) (ρ g v)
  have hF : ∀ x, ∀ h ∈ stabK K g, F (x * h) = F x := term_inv hv
  have step : ∀ q : K ⧸ stabK K g, ρ k (ρ ((q.out : K) : G) (ρ g v)) =
      F (((⟨k, hk⟩ : K) • q).out) := by
    intro q
    have hq : ((⟨k, hk⟩ : K) • q) = (((⟨k, hk⟩ : K) * q.out : K) : K ⧸ stabK K g) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, out_mk_inv _ F hF]
    simp only [F, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp only [step]
  exact Equiv.sum_comp (MulAction.toPerm (⟨k, hk⟩ : K)) (fun q : K ⧸ stabK K g => F q.out)

open Classical in

def reps (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] : Finset G :=
  Finset.image (fun q : K ⧸ stabK K g => ((q.out : K) : G) * g) Finset.univ

theorem hop_eq_reps (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] (v : V) :
    hop ρ K g v = ∑ γ ∈ reps K g, ρ γ v := by
  classical
  rw [hop_apply, finsum_eq_sum_of_fintype, reps]
  rw [Finset.sum_image]
  · simp only [map_mul, Module.End.mul_apply]
  · intro a _ b _ hab
    have : (a.out : K) = b.out := Subtype.ext (mul_right_cancel hab)
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, this]

theorem reps_spec (K : Subgroup G) (g : G) [Fintype (K ⧸ stabK K g)] :
    (∀ γ ∈ reps K g, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ reps K g ∧ γ⁻¹ * x ∈ K := by
  classical
  constructor
  · intro γ hγ
    unfold reps at hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hγ
    exact ⟨_, (q.out : K).2, 1, K.one_mem, by rw [mul_one]⟩
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    let q : K ⧸ stabK K g := ((⟨k₁, hk₁⟩ : K) : K ⧸ stabK K g)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (stabK K g) (⟨k₁, hk₁⟩ : K)
    have hhK : g⁻¹ * ((h : K) : G) * g ∈ K := mem_stabK.1 h.2
    have hx1 : (((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂) ∈ K := by
      have e : (((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂) = (g⁻¹ * ((h : K) : G) * g)⁻¹ * k₂ := by
        rw [show q.out = (⟨k₁, hk₁⟩ : K) * (h : K) from hh]
        simp only [Subgroup.coe_mul]
        group
      rw [e]
      exact K.mul_mem (K.inv_mem hhK) hk₂
    refine ⟨((q.out : K) : G) * g, ⟨by unfold reps; exact Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hx1⟩, ?_⟩
    rintro γ ⟨hγ, hγx⟩
    unfold reps at hγ
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hγ
    have hmem : g⁻¹ * (((q'.out : K)⁻¹ * q.out : K) : G) * g ∈ K := by
      have e : g⁻¹ * (((q'.out : K)⁻¹ * q.out : K) : G) * g =
          ((((q'.out : K) : G) * g)⁻¹ * (k₁ * g * k₂)) * ((((q.out : K) : G) * g)⁻¹ * (k₁ * g * k₂))⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact K.mul_mem hγx (K.inv_mem hx1)
    have hqq : q' = q := by
      rw [← QuotientGroup.out_eq' q', ← QuotientGroup.out_eq' q]
      exact QuotientGroup.eq.2 (mem_stabK.2 hmem)
    rw [hqq]

theorem comm_core (ρ : Representation ℂ G V) (J : Subgroup G) (τ : G → G) (hmul : ∀ a b, τ (a * b) = τ b * τ a)
    (hinv : ∀ a, τ (τ a) = a) (hdc : ∀ g : G, ∃ k₁ ∈ J, ∃ k₂ ∈ J, τ g = k₁ * g * k₂) (hJ : ∀ k ∈ J, τ k ∈ J)
    (α β : G) (R S : Finset G) (hR : ∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂)
    (hR' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J)
    (hS : ∀ γ ∈ S, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * β * k₂)
    (hS' : ∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * β * k₂) → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ J)
    (x : V) (hx : ∀ k ∈ J, ρ k x = x) :
    ∑ γ ∈ R, ρ γ (∑ δ ∈ S, ρ δ x) = ∑ δ ∈ S, ρ δ (∑ γ ∈ R, ρ γ x) := by
  classical
  let f : G ⧸ J → V := fun c => ρ c.out x
  have hf : ∀ g : G, f (g : G ⧸ J) = ρ g x := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul J g
    simp only [f, hk, map_mul, Module.End.mul_apply, hx k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ρ γ (∑ δ ∈ B, ρ δ x)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ J) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf, map_sum, map_mul, Module.End.mul_apply]
  rw [key, key]
  let T : Finset (G ⧸ J) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ J)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ J))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ J))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GlobalTheory.GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ α β R S hR hR' hS hS' c
  · convert GlobalTheory.GelfandTrick.card_pairs_le J τ hmul hinv hdc hJ β α S R hS hS' hR hR' c

def GelPair (K : Subgroup G) : Prop :=
  (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) ∧
    ∃ τ : G → G, (∀ a b, τ (a * b) = τ b * τ a) ∧ (∀ a, τ (τ a) = a) ∧
      (∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) ∧ ∀ k ∈ K, τ k ∈ K

theorem hop_comm {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (g h : G) {v : V}
    (hv : v ∈ fixed ρ K) : hop ρ K g (hop ρ K h v) = hop ρ K h (hop ρ K g v) := by
  obtain ⟨hfin, τ, hmul, hinv, hdc, hτK⟩ := hK
  haveI := finiteIndex_stabK (hfin g)
  haveI := finiteIndex_stabK (hfin h)
  letI := Fintype.ofFinite (K ⧸ stabK K g)
  letI := Fintype.ofFinite (K ⧸ stabK K h)
  simp only [hop_eq_reps]
  obtain ⟨a1, a2⟩ := reps_spec K g
  obtain ⟨b1, b2⟩ := reps_spec K h
  exact comm_core ρ K τ hmul hinv hdc hτK g h _ _ a1 a2 b1 b2 v (mem_fixed_iff.1 hv)

theorem finite_quot {K : Subgroup G} (hK : GelPair K) (g : G) : Finite (K ⧸ stabK K g) := by
  haveI := finiteIndex_stabK (hK.1 g)
  infer_instance

theorem fixed_simple {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    (W : Submodule ℂ (fixed ρ K)) (hW : W ≠ ⊥)
    (hst : ∀ g : G, ∀ w : fixed ρ K, w ∈ W → ∀ y : fixed ρ K, (y : V) = hop ρ K g w → y ∈ W) : W = ⊤ := by
  classical
  obtain ⟨-, hirr'⟩ := (GlobalTheory.CuspRep.isIrreducible_iff ρ).1 hirr
  let W' : Submodule ℂ V := W.map (fixed ρ K).subtype
  let U : Submodule ℂ V := Submodule.span ℂ {y | ∃ g : G, ∃ w ∈ W', y = ρ g w}
  have hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U := by
    intro g v hv
    have : U ≤ U.comap (ρ g) := by
      refine Submodule.span_le.2 ?_
      rintro y ⟨g', w, hw, rfl⟩
      refine Submodule.subset_span ⟨g * g', w, hw, ?_⟩
      rw [map_mul, Module.End.mul_apply]
    exact this hv
  obtain ⟨w0, hw0, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hUne : U ≠ ⊥ := by
    intro hb
    have : ((w0 : fixed ρ K) : V) ∈ U :=
      Submodule.subset_span ⟨1, _, Submodule.mem_map_of_mem hw0, by simp⟩
    rw [hb, Submodule.mem_bot] at this
    exact hw0ne (Subtype.ext this)
  have hUtop : U = ⊤ := (hirr' U hU).resolve_left hUne
  rw [eq_top_iff]
  intro x _
  have hxU : (x : V) ∈ U := hUtop ▸ Submodule.mem_top
  obtain ⟨n, c, s, hs⟩ := Submodule.mem_span_set'.1 hxU
  have hch : ∀ i, ∃ g : G, ∃ w ∈ W', (s i : V) = ρ g w := fun i => (s i).2
  choose gs ws hws hgw using hch
  haveI : ∀ i, (stabK K (gs i)).FiniteIndex := fun i => finiteIndex_stabK (hK.1 (gs i))
  let K' : Subgroup K := ⨅ i, stabK K (gs i)
  haveI : K'.FiniteIndex := Subgroup.finiteIndex_iInf (fun i => inferInstance)
  letI := Fintype.ofFinite (K ⧸ K')
  let P : V →ₗ[ℂ] V := ∑ q : K ⧸ K', ρ ((q.out : K) : G)
  have hPx : P x = (Fintype.card (K ⧸ K')) • (x : V) := by
    simp only [P, LinearMap.sum_apply, (mem_fixed_iff.1 x.2) _ (Subtype.coe_prop _), Finset.sum_const,
      Finset.card_univ]
  have hPs : ∀ i, P (ρ (gs i) (ws i)) ∈ W' := by
    intro i
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.1 (hws i)
    have hwf : ws i ∈ fixed ρ K := hue ▸ u.2
    haveI : Finite (K ⧸ stabK K (gs i)) := inferInstance
    have hle : K' ≤ stabK K (gs i) := iInf_le _ i
    have h1 : P (ρ (gs i) (ws i)) = ∑ᶠ q : K ⧸ K', ρ ((q.out : K) : G) (ρ (gs i) (ws i)) := by
      rw [finsum_eq_sum_of_fintype]
      simp only [P, LinearMap.sum_apply]
    rw [h1, finsum_refine K' (stabK K (gs i)) hle (fun y : K => ρ (y : G) (ρ (gs i) (ws i))) (term_inv hwf),
      ← hop_apply]
    refine W'.smul_of_tower_mem _ ?_
    refine Submodule.mem_map.2 ⟨⟨hop ρ K (gs i) (ws i), hop_mem_fixed hwf⟩,
      hst (gs i) u hu _ (by show hop ρ K (gs i) (ws i) = hop ρ K (gs i) u; rw [← hue]; rfl), rfl⟩
  have hsum : P x ∈ W' := by
    rw [← hs, map_sum]
    refine W'.sum_mem fun i _ => ?_
    rw [map_smul, hgw i]
    exact W'.smul_mem _ (hPs i)
  rw [hPx] at hsum
  have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hx' : (x : V) ∈ W' := by
    have := W'.smul_mem ((Fintype.card (K ⧸ K') : ℂ)⁻¹) hsum
    rwa [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul] at this
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx'
  have : y = x := Subtype.ext hyx
  rwa [← this]

theorem finrank_fixed_eq_one {K : Subgroup G} (hK : GelPair K) (ρ : Representation ℂ G V)
    (hirr : ρ.IsIrreducible) (hne : fixed ρ K ≠ ⊥) [FiniteDimensional ℂ (fixed ρ K)] :
    Module.finrank ℂ (fixed ρ K) = 1 := by
  classical
  haveI : Nontrivial (fixed ρ K) := (Submodule.nontrivial_iff_ne_bot).2 hne
  haveI : ∀ g, Finite (K ⧸ stabK K g) := finite_quot hK
  let T : G → Module.End ℂ (fixed ρ K) := fun g => (hop ρ K g).restrict fun _ hv => hop_mem_fixed hv
  have hT : ∀ g (x : fixed ρ K), ((T g x : fixed ρ K) : V) = hop ρ K g x := fun _ _ => rfl

  have hscal : ∀ g : G, ∃ c : ℂ, ∀ x : fixed ρ K, T g x = c • x := by
    intro g
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T g)
    obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
    let E : Submodule ℂ (fixed ρ K) := LinearMap.ker (T g - c • 1)
    have hmemE : ∀ w, w ∈ E ↔ T g w = c • w := fun w => by
      simp only [E, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        sub_eq_zero]
    have hvE : v ∈ E := (hmemE v).2 hv.apply_eq_smul
    have hEne : E ≠ ⊥ := fun hb => hv.2 (by rw [hb] at hvE; exact (Submodule.mem_bot ℂ).1 hvE)
    have hEst : ∀ h : G, ∀ w : fixed ρ K, w ∈ E → ∀ y : fixed ρ K, (y : V) = hop ρ K h w → y ∈ E := by
      intro h w hw y hy
      rw [hmemE] at hw ⊢
      apply Subtype.ext
      have hw' : hop ρ K g (w : V) = c • (w : V) := by rw [← hT]; exact congrArg Subtype.val hw
      rw [hT, hy, Submodule.coe_smul, hy, hop_comm hK ρ g h w.2, hw', map_smul]
    have hEtop := fixed_simple hK ρ hirr E hEne hEst
    refine ⟨c, fun x => ?_⟩
    have hx : x ∈ E := hEtop ▸ Submodule.mem_top
    exact (hmemE x).1 hx
  obtain ⟨x0, hx0⟩ := exists_ne (0 : fixed ρ K)
  let L : Submodule ℂ (fixed ρ K) := ℂ ∙ x0
  have hLne : L ≠ ⊥ := by
    intro hb
    have : x0 ∈ L := Submodule.mem_span_singleton_self x0
    rw [hb, Submodule.mem_bot] at this
    exact hx0 this
  have hLst : ∀ h : G, ∀ w : fixed ρ K, w ∈ L → ∀ y : fixed ρ K, (y : V) = hop ρ K h w → y ∈ L := by
    intro h w hw y hy
    obtain ⟨c, hc⟩ := hscal h
    have : y = c • w := by
      apply Subtype.ext
      rw [hy, ← hT, hc]
    rw [this]
    exact L.smul_mem c hw
  have hLtop := fixed_simple hK ρ hirr L hLne hLst
  rw [← finrank_top ℂ (fixed ρ K), ← hLtop, finrank_span_singleton hx0]

end PositivityTheory.Rg.BcB.F.EigA

end
