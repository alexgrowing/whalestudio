import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff (ρ : Representation ℂ G V) (H : Subgroup G) (v : V) :
    v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  show (∀ h : H, ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun H h hh => H ⟨h, hh⟩, fun H h => H h h.2⟩

theorem finite_out_support [TopologicalSpace G] [IsTopologicalGroup G] {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) {f : G → ℂ} (hf : HasCompactSupport f) :
    {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  haveI : DiscreteTopology (G ⧸ K') := QuotientGroup.discreteTopology hK'
  have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ K') '' tsupport f) :=
    hf.image QuotientGroup.continuous_mk
  refine hc.finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

theorem term_fin (ρ : Representation ℂ G V) (K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    Function.HasFiniteSupport fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A) :=
  h.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out ∘ₗ A)

theorem levOp_add (ρ : Representation ℂ G V) (K K' : Subgroup G) (f f' : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : {q : G ⧸ K' | f q.out ≠ 0}.Finite) (h' : {q : G ⧸ K' | f' q.out ≠ 0}.Finite) :
    levOp ρ K K' (f + f') A = levOp ρ K K' f A + levOp ρ K K' f' A := by
  unfold levOp
  rw [← smul_add, ← finsum_add_distrib (term_fin ρ K' f A h) (term_fin ρ K' f' A h')]
  congr 1
  exact finsum_congr fun q => by simp [add_smul]

theorem levOp_smul_fun (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' (c • f) A = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by simp [mul_smul]

theorem levOp_smul_op (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V) (c : ℂ) :
    levOp ρ K K' f (c • A) = c • levOp ρ K K' f A := by
  unfold levOp
  rw [smul_comm c, smul_finsum c]
  congr 1
  exact finsum_congr fun q => by rw [LinearMap.comp_smul, smul_comm]

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem A_fixed (ρ : Representation ℂ G V) (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (K' : Subgroup G)
    (hK'θ : ∀ k ∈ K', θ k ∈ K') (A : V →ₗ[ℂ] V) (hA : ∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) {v : V}
    (hv : v ∈ fixed ρ K') : A v ∈ fixed ρ K' := by
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  have := LinearMap.congr_fun (hA (θ k)) v
  simp only [LinearMap.comp_apply, hθ] at this
  rw [← this, hv _ (hK'θ k hk)]

theorem levOp_mapsTo (ρ : Representation ℂ G V) (K K' : Subgroup G) (A : V →ₗ[ℂ] V) (f : G → ℂ)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite)
    (hl : ∀ k ∈ K', ∀ x, f (k * x) = f x) (hr : ∀ k ∈ K', ∀ x, f (x * k) = f x)
    (hA : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K') :
    ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := by
  intro v hv
  have hw := hA v hv
  have hw' := (mem_fixed_iff ρ K' (A v)).1 hw
  let F : G ⧸ K' → V := fun q => f q.out • ρ q.out (A v)
  have hF : ∀ x : G, F (QuotientGroup.mk x) = f x • ρ x (A v) := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' x
    simp only [F, hh, hr _ h.2, map_mul, Module.End.mul_apply, hw' _ h.2]
  have hFfin : Function.HasFiniteSupport F :=
    hfin.subset (Function.support_smul_subset_left (fun q : G ⧸ K' => f q.out) fun q => ρ q.out (A v))
  have hL : levOp ρ K K' f A v = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q, F q := by
    unfold levOp
    rw [LinearMap.smul_apply, ← LinearMap.applyₗ_apply_apply (R := ℂ) v,
      map_finsum _ (term_fin ρ K' f A hfin)]
    rfl
  rw [hL, mem_fixed_iff]
  intro k hk
  rw [map_smul, map_finsum _ hFfin]
  congr 1
  have hk' : ∀ q, ρ k (F q) = F (k • q) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, hF, smul_eq_mul, hl _ hk]
    simp only [F, map_smul, map_mul, Module.End.mul_apply]
  simp_rw [hk']
  exact finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (G ⧸ K'))

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twTr_eq (ρ : Representation ℂ G V) (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V)
    (h : ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K') :
    twTr ρ K K' f A = LinearMap.trace ℂ (fixed ρ K') ((levOp ρ K K' f A).restrict h) := dif_pos h

theorem trace_restrict_congr {W : Submodule ℂ V} {L L' : V →ₗ[ℂ] V} (e : L = L') (h : ∀ v ∈ W, L v ∈ W)
    (h' : ∀ v ∈ W, L' v ∈ W) : LinearMap.trace ℂ W (L.restrict h) = LinearMap.trace ℂ W (L'.restrict h') := by
  subst e; rfl

theorem restrict_add' {W : Submodule ℂ V} (L₁ L₂ : V →ₗ[ℂ] V) (h₁ : ∀ v ∈ W, L₁ v ∈ W) (h₂ : ∀ v ∈ W, L₂ v ∈ W)
    (h : ∀ v ∈ W, (L₁ + L₂) v ∈ W) : (L₁ + L₂).restrict h = L₁.restrict h₁ + L₂.restrict h₂ := by
  ext x; simp [LinearMap.restrict_apply]

theorem restrict_smul' {W : Submodule ℂ V} (L : V →ₗ[ℂ] V) (c : ℂ) (h₁ : ∀ v ∈ W, L v ∈ W)
    (h : ∀ v ∈ W, (c • L) v ∈ W) : (c • L).restrict h = c • L.restrict h₁ := by
  ext x; simp [LinearMap.restrict_apply]

theorem trace_id_eq_finrank (W : Type) [AddCommGroup W] [Module ℂ W] :
    LinearMap.trace ℂ W LinearMap.id = (Module.finrank ℂ W : ℂ) := by
  by_cases hW : Module.Finite ℂ W
  · exact LinearMap.trace_id ℂ W
  · rw [Module.finrank_of_not_finite hW]
    unfold LinearMap.trace
    rw [dif_neg]
    · simp
    · rintro ⟨s, ⟨b⟩⟩
      exact hW (Module.Finite.of_basis b)

theorem relIndex_ne_zero_of_isOpen [TopologicalSpace G] [IsTopologicalGroup G] {K K' : Subgroup G}
    (hKc : IsCompact (K : Set G)) (hK'o : IsOpen (K' : Set G)) : K'.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  haveI : Finite (K ⧸ K'.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hK'o.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem levOp_unit (ρ : Representation ℂ G V) (K K' : Subgroup G) :
    ∃ x₀ ∈ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ρ x₀ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K' (1 : G)
  refine ⟨h, h.2, ?_⟩
  unfold levOp
  have hout : ∀ q : G ⧸ K', q ≠ (QuotientGroup.mk 1 : G ⧸ K') → q.out ∉ K' := by
    intro q hq hm
    apply hq
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using K'.inv_mem hm)
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K')
    (fun q hq => by rw [Set.indicator_of_notMem (hout q hq), zero_smul])]
  rw [hh, one_mul, Set.indicator_of_mem h.2]
  simp

end GlobalTheory.TwTrLin

namespace GlobalTheory.TwTrLin

theorem twTr_linear : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), ∀ (θ : G →* G), (∀ g, θ (θ g) = g) → ∀ A : V →ₗ[ℂ] V, (∀ g, A ∘ₗ ρ g = ρ (θ g) ∘ₗ A) → ∀ K' : Subgroup G, IsLevel θ K K' → (∀ f f' (c : ℂ), IsHecke K' f → IsHecke K' f' → twTr ρ K K' (f + f') A = twTr ρ K K' f A + twTr ρ K K' f' A ∧ twTr ρ K K' (c • f) A = c * twTr ρ K K' f A ∧ twTr ρ K K' f (c • A) = c * twTr ρ K K' f A) ∧ (fixed ρ K' = ⊥ → ∀ f, twTr ρ K K' f A = 0) ∧ twTr ρ K K' ((K' : Set G).indicator 1) LinearMap.id = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * (Module.finrank ℂ (fixed ρ K') : ℂ) ∧ K'.relIndex K ≠ 0 := by
  intro G _ _ _ K _ hKc V _ _ ρ θ hθ A hA K' hlev
  obtain ⟨hK'o, _, hK'θ⟩ := hlev
  have hAf : ∀ v ∈ fixed ρ K', A v ∈ fixed ρ K' := fun v hv => A_fixed ρ θ hθ K' hK'θ A hA hv
  have hmaps : ∀ f, IsHecke K' f → ∀ v ∈ fixed ρ K', levOp ρ K K' f A v ∈ fixed ρ K' := fun f hf =>
    levOp_mapsTo ρ K K' A f (finite_out_support hK'o hf.1) (fun k hk x => (hf.2 k hk x).1)
      (fun k hk x => (hf.2 k hk x).2) hAf
  refine ⟨?_, ?_, ?_, relIndex_ne_zero_of_isOpen hKc hK'o⟩
  · intro f f' c hf hf'
    have h1 := hmaps f hf
    have h2 := hmaps f' hf'
    have e1 := levOp_add ρ K K' f f' A (finite_out_support hK'o hf.1) (finite_out_support hK'o hf'.1)
    have e2 := levOp_smul_fun ρ K K' f A c
    have e3 := levOp_smul_op ρ K K' f A c
    have h12 : ∀ v ∈ fixed ρ K', levOp ρ K K' (f + f') A v ∈ fixed ρ K' := by
      intro v hv; rw [e1]; exact add_mem (h1 v hv) (h2 v hv)
    have hs : ∀ v ∈ fixed ρ K', (c • levOp ρ K K' f A) v ∈ fixed ρ K' := fun v hv =>
      Submodule.smul_mem _ c (h1 v hv)
    have hc : ∀ v ∈ fixed ρ K', levOp ρ K K' (c • f) A v ∈ fixed ρ K' := by
      intro v hv; rw [e2]; exact hs v hv
    have hc' : ∀ v ∈ fixed ρ K', levOp ρ K K' f (c • A) v ∈ fixed ρ K' := by
      intro v hv; rw [e3]; exact hs v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [twTr_eq _ _ _ _ _ h12, twTr_eq _ _ _ _ _ h1, twTr_eq _ _ _ _ _ h2,
        trace_restrict_congr e1 h12 (fun v hv => add_mem (h1 v hv) (h2 v hv)), restrict_add' _ _ h1 h2, map_add]
    · rw [twTr_eq _ _ _ _ _ hc, twTr_eq _ _ _ _ _ h1, trace_restrict_congr e2 hc hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
    · rw [twTr_eq _ _ _ _ _ hc', twTr_eq _ _ _ _ _ h1, trace_restrict_congr e3 hc' hs, restrict_smul' _ c h1,
        map_smul, smul_eq_mul]
  · intro h0 f
    unfold twTr
    split_ifs with h
    · haveI : Subsingleton (fixed ρ K') := by
        have key : ∀ v : V, v ∈ fixed ρ K' → v = 0 := fun v hv => by
          rw [h0] at hv
          exact (Submodule.mem_bot ℂ).1 hv
        exact ⟨fun a b => Subtype.ext ((key _ a.2).trans (key _ b.2).symm)⟩
      rw [show (levOp ρ K K' f A).restrict h = 0 from LinearMap.ext fun x => Subsingleton.elim _ _, map_zero]
    · rfl
  · obtain ⟨x₀, hx₀, hL⟩ := levOp_unit ρ K K'
    have hfx : ∀ v ∈ fixed ρ K', ρ x₀ v = v := fun v hv => (mem_fixed_iff ρ K' v).1 hv x₀ hx₀
    have hm : ∀ v ∈ fixed ρ K', levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id v ∈ fixed ρ K' := by
      intro v hv
      rw [hL, LinearMap.smul_apply, hfx v hv]
      exact Submodule.smul_mem _ _ hv
    rw [twTr_eq _ _ _ _ _ hm]
    have hr : (levOp ρ K K' ((K' : Set G).indicator 1) LinearMap.id).restrict hm =
        ((K'.relIndex K : ℕ) : ℂ)⁻¹ • LinearMap.id := by
      ext x
      simp [LinearMap.restrict_apply, hL, hfx x.1 x.2]
    rw [hr, map_smul, trace_id_eq_finrank, smul_eq_mul]

end GlobalTheory.TwTrLin
