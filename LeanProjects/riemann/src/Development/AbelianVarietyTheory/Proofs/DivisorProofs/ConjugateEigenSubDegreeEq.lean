import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne

noncomputable section

open scoped Classical

namespace GlobalTheory.FinTF

variable {G : Type} [Group G]

def cosetSet (Γ K : Subgroup G) (x g : G) : Set Γ := {γ | x⁻¹ * ((γ : G)⁻¹ * g) ∈ K}

def lift (Γ K : Subgroup G) {W : Type} [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ Γ W)
    (v : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) (g : G) : W :=
  ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (Nat.card (GlobalTheory.LKLoc.locPart Γ K (Quotient.out q)) : ℂ)⁻¹ •
      ∑ᶠ γ ∈ cosetSet Γ K (Quotient.out q) g, ξ γ (v q)

theorem cosetSet_mul_right (Γ K : Subgroup G) (x g k : G) (hk : k ∈ K) :
    cosetSet Γ K x (g * k) = cosetSet Γ K x g := by
  ext γ
  simp only [cosetSet, Set.mem_setOf_eq]
  rw [← mul_assoc, ← mul_assoc, K.mul_mem_cancel_right hk, mul_assoc]

theorem lift_mul_right (Γ K : Subgroup G) {W : Type} [AddCommGroup W] [Module ℂ W] (ξ : Representation ℂ Γ W)
    (v : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) (g k : G) (hk : k ∈ K) :
    lift Γ K ξ v (g * k) = lift Γ K ξ v g := by
  simp only [lift, cosetSet_mul_right Γ K _ g k hk]

theorem cosetSet_eq_empty (Γ K : Subgroup G) (x g : G)
    (h : DoubleCoset.mk Γ K x ≠ DoubleCoset.mk Γ K g) :
    cosetSet Γ K x g = ∅ := by
  ext γ
  simp only [cosetSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hm
  apply h
  rw [DoubleCoset.eq]
  refine ⟨γ, γ.2, _, hm, ?_⟩
  simp [mul_assoc]

end GlobalTheory.FinTF

namespace GlobalTheory.FinTF
variable {G : Type} [Group G]

theorem mem_locPart_iff (Γ K : Subgroup G) (x δ : G) :
    δ ∈ GlobalTheory.LKLoc.locPart Γ K x ↔ δ ∈ Γ ∧ x⁻¹ * δ * x ∈ K := by
  simp only [GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by group⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

def cosetEquiv (Γ K : Subgroup G) (x g : G) (γ₀ : Γ) (h₀ : γ₀ ∈ cosetSet Γ K x g) :
    GlobalTheory.LKLoc.locPart Γ K x ≃ cosetSet Γ K x g where
  toFun δ := ⟨γ₀ * ⟨δ, ((mem_locPart_iff Γ K x δ).1 δ.2).1⟩, by
    have hδ := ((mem_locPart_iff Γ K x δ).1 δ.2).2
    have h0 : x⁻¹ * ((γ₀ : G)⁻¹ * g) ∈ K := h₀
    show x⁻¹ * (((γ₀ : G) * δ)⁻¹ * g) ∈ K
    have := K.mul_mem (K.inv_mem hδ) h0
    convert this using 1
    group⟩
  invFun γ := ⟨γ₀⁻¹ * (γ : Γ), (mem_locPart_iff Γ K x _).2 ⟨(γ₀⁻¹ * (γ : Γ)).2, by
    have h0 : x⁻¹ * ((γ₀ : G)⁻¹ * g) ∈ K := h₀
    have h1 : x⁻¹ * ((((γ : Γ)) : G)⁻¹ * g) ∈ K := γ.2
    have := K.mul_mem h0 (K.inv_mem h1)
    convert this using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group⟩⟩
  left_inv δ := by ext; simp
  right_inv γ := by ext; simp

theorem cosetSet_finite {Γ K : Subgroup G} (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) (x g : G) :
    (cosetSet Γ K x g).Finite := by
  rcases (cosetSet Γ K x g).eq_empty_or_nonempty with h | ⟨γ₀, h₀⟩
  · rw [h]; exact Set.finite_empty
  · haveI := hloc x
    exact Set.finite_coe_iff.1 (Finite.of_equiv _ (cosetEquiv Γ K x g γ₀ h₀))

theorem card_cosetSet (Γ K : Subgroup G) (x : G) (γ₀ : Γ) (k : G) (hk : k ∈ K) :
    Nat.card (cosetSet Γ K x ((γ₀ : G) * x * k)) = Nat.card (GlobalTheory.LKLoc.locPart Γ K x) := by
  refine (Nat.card_congr (cosetEquiv Γ K x _ γ₀ ?_)).symm
  show x⁻¹ * ((γ₀ : G)⁻¹ * ((γ₀ : G) * x * k)) ∈ K
  simpa [mul_assoc] using hk

end GlobalTheory.FinTF

namespace GlobalTheory.FinTF
variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem lift_smul {Γ K : Subgroup G} (ξ : Representation ℂ Γ W) (c : ℂ)
    (v : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) :
    lift Γ K ξ (c • v) = c • lift Γ K ξ v := by
  funext g
  simp only [lift, Pi.smul_apply, map_smul, smul_finsum]
  congr 1; funext q
  simp only [smul_comm c]

theorem lift_single {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (q : DoubleCoset.Quotient (Γ : Set G) (K : Set G)) (w : W) (g : G) :
    lift Γ K ξ (Pi.single q w) g =
      (Nat.card (GlobalTheory.LKLoc.locPart Γ K (Quotient.out q)) : ℂ)⁻¹ •
        ∑ᶠ γ ∈ cosetSet Γ K (Quotient.out q) g, ξ γ w := by
  simp only [lift]
  rw [finsum_eq_single _ q]
  · simp
  · intro q' hq'
    simp [Pi.single_eq_of_ne hq']

theorem trace_pi (ι : Type) [Fintype ι] [DecidableEq ι] (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : (ι → V) →ₗ[ℂ] (ι → V)) :
    LinearMap.trace ℂ (ι → V) A =
      ∑ i, LinearMap.trace ℂ V (LinearMap.proj i ∘ₗ A ∘ₗ LinearMap.single ℂ (fun _ => V) i) := by
  have hid : (∑ i : ι, LinearMap.single ℂ (fun _ => V) i ∘ₗ LinearMap.proj i) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp [Finset.univ_sum_single]
  calc LinearMap.trace ℂ (ι → V) A
      = LinearMap.trace ℂ (ι → V) (A ∘ₗ ∑ i, LinearMap.single ℂ (fun _ => V) i ∘ₗ LinearMap.proj i) := by
        rw [hid, LinearMap.comp_id]
    _ = ∑ i, LinearMap.trace ℂ (ι → V) ((A ∘ₗ LinearMap.single ℂ (fun _ => V) i) ∘ₗ LinearMap.proj i) := by
        have hs : (A ∘ₗ ∑ i : ι, LinearMap.single ℂ (fun _ => V) i ∘ₗ LinearMap.proj i) =
            ∑ i : ι, (A ∘ₗ LinearMap.single ℂ (fun _ => V) i) ∘ₗ LinearMap.proj i := by
          apply LinearMap.ext; intro v; simp
        rw [hs, map_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.trace_comp_comm']

end GlobalTheory.FinTF

namespace GlobalTheory.FinTF
variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem lift_add {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (hQ : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x))
    (v v' : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) :
    lift Γ K ξ (v + v') = lift Γ K ξ v + lift Γ K ξ v' := by
  funext g
  simp only [lift, Pi.add_apply, map_add]
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1; funext q
  rw [finsum_mem_add_distrib (cosetSet_finite hloc _ g), smul_add]

theorem sum_cosetSet_ev {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) (φ : G → W)
    (h1 : ∀ γ : Γ, ∀ g, φ ((γ : G) * g) = ξ γ (φ g)) (h2 : ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (x g : G) :
    ∑ᶠ γ ∈ cosetSet Γ K x g, ξ γ (φ x) = (Nat.card (cosetSet Γ K x g) : ℂ) • φ g := by
  have hfin := cosetSet_finite hloc x g
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_congr rfl (g := fun _ => φ g)]
  · rw [Finset.sum_const, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin, Nat.cast_smul_eq_nsmul]
  · intro γ hγ
    rw [Set.Finite.mem_toFinset] at hγ
    have hk : x⁻¹ * ((γ : G)⁻¹ * g) ∈ K := hγ
    have := h1 γ (x * (x⁻¹ * ((γ : G)⁻¹ * g)))
    rw [h2 _ hk] at this
    rw [← this]
    congr 1
    group

theorem lift_ev {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) (φ : G → W)
    (h1 : ∀ γ : Γ, ∀ g, φ ((γ : G) * g) = ξ γ (φ g)) (h2 : ∀ k ∈ K, ∀ g, φ (g * k) = φ g) (g : G) :
    lift Γ K ξ (fun q => φ (Quotient.out q)) g = φ g := by
  simp only [lift, sum_cosetSet_ev ξ hloc φ h1 h2]
  rw [finsum_eq_single _ (DoubleCoset.mk Γ K g)]
  · obtain ⟨γ₀, hγ₀, k, hk, he⟩ := (DoubleCoset.eq Γ K _ _).1 (DoubleCoset.out_eq' Γ K (DoubleCoset.mk Γ K g))
    have hc := card_cosetSet Γ K (Quotient.out (DoubleCoset.mk Γ K g)) ⟨γ₀, hγ₀⟩ k hk
    rw [← he] at hc
    rw [hc, smul_smul]
    haveI := hloc (Quotient.out (DoubleCoset.mk Γ K g))
    have hpos : (Nat.card (GlobalTheory.LKLoc.locPart Γ K (Quotient.out (DoubleCoset.mk Γ K g))) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [inv_mul_cancel₀ hpos, one_smul]
  · intro q hq
    have he : cosetSet Γ K (Quotient.out q) g = ∅ := by
      apply cosetSet_eq_empty
      rwa [DoubleCoset.out_eq']
    rw [he]
    simp
end GlobalTheory.FinTF

namespace GlobalTheory.FinTF
variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem mem_cosetSet_mul_iff (Γ K : Subgroup G) (x y : G) (γ : Γ) :
    γ ∈ cosetSet Γ K x (x * y) ↔ (QuotientGroup.mk (x⁻¹ * γ * x) : G ⧸ K) = QuotientGroup.mk y := by
  simp only [cosetSet, Set.mem_setOf_eq, QuotientGroup.eq, mul_inv_rev, inv_inv, mul_assoc]

theorem f_out_mk {K : Subgroup G} (f : G → ℂ) (hfr : ∀ g, ∀ k ∈ K, f (g * k) = f g) (g : G) :
    f (QuotientGroup.mk g : G ⧸ K).out = f g := by
  obtain ⟨k, he⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [he, hfr _ _ k.2]

theorem support_finite {Γ K : Subgroup G} (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) (f : G → ℂ)
    (hfr : ∀ g, ∀ k ∈ K, f (g * k) = f g) (hfs : (Function.support (fun q : G ⧸ K => f q.out)).Finite) (x : G) :
    (Function.support fun γ : Γ => f (x⁻¹ * γ * x)).Finite := by
  refine (hfs.biUnion fun h _ => cosetSet_finite hloc x (x * h.out)).subset ?_
  intro γ hγ
  simp only [Set.mem_iUnion]
  refine ⟨QuotientGroup.mk (x⁻¹ * γ * x), ?_, ?_⟩
  · simpa [Function.mem_support, f_out_mk f hfr] using hγ
  · rw [mem_cosetSet_mul_iff, QuotientGroup.out_eq']

theorem cosetSet_mul_left (Γ K : Subgroup G) (x g : G) (γ : Γ) :
    cosetSet Γ K x ((γ : G) * g) = (fun γ' => γ * γ') '' cosetSet Γ K x g := by
  ext γ'
  simp only [cosetSet, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨γ⁻¹ * γ', ?_, by simp⟩
    simpa [mul_assoc] using h
  · rintro ⟨γ'', h, rfl⟩
    simpa [mul_assoc] using h

theorem lift_mul_left {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (hQ : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x))
    (v : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) (γ : Γ) (g : G) :
    lift Γ K ξ v ((γ : G) * g) = ξ γ (lift Γ K ξ v g) := by
  have hin : ∀ x w, ∑ᶠ γ' ∈ cosetSet Γ K x ((γ : G) * g), ξ γ' w = ξ γ (∑ᶠ γ' ∈ cosetSet Γ K x g, ξ γ' w) := by
    intro x w
    have hfin := cosetSet_finite hloc x g
    rw [cosetSet_mul_left, finsum_mem_image (mul_right_injective γ).injOn,
      finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, map_sum]
    refine Finset.sum_congr rfl fun γ' _ => ?_
    rw [map_mul, Module.End.mul_apply]
  simp only [lift, hin]
  rw [map_finsum _ (Set.toFinite _)]
  simp only [map_smul]
end GlobalTheory.FinTF

namespace GlobalTheory.FinTF
variable {G : Type} [Group G] {W : Type} [AddCommGroup W] [Module ℂ W]

theorem block_sum {Γ K : Subgroup G} (ξ : Representation ℂ Γ W)
    (hloc : ∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) (f : G → ℂ)
    (hfr : ∀ g, ∀ k ∈ K, f (g * k) = f g) (hfs : (Function.support (fun q : G ⧸ K => f q.out)).Finite)
    (x : G) (w : W) :
    ∑ᶠ h : G ⧸ K, f h.out • ∑ᶠ γ ∈ cosetSet Γ K x (x * h.out), ξ γ w = ∑ᶠ γ : Γ, f (x⁻¹ * γ * x) • ξ γ w := by
  have hS := support_finite hloc f hfr hfs x
  have hmem : ∀ γ : Γ, γ ∈ hS.toFinset ↔ f (x⁻¹ * γ * x) ≠ 0 := fun γ => by simp
  have hF : ∀ h : G ⧸ K, h ∈ hfs.toFinset ↔ f h.out ≠ 0 := fun h => by simp
  rw [finsum_eq_sum_of_support_subset (s := hS.toFinset) _
    (fun γ hγ => (hmem γ).2 (fun h0 => hγ (by simp [h0])))]
  rw [finsum_eq_sum_of_support_subset (s := hfs.toFinset) _
    (fun h hh => (hF h).2 (fun h0 => hh (by simp [h0])))]
  rw [← Finset.sum_fiberwise_of_maps_to (s := hS.toFinset) (t := hfs.toFinset)
    (g := fun γ : Γ => (QuotientGroup.mk (x⁻¹ * γ * x) : G ⧸ K))
    (fun γ hγ => (hF _).2 (by rw [f_out_mk f hfr]; exact (hmem γ).1 hγ))]
  refine Finset.sum_congr rfl fun h hh => ?_
  have hfin := cosetSet_finite hloc x (x * h.out)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.smul_sum]
  have hset : hfin.toFinset =
      hS.toFinset.filter (fun γ : Γ => (QuotientGroup.mk (x⁻¹ * γ * x) : G ⧸ K) = h) := by
    ext γ
    rw [Set.Finite.mem_toFinset, Finset.mem_filter, mem_cosetSet_mul_iff, QuotientGroup.out_eq', hmem]
    constructor
    · intro he
      refine ⟨?_, he⟩
      rw [← f_out_mk f hfr, he]
      exact (hF h).1 hh
    · exact fun h' => h'.2
  rw [hset]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [Finset.mem_filter] at hγ
  rw [← hγ.2, f_out_mk f hfr]
end GlobalTheory.FinTF

namespace GlobalTheory.FinTF

theorem finite_trace_formula : ∀ (G : Type) [Group G] (Γ K : Subgroup G) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ξ : Representation ℂ Γ W),
  Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) → (∀ x : G, Finite (GlobalTheory.LKLoc.locPart Γ K x)) →
  ∀ f : G → ℂ, (∀ k ∈ K, ∀ k' ∈ K, ∀ g, f (k * g * k') = f g) → (Function.support (fun q : G ⧸ K => f q.out)).Finite →
  ∀ M : Submodule ℂ (G → W), (∀ φ, φ ∈ M ↔ (∀ γ : Γ, ∀ g, φ ((γ : G) * g) = ξ γ (φ g)) ∧ ∀ k ∈ K, ∀ g, φ (g * k) = φ g) →
  ∀ T : M →ₗ[ℂ] M, (∀ φ : M, ∀ g, (T φ : G → W) g = ∑ᶠ h : G ⧸ K, f h.out • (φ : G → W) (g * h.out)) →
  LinearMap.trace ℂ M T = ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
    (1 / (Nat.card (GlobalTheory.LKLoc.locPart Γ K q.out) : ℂ)) * ∑ᶠ γ : Γ, f (q.out⁻¹ * γ * q.out) * LinearMap.trace ℂ W (ξ γ) := by
  intro G _ Γ K W _ _ _ ξ hQ hloc f hf hfs M hM T hT
  classical
  letI : Fintype (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := Fintype.ofFinite _
  have hfr : ∀ g, ∀ k ∈ K, f (g * k) = f g := fun g k hk => by simpa using hf 1 K.one_mem k hk g
  have hliftM : ∀ v, lift Γ K ξ v ∈ M := fun v =>
    (hM _).2 ⟨fun γ g => lift_mul_left ξ hQ hloc v γ g, fun k hk g => lift_mul_right Γ K ξ v g k hk⟩
  let E : (DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) →ₗ[ℂ] M :=
    { toFun := fun v => ⟨lift Γ K ξ v, hliftM v⟩
      map_add' := fun v v' => Subtype.ext (lift_add ξ hQ hloc v v')
      map_smul' := fun c v => Subtype.ext (lift_smul ξ c v) }
  let ev : M →ₗ[ℂ] (DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) :=
    LinearMap.pi fun q => (LinearMap.proj (Quotient.out q) : (G → W) →ₗ[ℂ] W) ∘ₗ M.subtype
  have hret : E ∘ₗ ev = LinearMap.id := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    funext g
    have hφ := (hM φ).1 φ.2
    exact lift_ev ξ hloc φ hφ.1 hφ.2 g
  have hinj : Function.Injective ev := fun a b hab => by
    have ha := LinearMap.congr_fun hret a
    have hb := LinearMap.congr_fun hret b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    calc a = E (ev a) := ha.symm
      _ = E (ev b) := by rw [hab]
      _ = b := hb
  haveI : FiniteDimensional ℂ M := FiniteDimensional.of_injective ev hinj
  have h1 : LinearMap.trace ℂ M T =
      LinearMap.trace ℂ (DoubleCoset.Quotient (Γ : Set G) (K : Set G) → W) (ev ∘ₗ T ∘ₗ E) := by
    calc LinearMap.trace ℂ M T = LinearMap.trace ℂ M ((T ∘ₗ E) ∘ₗ ev) := by
          rw [LinearMap.comp_assoc, hret, LinearMap.comp_id]
      _ = _ := by rw [LinearMap.trace_comp_comm']
  rw [h1, trace_pi, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨S, hS⟩ : ∃ S : Finset Γ, ∀ γ : Γ, f ((Quotient.out q)⁻¹ * γ * Quotient.out q) ≠ 0 → γ ∈ S :=
    ⟨(support_finite hloc f hfr hfs (Quotient.out q)).toFinset, fun γ hγ => by simpa using hγ⟩
  have hblock : LinearMap.proj q ∘ₗ (ev ∘ₗ T ∘ₗ E) ∘ₗ LinearMap.single ℂ (fun _ => W) q =
      (Nat.card (GlobalTheory.LKLoc.locPart Γ K (Quotient.out q)) : ℂ)⁻¹ • ∑ γ ∈ S, f ((Quotient.out q)⁻¹ * γ * Quotient.out q) • ξ γ := by
    apply LinearMap.ext
    intro w
    show ((T (E (Pi.single q w)) : M) : G → W) (Quotient.out q) = _
    rw [hT]
    show ∑ᶠ h : G ⧸ K, f h.out • lift Γ K ξ (Pi.single q w) (Quotient.out q * h.out) = _
    simp only [lift_single]
    simp_rw [smul_comm (f _) ((Nat.card (GlobalTheory.LKLoc.locPart Γ K (Quotient.out q)) : ℂ)⁻¹)]
    rw [← smul_finsum, block_sum ξ hloc f hfr hfs (Quotient.out q) w, LinearMap.smul_apply, LinearMap.sum_apply]
    congr 1
    rw [finsum_eq_sum_of_support_subset _ (s := S)]
    · simp [LinearMap.smul_apply]
    · intro γ hγ
      by_contra hn
      have h0 : f ((Quotient.out q)⁻¹ * γ * Quotient.out q) = 0 := by_contra fun h => hn (hS γ h)
      exact hγ (by simp [h0])
  rw [hblock, map_smul, map_sum, smul_eq_mul, one_div]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := S)]
  · simp [map_smul]
  · intro γ hγ
    by_contra hn
    have h0 : f ((Quotient.out q)⁻¹ * γ * Quotient.out q) = 0 := by_contra fun h => hn (hS γ h)
    exact hγ (by simp [h0])

end GlobalTheory.FinTF
