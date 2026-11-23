import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave

noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology

namespace GlobalTheory.LocMod.Inhab

theorem exists_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] {χ : G → G → ℂ} (h : IsBichar χ)
    (ρ σ : G → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f) (hσ : ∀ y f, σ y f = 0 → f = 0)
    (hc : ∀ x y f, ρ x (σ y f) = χ x y • σ y (ρ x f)) (L K : AddSubgroup G) [Finite (L ⧸ K.addSubgroupOf L)]
    (hsep : ∀ u ∈ L, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (P : Submodule ℂ V)
    (hP : ∀ u ∈ L, ∀ f ∈ P, ρ u f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P) {f : V} (hf : f ∈ P) (f0 : f ≠ 0)
    (hK : ∀ κ ∈ K, ρ κ f = f) : ∃ g ∈ P, g ≠ 0 ∧ ∀ u ∈ L, ρ u g = g := by
  classical
  letI : Fintype (L ⧸ K.addSubgroupOf L) := Fintype.ofFinite _
  let A : AddSubgroup G :=
    { carrier := {y | ∀ κ ∈ K, χ κ y = 1}
      zero_mem' := fun κ _ => h.zero_right κ
      add_mem' := fun {a b} ha hb κ hκ => by rw [h.right, ha κ hκ, hb κ hκ, mul_one]
      neg_mem' := fun {a} ha κ hκ => by
        have := h.right κ a (-a)
        rwa [add_neg_cancel, h.zero_right, ha κ hκ, one_mul, eq_comm] at this }
  have hcl : ∀ g : V, (∀ κ ∈ K, ρ κ g = g) → ∀ a b : L,
      (QuotientAddGroup.mk a : L ⧸ K.addSubgroupOf L) = QuotientAddGroup.mk b → ρ a g = ρ b g := fun g hg a b hab => by
    have : -(a : G) + b ∈ K := (QuotientAddGroup.eq (s := K.addSubgroupOf L)).1 hab
    rw [← hg _ this, hρ, add_neg_cancel_left, hg _ this]
  by_contra hcon
  have hz : ∀ y ∈ A, ∑ q : L ⧸ K.addSubgroupOf L, χ (q.out : L) y • ρ (q.out : L) f = 0 := fun y hy => by
    have hfix : ∀ κ ∈ K, ρ κ (σ y f) = σ y f := fun κ hκ => by rw [hc, hy κ hκ, hK κ hκ, one_smul]
    refine hσ y _ ?_
    simp only [map_sum, map_smul, ← hc]
    by_contra hne
    refine hcon ⟨_, P.sum_mem fun q _ => hP _ (q.out : L).2 _ (hP' y f hf), hne, fun u hu => ?_⟩
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨u, hu⟩ : L))) _ _ fun q => ?_
    rw [hρ]
    refine hcl _ hfix (⟨u, hu⟩ + q.out) _ ?_
    simp
  let ch : (L ⧸ K.addSubgroupOf L) → (Multiplicative A →* ℂ) := fun q =>
    { toFun := fun y => χ (q.out : L) (y.toAdd : A)
      map_one' := h.zero_right _
      map_mul' := fun a b => h.right _ _ _ }
  have hinj : Function.Injective ch := by
    intro q q' hq
    rw [← q.out_eq', ← q'.out_eq', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    by_contra hn
    obtain ⟨y, hy, hne⟩ := hsep _ (-q.out + q'.out : L).2 hn
    have e : χ (q.out : L) y = χ (q'.out : L) y := DFunLike.congr_fun hq (Multiplicative.ofAdd ⟨y, hy⟩)
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, h.left, ← e, h.neg_mul] at hne
    exact hne rfl
  have hli := (linearIndependent_monoidHom (Multiplicative A) ℂ).comp ch hinj
  rw [Fintype.linearIndependent_iff] at hli
  refine f0 ((Module.forall_dual_apply_eq_zero_iff ℂ f).1 fun ℓ => ?_)
  have := hli (fun q => ℓ (ρ (q.out : L) f)) (by
    funext y
    have := congrArg ℓ (hz _ y.toAdd.2)
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
    rw [Finset.sum_apply]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) this
    simp [ch, mul_comm]) (QuotientAddGroup.mk 0)
  rwa [hcl f hK _ 0 (QuotientAddGroup.out_eq' _), hK ((0 : L) : G) K.zero_mem] at this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

variable (Y Y') in

def box (a : kˣ) : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, valuation k (x r q) ≤ valuation k (a : k)}
  zero_mem' := fun r q => by simp
  add_mem' := fun ha hb r q => Valuation.map_add_le _ (ha r q) (hb r q)
  neg_mem' := fun ha r q => by simpa using ha r q

theorem box_eq (a : kˣ) :
    (box Y Y' a : Set (Matrix Y Y' k)) = Set.pi Set.univ fun _ : Y => Set.pi Set.univ fun _ : Y' => cball a := by
  ext x
  exact ⟨fun h r _ q _ => h r q, fun h r q => h r trivial q trivial⟩

theorem isCompact_box (a : kˣ) : IsCompact (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball a

theorem isOpen_box (a : kˣ) : IsOpen (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_cball a

theorem finite_box (a b : kˣ) : Finite (box Y Y' a ⧸ (box Y Y' b).addSubgroupOf (box Y Y' a)) := by
  haveI : CompactSpace (box Y Y' a) := isCompact_iff_compactSpace.1 (isCompact_box a)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((isOpen_box b).preimage continuous_subtype_val)

theorem exists_box_subset {U : Set (Matrix Y Y' k)} (hU : U ∈ 𝓝 0) : ∃ a : kˣ, ∀ x ∈ box Y Y' a, x ∈ U := by
  have h := (isCompact_box (Y := Y) (Y' := Y') (1 : kˣ)).eventually_forall_of_forall_eventually (x₀ := (0 : k))
    (P := fun c x => c • x ∈ U) fun x _ =>
      (continuous_smul.tendsto' ((0 : k), x) 0 (zero_smul _ _)).eventually hU
  obtain ⟨s, hs⟩ := exists_cball_subset h
  refine ⟨s, fun x hx => ?_⟩
  have := hs (show (s : k) ∈ cball s from le_refl (valuation k (s : k))) ((s : k)⁻¹ • x) fun r q => by
    have h0 : valuation k (s : k) ≠ 0 := by simp
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, Units.val_one, map_one]
    exact inv_mul_le_one_of_le₀ (hx r q) zero_le'
  rwa [smul_inv_smul₀ s.ne_zero] at this

def pairing (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : ℂ := ψ (∑ r, ∑ q, b r q * t r q)

theorem pairing_comm (ψ : AddChar k Circle) (t b : Matrix Y Y' k) : pairing ψ t b = pairing ψ b t := by
  simp only [pairing, mul_comm]

theorem isBichar_pairing (ψ : AddChar k Circle) : IsBichar (pairing (Y := Y) (Y' := Y') ψ) where
  left a b y := by simp [pairing, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  right a b y := by simp [pairing, add_mul, Finset.sum_add_distrib, AddChar.map_add_eq_mul]
  zero_left y := by simp [pairing]
  zero_right y := by simp [pairing]

theorem pairing_single (ψ : AddChar k Circle) (t : Matrix Y Y' k) (r : Y) (q : Y') (c : k) :
    pairing ψ t (Matrix.single r q c) = ψ (c * t r q) := by
  unfold pairing
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h; simp [h.symm]
  · simp
  · intro r' _ h; simp [h.symm]
  · simp

theorem pairing_eq_one {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {t b : Matrix Y Y' k}
    (h : ∀ r q, valuation k (b r q * t r q) ≤ valuation k (d : k)) : pairing ψ t b = 1 := by
  rw [pairing, (hd d).2 le_rfl _ (Valuation.map_sum_le _ fun r _ => Valuation.map_sum_le _ fun q _ => h r q)]
  rfl

theorem exists_sep {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) (a : kˣ) {u : Matrix Y Y' k}
    (hu : u ∉ box Y Y' a) : ∃ y ∈ box Y Y' (d / a), pairing ψ u y ≠ 1 := by
  obtain ⟨r, q, h⟩ : ∃ r q, valuation k (a : k) < valuation k (u r q) := by
    by_contra hh
    push Not at hh
    exact hu hh
  have ha : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hd0 : 0 < valuation k (d : k) := zero_lt_iff.2 (by simp)
  have hu0 : 0 < valuation k (u r q) := ha.trans h
  have hne : u r q ≠ 0 := fun e => by simp [e] at hu0
  have : ¬ ∀ z : k, valuation k z ≤ valuation k (u r q * (d / a)) → ψ z = 1 := fun hh => by
    have := (hd _).1 hh
    rw [map_mul, map_div₀, mul_div_left_comm, mul_le_iff_le_one_right hd0, div_le_one₀ ha] at this
    exact absurd h (not_lt.2 this)
  push Not at this
  obtain ⟨z, hz, hz1⟩ := this
  refine ⟨Matrix.single r q (z / u r q), fun r' q' => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · rw [map_div₀, div_le_iff₀ hu0, mul_comm, ← map_mul]
      simpa using hz
    · simp
  · rw [pairing_single, div_mul_cancel₀ _ hne]
    exact fun e => hz1 (Subtype.ext e)

theorem pairing_box {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {a : kˣ} {u y : Matrix Y Y' k}
    (hu : u ∈ box Y Y' a) (hy : y ∈ box Y Y' (d / a)) : pairing ψ u y = 1 :=
  pairing_eq_one hd fun r q => by
    rw [map_mul]
    refine (mul_le_mul' (hy r q) (hu r q)).trans_eq ?_
    rw [← map_mul, ← Units.val_mul, div_mul_cancel]

theorem exists_vacuum {V : Type} [AddCommGroup V] [Module ℂ V] {ψ : AddChar k Circle} (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ρ σ : Matrix Y Y' k → V →ₗ[ℂ] V) (hρ : ∀ x x' f, ρ x (ρ x' f) = ρ (x + x') f)
    (hσ : ∀ x x' f, σ x (σ x' f) = σ (x + x') f) (ρ0 : ∀ f, ρ 0 f = f) (σ0 : ∀ f, σ 0 f = f)
    (hc : ∀ x y f, ρ x (σ y f) = pairing ψ x y • σ y (ρ x f)) (P : Submodule ℂ V)
    (hP : ∀ x, ∀ f ∈ P, ρ x f ∈ P) (hP' : ∀ y, ∀ f ∈ P, σ y f ∈ P)
    (sm : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, ρ x f = f) (sm' : ∀ f ∈ P, ∀ᶠ x in 𝓝 0, σ x f = f) {f : V} (hf : f ∈ P) (f0 : f ≠ 0) :
    ∃ g ∈ P, g ≠ 0 ∧ (∀ x ∈ box Y Y' (1 : kˣ), ρ x g = g) ∧
      ∀ y, (∀ x ∈ box Y Y' (1 : kˣ), pairing ψ x y = 1) → σ y g = g := by
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψ hψ h1
  have hb := isBichar_pairing (Y := Y) (Y' := Y') ψ
  obtain ⟨a, ha⟩ := exists_box_subset (sm f hf)
  haveI := finite_box (Y := Y) (Y' := Y') 1 a
  obtain ⟨g, hg, g0, hg1⟩ := exists_fixed hb ρ σ hρ
    (fun y f h => by rw [← σ0 f, ← neg_add_cancel y, ← hσ, h, map_zero]) hc (box Y Y' 1) (box Y Y' a)
    (fun u _ hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    P (fun u _ => hP u) hP' hf f0 ha
  obtain ⟨b, hb'⟩ := exists_box_subset (sm' g hg)
  haveI := finite_box (Y := Y) (Y' := Y') (d / 1) b
  let Q : Submodule ℂ V :=
    { carrier := {v | v ∈ P ∧ ∀ x ∈ box Y Y' (1 : kˣ), ρ x v = v}
      zero_mem' := ⟨P.zero_mem, fun _ _ => map_zero _⟩
      add_mem' := fun h h' => ⟨P.add_mem h.1 h'.1, fun x hx => by rw [map_add, h.2 x hx, h'.2 x hx]⟩
      smul_mem' := fun c _ h => ⟨P.smul_mem c h.1, fun x hx => by rw [map_smul, h.2 x hx]⟩ }
  have hb2 : IsBichar fun y x : Matrix Y Y' k => pairing ψ (-x) y :=
    ⟨fun a b y => hb.right _ _ _, fun a y z => by rw [neg_add, hb.left], fun y => hb.zero_right _,
      fun a => by rw [neg_zero, hb.zero_left]⟩
  obtain ⟨g', hg', g0', hg2⟩ := exists_fixed hb2 σ ρ hσ
    (fun y f h => by rw [← ρ0 f, ← neg_add_cancel y, ← hρ, h, map_zero])
    (fun y x f => by rw [hc, smul_smul, hb.neg_mul, one_smul]) (box Y Y' (d / 1)) (box Y Y' b)
    (fun u _ hu => by
      obtain ⟨y, hy, hne⟩ := exists_sep hd b hu
      refine ⟨-y, fun κ hκ => ?_, ?_⟩
      · rw [neg_neg, pairing_comm]
        exact pairing_box hd hκ hy
      · rwa [neg_neg, pairing_comm])
    Q (fun u hu v hv => ⟨hP' u v hv.1, fun x hx => by rw [hc, pairing_box hd hx hu, hv.2 x hx, one_smul]⟩)
    (fun y v hv => ⟨hP y v hv.1, fun x hx => by rw [hρ, add_comm, ← hρ, hv.2 x hx]⟩) ⟨hg, hg1⟩ g0 hb'
  refine ⟨g', hg'.1, g0', hg'.2, fun y hy => hg2 y ?_⟩
  by_contra hn
  obtain ⟨x, hx, hne⟩ := exists_sep hd _ hn
  rw [div_one, div_self'] at hx
  exact hne ((pairing_comm ψ y x).trans (hy x hx))

end GlobalTheory.LocMod.Inhab
end
