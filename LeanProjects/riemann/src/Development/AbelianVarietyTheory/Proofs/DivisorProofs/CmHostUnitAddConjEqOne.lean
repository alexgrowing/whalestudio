import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LowFilt

open GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsOpp (D : Datum H) (Z Z' : Submodule (𝓞 E) D.La) : Prop :=
  Z ≤ perp D Z ∧ Z' ≤ perp D Z' ∧ (∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) ∧
    ∀ φ : Z' →+ ℤ, ∃! a : Z, ∀ b : Z', D.EF a b = φ b

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]

def Cois (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) : Prop :=
  (∀ x, ∃ a e, y a = x + n • e) ∧
    ∀ a, (∀ b, (∃ e, y b = n • e) → (n : ℤ) ∣ D.EF a b) → ∃ e, y a = n • e

def KerIs (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (n : ℕ) : Prop :=
  ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e

abbrev img (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (Z : Submodule (𝓞 E) D.La) (I : Ideal (𝓞 E)) : Submodule (𝓞 E) X :=
  Z.map y ⊔ I • (⊤ : Submodule (𝓞 E) X)

def Improves (D : Datum H) (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (𝔭 : Ideal (𝓞 E)) (Z Z' Z'' : Submodule (𝓞 E) D.La) : Prop :=
  IsOpp D Z Z'' ∧ (∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → img D y Z' 𝔮 ≤ img D y Z'' 𝔮) ∧
    ¬ img D y Z'' 𝔭 ≤ img D y Z' 𝔭

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := H.starRing.star_involutive a

theorem ef_swap (D : Datum H) (a b : D.La) : D.EF a b = -D.EF b a := by
  have h := D.alt (a + b)
  simp only [map_add, LinearMap.add_apply, D.alt] at h
  linear_combination h

theorem mem_perp {D : Datum H} {Z : Submodule (𝓞 E) D.La} {a : D.La} : a ∈ perp D Z ↔ ∀ z ∈ Z, D.EF a z = 0 := Iff.rfl

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem IsOpp.symm (h : IsOpp D Z Z') : IsOpp D Z' Z := by
  refine ⟨h.2.1, h.1, fun φ => ?_, fun φ => ?_⟩
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp
  · obtain ⟨a, ha, hu⟩ := h.2.2.1 (-φ)
    refine ⟨a, fun b => by rw [ef_swap, ha]; simp, fun a' ha' => hu a' fun b => ?_⟩
    rw [ef_swap, ha']; simp

theorem IsOpp.eq_zero (h : IsOpp D Z Z') {b : D.La} (hb : b ∈ Z') (h0 : b ∈ perp D Z) : b = 0 := by
  obtain ⟨c, -, hu⟩ := h.2.2.1 0
  have h1 := hu ⟨b, hb⟩ fun a => by rw [ef_swap, h0 _ a.2]; simp
  have h2 := hu 0 fun a => by simp
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem IsOpp.exists_sub_mem_perp (h : IsOpp D Z Z') (a : D.La) : ∃ b ∈ Z', a - b ∈ perp D Z := by
  obtain ⟨b, hb, -⟩ := h.2.2.1 ((D.EF.flip a).toAddMonoidHom.comp Z.subtype.toAddMonoidHom)
  refine ⟨b, b.2, fun z hz => ?_⟩
  have := hb ⟨z, hz⟩
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, LinearMap.flip_apply] at this
  rw [ef_swap, map_sub, this]
  exact neg_eq_zero.2 (sub_self _)

theorem IsOpp.exists_decomp (h : IsOpp D Z Z') (a : D.La) :
    ∃ z ∈ Z, ∃ m ∈ perp D Z ⊓ perp D Z', ∃ b ∈ Z', a = z + m + b := by
  obtain ⟨b, hb, h1⟩ := h.exists_sub_mem_perp a
  obtain ⟨z, hz, h2⟩ := h.symm.exists_sub_mem_perp a
  refine ⟨z, hz, a - b - z, ⟨sub_mem h1 (h.1 hz), ?_⟩, b, hb, by abel⟩
  rw [sub_right_comm]
  exact sub_mem h2 (h.2.1 hb)

theorem IsOpp.isIsoSat (h : IsOpp D Z Z') : IsIsoSat D Z := by
  refine ⟨h.1, fun n x hn hx => ?_⟩
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp x
  have cancel : ∀ (W : Submodule (𝓞 E) D.La) (v : D.La), n • v ∈ perp D W → v ∈ perp D W := fun W v hv w hw => by
    have := hv w hw
    rw [map_nsmul, LinearMap.smul_apply, smul_eq_zero] at this
    exact this.resolve_left hn
  have hb0 : b = 0 := h.eq_zero hb (by
    have := sub_mem (cancel Z _ (h.1 hx)) (add_mem (h.1 hz) hm.1)
    rwa [add_sub_cancel_left] at this)
  subst hb0
  have hm0 : n • m = 0 := h.symm.eq_zero
    (by have := sub_mem hx (nsmul_mem hz n); rwa [add_zero, smul_add, add_sub_cancel_left] at this) (nsmul_mem hm.2 n)
  have : m = 0 := D.unimod.1 (LinearMap.ext fun w => by
    have := congrArg (fun v => D.EF v w) hm0
    simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, smul_eq_zero] at this
    simpa using this.resolve_left hn)
  simpa [this] using hz

theorem IsOpp.shear (h : IsOpp D Z Z') (t : Z' →ₗ[𝓞 E] D.La) (ht : ∀ b, t b - b ∈ perp D Z)
    (hiso : ∀ b b', D.EF (t b) (t b') = 0) : IsOpp D Z (LinearMap.range t) := by
  have key : ∀ (a : Z) (b : Z'), D.EF a (t b) = D.EF a b := fun a b => by
    have := ht b a a.2
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    rw [ef_swap, this, ← ef_swap]
  refine ⟨h.1, ?_, fun φ => ?_, fun φ => ?_⟩
  · rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
    exact hiso b b'
  · obtain ⟨b, hb, hu⟩ := h.2.2.1 φ
    refine ⟨⟨t b, b, rfl⟩, fun a => (key a b).trans (hb a), ?_⟩
    rintro ⟨_, b', rfl⟩ hb'
    exact Subtype.ext (congrArg t (hu b' fun a => (key a b').symm.trans (hb' a)))
  · obtain ⟨a, ha, hu⟩ := h.2.2.2 (φ.comp t.rangeRestrict.toAddMonoidHom)
    refine ⟨a, ?_, fun a' ha' => hu a' fun b => (key a' b).symm.trans (ha' ⟨t b, b, rfl⟩)⟩
    rintro ⟨_, b, rfl⟩
    exact (key a b).trans (ha b)

theorem isOpp_bot (D : Datum H) : IsOpp D ⊥ ⊥ :=
  ⟨bot_le, bot_le, fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩,
    fun φ => ⟨0, fun a => by rw [Subsingleton.elim a 0]; simp, fun _ _ => Subsingleton.elim _ _⟩⟩

theorem cmHostUnit_add_conj_eq_one (H : Host E) : H.w0 + H.bar H.w0 = 1 := by
  have h1 := congrArg H.bar H.two_weight_eq_one_add_root
  rw [map_mul, map_add, map_one, GlobalTheory.CharRank.bar_rt_neg, map_ofNat] at h1
  have h2 := H.two_weight_eq_one_add_root
  exact mul_left_cancel₀ (two_ne_zero (α := 𝓞 E)) (by linear_combination h1 + h2)

theorem exists_skew_solve (hd : ∀ φ : Z →+ ℤ, ∃! b : Z', ∀ a : Z, D.EF a b = φ a) (β : LinearMap.BilinForm ℤ Z)
    (hβ : ∀ a b, β a b = -β b a) (hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b)) :
    ∃ c : Z →ₗ[𝓞 E] Z', ∀ a b : Z, D.EF a (c b) + D.EF (c a) b = β a b := by
  choose c hc hu using fun b : Z => hd (AddMonoidHom.mk' (fun a => β (H.w0 • a) b) fun a a' => by simp)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  refine ⟨{ toFun := c, map_add' := fun b b' => (hu _ _ fun a => ?_).symm,
            map_smul' := fun x b => (hu _ _ fun a => ?_).symm }, fun a b => ?_⟩
  · simp [hc]
  · have h1 := hc b (H.bar x • a)
    rw [Submodule.coe_smul, D.adj, bar_bar, smul_comm, hadj, bar_bar] at h1
    exact h1
  · show D.EF a (c b) + D.EF (c a) b = _
    rw [ef_swap D (c a), hc, hc, ← hβ]
    have h2 := hadj (H.bar H.w0) a b
    rw [bar_bar] at h2
    rw [← h2, ← LinearMap.add_apply, ← map_add, ← add_smul, cmHostUnit_add_conj_eq_one, one_smul]

theorem IsOpp.exists_rank_one (h : IsOpp D Z Z') {m : D.La} (hm : m ∈ perp D Z ⊓ perp D Z') (θ : 𝓞 E →+ ℤ)
    (hθ : ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0) :
    ∃ ζ : (Z' →ₗ[𝓞 E] 𝓞 E) →+ D.La, (∀ ℓ, ζ ℓ ∈ Z) ∧ (∀ ℓ (x : Z'), D.EF x (ζ ℓ) = θ (ℓ x)) ∧
      (∀ (c : 𝓞 E) ℓ, ζ (c • ℓ) = H.bar c • ζ ℓ) ∧
      ∀ ℓ : Z' →ₗ[𝓞 E] 𝓞 E, IsOpp D Z (LinearMap.range (Z'.subtype + ℓ.smulRight (m + ζ ℓ))) := by
  choose z hz hu using fun ℓ : Z' →ₗ[𝓞 E] 𝓞 E => h.symm.2.2.1 (θ.comp ℓ.toAddMonoidHom)
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe] at hz hu
  refine ⟨AddMonoidHom.mk' (fun ℓ => (z ℓ : D.La)) fun ℓ ℓ' => congrArg Subtype.val (hu _ (z ℓ + z ℓ') fun x => ?_).symm,
    fun ℓ => (z ℓ).2, hz, fun c ℓ => congrArg Subtype.val (hu _ (H.bar c • z ℓ) fun x => ?_).symm, fun ℓ => ?_⟩
  · simp [hz]
  · have := hz ℓ (c • x)
    rw [Submodule.coe_smul, D.adj, ℓ.map_smul] at this
    exact this
  · refine h.shear _ (fun b => ?_) fun b b' => ?_
    · simpa using (perp D Z).smul_mem (ℓ b) (add_mem hm.1 (h.1 (z ℓ).2))
    · have e1 : D.EF b b' = 0 := h.2.1 b.2 _ b'.2
      have e2 : ∀ (c : 𝓞 E) (x : Z'), D.EF (c • m) x = 0 := fun c x => (perp D Z').smul_mem c hm.2 _ x.2
      have e3 : ∀ c c' : 𝓞 E, D.EF (c • m) (c' • z ℓ) = 0 := fun c c' =>
        (perp D Z).smul_mem c hm.1 _ (Z.smul_mem c' (z ℓ).2)
      have e4 : ∀ c c' : 𝓞 E, D.EF (c • z ℓ) (c' • z ℓ) = 0 := fun c c' =>
        h.1 (Z.smul_mem c (z ℓ).2) _ (Z.smul_mem c' (z ℓ).2)
      have e5 : ∀ (c : 𝓞 E) (x : Z'), D.EF x (c • z ℓ) = θ (H.bar c * ℓ x) := fun c x => by
        have := hz ℓ (H.bar c • x)
        rw [Submodule.coe_smul, D.adj, bar_bar, ℓ.map_smul] at this
        exact this
      have e6 : D.EF (ℓ b • m) (ℓ b' • m) = D.EF ((H.bar (ℓ b') * ℓ b) • m) m := by
        rw [mul_smul, D.adj (H.bar (ℓ b')), bar_bar]
      have e7 := hθ (H.bar (ℓ b') * ℓ b)
      rw [map_mul H.bar, bar_bar, mul_comm (ℓ b')] at e7
      simp only [LinearMap.add_apply, Submodule.subtype_apply, LinearMap.smulRight_apply, AddMonoidHom.mk'_apply,
        smul_add, map_add]
      rw [ef_swap D b (ℓ b' • m), ef_swap D (ℓ b • (z ℓ : D.La)) b', ef_swap D (ℓ b • (z ℓ : D.La)) (ℓ b' • m),
        e1, e2, e2, e3, e3, e4, e5, e5, e6]
      linear_combination e7

theorem exists_theta_vec (D : Datum H) (m : D.La) :
    ∃ θ : 𝓞 E →+ ℤ, ∀ t, θ t - θ (H.bar t) + D.EF (t • m) m = 0 := by
  refine ⟨AddMonoidHom.mk' (fun t => -D.EF ((H.w0 * t) • m) m) fun a b => by simp [mul_add, add_smul, add_comm],
    fun t => ?_⟩
  have h1 : D.EF ((H.w0 * H.bar t) • m) m = -D.EF ((H.bar H.w0 * t) • m) m := by
    rw [D.adj, map_mul, bar_bar, ef_swap]
  have h2 : D.EF (t • m) m = D.EF ((H.w0 * t) • m) m + D.EF ((H.bar H.w0 * t) • m) m := by
    rw [← LinearMap.add_apply, ← map_add, ← add_smul, ← add_mul, cmHostUnit_add_conj_eq_one, one_mul]
  simp only [AddMonoidHom.mk'_apply]
  linear_combination h1 + h2

theorem range_le_of_mem {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (h : ∀ x, ℓ x ∈ I) :
    LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  refine sup_le ?_ le_sup_right
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem_smul (h x) trivial))

theorem range_le_of_ker {O P X : Type} [CommRing O] [AddCommGroup P] [Module O P] [AddCommGroup X] [Module O X]
    (f : P →ₗ[O] X) (ℓ : P →ₗ[O] O) (u : X) (I : Ideal O) (hI : I.IsMaximal) {v : P}
    (hv : f v ∈ I • (⊤ : Submodule O X)) (hl : ℓ v ∉ I) :
    u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) ∧
      LinearMap.range f ⊔ I • (⊤ : Submodule O X) ≤ LinearMap.range (f + ℓ.smulRight u) ⊔ I • ⊤ := by
  have hu : u ∈ LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) := by
    obtain ⟨c, i, hi, hc⟩ := hI.exists_inv hl
    have : (f + ℓ.smulRight u) (c • v) - c • f v + i • u = u := by
      simp only [LinearMap.add_apply, map_smul, LinearMap.smulRight_apply, smul_add, add_sub_cancel_left, smul_smul]
      rw [← add_smul, hc, one_smul]
    have h2 : (f + ℓ.smulRight u) (c • v) - c • f v + i • u ∈
        LinearMap.range (f + ℓ.smulRight u) ⊔ I • (⊤ : Submodule O X) :=
      add_mem (sub_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (Submodule.smul_mem _ _ hv)))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul hi trivial))
    rwa [this] at h2
  refine ⟨hu, sup_le ?_ le_sup_right⟩
  rintro _ ⟨x, rfl⟩
  have : f x = (f + ℓ.smulRight u) x - ℓ x • u := by simp
  rw [this]
  exact sub_mem (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.smul_mem _ _ hu)

end GlobalTheory.LowFilt
