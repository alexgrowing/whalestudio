import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
open GlobalTheory.UnitLemma Polynomial

noncomputable section
namespace GlobalTheory.SigmaExtCount

section
variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (τ : Q →+ Q)
    (hττ : ∀ f : Q, τ (τ f) = f) (θ θ' u : R) (hθ : ∀ f : Q, τ (θ • f) = θ' • τ f)
    (hu : ∀ f : Q, τ (u • f) = -(u • τ f)) (hinv : ∀ f : Q, u • ((θ - θ') • f) = f)
include hττ hθ hu hinv

theorem half_snd (f : Q) : τ (u • (f - τ f)) = u • (f - τ f) := by
  rw [hu, map_sub, hττ, ← smul_neg, neg_sub]

theorem half_fst (f : Q) : τ (f - θ • (u • (f - τ f))) = f - θ • (u • (f - τ f)) := by
  have h2 : (θ - θ') • (u • (f - τ f)) = f - τ f := by rw [smul_comm, hinv]
  rw [map_sub, hθ, half_snd τ hττ θ θ' u hθ hu hinv f]
  rw [sub_smul] at h2
  generalize u • (f - τ f) = b at h2 ⊢
  rw [← sub_eq_zero]
  have : τ f - θ' • b - (f - θ • b) = (θ • b - θ' • b) - (f - τ f) := by abel
  rw [this, h2, sub_self]

theorem half_left (a b : Q) (ha : τ a = a) (hb : τ b = b) :
    u • ((a + θ • b) - τ (a + θ • b)) = b := by
  rw [map_add, hθ, ha, hb]
  have : a + θ • b - (a + θ' • b) = (θ - θ') • b := by rw [sub_smul]; abel
  rw [this, hinv]

def halfEquiv : {f : Q // τ f = f} × {f : Q // τ f = f} ≃ Q where
  toFun p := p.1.1 + θ • p.2.1
  invFun f := (⟨f - θ • (u • (f - τ f)), half_fst τ hττ θ θ' u hθ hu hinv f⟩,
    ⟨u • (f - τ f), half_snd τ hττ θ θ' u hθ hu hinv f⟩)
  left_inv p := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    have h := half_left τ hττ θ θ' u hθ hu hinv a b ha hb
    ext <;> simp only [h] <;> abel
  right_inv f := by simp
end

section Torsor
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁] [AddCommGroup A₂]
  [Module O A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂)

def Ext (M : Submodule O (A₁ × A₂)) : Prop :=
  M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂

variable {M₁ M₂}

theorem Ext.exists {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : ∃ x, (x, (b : A₂)) ∈ M := by
  obtain ⟨b, hb⟩ := b
  rw [← hM.2, Submodule.mem_map] at hb
  obtain ⟨y, hy, e⟩ := hb
  exact ⟨y.1, by simpa [← e] using hy⟩

theorem Ext.sub_mem {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x x' : A₁} {b : A₂}
    (h : (x, b) ∈ M) (h' : (x', b) ∈ M) : x - x' ∈ M₁ := by
  rw [← hM.1, Submodule.mem_comap]
  have := M.sub_mem h h'
  simpa using this

def Ext.fn {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (Classical.choose (hM.exists b))

theorem Ext.fn_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.fn b = Submodule.Quotient.mk x := by
  unfold Ext.fn
  rw [Submodule.Quotient.eq]
  exact hM.sub_mem (Classical.choose_spec (hM.exists b)) h

def Ext.lin {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := hM.fn
  map_add' b b' := by
    obtain ⟨x, hx⟩ := hM.exists b
    obtain ⟨x', hx'⟩ := hM.exists b'
    rw [hM.fn_eq b hx, hM.fn_eq b' hx', hM.fn_eq (b + b') (x := x + x') (by simpa using M.add_mem hx hx')]
    simp
  map_smul' o b := by
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.fn_eq b hx, hM.fn_eq (o • b) (x := o • x) (by simpa using M.smul_mem o hx)]
    simp

theorem Ext.lin_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.lin b = Submodule.Quotient.mk x := hM.fn_eq b h

theorem Ext.mem_iff {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (y : A₁ × A₂) :
    y ∈ M ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = hM.lin ⟨y.2, h⟩ := by
  constructor
  · intro hy
    have h2 : y.2 ∈ M₂ := by rw [← hM.2]; exact ⟨y, hy, rfl⟩
    exact ⟨h2, (hM.lin_eq ⟨y.2, h2⟩ hy).symm⟩
  · rintro ⟨h2, e⟩
    obtain ⟨x, hx⟩ := hM.exists ⟨y.2, h2⟩
    rw [hM.lin_eq _ hx, Submodule.Quotient.eq] at e
    have h0 : (y.1 - x, (0 : A₂)) ∈ M := by
      have : LinearMap.inl O A₁ A₂ (y.1 - x) ∈ M := by
        rw [← Submodule.mem_comap, hM.1]; exact e
      simpa using this
    have := M.add_mem hx h0
    simpa using this

def graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {y | ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩}
  add_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    refine ⟨M₂.add_mem ha hb, ?_⟩
    show _ = f (⟨a.2, ha⟩ + ⟨b.2, hb⟩)
    rw [map_add, ← ea, ← eb]; simp
  zero_mem' := ⟨M₂.zero_mem, by
    show _ = f 0
    simp⟩
  smul_mem' := by
    rintro o a ⟨ha, ea⟩
    refine ⟨M₂.smul_mem o ha, ?_⟩
    show _ = f (o • ⟨a.2, ha⟩)
    rw [map_smul, ← ea]; simp

theorem mem_graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) (y : A₁ × A₂) :
    y ∈ graphSub f ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩ := Iff.rfl

theorem graphSub_ext (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Ext M₁ M₂ (graphSub f) := by
  constructor
  · ext x
    simp only [Submodule.mem_comap, LinearMap.inl_apply, mem_graphSub]
    constructor
    · rintro ⟨h, e⟩
      have : f ⟨0, h⟩ = 0 := by
        have : (⟨0, h⟩ : M₂) = 0 := rfl
        rw [this, map_zero]
      rw [this, Submodule.Quotient.mk_eq_zero] at e; exact e
    · intro hx
      refine ⟨M₂.zero_mem, ?_⟩
      rw [(Submodule.Quotient.mk_eq_zero M₁).2 hx]
      have : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [this, map_zero]
  · ext b
    simp only [Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨y, ⟨h, _⟩, rfl⟩; exact h
    · intro hb
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨b, hb⟩)
      exact ⟨(x, b), ⟨hb, hx⟩, rfl⟩

def extEquiv : {M : Submodule O (A₁ × A₂) // Ext M₁ M₂ M} ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun M := M.2.lin
  invFun f := ⟨graphSub f, graphSub_ext f⟩
  left_inv M := by
    apply Subtype.ext
    ext y
    rw [mem_graphSub, M.2.mem_iff]
  right_inv f := by
    ext b
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
    have hm : (x, (b : A₂)) ∈ graphSub f := ⟨b.2, hx⟩
    exact ((graphSub_ext f).lin_eq b hm).trans hx

end Torsor

section Twist
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

def compat (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) :
    Submodule O (M₂ →ₗ[O] A₁ ⧸ M₁) where
  carrier := {f | ∀ b : M₂, f ⟨g₂ b, hg₂ b.2⟩ = M₁.mapQ M₁ g₁ hg₁ (f b)}
  add_mem' := by
    intro f f' hf hf' b
    simp only [LinearMap.add_apply, hf b, hf' b, map_add]
  zero_mem' := by intro b; simp
  smul_mem' := by
    intro o f hf b
    simp only [LinearMap.smul_apply, hf b, map_smul]

theorem gstab_iff (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ↔ hM.lin ∈ compat g₁ g₂ hg₁ hg₂ := by
  constructor
  · intro h b
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.lin_eq b hx, Submodule.mapQ_apply]
    exact hM.lin_eq ⟨g₂ b, hg₂ b.2⟩ (h _ hx)
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hg₂ h2, ?_⟩
    have := h ⟨y.2, h2⟩
    simp only at this
    rw [this, ← e, Submodule.mapQ_apply]

variable (hcc : ∀ o, cO (cO o) = o) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
  (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)

def twist (f : M₂ →ₗ[O] A₁ ⧸ M₁) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun b := M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  map_add' b b' := by
    have : (⟨σ₂ (b + b' : M₂), hs₂ (b + b').2⟩ : M₂) = ⟨σ₂ b, hs₂ b.2⟩ + ⟨σ₂ b', hs₂ b'.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_add, map_add]
  map_smul' o b := by
    have : (⟨σ₂ (o • b : M₂), hs₂ (o • b).2⟩ : M₂) = cO o • ⟨σ₂ b, hs₂ b.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_smul, LinearMap.map_smulₛₗ, hcc]
    rfl

theorem twist_apply (f : M₂ →ₗ[O] A₁ ⧸ M₁) (b : M₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f b = M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩) := rfl

def twistHom : (M₂ →ₗ[O] A₁ ⧸ M₁) →+ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun := twist hcc σ₁ σ₂ hs₁ hs₂
  map_zero' := by ext b; simp [twist_apply]
  map_add' f f' := by ext b; simp [twist_apply]

theorem twist_smul (r : O) (f : M₂ →ₗ[O] A₁ ⧸ M₁) :
    twist hcc σ₁ σ₂ hs₁ hs₂ (r • f) = cO r • twist hcc σ₁ σ₂ hs₁ hs₂ f := by
  ext b; simp [twist_apply]

theorem twist_twist (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (f : M₂ →ₗ[O] A₁ ⧸ M₁) : twist hcc σ₁ σ₂ hs₁ hs₂ (twist hcc σ₁ σ₂ hs₁ hs₂ f) = f := by
  ext b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (σ₂ b), hs₂ (hs₂ b.2)⟩ : M₂) = b := Subtype.ext (hσ₂ _)
  simp only [hb]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
  rw [← hx, Submodule.mapQ_apply, Submodule.mapQ_apply, hσ₁]

theorem twist_mem (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x))
    {f : M₂ →ₗ[O] A₁ ⧸ M₁} (hf : f ∈ compat g₁ g₂ hg₁ hg₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f ∈ compat g₁ g₂ hg₁ hg₂ := by
  intro b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (g₂ b), hs₂ (hg₂ b.2)⟩ : M₂) = ⟨g₂ (σ₂ b), hg₂ (hs₂ b.2)⟩ := Subtype.ext (hc₂ _)
  simp only [hb]
  rw [hf ⟨σ₂ b, hs₂ b.2⟩]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  rw [← hx]
  simp only [Submodule.mapQ_apply, hc₁]

theorem sstab_iff (hσ₂ : ∀ x, σ₂ (σ₂ x) = x) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ↔ twist hcc σ₁ σ₂ hs₁ hs₂ hM.lin = hM.lin := by
  constructor
  · intro h
    ext b
    rw [twist_apply]
    obtain ⟨x, hx⟩ := hM.exists ⟨σ₂ b, hs₂ b.2⟩
    rw [hM.lin_eq _ hx, Submodule.mapQ_apply]
    have := h _ hx
    simp only [hσ₂] at this
    exact (hM.lin_eq b this).symm
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hs₂ h2, ?_⟩
    simp only
    rw [← h, twist_apply]
    have hb : (⟨σ₂ (σ₂ y.2), hs₂ (hs₂ h2)⟩ : M₂) = ⟨y.2, h2⟩ := Subtype.ext (hσ₂ _)
    simp only [hb]
    rw [← e, Submodule.mapQ_apply]

end Twist

section Count
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem conj_inv_eq_neg (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ)) :
    cO ((hδ.unit⁻¹ : Oˣ) : O) = -((hδ.unit⁻¹ : Oˣ) : O) := by
  set u : O := ((hδ.unit⁻¹ : Oˣ) : O)
  have hu1 : u * (θ - cO θ) = 1 := hδ.val_inv_mul
  have h1 : cO u * (-(θ - cO θ)) = 1 := by
    have : cO (θ - cO θ) = -(θ - cO θ) := by rw [map_sub, hcc, neg_sub]
    rw [← this, ← map_mul, hu1, map_one]
  linear_combination (-u) * h1 + (-cO u) * hu1

theorem card_stable_sq (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ))
    (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
    (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
    (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x)) :
    Nat.card {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ^ 2 =
    Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} := by
  set Q := compat g₁ g₂ hg₁ hg₂
  let τQ : Q →+ Q :=
    { toFun := fun f => ⟨twist hcc σ₁ σ₂ hs₁ hs₂ f.1, twist_mem hcc σ₁ σ₂ hs₁ hs₂ g₁ g₂ hg₁ hg₂ hc₁ hc₂ f.2⟩
      map_zero' := Subtype.ext (map_zero (twistHom hcc σ₁ σ₂ hs₁ hs₂))
      map_add' := fun f f' => Subtype.ext (map_add (twistHom hcc σ₁ σ₂ hs₁ hs₂) f.1 f'.1) }
  have hτ : ∀ f : Q, ((τQ f : Q) : M₂ →ₗ[O] A₁ ⧸ M₁) = twist hcc σ₁ σ₂ hs₁ hs₂ f.1 := fun _ => rfl
  set u : O := ((hδ.unit⁻¹ : Oˣ) : O)
  have hcu := conj_inv_eq_neg hcc θ hδ
  have e := halfEquiv τQ (fun f => Subtype.ext (by rw [hτ, hτ, twist_twist hcc σ₁ σ₂ hs₁ hs₂ hσ₁ hσ₂]))
    θ (cO θ) u (fun f => Subtype.ext (by rw [hτ, Submodule.coe_smul, Submodule.coe_smul, hτ, twist_smul]))
    (fun f => Subtype.ext (by
      rw [hτ, Submodule.coe_smul, Submodule.coe_neg, Submodule.coe_smul, hτ, twist_smul, hcu, neg_smul]))
    (fun f => by rw [smul_smul, hδ.val_inv_mul, one_smul])
  have e1 : {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ Q :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        (Equiv.subtypeEquiv extEquiv (fun M => gstab_iff g₁ g₂ hg₁ hg₂ M.2)))
  have e2 : {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ {f : Q // τQ f = f} :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        ((Equiv.subtypeEquiv extEquiv (fun M => and_congr (gstab_iff g₁ g₂ hg₁ hg₂ M.2)
          (sstab_iff hcc σ₁ σ₂ hs₁ hs₂ hσ₂ M.2))).trans
        ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ Q) (fun f => twist hcc σ₁ σ₂ hs₁ hs₂ f = f)).symm.trans
          (Equiv.subtypeEquivRight (fun f => by rw [Subtype.ext_iff, hτ])))))
  rw [Nat.card_congr e2, Nat.card_congr e1, sq, ← Nat.card_prod, Nat.card_congr e]

end Count

section Special
open GlobalTheory.UnitLemma

def conjFun (K : UQ) (o : K.O) : K.O := Classical.choose (K.c_int o)

theorem algebraMap_conjFun (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjFun K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

def conjO (K : UQ) : K.O →+* K.O where
  toFun := conjFun K
  map_one' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_one])
  map_mul' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_mul])
  map_zero' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_zero])
  map_add' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_add])

theorem algebraMap_conjO (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) := algebraMap_conjFun K o

theorem conjO_conjO (K : UQ) (o : K.O) : conjO K (conjO K o) = o :=
  IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, algebraMap_conjO, K.c_c])

def sigmaSL {K : UQ} (B : InvAlg K) : B.A →ₛₗ[conjO K] B.A where
  toFun := B.σ
  map_add' := map_add B.σ
  map_smul' o a := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply K.O K.E B.A,
      IsScalarTower.algebraMap_apply K.O K.E B.A (conjO K o), B.σ_alg, algebraMap_conjO]

theorem sigmaSL_apply {K : UQ} (B : InvAlg K) (a : B.A) : sigmaSL B a = B.σ a := rfl

theorem card_sigma_stable_ext_sq : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin →
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧
      M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 =
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  intro K B₁ B₂ h1 h2 M₁ M₂ hM₁ hM₂
  obtain ⟨θ, θ', hθ, hδ⟩ := K.c_res
  have hθ' : conjO K θ = θ' := IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, hθ])
  have hu : IsUnit (θ - conjO K θ) := by
    rw [hθ']
    by_contra h
    exact hδ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
  have hmul : ∀ y : B₁.A × B₂.A, (B₁.g, B₂.g) * y =
      (LinearMap.mulLeft K.O B₁.g y.1, LinearMap.mulLeft K.O B₂.g y.2) := fun y => rfl
  have key := card_stable_sq (conjO_conjO K) θ hu (LinearMap.mulLeft K.O B₁.g)
    (LinearMap.mulLeft K.O B₂.g) (sigmaSL B₁) (sigmaSL B₂) (M₁ := M₁) (M₂ := M₂)
    (fun x hx => by simpa using hM₁.2.1 x hx) (fun x hx => by simpa using hM₂.2.1 x hx)
    (fun x hx => hM₁.2.2 x hx) (fun x hx => hM₂.2.2 x hx) B₁.σ_σ B₂.σ_σ
    (fun x => by simp [sigmaSL_apply, h1]) (fun x => by simp [sigmaSL_apply, h2])
  simp only [hmul]
  exact key

end Special

end GlobalTheory.SigmaExtCount
