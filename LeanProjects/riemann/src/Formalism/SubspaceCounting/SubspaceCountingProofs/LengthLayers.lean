import Formalism.SubspaceCounting.Statement

noncomputable section

open scoped BigOperators

namespace Formalism.G0

namespace LengthLayersP

section General

variable {O : Type} [CommRing O]

theorem length_sup_le {X : Type} [AddCommGroup X] [Module O X] (A B : Submodule O X) :
    Module.length O ↥(A ⊔ B) ≤ Module.length O ↥A + Module.length O ↥B := by
  let f : ↥A × ↥B →ₗ[O] ↥(A ⊔ B) :=
    LinearMap.coprod (Submodule.inclusion le_sup_left) (Submodule.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have hprod : Module.length O (↥A × ↥B) = Module.length O ↥A + Module.length O ↥B :=
    Module.length_eq_add_of_exact (LinearMap.inl O ↥A ↥B) (LinearMap.snd O ↥A ↥B)
      LinearMap.inl_injective LinearMap.snd_surjective (by
        rintro ⟨a, b⟩
        constructor
        · intro h
          exact ⟨a, by simp [show b = 0 from h]⟩
        · rintro ⟨a', h⟩
          exact (congrArg Prod.snd h).symm)
  exact hprod ▸ Module.length_le_of_surjective f hf

theorem length_eq_add_of_le {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O ↥V = Module.length O ↥U + Module.length O (↥V ⧸ U.comap V.subtype) := by
  rw [Module.length_eq_add_of_exact (U.comap V.subtype).subtype (U.comap V.subtype).mkQ
    Subtype.val_injective (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.comapSubtypeEquivOfLe h).length_eq]

theorem length_quot_eq_add {X : Type} [AddCommGroup X] [Module O X] {U V : Submodule O X}
    (h : U ≤ V) :
    Module.length O (X ⧸ U) = Module.length O ↥(V.map U.mkQ) + Module.length O (X ⧸ V) := by
  refine Module.length_eq_add_of_exact (V.map U.mkQ).subtype (U.mapQ V LinearMap.id (fun x hx => h hx))
    Subtype.val_injective ?_ ?_
  · intro y
    obtain ⟨x, rfl⟩ := V.mkQ_surjective y
    exact ⟨U.mkQ x, rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := U.mkQ_surjective y
    constructor
    · intro hx
      have hxV : x ∈ V := (Submodule.Quotient.mk_eq_zero V).mp hx
      exact ⟨⟨U.mkQ x, Submodule.mem_map_of_mem hxV⟩, rfl⟩
    · rintro ⟨⟨z, hz⟩, hzx⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
      have h1 : U.mkQ w = U.mkQ x := hzx
      have h2 : w - x ∈ U := (Submodule.Quotient.eq U).mp h1
      have h3 : x ∈ V := by simpa using V.sub_mem hw (h h2)
      exact (Submodule.Quotient.mk_eq_zero V).mpr h3

theorem mem_span_smul_top {X : Type} [AddCommGroup X] [Module O X] (a : O) (x : X) :
    x ∈ (Ideal.span {a}) • (⊤ : Submodule O X) ↔ ∃ y, a • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

def pw (π : O) (X : Type) [AddCommGroup X] [Module O X] (e : ℕ) : Submodule O X :=
  (Ideal.span {π ^ e}) • (⊤ : Submodule O X)

theorem mem_pw {π : O} {X : Type} [AddCommGroup X] [Module O X] {e : ℕ} {x : X} :
    x ∈ pw π X e ↔ ∃ y, π ^ e • y = x := by
  exact mem_span_smul_top (π ^ e) x

end General

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem length_residue (π : O) (hπ : Irreducible π) :
    Module.length O (O ⧸ Ideal.span {π}) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact (PrincipalIdealRing.isMaximal_of_irreducible hπ).out

private theorem length_sup_span_le_add_one_of_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (W : Submodule O X) (z : X) (hz : π • z ∈ W) :
    Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + 1 := by
  have hWT : W ≤ W ⊔ O ∙ z := le_sup_left
  rw [length_eq_add_of_le hWT]
  refine add_le_add le_rfl ?_
  set T := W ⊔ O ∙ z with hT
  set K := W.comap T.subtype with hK
  have hzT : z ∈ T := Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
  set q : ↥T ⧸ K := K.mkQ ⟨z, hzT⟩ with hq
  have hπq : π • q = 0 := by
    rw [hq, ← map_smul]
    exact (Submodule.Quotient.mk_eq_zero K).mpr hz
  let f : O →ₗ[O] ↥T ⧸ K := LinearMap.toSpanSingleton O _ q
  have hker : Ideal.span {π} ≤ LinearMap.ker f := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact hπq
  have hsurj : Function.Surjective ((Ideal.span {π}).liftQ f hker) := by
    intro y
    obtain ⟨⟨t, ht⟩, rfl⟩ := K.mkQ_surjective y
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp ht
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨Submodule.Quotient.mk r, ?_⟩
    rw [Submodule.liftQ_apply]
    show r • q = K.mkQ ⟨w + r • z, ht⟩
    rw [hq, ← map_smul]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq, hK, Submodule.mem_comap]
    have e : T.subtype (r • ⟨z, hzT⟩ - ⟨w + r • z, ht⟩) = -w := by
      show r • z - (w + r • z) = -w
      abel
    rw [e]
    exact W.neg_mem hw
  exact (Module.length_le_of_surjective _ hsurj).trans (length_residue π hπ).le

private theorem length_sup_span_le_add_of_pow_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (W : Submodule O X) (z : X), π ^ s • z ∈ W →
      Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥W + (s : ℕ∞) := by
  intro s
  induction s with
  | zero =>
    intro W z hz
    rw [pow_zero, one_smul] at hz
    have e : W ⊔ O ∙ z = W := sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hz)
    rw [e]
    simp
  | succ s ih =>
    intro W z hz
    have h1 : π ^ s • (π • z) ∈ W := by rw [smul_smul, ← pow_succ]; exact hz
    have h2 := ih W (π • z) h1
    have h3 := length_sup_span_le_add_one_of_smul_mem π hπ (W ⊔ O ∙ (π • z)) z
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    have h4 : W ⊔ O ∙ (π • z) ⊔ O ∙ z = W ⊔ O ∙ z := by
      apply le_antisymm
      · refine sup_le (sup_le le_sup_left ?_) le_sup_right
        exact le_trans ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (Submodule.smul_mem _ π (Submodule.mem_span_singleton_self z))) le_sup_right
      · exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right
    rw [h4] at h3
    calc Module.length O ↥(W ⊔ O ∙ z) ≤ Module.length O ↥(W ⊔ O ∙ (π • z)) + 1 := h3
      _ ≤ Module.length O ↥W + (s : ℕ∞) + 1 := add_le_add h2 le_rfl
      _ = Module.length O ↥W + ((s + 1 : ℕ) : ℕ∞) := by push_cast; ring

theorem length_span_singleton_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] : ∀ (s : ℕ) (x : X), π ^ s • x = 0 → Module.length O ↥(O ∙ x) ≤ s := by
  intro s x hx
  have h := length_sup_span_le_add_of_pow_smul_mem π hπ s ⊥ x (by rw [hx]; exact Submodule.zero_mem _)
  have h0 : Module.length O ↥(⊥ : Submodule O X) = 0 := Module.length_eq_zero
  rw [bot_sup_eq, h0, zero_add] at h
  exact h

theorem length_span_finset_le (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0) :
    Module.length O ↥(Submodule.span O (D : Set X)) ≤ ((D.card * s : ℕ) : ℕ∞) := by
  classical
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    rw [Finset.coe_empty, Submodule.span_empty, Module.length_eq_zero]
    simp
  · intro x D hxD ih hD
    rw [Finset.coe_insert, Submodule.span_insert]
    calc Module.length O ↥(O ∙ x ⊔ Submodule.span O (D : Set X))
        ≤ Module.length O ↥(O ∙ x) + Module.length O ↥(Submodule.span O (D : Set X)) :=
          length_sup_le _ _
      _ ≤ (s : ℕ∞) + ((D.card * s : ℕ) : ℕ∞) :=
          add_le_add (length_span_singleton_le π hπ s x (hD x (Finset.mem_insert_self x D)))
            (ih (fun y hy => hD y (Finset.mem_insert_of_mem hy)))
      _ = (((insert x D).card * s : ℕ) : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hxD]; push_cast; ring

theorem length_le_of_span_eq_top (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0)
    (htop : Submodule.span O (D : Set X) = ⊤) :
    Module.length O X ≤ ((D.card * s : ℕ) : ℕ∞) := by
  have h := length_span_finset_le π hπ s D hD
  rw [htop] at h
  rwa [(Submodule.topEquiv).length_eq] at h

private theorem length_le_length_add_card_mul_of_pow_smul_mem (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (C : Finset X) : ∀ (U V : Submodule O X), U ≤ V →
      V ≤ U ⊔ Submodule.span O (C : Set X) → (∀ v ∈ V, π ^ s • v ∈ U) →
      Module.length O ↥V ≤ Module.length O ↥U + ((C.card * s : ℕ) : ℕ∞) := by
  classical
  refine Finset.induction_on C ?_ ?_
  · intro U V hUV hV _
    rw [Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at hV
    rw [le_antisymm hV hUV]
    simp
  · intro c C' hc ih U V hUV hV hs
    set W' := U ⊔ Submodule.span O (C' : Set X) with hW'
    set V' := V ⊓ W' with hV'
    have hUV' : U ≤ V' := le_inf hUV le_sup_left
    have h1 : Module.length O ↥V' ≤ Module.length O ↥U + ((C'.card * s : ℕ) : ℕ∞) :=
      ih U V' hUV' inf_le_right (fun v hv => hs v hv.1)
    let J : Ideal O := (V ⊔ W').comap (LinearMap.toSpanSingleton O X c)
    obtain ⟨j, hj⟩ := (IsPrincipalIdealRing.principal J).principal
    have hjJ : j ∈ J := by rw [hj]; exact Submodule.mem_span_singleton_self j
    have hjJ' := Submodule.mem_comap.mp hjJ
    rw [LinearMap.toSpanSingleton_apply] at hjJ'
    obtain ⟨vj, hvj, wj, hwj, hvw⟩ := Submodule.mem_sup.mp hjJ'
    have hVeq : V = V' ⊔ O ∙ vj := by
      apply le_antisymm
      · intro v hv
        have hv2 : v ∈ W' ⊔ O ∙ c := by
          have h5 := hV hv
          rw [Finset.coe_insert, Submodule.span_insert, sup_comm (O ∙ c), ← sup_assoc] at h5
          exact h5
        obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv2
        obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
        have hrJ : r ∈ J := by
          apply Submodule.mem_comap.mpr
          rw [LinearMap.toSpanSingleton_apply]
          have e : r • c = (w + r • c) + (-w) := by abel
          rw [e]
          exact Submodule.add_mem_sup hv (W'.neg_mem hw)
        rw [hj] at hrJ
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hrJ
        have e2 : (a • j) • c = a • vj + a • wj := by rw [smul_assoc, ← hvw, smul_add]
        have hdiff : w + (a • j) • c - a • vj ∈ V' := by
          refine ⟨V.sub_mem hv (V.smul_mem a hvj), ?_⟩
          have e3 : w + (a • j) • c - a • vj = w + a • wj := by rw [e2]; abel
          show w + (a • j) • c - a • vj ∈ W'
          rw [e3]
          exact W'.add_mem hw (W'.smul_mem a hwj)
        have e4 : w + (a • j) • c = (w + (a • j) • c - a • vj) + a • vj := by abel
        rw [e4]
        exact Submodule.add_mem_sup hdiff
          (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self vj))
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hvj)
    have h2 : Module.length O ↥V ≤ Module.length O ↥V' + (s : ℕ∞) := by
      rw [hVeq]
      exact length_sup_span_le_add_of_pow_smul_mem π hπ s V' vj (hUV' (hs vj hvj))
    calc Module.length O ↥V ≤ Module.length O ↥V' + (s : ℕ∞) := h2
      _ ≤ Module.length O ↥U + ((C'.card * s : ℕ) : ℕ∞) + (s : ℕ∞) := add_le_add h1 le_rfl
      _ = Module.length O ↥U + (((insert c C').card * s : ℕ) : ℕ∞) := by
          rw [Finset.card_insert_of_notMem hc]; push_cast; ring

theorem layer (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X] [Module O X]
    (U V : Submodule O X) (hUV : U ≤ V) (C : Finset X) (g s : ℕ) (hC : C.card ≤ g)
    (hV : V ≤ Submodule.span O (C : Set X)) (hs : ∀ v ∈ V, π ^ s • v ∈ U) :
    Module.length O ↥V ≤ Module.length O ↥U + ((g * s : ℕ) : ℕ∞) := by
  have h := length_le_length_add_card_mul_of_pow_smul_mem π hπ s C U V hUV (le_trans hV le_sup_right) hs
  refine le_trans h (add_le_add le_rfl ?_)
  exact_mod_cast Nat.mul_le_mul_right s hC

end DVR

section Main

variable {O : Type} [CommRing O]

theorem pw_le_span {M : Type} [AddCommGroup M] [Module O M] (π : O) (P : Submodule O M)
    (g E : ℕ) (h : AllButLE π ⊤ P g E) :
    ∃ C : Finset (M ⧸ P), C.card ≤ g ∧ pw π (M ⧸ P) E ≤ Submodule.span O (C : Set (M ⧸ P)) := by
  classical
  obtain ⟨C, -, hcard, hC⟩ := h
  refine ⟨C.image P.mkQ, le_trans Finset.card_image_le hcard, ?_⟩
  intro y hy
  obtain ⟨y0, rfl⟩ := mem_pw.mp hy
  obtain ⟨x, rfl⟩ := P.mkQ_surjective y0
  have hx := hC x Submodule.mem_top
  rw [Finset.coe_image, Submodule.span_image]
  obtain ⟨p, hp, t, ht, hpt⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_map.mpr ⟨t, ht, ?_⟩
  have hp0 : P.mkQ p = 0 := (Submodule.Quotient.mk_eq_zero P).mpr hp
  rw [← map_smul, ← hpt, map_add, hp0, zero_add]

theorem allBut_zero {M : Type} [AddCommGroup M] [Module O M] (π : O) (P : Submodule O M)
    (E : ℕ) (h : AllButLE π ⊤ P 0 E) : ∀ y : M, π ^ E • y ∈ P := by
  intro y
  obtain ⟨C, -, hcard, hC⟩ := h
  have hC0 : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  have h1 := hC y Submodule.mem_top
  rwa [hC0, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at h1

end Main

private theorem length_pw_quot_le_sum_of_allButLE {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] (π : O) (hπ : Irreducible π) (P : Submodule O M)
    (τ S Stop β₀ : ℕ) (g : ℕ → ℕ)
    (hg : ∀ β ≤ β₀, AllButLE π ⊤ P (g β) (τ + β * S))
    (hstop : AllButLE π ⊤ P 0 (τ + Stop)) :
    ∀ d, d ≤ β₀ → Module.length O ↥(pw π (M ⧸ P) (τ + (β₀ - d) * S)) ≤
      ((S * ∑ β ∈ Finset.Ico (β₀ - d) β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) := by
  have hz := allBut_zero π P _ hstop
  intro d
  induction d with
  | zero =>
    intro _
    rw [Nat.sub_zero, Finset.Ico_self, Finset.sum_empty, mul_zero, zero_add]
    obtain ⟨C, hCc, hCs⟩ := pw_le_span π P _ _ (hg β₀ le_rfl)
    have hl := layer π hπ ⊥ (pw π (M ⧸ P) (τ + β₀ * S)) bot_le C (g β₀) Stop hCc hCs ?_
    · have h0 : Module.length O ↥(⊥ : Submodule O (M ⧸ P)) = 0 := Module.length_eq_zero
      rw [h0, zero_add] at hl
      rw [mul_comm Stop (g β₀)]
      exact hl
    · intro v hv
      obtain ⟨y, rfl⟩ := mem_pw.mp hv
      obtain ⟨x, rfl⟩ := P.mkQ_surjective y
      have h0 : π ^ (τ + Stop) • P.mkQ x = 0 := by
        rw [← map_smul]
        exact (Submodule.Quotient.mk_eq_zero P).mpr (hz x)
      rw [Submodule.mem_bot, smul_smul, ← pow_add,
        show Stop + (τ + β₀ * S) = β₀ * S + (τ + Stop) by ring, pow_add, ← smul_smul, h0,
        smul_zero]
  | succ d ih =>
    intro hd
    have hk : β₀ - d = (β₀ - (d + 1)) + 1 := by omega
    have ih' := ih (by omega)
    rw [hk] at ih'
    set k := β₀ - (d + 1) with hkdef
    obtain ⟨C, hCc, hCs⟩ := pw_le_span π P _ _ (hg k (by omega))
    have hUV : pw π (M ⧸ P) (τ + (k + 1) * S) ≤ pw π (M ⧸ P) (τ + k * S) := by
      intro u hu
      obtain ⟨y, rfl⟩ := mem_pw.mp hu
      refine mem_pw.mpr ⟨π ^ S • y, ?_⟩
      rw [smul_smul, ← pow_add, show τ + k * S + S = τ + (k + 1) * S by ring]
    have hs : ∀ v ∈ pw π (M ⧸ P) (τ + k * S), π ^ S • v ∈ pw π (M ⧸ P) (τ + (k + 1) * S) := by
      intro v hv
      obtain ⟨y, rfl⟩ := mem_pw.mp hv
      refine mem_pw.mpr ⟨y, ?_⟩
      rw [smul_smul, ← pow_add, show S + (τ + k * S) = τ + (k + 1) * S by ring]
    have hl := layer π hπ _ _ hUV C (g k) S hCc hCs hs
    have hsum : ∑ β ∈ Finset.Ico k β₀, g β = g k + ∑ β ∈ Finset.Ico (k + 1) β₀, g β :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) g
    calc Module.length O ↥(pw π (M ⧸ P) (τ + k * S))
        ≤ Module.length O ↥(pw π (M ⧸ P) (τ + (k + 1) * S)) + ((g k * S : ℕ) : ℕ∞) := hl
      _ ≤ ((S * ∑ β ∈ Finset.Ico (k + 1) β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) +
            ((g k * S : ℕ) : ℕ∞) := add_le_add ih' le_rfl
      _ = ((S * ∑ β ∈ Finset.Ico k β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) := by
          rw [hsum]; push_cast; ring

theorem main : LengthLayers := by
  unfold LengthLayers
  intro O M _ _ _ _ _ _ _ π hπ P τ S Stop β₀ g hg hstop
  set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M) with hN
  have hNV : N ≤ pw π M τ := inf_le_right
  rw [length_quot_eq_add hNV]
  have hA : Module.length O ↥((pw π M τ).map N.mkQ) ≤ Module.length O ↥(pw π (M ⧸ P) τ) := by
    let f : M ⧸ N →ₗ[O] M ⧸ P := N.mapQ P LinearMap.id (fun x hx => hx.1)
    have hf : ∀ x ∈ (pw π M τ).map N.mkQ, f x ∈ pw π (M ⧸ P) τ := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨y, rfl⟩ := mem_pw.mp hm
      exact mem_pw.mpr ⟨P.mkQ y, rfl⟩
    refine Module.length_le_of_injective (f.restrict hf) ((injective_iff_map_eq_zero _).mpr ?_)
    rintro ⟨x, hx⟩ h0
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hx
    have h1 : f (N.mkQ m) = 0 := congrArg Subtype.val h0
    have h2 : m ∈ P := (Submodule.Quotient.mk_eq_zero P).mp h1
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero N).mpr ⟨h2, hm⟩
  have hB : Module.length O (M ⧸ pw π M τ) ≤ ((Module.finrank O M * τ : ℕ) : ℕ∞) := by
    classical
    let b := Module.Free.chooseBasis O M
    let D : Finset (M ⧸ pw π M τ) := Finset.univ.image (fun i => (pw π M τ).mkQ (b i))
    have hDc : D.card ≤ Module.finrank O M := by
      rw [Module.finrank_eq_card_chooseBasisIndex]
      exact Finset.card_image_le
    have hD : ∀ x ∈ D, π ^ τ • x = 0 := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_pw.mpr ⟨b i, rfl⟩)
    have htop : Submodule.span O (D : Set (M ⧸ pw π M τ)) = ⊤ := by
      have e : (D : Set (M ⧸ pw π M τ)) = (pw π M τ).mkQ '' Set.range b := by
        ext y
        simp [D]
      rw [e, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
    calc Module.length O (M ⧸ pw π M τ) ≤ ((D.card * τ : ℕ) : ℕ∞) :=
          length_le_of_span_eq_top π hπ τ D hD htop
      _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right τ hDc
  have hC := length_pw_quot_le_sum_of_allButLE π hπ P τ S Stop β₀ g hg hstop β₀ le_rfl
  rw [Nat.sub_self, zero_mul, add_zero, ← Finset.range_eq_Ico] at hC
  calc Module.length O ↥((pw π M τ).map N.mkQ) + Module.length O (M ⧸ pw π M τ)
      ≤ ((S * ∑ β ∈ Finset.range β₀, g β + Stop * g β₀ : ℕ) : ℕ∞) +
          ((Module.finrank O M * τ : ℕ) : ℕ∞) := add_le_add (hA.trans hC) hB
    _ = _ := by push_cast; ring

end LengthLayersP

theorem lengthBoundOfLayers : LengthLayers := by
  exact LengthLayersP.main

end Formalism.G0
