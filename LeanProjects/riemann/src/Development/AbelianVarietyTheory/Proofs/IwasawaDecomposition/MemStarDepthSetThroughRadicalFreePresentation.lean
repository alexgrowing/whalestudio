import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section RadicalFree

theorem bilin_eq_zero_of_self_eq_zero {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hs : ∀ y z, β y z = β z y) (hn : ∀ y, 0 ≤ β y y) {x : X} (hx : β x x = 0) (y : X) : β x y = 0 := by
  have key : ∀ k : ℤ, 0 ≤ 2 * k * β x y + β y y := fun k => by
    have h := hn (k • x + y)
    simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hx, hs y x] at h
    nlinarith
  have hc := hn y
  rcases lt_trichotomy (β x y) 0 with h | h | h
  · have h1 := key (β y y + 1)
    have hb : β x y ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℤ) ≤ β y y + 1)
    nlinarith
  · exact h
  · have h1 := key (-(β y y + 1))
    have hb : 1 ≤ β x y := by omega
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0 : ℤ) ≤ β y y + 1)
    nlinarith

theorem exists_descent {X X₁ M F' : Type} [AddCommGroup X] [AddCommGroup X₁] [AddCommGroup M] [iM : Module ℤ M]
    [FunLike F' X X₁] [AddMonoidHomClass F' X X₁] (q : F') (hq : Function.Surjective q) (F : X →ₗ[ℤ] X →ₗ[ℤ] M)
    (hL : ∀ x, q x = 0 → ∀ y, F x y = 0) (hR : ∀ x, q x = 0 → ∀ y, F y x = 0) :
    ∃ F₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] M, ∀ a b, F₁ (q a) (q b) = F a b := by
  have hw : ∀ a a' b b', q a = q a' → q b = q b' → F a b = F a' b' := by
    intro a a' b b' ha hb
    have h1 : q (a - a') = 0 := by rw [map_sub, ha, sub_self]
    have h2 : q (b - b') = 0 := by rw [map_sub, hb, sub_self]
    have e1 := hL _ h1 b
    have e2 := hR _ h2 a'
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at e1
    rw [map_sub, sub_eq_zero] at e2
    rw [e1, e2]
  let p := Function.surjInv hq
  have hp : ∀ x, q (p x) = x := Function.surjInv_eq hq
  let f : X₁ → X₁ → M := fun x y => F (p x) (p y)
  have hf : ∀ a b, f (q a) (q b) = F a b := fun a b => hw _ _ _ _ (hp _) (hp _)
  refine ⟨LinearMap.mk₂ ℤ f ?_ ?_ ?_ ?_, fun a b => hf a b⟩
  · intro x x' y
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨a', rfl⟩ := hq x'
    obtain ⟨b, rfl⟩ := hq y
    rw [← map_add, hf, hf, hf, map_add, LinearMap.add_apply]
  · intro c x y
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [← map_zsmul, hf, hf]
    let g : X →+ M := AddMonoidHom.mk' (fun a => F a b) fun a a' => by rw [map_add, LinearMap.add_apply]
    exact (map_zsmul g c a).trans (int_smul_eq_zsmul iM c (F a b)).symm
  · intro x y y'
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    obtain ⟨b', rfl⟩ := hq y'
    rw [← map_add, hf, hf, hf, map_add]
  · intro c x y
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [← map_zsmul, hf, hf]
    let g : X →+ M := AddMonoidHom.mk' (fun b => F a b) fun b b' => map_add (F a) b b'
    exact (map_zsmul g c b).trans (int_smul_eq_zsmul iM c (F a b)).symm

theorem sum_eq_sum_emb {M : Type} [AddCommMonoid M] {m k : ℕ} (s : Fin k ↪ Fin m) (g : Fin m → M)
    (h : ∀ i, g i ≠ 0 → ∃ j, s j = i) : ∑ i, g i = ∑ j, g (s j) :=
  (Fintype.sum_of_injective s s.injective (fun j => g (s j)) g
    (fun i hi => by_contra fun h' => hi (h i h')) fun _ => rfl).symm

variable {X : Type} [AddCommGroup X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X}

theorem self_eq_zero_of_sum (hn : ∀ i y, 0 ≤ γ i y y) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) {x : X}
    (hx : (∑ i, c i • toReal (γ i)) x x = 0) (i : Fin m) (hi : c i ≠ 0) : γ i x x = 0 := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at hx
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_nonneg (hc j) (by exact_mod_cast hn j x)).1 hx i
    (Finset.mem_univ _)
  exact_mod_cast (mul_eq_zero.1 h0).resolve_left hi

theorem rcone_self_nonneg (hn : ∀ i y, 0 ≤ γ i y y) {G : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hG : G ∈ rcone γ) (y : X) :
    0 ≤ G y y := by
  obtain ⟨c, hc, rfl⟩ := hG
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hn i y)

theorem rcone_symm (hs : ∀ i y z, γ i y z = γ i z y) {G : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hG : G ∈ rcone γ) (y z : X) :
    G y z = G z y := by
  obtain ⟨c, hc, rfl⟩ := hG
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hs _ y z]

theorem rcone_bal {O : Type} [CommRing O] {bar : O → O} [Module O X] (hb : ∀ i, γ i ∈ balForms bar X)
    {G : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hG : G ∈ rcone γ) (a : O) (y z : X) : G (a • y) z = G y (bar a • z) := by
  obtain ⟨c, hc, rfl⟩ := hG
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, fun i => (hb i).2 a y z]

theorem descend_rcone {X₁ F' : Type} [AddCommGroup X₁] [FunLike F' X X₁] [AddMonoidHomClass F' X X₁] (q : F')
    (hq : Function.Surjective q) {k : ℕ} (s : Fin k ↪ Fin m) (γ₁ : Fin k → LinearMap.BilinForm ℤ X₁)
    (hγ₁ : ∀ j a b, γ₁ j (q a) (q b) = γ (s j) a b) {c : Fin m → ℝ} (hcs : ∀ i, c i ≠ 0 → ∃ j, s j = i)
    {G₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} (hG : ∀ a b, G₁ (q a) (q b) = (∑ i, c i • toReal (γ i)) a b) :
    G₁ = ∑ j, c (s j) • toReal (γ₁ j) := by
  refine LinearMap.ext₂ fun x y => ?_
  obtain ⟨a, rfl⟩ := hq x
  obtain ⟨b, rfl⟩ := hq y
  rw [hG]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, hγ₁]
  exact sum_eq_sum_emb s _ fun i hi => hcs i (left_ne_zero_of_mul hi)

theorem mem_balForms_of_pull {O : Type} [CommRing O] {bar : O → O} [Module O X] {X₁ : Type} [AddCommGroup X₁]
    [Module O X₁] {q : X →ₗ[O] X₁} (hq : Function.Surjective q) {β : LinearMap.BilinForm ℤ X₁}
    (h : pull q β ∈ balForms bar X) : β ∈ balForms bar X₁ := by
  refine ⟨fun y z => ?_, fun c y z => ?_⟩
  · obtain ⟨a, rfl⟩ := hq y
    obtain ⟨b, rfl⟩ := hq z
    exact h.1 a b
  · obtain ⟨a, rfl⟩ := hq y
    obtain ⟨b, rfl⟩ := hq z
    have := h.2 c a b
    simp only [pull_apply, map_smul] at this
    exact this

end RadicalFree

section Depth

variable {O : Type} [CommRing O] {bar : O → O} {ψ w : InvFun O}

theorem mem_depthSet_of_quot {X X₁ : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (q : X →ₗ[O] X₁) (hq : Function.Surjective q)
    {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} {v : LinearMap.BilinForm ℤ X} {t : ℝ}
    (hγ : IsCell bar ψ γ) (hB : B ∈ rcone γ) (hv : v ∈ balForms bar X) (hvn : ∀ y, 0 ≤ v y y)
    (hvw : w.evalZ v = 1) (hvc : InRCone γ v) (ht : 0 < t) (hBt : B - t • toReal v ∈ rcone γ)
    (hq0 : ∀ x, q x = 0 ↔ ∀ y, B x y = 0) {n : ℕ} {π : (Fin n → O) →ₗ[O] X} (hπ : Function.Surjective π) :
    t ∈ depthSet bar ψ w n (fun a b => B (π a) (π b)) := by
  classical
  have hs : ∀ i y z, γ i y z = γ i z y := fun i => (hγ.mem i).1
  have hn := hγ.nonneg

  let S : Finset (Fin m) := Finset.univ.filter fun i => ∀ x, q x = 0 → ∀ y, γ i x y = 0
  let s : Fin S.card ↪ Fin m := (S.orderEmbOfFin rfl).toEmbedding
  have hS : ∀ i, i ∈ S → ∃ j, s j = i := fun i hi => by
    have : i ∈ Set.range (S.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hi
    exact this
  have hsS : ∀ j, ∀ x, q x = 0 → ∀ y, γ (s j) x y = 0 := fun j =>
    (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem S rfl j)).2
  have hcoef : ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → (∀ x, q x = 0 → (∑ i, c i • toReal (γ i)) x x = 0) →
      ∀ i, c i ≠ 0 → ∃ j, s j = i := fun c hc h i hi =>
    hS i (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x hx y =>
      bilin_eq_zero_of_self_eq_zero _ (hs i) (hn i) (self_eq_zero_of_sum hn hc (h x hx) i hi) y⟩)

  have hBs : ∀ y z, B y z = B z y := rcone_symm hs hB
  have hBL : ∀ x, q x = 0 → ∀ y, B x y = 0 := fun x hx => (hq0 x).1 hx
  have hBR : ∀ x, q x = 0 → ∀ y, B y x = 0 := fun x hx y => by rw [hBs]; exact hBL x hx y
  have hvL : ∀ x, q x = 0 → ∀ y, v x y = 0 := fun x hx => by
    have h1 := rcone_self_nonneg hn hBt x
    have h2 : B x x = 0 := hBL x hx x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul, h2] at h1
    have h3 : (v x x : ℝ) ≤ 0 := by nlinarith
    have h4 : v x x = 0 := le_antisymm (by exact_mod_cast h3) (hvn x)
    exact bilin_eq_zero_of_self_eq_zero v hv.1 hvn h4
  have hvR : ∀ x, q x = 0 → ∀ y, v y x = 0 := fun x hx y => by rw [hv.1]; exact hvL x hx y

  choose γ₁ hγ₁ using fun j => exists_descent q hq (γ (s j)) (hsS j) fun x hx y => by
    rw [hs]; exact hsS j x hx y
  obtain ⟨v₁, hv₁⟩ := exists_descent q hq v hvL hvR
  obtain ⟨B₁, hB₁⟩ := exists_descent q hq B hBL hBR
  have hpull : ∀ j, pull q (γ₁ j) = γ (s j) := fun j => LinearMap.ext₂ fun a b => hγ₁ j a b
  have hvpull : pull q v₁ = v := LinearMap.ext₂ fun a b => hv₁ a b
  have hrc : ∀ {G₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ} {G : X →ₗ[ℤ] X →ₗ[ℤ] ℝ}, G ∈ rcone γ →
      (∀ a b, G₁ (q a) (q b) = G a b) → G₁ ∈ rcone γ₁ := by
    rintro G₁ G ⟨c, hc, rfl⟩ hG
    refine ⟨fun j => c (s j), fun j => hc _, descend_rcone q hq s γ₁ hγ₁ (hcoef c hc fun x hx => ?_) hG⟩
    rw [← hG x x, hx]
    simp

  have hcell : IsCell bar ψ γ₁ := by
    refine ⟨fun j => mem_balForms_of_pull hq (by rw [hpull]; exact hγ.mem _), fun j y => ?_, ?_, ?_⟩
    · obtain ⟨a, rfl⟩ := hq y
      rw [hγ₁]
      exact hn _ a
    · refine (linearOn_pull_iff hq).1 ?_
      simp only [hpull]
      exact linearOn_comp hγ.linear s
    · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
      let P : LinearMap.BilinForm ℤ X₁ →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
        { toFun := pull q, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      refine ⟨N, ℓ ∘ₗ P, hN, fun j => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
      · show (ℓ (pull q (γ₁ j)) : ℝ) = N * ψ.evalZ (γ₁ j)
        rw [← evalZ_pull ψ hq, hpull]
        exact h1 (s j)
      · show N * ψ.evalZ β ≤ (ℓ (pull q β) : ℝ)
        rw [← evalZ_pull ψ hq]
        exact h2 _ (pull_mem q hβ) fun y => hp _
      · have he' : N * ψ.evalZ (pull q β) = ℓ (pull q β) := by rw [evalZ_pull ψ hq]; exact he
        obtain ⟨k, c, hk, hc⟩ := h3 _ (pull_mem q hβ) (fun y => hp _) he'
        have hcS : ∀ i, c i ≠ 0 → ∃ j, s j = i := fun i hi => hS i (Finset.mem_filter.2 ⟨Finset.mem_univ _,
          fun x hx y => by
            have h0 := LinearMap.congr_fun₂ hc x x
            simp only [LinearMap.smul_apply, pull_apply, hx, map_zero, LinearMap.zero_apply, smul_zero,
              LinearMap.sum_apply] at h0
            have h4 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => nsmul_nonneg (hn j x) _).1 h0.symm i
              (Finset.mem_univ _)
            exact bilin_eq_zero_of_self_eq_zero _ (hs i) (hn i) ((smul_eq_zero.1 h4).resolve_left hi) y⟩)
        refine ⟨k, fun j => c (s j), hk, LinearMap.ext₂ fun x y => ?_⟩
        obtain ⟨a, rfl⟩ := hq x
        obtain ⟨b, rfl⟩ := hq y
        have h0 := LinearMap.congr_fun₂ hc a b
        simp only [LinearMap.smul_apply, pull_apply, LinearMap.sum_apply] at h0
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, hγ₁]
        rw [h0]
        exact sum_eq_sum_emb s _ fun i hi => hcS i fun h => hi (by rw [h, zero_smul])
  refine ⟨X₁, inferInstance, inferInstance, inferInstance, q ∘ₗ π, B₁, hq.comp hπ, fun x hx => ?_,
    fun a b => (hB₁ (π a) (π b)).symm, ht.le, S.card, γ₁, v₁, hcell,
    mem_balForms_of_pull hq (by rw [hvpull]; exact hv), fun y => ?_, ?_, hrc hvc fun a b => ?_, hrc hB hB₁,
    hrc hBt fun a b => ?_⟩
  · obtain ⟨a, rfl⟩ := hq x
    exact (hq0 a).2 fun y => by rw [← hB₁]; exact hx (q y)
  · obtain ⟨a, rfl⟩ := hq y
    rw [hv₁]
    exact hvn a
  · rw [← evalZ_pull w hq, hvpull]
    exact hvw
  · simp only [toReal_apply, hv₁]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, toReal_apply, hB₁, hv₁]

end Depth

theorem mem_depthSet_of_rcone : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X]
    [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ)
    (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) →
    w.evalZ v = 1 → InRCone γ v → 0 < t → B - t • toReal v ∈ rcone γ → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X),
    Function.Surjective π → t ∈ depthSet bar ψ w n (fun a b => B (π a) (π b)) := by
  intro O _ bar ψ w X _ _ _ m γ B v t hγ hB hv hvn hvw hvc ht hBt n π hπ
  let R : Submodule O X :=
    { carrier := {x | ∀ y, B x y = 0}
      add_mem' := fun {x x'} hx hx' y => by
        simp only [Set.mem_setOf_eq, map_add, LinearMap.add_apply, hx y, hx' y, add_zero]
      zero_mem' := fun y => by simp
      smul_mem' := fun c x hx y => by
        show B (c • x) y = 0
        rw [rcone_bal hγ.mem hB c x y]
        exact hx _ }
  exact mem_depthSet_of_quot R.mkQ R.mkQ_surjective hγ hB hv hvn hvw hvc ht hBt
    (fun x => Submodule.Quotient.mk_eq_zero R) hπ

end GlobalTheory.PolFan
