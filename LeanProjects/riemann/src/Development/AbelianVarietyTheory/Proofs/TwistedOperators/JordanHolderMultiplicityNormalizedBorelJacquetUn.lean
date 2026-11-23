import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.UnramFixed

theorem occursTimes_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ θ η : G →* ℂˣ} (h : ∀ g v, τ g v = (δ g : ℂ) • ρ g v)
    (hη : ∀ g, η g = θ g * δ g) {r : ℕ} (hr : OccursTimes (ofChar θ) ρ r) :
    OccursTimes (ofChar η) τ r := by
  obtain ⟨S, T, h1, h2, h3⟩ := hr
  have hst : ∀ (P : Subrepresentation ρ) (g : G) (v : V), v ∈ P.toSubmodule → τ g v ∈ P.toSubmodule :=
    fun P g v hv => by
      rw [h]
      exact P.toSubmodule.smul_mem _ (P.apply_mem_toSubmodule g hv)
  refine ⟨fun i => ⟨(S i).toSubmodule, hst (S i)⟩, fun i => ⟨(T i).toSubmodule, hst (T i)⟩,
    fun i => h1 i, fun i j hij => h2 i j hij, fun i => ?_⟩
  obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
  refine step_iff.2 ⟨f, hsurj, fun g v hv => ?_, hker⟩
  have e := hint g v hv
  rw [ofChar_apply] at e
  show f (τ g v) = ofChar η g (f v)
  rw [h, map_smul, e, ofChar_apply, hη, Units.val_mul, smul_eq_mul]
  ring

theorem jhMult_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ : G →* ℂˣ} (θ : G →* ℂˣ)
    (h : ∀ g v, τ g v = (((δ g)⁻¹ : ℂˣ) : ℂ) • ρ g v) :
    jhMult (ofChar θ) τ = jhMult (ofChar (θ * δ)) ρ := by
  have key : ∀ r, OccursTimes (ofChar θ) τ r ↔ OccursTimes (ofChar (θ * δ)) ρ r := fun r =>
    ⟨occursTimes_of_twist (δ := δ)
        (fun g v => by rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
        (fun g => MonoidHom.mul_apply θ δ g),
      occursTimes_of_twist (δ := δ⁻¹) (fun g v => by rw [MonoidHom.inv_apply]; exact h g v)
        (fun g => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right])⟩
  simp only [jhMult, key]

private lemma pres_iterate_zero {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) (S : Subrepresentation ρ)
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = ofChar θ g (f v)) (v : V)
    (hv : v ∈ S.toSubmodule) : ∃ u ∈ fixed ρ H, u ∈ S.toSubmodule ∧ f u = f v := by

  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix hρ hH v
  haveI : U.FiniteIndex := hU
  letI : Fintype (H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨GlobalTheory.LocGL.idem hρ hH v, GlobalTheory.LocGL.idem_mem hρ hH v, ?_, ?_⟩
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv]
    exact S.toSubmodule.smul_mem _ (S.toSubmodule.sum_mem fun q _ => S.apply_mem_toSubmodule _ hv)
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv, map_smul, map_sum]
    have hq : ∀ q : H ⧸ U, f (ρ (q.out : H) v) = f v := fun q => by
      rw [hf _ v hv, ofChar_apply, hθ _ (q.out).2, Units.val_one, one_mul]
    have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem jhMult_onFixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) :
    jhMult (ofChar θ) ρ = jhMult (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) := by
  let ι : (onFixed ρ H (MonoidHom.id G) hn).IntertwiningMap ρ :=
    { toLinearMap := (fixed ρ H).subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have key : ∀ r, OccursTimes (ofChar θ) ρ r ↔
      OccursTimes (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) r := by
    intro r
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      refine ⟨fun i => subComap ι (S i), fun i => subComap ι (T i), fun i => subComap_mono ι (h1 i),
        fun i j hij => subComap_mono ι (h2 i j hij), fun i => ?_⟩
      obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
      refine step_iff.2 ⟨f ∘ₗ (fixed ρ H).subtype, fun w => ?_, fun g u hu => hint g u.1 hu,
        fun u hu => hker u.1 hu⟩
      obtain ⟨v, hv, rfl⟩ := hsurj w
      obtain ⟨u, huF, huS, hfu⟩ := pres_iterate_zero hρ hH hθ (S i) f hint v hv
      exact ⟨⟨u, huF⟩, huS, hfu⟩
    · rintro ⟨S, T, h1, h2, h3⟩
      exact ⟨fun i => subMap ι (S i), fun i => subMap ι (T i), fun i => subMap_mono ι (h1 i),
        fun i j hij => subMap_mono ι (h2 i j hij),
        fun i => step_iff.2 (step_map ι hι (step_iff.1 (h3 i)))⟩
  simp only [jhMult, key]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_unitsO : IsCompact {x : kˣ | valuation k (x : k) = 1} := by
  haveI : T1Space k := IsTopologicalAddGroup.t1Space k (by
    first
      | exact isClosed_singleton
      | (convert (Valuation.isClosed_sphere (v := valuation k) 0) using 1
         ext x
         simp))
  have hS : IsCompact (((valuation k).integer.toSubmonoid : Submonoid k) : Set k) :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  convert Submonoid.units_isCompact hS using 1
  ext x
  have h0 : valuation k (x : k) ≠ 0 := by simp
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨h1, h2⟩
    rw [inv_le_one₀ (zero_lt_iff.2 h0)] at h2
    exact le_antisymm h1 h2

theorem isCompact_torusO (n : Type) : IsCompact (torusO k n : Set (n → kˣ)) :=
  isCompact_pi_infinite fun _ => isCompact_unitsO k

theorem deltaHalf_torusO {n : Type} [Fintype n] [LinearOrder n] {t : n → kˣ} (ht : t ∈ torusO k n) :
    deltaHalf k (fun _ : n => Unit) (leviTorus k n t) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hdet : Matrix.GeneralLinearGroup.det (leviTorus k n t a) = t a :=
    congrFun ((leviTorus k n).symm_apply_apply t) a
  have hv : valuation k (t a : k) = 1 := (show ∀ i, valuation k (t i : k) = 1 from ht) a
  apply Units.ext
  rw [hdet, val_absPow, nabs_eq_one k hv, Units.val_one]
  simp

variable {k} {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]

theorem jacB_apply (π : Representation ℂ (GL n k) V) (g : n → kˣ) (v : Jacquet π (unipB k n)) :
    jacB π g v = (((((deltaHalf k fun _ : n => Unit).comp
      (leviTorus k n).toMonoidHom) g)⁻¹ : ℂˣ) : ℂ) • jacBU π g v := by
  first
    | exact twist_apply (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v
    | (show twist (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v = _
       rw [twist_apply]
       rfl)

theorem jhMult_jacBU_eq_expMult {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    {θ : (n → kˣ) →* ℂˣ} (hθ : ∀ t ∈ torusO k n, θ t = 1) :
    jhMult (ofChar θ) (jacBU π) = expMult π θ := by
  unfold expMult jacBUFixed
  exact jhMult_onFixed (isSmooth_jacBU hπ) (isCompact_torusO k n) _ hθ

theorem jhMult_jacB_eq_expMult : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  intro k _ _ _ _ n V _ _ π hπ θ hθ
  rw [jhMult_of_twist θ (fun g v => jacB_apply π g v)]
  refine jhMult_jacBU_eq_expMult hπ fun t ht => ?_
  rw [MonoidHom.mul_apply, hθ t ht, one_mul]
  exact deltaHalf_torusO k ht

end GlobalTheory.SmGL.UnramFixed
