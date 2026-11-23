import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrincipalSeriesAppendEquivParabolicProduct

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace UpperTheory.V.Z.J.D

section Abs

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

private def mulMap (P K : Subgroup G) (hK : IsOpen (K : Set G)) (σ σ' : Representation ℂ P W) (c : G → ℂˣ)
    (hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v))
    (hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x) : smoothPart (ind P σ) →ₗ[ℂ] smoothPart (ind P σ') where
  toFun f := ⟨⟨fun x => ((c x : ℂˣ) : ℂ) • f.1.1 x, fun p x => by
      have h := f.1.2 p x
      show ((c ((p : G) * x) : ℂˣ) : ℂ) • f.1.1 ((p : G) * x) = _
      rw [h]
      exact hl p x _⟩, by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (Filter.inter_mem (f.2.mem_nhds (by simp)) (hK.mem_nhds K.one_mem)) ?_)
      rintro g ⟨h1, h2⟩
      have h3 : ind P σ g f.1 = f.1 := h1
      refine Subtype.ext (funext fun x => ?_)
      have h4 : f.1.1 (x * g) = f.1.1 x := congrArg (fun φ : indSpace P σ => φ.1 x) h3
      show ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c x : ℂˣ) : ℂ) • f.1.1 x
      rw [h4, hr g h2]⟩
  map_add' f f' := Subtype.ext (Subtype.ext (funext fun x => smul_add _ (f.1.1 x) (f'.1.1 x)))
  map_smul' a f := Subtype.ext (Subtype.ext (funext fun x => smul_comm _ a (f.1.1 x)))

private theorem equiv_of_char (P K : Subgroup G) (hK : IsOpen (K : Set G))
    (hPK : ∀ x : G, ∃ p : P, ∃ w ∈ K, x = (p : G) * w) (σ σ' : Representation ℂ P W) (R : P →* ℂˣ)
    (hR : ∀ p : P, (p : G) ∈ K → R p = 1) (hσ : ∀ (p : P) (v : W), σ' p v = ((R p : ℂˣ) : ℂ) • σ p v) :
    Nonempty (Representation.Equiv ((smInd P σ).comp K.subtype) ((smInd P σ').comp K.subtype)) := by
  obtain ⟨c, hc⟩ : ∃ c : G → ℂˣ, ∀ (p : P) (w : G), w ∈ K → c ((p : G) * w) = R p := by
    refine ⟨fun x => R (Classical.choose (hPK x)), fun p w hw => ?_⟩
    obtain ⟨w', hw', hx⟩ := Classical.choose_spec (hPK ((p : G) * w))
    set q := Classical.choose (hPK ((p : G) * w))
    have hqp : ((q⁻¹ * p : P) : G) ∈ K := by
      have : ((q⁻¹ * p : P) : G) = w' * w⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hx, mul_inv_cancel_right]
      rw [this]
      exact K.mul_mem hw' (K.inv_mem hw)
    have := hR _ hqp
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hr : ∀ κ ∈ K, ∀ x, c (x * κ) = c x := by
    intro κ hκ x
    obtain ⟨p, w, hw, rfl⟩ := hPK x
    rw [mul_assoc, hc _ _ (K.mul_mem hw hκ), hc _ _ hw]
  have hmul : ∀ (p : P) (x : G), c ((p : G) * x) = R p * c x := by
    intro p x
    obtain ⟨q, w, hw, rfl⟩ := hPK x
    rw [← mul_assoc, ← Subgroup.coe_mul, hc _ _ hw, hc _ _ hw, map_mul]
  have hl : ∀ (p : P) (x : G) (v : W), ((c ((p : G) * x) : ℂˣ) : ℂ) • σ p v = σ' p (((c x : ℂˣ) : ℂ) • v) := by
    intro p x v
    rw [hσ, map_smul, smul_smul, hmul, Units.val_mul]
  have hl' : ∀ (p : P) (x : G) (v : W),
      ((((fun y => (c y)⁻¹) ((p : G) * x)) : ℂˣ) : ℂ) • σ' p v = σ p ((((fun y => (c y)⁻¹) x : ℂˣ) : ℂ) • v) := by
    intro p x v
    simp only [hσ, map_smul, smul_smul, hmul, ← Units.val_mul]
    congr 2
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hr' : ∀ κ ∈ K, ∀ x, (fun y => (c y)⁻¹) (x * κ) = (fun y => (c y)⁻¹) x := by
    intro κ hκ x
    simp only [hr κ hκ x]
  refine ⟨{ toFun := mulMap P K hK σ σ' c hl hr
            map_add' := (mulMap P K hK σ σ' c hl hr).map_add
            map_smul' := (mulMap P K hK σ σ' c hl hr).map_smul
            isIntertwining' := ?_
            invFun := mulMap P K hK σ' σ (fun y => (c y)⁻¹) hl' hr'
            left_inv := ?_
            right_inv := ?_ }⟩
  · intro g
    refine LinearMap.ext fun f => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • f.1.1 (x * g) = ((c (x * g) : ℂˣ) : ℂ) • f.1.1 (x * g)
    rw [hr g g.2]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show (((c x)⁻¹ : ℂˣ) : ℂ) • (((c x : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  · intro f
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ((c x : ℂˣ) : ℂ) • ((((c x)⁻¹ : ℂˣ) : ℂ) • f.1.1 x) = f.1.1 x
    rw [smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end Abs

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem exists_pw (x : GL (Fin n) k) :
    ∃ p : parab k (points (Fin n)), ∃ w ∈ KO k (Fin n), x = (p : GL (Fin n) k) * w := by
  obtain ⟨u, g, w, hw, hx⟩ := UnitInd.exists_iwasawa (points (Fin n)) x
  refine ⟨⟨(u : GL (Fin n) k) * leviEmb k (points (Fin n)) g,
    mul_mem (unipRad_le_parab k (points (Fin n)) u.2) (leviEmb_mem_parab k (points (Fin n)) g)⟩, w, hw, hx⟩

open GlobalTheory.SmGL.PrinProd in
private theorem dg_mem_Uo (p : parab k (points (Fin n))) (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (i : Fin n) :
    dg p i ∈ UpperTheory.V.Hi.Uo k := by
  have h1 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).1 i i
  have h2 := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hp).2 i i
  rw [← PrinProd.val_dg] at h1
  have h3 : ((dg p⁻¹ i : kˣ) : k) ∈ 𝒪[k] := by
    rw [PrinProd.val_dg]
    simpa using h2
  rw [map_inv, Pi.inv_apply, Units.val_inv_eq_inv_val] at h3
  change valuation k _ = 1
  have a1 : valuation k ((dg p i : kˣ) : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 h1
  have a2 : valuation k ((dg p i : kˣ) : k)⁻¹ ≤ 1 := (Valuation.mem_integer_iff _ _).1 h3
  rw [map_inv₀] at a2
  have hne : valuation k ((dg p i : kˣ) : k) ≠ 0 := by simp
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 a2)

open GlobalTheory.SmGL.PrinProd in
private theorem sB_apply (χ : Fin n → kˣ →* ℂˣ) (p : parab k (points (Fin n))) (v : ℂ) :
    sB χ p v = ((deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂˣ) : ℂ) *
      (((torusChar χ (dg p) : ℂˣ) : ℂ) * v) := rfl

end Loc

open GlobalTheory.SmGL.PrinProd in

theorem psRes : PsRes := by
  intro k _ _ _ _ n ω ω' _ _ h
  let χ : Fin n → kˣ →* ℂˣ := fun i => ω i * absPow k ((↑n - 1) / 2)
  let χ' : Fin n → kˣ →* ℂˣ := fun i => ω' i * absPow k ((↑n - 1) / 2)
  let ρ : Fin n → kˣ →* ℂˣ := fun i => ω' i * (ω i)⁻¹
  have hχ : ∀ t, torusChar χ' t = torusChar ρ t * torusChar χ t := by
    intro t
    simp only [torusChar_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [χ, χ', ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    group
  refine equiv_of_char (parab k (points (Fin n))) (KO k (Fin n)) GlobalTheory.SplitFlip.isOpen_KO exists_pw
    (sB χ) (sB χ') ((torusChar ρ).comp dg) (fun p hp => ?_) (fun p v => ?_)
  · rw [MonoidHom.comp_apply, torusChar_apply]
    refine Finset.prod_eq_one fun i _ => ?_
    simp only [ρ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← h i ⟨_, dg_mem_Uo p hp i⟩, mul_inv_cancel]
  · rw [sB_apply, sB_apply, smul_eq_mul, MonoidHom.comp_apply, hχ, Units.val_mul]
    ring

end UpperTheory.V.Z.J.D
