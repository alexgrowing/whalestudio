import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open Module Submodule
open scoped Pointwise

namespace TorsionFreeQuotientLength

variable {R : Type*} [CommRing R]

theorem length_pi_quot_smul_top (t : ℕ) (a : R) :
    Module.length R ((Fin t → R) ⧸ (a • ⊤ : Submodule R (Fin t → R))) =
      t * Module.length R (R ⧸ Ideal.span {a}) := by
  let f : (Fin t → R) →ₗ[R] (Fin t → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a}).mkQ ∘ₗ LinearMap.proj i
  have hf : Function.Surjective f := by
    intro y
    choose g hg using fun i => Ideal.Quotient.mk_surjective (y i)
    exact ⟨g, funext fun i => by simp [f, hg i]⟩
  have hker : LinearMap.ker f = a • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and]
    constructor
    · intro h
      have hx : ∀ i, x i ∈ Ideal.span {a} := fun i => by
        have := congrFun h i
        exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [f] using this)
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (hx i)
      exact ⟨c, funext fun i => by simp [← hc i, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      funext i
      simp only [f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.smul_apply,
        LinearMap.coe_proj, Function.eval, mkQ_apply, Pi.zero_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a))
  rw [← hker, (f.quotKerEquivOfSurjective hf).length_eq, Module.length_pi]
  simp

theorem isFiniteLength_of_torsion [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (Q : Type*) [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (hQ : ∀ q : Q, ∃ c : R, c ≠ 0 ∧ c • q = 0) : IsFiniteLength R Q := by
  have htors : Module.IsTorsion R Q := fun q => by
    obtain ⟨c, hc, hcq⟩ := hQ q
    exact ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hcq⟩
  obtain ⟨c, hc1, hc2⟩ := Submodule.annihilator_top_inter_nonZeroDivisors htors
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R Q
  have hle : (c • ⊤ : Submodule R (Fin n → R)) ≤ LinearMap.ker f := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
    rw [LinearMap.mem_ker, map_smul]
    exact (Submodule.mem_annihilator.mp hc1) _ Submodule.mem_top
  have hs : Function.Surjective ((c • ⊤ : Submodule R (Fin n → R)).liftQ f hle) := by
    intro q
    obtain ⟨x, rfl⟩ := hf q
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  rw [← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hs)
  rw [length_pi_quot_smul_top]
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
    (Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton R hc2))

theorem length_quot_smul_eq {N F₀ : Type*} [AddCommGroup N] [Module R N]
    [AddCommGroup F₀] [Module R F₀] (φ : F₀ →ₗ[R] N) (hφ : Function.Injective φ) {a : R}
    (hreg : Function.Injective fun x : N => a • x)
    (hfin : IsFiniteLength R (N ⧸ LinearMap.range φ)) :
    Module.length R (N ⧸ (a • ⊤ : Submodule R N)) =
      Module.length R (F₀ ⧸ (a • ⊤ : Submodule R F₀)) := by
  set P := LinearMap.range φ
  have hPa : a • P ≤ a • ⊤ := fun x hx => by
    obtain ⟨p, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact smul_mem_pointwise_smul p a ⊤ mem_top
  have hPP : a • P ≤ P := fun x hx => by
    obtain ⟨p, hp, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    exact P.smul_mem a hp
  let f1 : (N ⧸ P) →ₗ[R] (N ⧸ a • P) := P.mapQ (a • P) (a • LinearMap.id)
    (fun x hx => by simpa using smul_mem_pointwise_smul x a P hx)
  let g1 : (N ⧸ a • P) →ₗ[R] (N ⧸ (a • ⊤ : Submodule R N)) := Submodule.factor hPa
  let f2 : (F₀ ⧸ (a • ⊤ : Submodule R F₀)) →ₗ[R] (N ⧸ a • P) := (a • ⊤ : Submodule R F₀).mapQ (a • P) φ
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simpa using smul_mem_pointwise_smul (φ y) a P (LinearMap.mem_range_self φ y))
  let g2 : (N ⧸ a • P) →ₗ[R] (N ⧸ P) := Submodule.factor hPP
  have hf1 : Function.Injective f1 := by
    refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [f1, mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply, Quotient.mk_eq_zero,
      mem_smul_pointwise_iff_exists] at hq ⊢
    obtain ⟨p, hp, hpx⟩ := hq
    rwa [← hreg hpx]
  have hg1 : Function.Surjective g1 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex1 : Function.Exact f1 g1 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro h
      have : x ∈ (a • ⊤ : Submodule R N) := (Quotient.mk_eq_zero _).mp h
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp this
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hb : a • b - x ∈ a • P := (Submodule.Quotient.eq _).mp hq
      refine (Quotient.mk_eq_zero _).mpr ?_
      have h1 : a • b ∈ (a • ⊤ : Submodule R N) := smul_mem_pointwise_smul b a ⊤ mem_top
      simpa using sub_mem h1 (hPa hb)
  have hf2 : Function.Injective f2 := by
    refine (injective_iff_map_eq_zero _).mpr fun q hq => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [f2, mapQ_apply, Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists] at hq ⊢
    obtain ⟨p, ⟨z, rfl⟩, hp⟩ := hq
    refine ⟨z, mem_top, hφ ?_⟩
    rw [map_smul, hp]
  have hg2 : Function.Surjective g2 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex2 : Function.Exact f2 g2 := fun y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro h
      obtain ⟨z, rfl⟩ : x ∈ P := (Quotient.mk_eq_zero _).mp h
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    · rintro ⟨q, hq⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      have hb : φ z - x ∈ a • P := (Submodule.Quotient.eq _).mp hq
      refine (Quotient.mk_eq_zero _).mpr ?_
      have := sub_mem (LinearMap.mem_range_self φ z) (hPP hb)
      rwa [sub_sub_cancel] at this
  have e1 := Module.length_eq_add_of_exact f1 g1 hf1 hg1 hex1
  have e2 := Module.length_eq_add_of_exact f2 g2 hf2 hg2 hex2
  rw [e1, add_comm (Module.length R (F₀ ⧸ _))] at e2
  exact WithTop.add_left_cancel (Module.length_ne_top_iff.mpr hfin) e2

end TorsionFreeQuotientLength

theorem TorsionFreeQuotientLength.proof : TorsionFreeQuotientLength.Statement := by
  intro R _ _ _ hdim M _ _ _ r hr a ha
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  rw [Submodule.ideal_span_singleton_smul, ← TorsionFreeQuotientLength.length_pi_quot_smul_top]

  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent_of_isDomain R M
  rw [hr] at hs
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hs
  let v : Fin r → M := fun i => (e.symm i : M)
  have hv : LinearIndependent R v := hli.comp e.symm e.symm.injective
  let φ : (Fin r → R) →ₗ[R] M :=
    Finsupp.linearCombination R v ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin r)).symm.toLinearMap
  have hφ : Function.Injective φ :=
    (show Function.Injective (Finsupp.linearCombination R v) from hv).comp
      (Finsupp.linearEquivFunOnFinite R R (Fin r)).symm.injective
  have hrange : LinearMap.range φ = span R (Set.range v) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Finsupp.range_linearCombination]
  have htor : ∀ x : M, ∃ c : R, c ≠ 0 ∧ c • x ∈ LinearMap.range φ := by
    have h1 := rank_quotient_add_rank_of_isDomain (span R (Set.range v))
    rw [rank_span hv, Cardinal.mk_range_eq v hv.injective, Cardinal.mk_fin, hr] at h1
    have h0 : Module.rank R (M ⧸ span R (Set.range v)) = 0 := by
      by_contra h
      have h2 := add_le_add_right (Cardinal.one_le_iff_ne_zero.mpr h) (r : Cardinal)
      rw [add_comm (r : Cardinal) (Module.rank _ _), h1] at h2
      exact absurd h2 (by exact_mod_cast Nat.not_succ_le_self r)
    intro x
    obtain ⟨c, hc, hcx⟩ := rank_eq_zero_iff.mp h0 (Submodule.Quotient.mk x)
    exact ⟨c, hc, hrange ▸ (Quotient.mk_eq_zero _).mp (by rwa [← Quotient.mk_smul] at hcx)⟩

  have hLtop : Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) ≠ ⊤ := by
    rw [TorsionFreeQuotientLength.length_pi_quot_smul_top]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha)))
  let T : Submodule R M := a • ⊤
  have hfg : ∀ N : Submodule R M, N.FG → LinearMap.range φ ≤ N →
      Module.length R (N.map T.mkQ) ≤ Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) := by
    intro N hN hφN
    have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
    let φN : (Fin r → R) →ₗ[R] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hreg : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (smul_right_injective M ha (congrArg Subtype.val h))
    have hfin : IsFiniteLength R (N ⧸ LinearMap.range φN) := by
      refine TorsionFreeQuotientLength.isFiniteLength_of_torsion _ fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule R N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule R N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← TorsionFreeQuotientLength.length_quot_smul_eq φN hφN' hreg hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)

  let S : Set ℕ := {n | ∃ N : Submodule R M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length R (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R)))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length R ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span R {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span R {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span R {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length R ((N₀ ⊔ span R {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length R (N₀.map T.mkQ) < Module.length R ((N₀ ⊔ span R {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length R (M ⧸ T) = Module.length R (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) := hfg N₀ hN₀ hφN₀

end GroundTheory.Heights₂.Heights.Model
