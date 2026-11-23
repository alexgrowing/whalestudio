import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulQuotEqSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R]
  {G : Cell U → Type v} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapCEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (i : ℕ) : Cochain G i ≃ₗ[R] Cochain G' i :=
  LinearEquiv.piCongrRight fun I : Idx U i => e I.1

theorem mapCEquiv_d (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : mapCEquiv e (i + 1) (d G ρ i s) = d G' ρ' i (mapCEquiv e i s) :=
  mapC_d (fun I => (e I).toLinearMap) he i s

theorem mem_bdry_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ bdry G ρ i ↔ mapCEquiv e i s ∈ bdry G' ρ' i := by
  cases i with
  | zero =>
    change s ∈ (⊥ : Submodule R _) ↔ mapCEquiv e 0 s ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, Submodule.mem_bot, LinearEquiv.map_eq_zero_iff]
  | succ i =>
    change s ∈ LinearMap.range (d G ρ i) ↔ mapCEquiv e (i + 1) s ∈ LinearMap.range (d G' ρ' i)
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨mapCEquiv e i t, (mapCEquiv_d e he i t).symm⟩
    · rintro ⟨t', ht'⟩
      refine ⟨(mapCEquiv e i).symm t', (mapCEquiv e (i + 1)).injective ?_⟩
      rw [mapCEquiv_d e he, LinearEquiv.apply_symm_apply, ht']

theorem mem_ker_iff (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m))
    (i : ℕ) (s : Cochain G i) : s ∈ LinearMap.ker (d G ρ i) ↔ mapCEquiv e i s ∈ LinearMap.ker (d G' ρ' i) := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← mapCEquiv_d e he, LinearEquiv.map_eq_zero_iff]

def kerEquiv (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    LinearMap.ker (d G ρ i) ≃ₗ[R] LinearMap.ker (d G' ρ' i) :=
  LinearEquiv.ofSubmodules (mapCEquiv e i) _ _ (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_ker_iff e he,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply])

def equivH (e : ∀ I, G I ≃ₗ[R] G' I) (he : ∀ I J h m, e J (ρ I J h m) = ρ' I J h (e I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  Submodule.Quotient.equiv _ _ (kerEquiv e he i) (by
    ext z
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Submodule.mem_comap,
      Submodule.mem_comap, Submodule.subtype_apply, Submodule.subtype_apply, mem_bdry_iff e he]
    congr! 1
    change mapCEquiv e i ((mapCEquiv e i).symm (z : Cochain G' i)) = z
    exact LinearEquiv.apply_symm_apply _ _)

end Cech

section Mul

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {F₁ F₂ G₁ G₂ : SubSystem k x Ω} {s : Ω}

def mulSubMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I) (I : Chart x) : F₁.sub I →ₗ[k] G₁.sub I where
  toFun y := ⟨s * y, h₁ I y y.2⟩
  map_add' a b := Subtype.ext (mul_add s (a : Ω) b)
  map_smul' c y := Subtype.ext (by
    change s * ((c • y : F₁.sub I) : Ω) = ((c • (⟨s * y, h₁ I y y.2⟩ : G₁.sub I) : G₁.sub I) : Ω)
    rw [Submodule.coe_smul_of_tower, Submodule.coe_smul_of_tower, mul_smul_comm])

def mulQuotMap (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) →ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
  (SubSystem.quotSub F₁ F₂ I).mapQ (SubSystem.quotSub G₁ G₂ I) (mulSubMap h₁ I)
    (fun y hy => (h₃ I y y.2).mpr hy)

theorem mulQuotMap_bijective (h₁ : ∀ I, ∀ y ∈ F₁.sub I, s * y ∈ G₁.sub I)
    (h₂ : ∀ I, ∀ z ∈ G₁.sub I, ∃ y ∈ F₁.sub I, z - s * y ∈ G₂.sub I)
    (h₃ : ∀ I, ∀ y ∈ F₁.sub I, (s * y ∈ G₂.sub I ↔ y ∈ F₂.sub I)) (I : Chart x) :
    Function.Bijective (mulQuotMap h₁ h₃ I) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [LinearMap.mem_ker] at hm
    change Submodule.Quotient.mk (mulSubMap h₁ I y) = 0 at hm
    rw [Submodule.Quotient.mk_eq_zero] at hm
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact (h₃ I y y.2).mp hm
  · intro m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    obtain ⟨y, hy, hz⟩ := h₂ I z z.2
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    change Submodule.Quotient.mk (mulSubMap h₁ I ⟨y, hy⟩) = Submodule.Quotient.mk z
    rw [Submodule.Quotient.eq]
    change ((mulSubMap h₁ I ⟨y, hy⟩ - z : G₁.sub I) : Ω) ∈ G₂.sub I
    rw [Submodule.coe_sub, ← neg_sub]
    exact (G₂.sub I).neg_mem hz

end Mul

theorem MulQuotEq.proof : MulQuotEq.Statement.{u, w} := by
  intro k _ Ω _ _ N x F₁ F₂ G₁ G₂ s h₁ h₂ h₃
  let e : ∀ I, (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[k] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I) :=
    fun I => LinearEquiv.ofBijective (mulQuotMap h₁ h₃ I) (mulQuotMap_bijective h₁ h₂ h₃ I)
  have he : ∀ I J h m, e J (SubSystem.quotRes F₁ F₂ I J h m) = SubSystem.quotRes G₁ G₂ I J h (e I m) := by
    intro I J h m
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rfl
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.equivH e he i).finrank_eq).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
