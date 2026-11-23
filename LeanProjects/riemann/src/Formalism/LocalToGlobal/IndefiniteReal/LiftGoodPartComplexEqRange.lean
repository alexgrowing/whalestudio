import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.CxPass
import Formalism.LocalToGlobal.IndefiniteReal.MemRangeAdjointOfKerStable
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfMemRangeAdjoint
import Formalism.LocalToGlobal.IndefiniteReal.EqZeroOfRangeAdjoint
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace LevelOperators

section Gen

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {F : Type} [AddCommGroup F] [Module K F]

def opF (r : Representation K G F) (a : MonoidAlgebra K G) : F →ₗ[K] F := ∑ g : G, a.coeff g • r g

def opV (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M) (a : MonoidAlgebra K G) :
    M →ₗ[ℂ] M :=
  ∑ g : G, σ (a.coeff g) • T g

theorem opF_eq_lift (r : Representation K G F) (a : MonoidAlgebra K G) :
    opF r a = MonoidAlgebra.lift K (F →ₗ[K] F) G r a := by
  classical
  first
  | (rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)]; rfl)
  | (rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)]; simp [opF])
  | (simp [opF, MonoidAlgebra.lift_apply, Finsupp.sum_fintype]; done)

theorem opF_mul (r : Representation K G F) (a b : MonoidAlgebra K G) :
    opF r (a * b) = opF r a ∘ₗ opF r b := by
  rw [opF_eq_lift, opF_eq_lift, opF_eq_lift, map_mul]
  first | rfl | exact LinearMap.mul_eq_comp _ _

theorem opF_smul (r : Representation K G F) (c : K) (a : MonoidAlgebra K G) : opF r (c • a) = c • opF r a := by
  rw [opF_eq_lift, opF_eq_lift, map_smul]

theorem opF_single (r : Representation K G F) (g : G) : opF r (MonoidAlgebra.single g 1) = r g := by
  rw [opF_eq_lift, MonoidAlgebra.lift_single, one_smul]

private theorem opV_add_lemma (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M)
    (a b : MonoidAlgebra K G) : opV σ T (a + b) = opV σ T a + opV σ T b := by
  first
  | (simp only [opV, ← Finset.sum_add_distrib, ← add_smul, ← map_add]; rfl)
  | (simp [opV, add_smul, Finset.sum_add_distrib, MonoidAlgebra.coeff_add]; done)
  | (simp [opV, add_smul, Finset.sum_add_distrib]; done)

private theorem opV_single_lemma_2 (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M)
    (g : G) (c : K) : opV σ T (MonoidAlgebra.single g c) = σ c • T g := by
  classical
  simp only [opV]
  rw [Finset.sum_eq_single g]
  · first
    | (simp; done)
    | (simp [MonoidAlgebra.coeff_single]; done)
    | (simp [MonoidAlgebra.single_apply]; done)
  · intro b _ hb
    first
    | (simp [hb, Ne.symm hb]; done)
    | (simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hb, Ne.symm hb]; done)
    | (simp [MonoidAlgebra.single_apply, hb, Ne.symm hb]; done)
  · intro h
    exact absurd (Finset.mem_univ g) h

private theorem opV_zero_lemma_3 (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M) :
    opV σ T 0 = 0 := by
  first
  | (simp [opV]; done)
  | (simp [opV, MonoidAlgebra.coeff_zero]; done)
  | (have h := opV_add_lemma σ T 0 0
     rw [add_zero] at h
     simpa using h)

theorem opV_sum_single (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M) {ι : Type}
    (s : Finset ι) (f : ι → G) (c : ι → K) :
    opV σ T (∑ i ∈ s, MonoidAlgebra.single (f i) (c i)) = ∑ i ∈ s, σ (c i) • T (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, opV_zero_lemma_3]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, opV_add_lemma, opV_single_lemma_2, ih]

theorem opV_lvlIdem [CharZero K] (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M] (T : G → M →ₗ[ℂ] M)
    (P : Subgroup G) (ψ : P →* Kˣ) (v : M) (hv : ∀ h : P, T (h : G) v = σ ((ψ h : Kˣ) : K) • v) :
    opV σ T (lvlIdem P ψ) v = v := by
  classical
  unfold lvlIdem
  rw [opV_sum_single, LinearMap.sum_apply]
  have key : ∀ h : P, σ ((Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)) * σ ((ψ h : Kˣ) : K) =
      σ ((Nat.card P : K)⁻¹) := by
    intro h
    rw [← map_mul, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [LinearMap.smul_apply, hv, smul_smul, key, Finset.sum_const, Finset.card_univ]
  have hc : ((Nat.card P : ℂ) * σ ((Nat.card P : K)⁻¹)) = 1 := by
    rw [map_inv₀, map_natCast]
    refine mul_inv_cancel₀ ?_
    first
    | exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    | exact Nat.cast_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
  rw [← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hc, one_smul]

variable {σ : K →+* ℂ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem ext_j {M : Type} [AddCommGroup M] [Module ℂ M] {j : F →ₛₗ[σ] V}
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {f f' : V →ₗ[ℂ] M} (h : ∀ x, f (j x) = f' (j x)) : f = f' := by
  exact LinearMap.ext_on_range hsp h

variable {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V}

theorem j_opF (hjr : ∀ g x, j (r g x) = ρ g (j x)) (a : MonoidAlgebra K G) (x : F) :
    j (opF r a x) = opV σ ρ a (j x) := by
  first
  | (simp only [opF, opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smulₛₗ, hjr]; done)
  | (simp [opF, opV, map_sum, hjr]; done)
  | (simp only [opF, opV, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hjr]; done)

theorem opV_mul (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (a b : MonoidAlgebra K G) : opV σ ρ (a * b) = opV σ ρ a ∘ₗ opV σ ρ b := by
  apply ext_j hsp
  intro x
  rw [LinearMap.comp_apply, ← j_opF hjr, ← j_opF hjr, ← j_opF hjr, opF_mul, LinearMap.comp_apply]

theorem opV_idem (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (e : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e) : opV σ ρ e ∘ₗ opV σ ρ e = opV σ ρ e := by
  apply ext_j hsp
  intro x
  have h2 : opF r e (opF r e x) = opF r e x := LinearMap.congr_fun he x
  rw [LinearMap.comp_apply, ← j_opF hjr, ← j_opF hjr, h2]

theorem rho_mul (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x)) (g h : G) :
    ρ (g * h) = ρ g ∘ₗ ρ h := by
  apply ext_j hsp
  intro x
  rw [LinearMap.comp_apply, ← hjr, ← hjr, ← hjr, map_mul, Module.End.mul_apply]

theorem rho_one (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x)) :
    ρ 1 = LinearMap.id := by
  apply ext_j hsp
  intro x
  rw [LinearMap.id_apply, ← hjr, map_one, Module.End.one_apply]

theorem rho_inv_apply (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x)) (g : G)
    (u : V) : ρ g (ρ g⁻¹ u) = u := by
  have h1 := LinearMap.congr_fun (rho_mul hsp hjr g g⁻¹) u
  rw [mul_inv_cancel, rho_one hsp hjr] at h1
  exact h1.symm

theorem rho_unitary (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (hiso : ∀ g x y, ⟪j (r g x), j (r g y)⟫_ℂ = ⟪j x, j y⟫_ℂ) (g : G) (u w : V) :
    ⟪ρ g u, ρ g w⟫_ℂ = ⟪u, w⟫_ℂ := by
  have h1 : ∀ x w, ⟪ρ g (j x), ρ g w⟫_ℂ = ⟪j x, w⟫_ℂ := by
    intro x w
    have hext := LinearMap.ext_on_range hsp (f := (innerₛₗ ℂ (ρ g (j x))).comp (ρ g))
      (g := innerₛₗ ℂ (j x)) (fun y => by
        show ⟪ρ g (j x), ρ g (j y)⟫_ℂ = ⟪j x, j y⟫_ℂ
        rw [← hjr, ← hjr, hiso])
    first
    | exact LinearMap.congr_fun hext w
    | simpa using LinearMap.congr_fun hext w
  have h2 : ∀ w u, ⟪ρ g w, ρ g u⟫_ℂ = ⟪w, u⟫_ℂ := by
    intro w u
    have hext := LinearMap.ext_on_range hsp (f := (innerₛₗ ℂ (ρ g w)).comp (ρ g))
      (g := innerₛₗ ℂ w) (fun y => by
        show ⟪ρ g w, ρ g (j y)⟫_ℂ = ⟪w, j y⟫_ℂ
        rw [← inner_conj_symm (ρ g w) (ρ g (j y)), h1, inner_conj_symm])
    first
    | exact LinearMap.congr_fun hext u
    | simpa using LinearMap.congr_fun hext u
  exact h2 u w

variable {gE : Representation ℂ G E} {Θ : V →ₗ[ℂ] E}

theorem theta_rho (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (heq : ∀ g x, Θ (j (r g x)) = gE g (Θ (j x))) (g : G) : Θ ∘ₗ ρ g = gE g ∘ₗ Θ := by
  apply ext_j hsp
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hjr, heq]

theorem gE_inv_apply (g : G) (z : E) : gE g (gE g⁻¹ z) = z := by
  first
  | (rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
  | (simp [← Module.End.mul_apply, ← map_mul]; done)
  | (show (gE g * gE g⁻¹) z = z; rw [← map_mul]; simp)

theorem rho_adj (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (hiso : ∀ g x y, ⟪j (r g x), j (r g y)⟫_ℂ = ⟪j x, j y⟫_ℂ) (heq : ∀ g x, Θ (j (r g x)) = gE g (Θ (j x)))
    (hu : ∀ (g : G) (x y : E), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) (e : E) :
    ρ g (LinearMap.adjoint Θ e) = LinearMap.adjoint Θ (gE g e) := by
  have hinv : ∀ y, ρ g⁻¹ (ρ g y) = y := fun y => by
    simpa using rho_inv_apply hsp hjr g⁻¹ y
  have hth : ∀ v, Θ (ρ g⁻¹ v) = gE g⁻¹ (Θ v) := fun v =>
    LinearMap.congr_fun (theta_rho hsp hjr heq g⁻¹) v
  apply ext_inner_left ℂ
  intro v
  calc ⟪v, ρ g (LinearMap.adjoint Θ e)⟫_ℂ
      = ⟪ρ g⁻¹ v, ρ g⁻¹ (ρ g (LinearMap.adjoint Θ e))⟫_ℂ := (rho_unitary hsp hjr hiso g⁻¹ _ _).symm
    _ = ⟪Θ (ρ g⁻¹ v), e⟫_ℂ := by rw [hinv, LinearMap.adjoint_inner_right]
    _ = ⟪gE g (gE g⁻¹ (Θ v)), gE g e⟫_ℂ := by rw [hth, hu]
    _ = ⟪v, LinearMap.adjoint Θ (gE g e)⟫_ℂ := by rw [gE_inv_apply, LinearMap.adjoint_inner_right]

theorem theta_opV (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (heq : ∀ g x, Θ (j (r g x)) = gE g (Θ (j x))) (a : MonoidAlgebra K G) (u : V) :
    Θ (opV σ ρ a u) = opV σ (fun g => gE g) a (Θ u) := by
  simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [show Θ (ρ g u) = gE g (Θ u) from LinearMap.congr_fun (theta_rho hsp hjr heq g) u]

theorem opV_adj (hsp : Submodule.span ℂ (Set.range j) = ⊤) (hjr : ∀ g x, j (r g x) = ρ g (j x))
    (hiso : ∀ g x y, ⟪j (r g x), j (r g y)⟫_ℂ = ⟪j x, j y⟫_ℂ) (heq : ∀ g x, Θ (j (r g x)) = gE g (Θ (j x)))
    (hu : ∀ (g : G) (x y : E), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ) (a : MonoidAlgebra K G) (e : E) :
    opV σ ρ a (LinearMap.adjoint Θ e) = LinearMap.adjoint Θ (opV σ (fun g => gE g) a e) := by
  simp only [opV, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [rho_adj hsp hjr hiso heq hu]

end Gen

section Gen2

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]
  {σ : K →+* ℂ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

structure Hyp (σ : K →+* ℂ) (j : F →ₛₗ[σ] V) (r : Representation K G F) (ρ : G → V →ₗ[ℂ] V)
    (gE : Representation ℂ G E) (Θ : V →ₗ[ℂ] E) : Prop where
  sp : Submodule.span ℂ (Set.range j) = ⊤
  jr : ∀ g x, j (r g x) = ρ g (j x)
  iso : ∀ g x y, ⟪j (r g x), j (r g y)⟫_ℂ = ⟪j x, j y⟫_ℂ
  eq : ∀ g x, Θ (j (r g x)) = gE g (Θ (j x))
  u : ∀ (g : G) (x y : E), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

variable {j : F →ₛₗ[σ] V} {r : Representation K G F} {ρ : G → V →ₗ[ℂ] V} {gE : Representation ℂ G E}
  {Θ : V →ₗ[ℂ] E}

namespace Hyp

variable (H : Hyp σ j r ρ gE Θ)
include H

theorem mem_R (a : MonoidAlgebra K G) {u : V} (hu : u ∈ LinearMap.range (LinearMap.adjoint Θ)) :
    opV σ ρ a u ∈ LinearMap.range (LinearMap.adjoint Θ) := by
  obtain ⟨e, rfl⟩ := LinearMap.mem_range.mp hu
  exact LinearMap.mem_range.mpr ⟨_, (opV_adj H.sp H.jr H.iso H.eq H.u a e).symm⟩

theorem ker (a : MonoidAlgebra K G) (u : V) (hu : Θ u = 0) : Θ (opV σ ρ a u) = 0 := by
  rw [theta_opV H.sp H.jr H.eq, hu, map_zero]

theorem range_opV (e : MonoidAlgebra K G) :
    LinearMap.range (opV σ ρ e) = Submodule.span ℂ (j '' (LinearMap.range (opF r e) : Set F)) := by
  rw [LinearMap.range_eq_map, ← H.sp, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨opF r e x, LinearMap.mem_range_self _ x, j_opF H.jr e x⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨j x, ⟨x, rfl⟩, (j_opF H.jr e x).symm⟩

theorem fix_of_idem (e : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e) {u : V}
    (hu : u ∈ LinearMap.range (opV σ ρ e)) : opV σ ρ e u = u := by
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hu
  exact LinearMap.congr_fun (opV_idem H.sp H.jr e he) w

theorem ratLev (hRZ : Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) =
      LinearMap.range (LinearMap.adjoint Θ))
    (e : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e) :
    Submodule.span ℂ (j '' ((((LinearMap.range (LinearMap.adjoint Θ)).comap j) ⊓ LinearMap.range (opF r e) :
        Submodule K F) : Set F)) = LinearMap.range (LinearMap.adjoint Θ) ⊓ LinearMap.range (opV σ ρ e) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxR, hxe⟩, rfl⟩
    refine ⟨hxR, ?_⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxe
    exact LinearMap.mem_range.mpr ⟨j y, (j_opF H.jr e y).symm⟩
  · rintro v ⟨hvR, hve⟩
    have hfix := H.fix_of_idem e he hve
    rw [← hfix]
    have hv' : v ∈ Submodule.span ℂ (j '' ((LinearMap.range (LinearMap.adjoint Θ)).comap j : Set F)) := by
      rw [hRZ]; exact hvR
    have hmap := Submodule.mem_map_of_mem (f := opV σ ρ e) hv'
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨opF r e z, ⟨?_, LinearMap.mem_range_self _ z⟩, j_opF H.jr e z⟩
    show j (opF r e z) ∈ LinearMap.range (LinearMap.adjoint Θ)
    rw [j_opF H.jr e z]
    exact H.mem_R e (u := j z) hz

theorem dn (e : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e) {u : V}
    (hu : u ∈ LinearMap.range (opV σ ρ e)) :
    ∃ u' ∈ LinearMap.range (LinearMap.adjoint Θ) ⊓ LinearMap.range (opV σ ρ e), Θ u' = Θ u := by
  have hdec : ∃ p ∈ LinearMap.range (LinearMap.adjoint Θ),
      ∃ k ∈ (LinearMap.range (LinearMap.adjoint Θ))ᗮ, u = p + k := by
    first
    | exact Submodule.exists_add_mem_mem_orthogonal _ u
    | exact ⟨_, Submodule.coe_mem ((LinearMap.range (LinearMap.adjoint Θ)).orthogonalProjection u), _,
        Submodule.sub_orthogonalProjection_mem_orthogonal u, by abel⟩
    | exact ⟨_, Submodule.starProjection_apply_mem _ u, _,
        Submodule.sub_starProjection_mem_orthogonal u, by abel⟩
    | exact ⟨_, Submodule.coe_mem (orthogonalProjection (LinearMap.range (LinearMap.adjoint Θ)) u), _,
        sub_orthogonalProjection_mem_orthogonal u, by abel⟩
    | (have hu' : u ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
       rw [← Submodule.sup_orthogonal_of_hasOrthogonalProjection (K := LinearMap.range (LinearMap.adjoint Θ)),
         Submodule.mem_sup] at hu'
       obtain ⟨p, hp, k, hk, hpk⟩ := hu'
       exact ⟨p, hp, k, hk, hpk.symm⟩)
    | (have hu' : u ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
       rw [← (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
         (K := LinearMap.range (LinearMap.adjoint Θ))).sup_eq_top, Submodule.mem_sup] at hu'
       obtain ⟨p, hp, k, hk, hpk⟩ := hu'
       exact ⟨p, hp, k, hk, hpk.symm⟩)
  obtain ⟨p, hp, k, hk, rfl⟩ := hdec
  have hk0 : Θ k = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ), ← LinearMap.adjoint_inner_right]
    first
    | exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ _) hk
    | exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self _ _) hk
    | (rw [inner_eq_zero_symm]
       exact (Submodule.mem_orthogonal _ _).mp hk _ (LinearMap.mem_range_self _ _))
    | exact (Submodule.mem_orthogonal _ _).mp hk _ (LinearMap.mem_range_self _ _)
  have hfix := H.fix_of_idem e he hu
  refine ⟨opV σ ρ e p, ⟨H.mem_R e hp, LinearMap.mem_range_self _ _⟩, ?_⟩
  have h1 : Θ (opV σ ρ e k) = 0 := H.ker e k hk0
  calc Θ (opV σ ρ e p) = Θ (opV σ ρ e (p + k)) := by rw [map_add, map_add, h1, add_zero]
    _ = Θ (p + k) := by rw [hfix]

theorem type (h : G) (c : K) (S : Set F) (hS : ∀ x ∈ S, r h x = c • x) {u : V}
    (hu : u ∈ Submodule.span ℂ (j '' S)) : gE h (Θ u) = σ c • Θ u := by
  have key : Set.EqOn ⇑(gE h ∘ₗ Θ) ⇑((σ c) • Θ : V →ₗ[ℂ] E) (j '' S) := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [← H.eq, hS x hx, LinearMap.map_smulₛₗ, map_smul]
  exact LinearMap.eqOn_span' key hu

theorem fixE (e : MonoidAlgebra K G) (he : opF r e ∘ₗ opF r e = opF r e) {w : V}
    (hw : w ∈ LinearMap.range (opV σ ρ e)) : opV σ (fun g => gE g) e (Θ w) = Θ w := by
  rw [← theta_opV H.sp H.jr H.eq, H.fix_of_idem e he hw]

theorem up [CharZero K] (Xc : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (v : E)
    (hi : opV σ (fun g => gE g) (idemOf Xc) v = v) (hl : ∀ h : P, gE (h : G) v = σ ((ψ h : Kˣ) : K) • v) :
    LinearMap.adjoint Θ v ∈ LinearMap.range (opV σ ρ (idemOf Xc * lvlIdem P ψ)) := by
  have hl' := opV_lvlIdem σ (fun g => gE g) P ψ v hl
  refine LinearMap.mem_range.mpr ⟨LinearMap.adjoint Θ v, ?_⟩
  rw [opV_mul H.sp H.jr, LinearMap.comp_apply, opV_adj H.sp H.jr H.iso H.eq H.u, hl',
    opV_adj H.sp H.jr H.iso H.eq H.u, hi]

theorem range_le (Xc : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) :
    LinearMap.range (opV σ ρ (idemOf Xc * lvlIdem P ψ)) ≤ LinearMap.range (opV σ ρ (idemOf Xc)) := by
  rw [opV_mul H.sp H.jr]
  first
  | exact LinearMap.range_comp_le_range _ _
  | (rw [LinearMap.range_comp]; exact LinearMap.map_le_range)

end Hyp

end Gen2

section Alg

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G] {F : Type} [AddCommGroup F] [Module K F]

theorem goodAt_idem (Xc : Finset (G → K)) (hX : ∀ χ ∈ Xc, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) :
    goodAt Xc P ψ * goodAt Xc P ψ = goodAt Xc P ψ := by
  show (idemOf Xc * lvlIdem P ψ) * (idemOf Xc * lvlIdem P ψ) = idemOf Xc * lvlIdem P ψ
  rw [mul_assoc, ← mul_assoc (lvlIdem P ψ), idemOf_central Xc hX (lvlIdem P ψ), mul_assoc, lvlIdem_idem,
    ← mul_assoc, idemOf_mul_self Xc hX]

theorem opF_goodAt_idem (r : Representation K G F) (Xc : Finset (G → K)) (hX : ∀ χ ∈ Xc, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* Kˣ) : opF r (goodAt Xc P ψ) ∘ₗ opF r (goodAt Xc P ψ) = opF r (goodAt Xc P ψ) := by
  rw [← opF_mul, goodAt_idem Xc hX P ψ]

theorem opF_goodAt_type (r : Representation K G F) (Xc : Finset (G → K)) (hX : ∀ χ ∈ Xc, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* Kˣ) (h : P) (x : F) (hx : x ∈ LinearMap.range (opF r (goodAt Xc P ψ))) :
    r (h : G) x = ((ψ h : Kˣ) : K) • x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  have key : MonoidAlgebra.single (h : G) (1 : K) * goodAt Xc P ψ = ((ψ h : Kˣ) : K) • goodAt Xc P ψ := by
    show MonoidAlgebra.single (h : G) (1 : K) * (idemOf Xc * lvlIdem P ψ) =
      ((ψ h : Kˣ) : K) • (idemOf Xc * lvlIdem P ψ)
    rw [← mul_assoc, idemOf_central Xc hX, mul_assoc, single_mul_lvlIdem, mul_smul_comm]
  have hy := LinearMap.congr_fun (congrArg (opF r) key) y
  rw [opF_mul, opF_smul, opF_single] at hy
  exact hy

theorem goodAt_bot (Xc : Finset (G → K)) (ψ : (⊥ : Subgroup G) →* Kˣ) : goodAt Xc (⊥ : Subgroup G) ψ = idemOf Xc := by
  show idemOf Xc * lvlIdem (⊥ : Subgroup G) ψ = idemOf Xc
  have hc : Nat.card (⊥ : Subgroup G) = 1 := by
    first
    | exact Subgroup.card_bot
    | simp
  have h1 : lvlIdem (⊥ : Subgroup G) ψ = 1 := by
    unfold lvlIdem
    rw [Finset.sum_eq_single (1 : (⊥ : Subgroup G))]
    · rw [hc, MonoidAlgebra.one_def]
      simp
    · intro b _ hb
      exact absurd (Subsingleton.elim b 1) hb
    · intro h
      exfalso
      apply h
      first
      | convert Finset.mem_univ (1 : (⊥ : Subgroup G))
      | simp
  rw [h1, mul_one]

end Alg

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  (B : BlockDat K G Pl0)

theorem actMat_coord' (g : G) (w : Fin B.S.dim → K) :
    (B.S.actMat B.r g).mulVec w = B.S.basis.equivFun (B.r g (B.S.basis.equivFun.symm w)) := by
  have hw : w = ⇑(B.S.basis.repr (B.S.basis.equivFun.symm w)) :=
    (B.S.basis.equivFun.apply_symm_apply w).symm
  conv_lhs => rw [hw]
  first
  | exact LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm w)
  | exact LinearMap.toMatrix_mulVec_repr (B.r g) (B.S.basis.equivFun.symm w)
  | exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem gaMat_mulVec (a : MonoidAlgebra K G) (w : Fin B.S.dim → K) :
    (B.S.gaMat B.r a).mulVec w = B.S.basis.equivFun (opF B.r a (B.S.basis.equivFun.symm w)) := by
  refine MonoidAlgebra.induction_linear a ?_ ?_ ?_
  · simp [CSD.gaMat_eq_lift, opF_eq_lift]
  · intro a b ha hb
    simp only [CSD.gaMat_eq_lift, opF_eq_lift, map_add, Matrix.add_mulVec, LinearMap.add_apply] at ha hb ⊢
    rw [ha, hb]
  · intro g c
    first
    | (simp only [CSD.gaMat_eq_lift, opF_eq_lift, MonoidAlgebra.lift_single, Matrix.smul_mulVec_assoc,
        LinearMap.smul_apply, map_smul]
       rw [← actMat_coord' B g w]
       rfl)
    | (simp only [CSD.gaMat_eq_lift, opF_eq_lift, MonoidAlgebra.lift_single, Matrix.smul_mulVec,
        LinearMap.smul_apply, map_smul]
       rw [← actMat_coord' B g w]
       rfl)

theorem goodR_eq (ℓ : Lvl K G) :
    BlockGood.goodR B ℓ = LinearMap.range (opF B.r (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext f
  constructor
  · rintro ⟨w, rfl⟩
    have hw : (B.vE ℓ).mulVecLin w ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
      rw [← hV]; exact ⟨w, rfl⟩
    obtain ⟨w', hw'⟩ := hw
    refine ⟨B.S.basis.equivFun.symm w', ?_⟩
    apply B.S.basis.equivFun.injective
    rw [← gaMat_mulVec]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simpa only [Matrix.mulVecLin_apply] using hw'
  · rintro ⟨f', rfl⟩
    have hw : (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin (B.S.basis.equivFun f') ∈
        LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]; exact ⟨_, rfl⟩
    obtain ⟨w, hw⟩ := hw
    refine ⟨w, ?_⟩
    apply B.S.basis.equivFun.injective
    have h1 := gaMat_mulVec B (goodAt ℓ.X ℓ.P ℓ.ψ) (B.S.basis.equivFun f')
    rw [LinearEquiv.symm_apply_apply] at h1
    rw [← h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simpa only [Matrix.mulVecLin_apply] using hw

theorem range_toF (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ BlockGood.goodR B ℓ := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    exact ⟨BlockGood.toF_mem B ℓ Z y, BlockGood.toF_mem_goodR B ℓ Z y⟩
  · rintro f ⟨hfZ, w, rfl⟩
    have hw : w ∈ B.Z0 ℓ Z := by
      show (B.vE ℓ).mulVecLin w ∈ B.coord Z
      refine ⟨_, hfZ, ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← (subspace_image_spec K _ (B.Z0 ℓ Z)).2] at hw
    obtain ⟨y, hy⟩ := hw
    have hy' : (B.zE ℓ Z).mulVec y = w := hy
    refine ⟨y, ?_⟩
    show B.S.basis.equivFun.symm ((B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y)) = _
    rw [hy']
    rfl

end Block

end LevelOperators

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnitL (gW : ∀ j, Representation ℂ G (X.W j)) : Prop :=
  ∀ j (g : G) (x y : X.W j), ⟪gW j g x, gW j g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquivL (gW : ∀ j, Representation ℂ G (X.W j)) : Prop :=
  ∀ j t (g : G) (x : A.fam.amb.FL j t),
    X.θ' j t (X.jL j t (A.fam.amb.opL j t (Sum.inr g) x)) = gW j g (X.θ' j t (X.jL j t x))

def typeSpW (j : A.fam.base.J) (gW : Representation ℂ G (X.W j)) (P : Subgroup G) (ψ : P →* Kˣ) :
    Submodule ℂ (X.W j) :=
  ⨅ h : P, LinearMap.ker (gW (h : G) - (A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)} {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def WgL (j : A.fam.base.J) : Submodule ℂ (X.W j) :=
  ⨆ t, LinearMap.range (X.tC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)

def LevTypeL (gW : ∀ j, Representation ℂ G (X.W j)) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ j, LinearMap.range (X.w0C b j) =
    WgL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j ⊓ typeSpW A X j (gW j) P ψ⁻¹

def KernelStableUnderHecke : Prop :=
  ∀ t (p : (A.fam.R t).Pl × ℕ) (u : X.FC t), X.Θ t u = 0 → X.Θ t (X.opC t (Sum.inl p) u) = 0

def KerStabLH : Prop :=
  ∀ j t (p : (A.fam.L j t).Pl × ℕ) (u : X.FLC j t), X.θ' j t u = 0 → X.θ' j t (X.opLC j t (Sum.inl p) u) = 0

end Defs

section Conc

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m} {X : CxData A.fam.amb}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)} {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

open LevelOperators

theorem spR (hK : X.KFormR) (t : A.fam.base.Tup) : Submodule.span ℂ (Set.range (X.jR t)) = ⊤ := by
  apply eq_top_iff.mpr
  rw [← (hK t).2]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem spL (hK : X.KFormL) (j : A.fam.base.J) (t : A.fam.base.Tup) :
    Submodule.span ℂ (Set.range (X.jL j t)) = ⊤ := by
  apply eq_top_iff.mpr
  first
  | rw [← (hK j t).2]
  | rw [← (hK t j).2]
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem hypR {s : ℕ} (hok : A.fam.Ok s) (hK : X.KFormR) (cv : CrdV A.fam.amb)
    (hcv : ∀ t (x y : A.fam.amb.FR t), cv.hR t x y = CSDForm.csumForm (A.fam.R t).S x y)
    (hJ : X.JIsoR cv) {gE : Representation ℂ G X.EE} (hU : GUnit A X gE) (hG : GEquiv A X gE)
    (t : A.fam.base.Tup) :
    Hyp A.fam.base.v0.embedding (X.jR t) (A.fam.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t) where
  sp := spR hK t
  jr g x := X.jR_opR hK t (Sum.inr g) x
  iso g x y := by
    rw [hJ t, hJ t, hcv, hcv, CSDForm.csumForm_apply, CSDForm.csumForm_apply, (hok.what₂ t).act.unitary]
  eq g x := hG t g x
  u := hU

theorem hypL {s : ℕ} (hok : A.fam.Ok s) (hK : X.KFormL) (cv : CrdV A.fam.amb)
    (hcv : ∀ j t (x y : A.fam.amb.FL j t), cv.hL j t x y = CSDForm.csumForm (A.fam.L j t).S x y)
    (hJ : X.JIsoL cv) {gW : ∀ j, Representation ℂ G (X.W j)} (hU : GUnitL A X gW) (hG : GEquivL A X gW)
    (j : A.fam.base.J) (t : A.fam.base.Tup) :
    Hyp A.fam.base.v0.embedding (X.jL j t) (A.fam.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j) (X.θ' j t) where
  sp := spL hK j t
  jr g x := X.jL_opL hK j t (Sum.inr g) x
  iso g x y := by
    rw [hJ j t, hJ j t, hcv, hcv, CSDForm.csumForm_apply, CSDForm.csumForm_apply, (hok.lifts j t).act.unitary]
  eq g x := hG j t g x
  u := hU j

theorem good_part_complex_eq_range {t : A.fam.base.Tup} {ρ : G → X.FC t →ₗ[ℂ] X.FC t} {gE : Representation ℂ G X.EE}
    (H : Hyp A.fam.base.v0.embedding (X.jR t) (A.fam.R t).r ρ gE (X.Θ t)) {cv : CrdV A.fam.amb} {b : Bool}
    {ℓ : Lvl K G} (hv : cv.v0R X.zs b t = BlockGood.goodR (A.fam.R t) ℓ) :
    X.V0C cv b t = LinearMap.range (opV A.fam.base.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have h1 : X.V0C cv b t = Submodule.span ℂ ((X.jR t) '' (cv.v0R X.zs b t : Set (A.fam.amb.FR t))) := rfl
  rw [h1, hv, goodR_eq (A.fam.R t) ℓ, ← H.range_opV]

theorem ratLev_at {t : A.fam.base.Tup} {ρ : G → X.FC t →ₗ[ℂ] X.FC t} {gE : Representation ℂ G X.EE}
    (H : Hyp A.fam.base.v0.embedding (X.jR t) (A.fam.R t).r ρ gE (X.Θ t)) (hRZ : X.RatZ) {cv : CrdV A.fam.amb}
    {b : Bool} (ℓ : Lvl K G) (hℓ : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (hv : cv.v0R X.zs b t = BlockGood.goodR (A.fam.R t) ℓ) :
    Submodule.span ℂ (Set.range fun x : Fin ((A.fam.R t).dZ ℓ (X.Z t)) → K => X.jR t ((A.fam.R t).toF ℓ (X.Z t) x)) =
      LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓ X.V0C cv b t := by
  have he := opF_goodAt_idem (A.fam.R t).r ℓ.X hℓ ℓ.P ℓ.ψ
  have key : Submodule.span ℂ ((X.jR t) '' ((X.Z t ⊓ LinearMap.range (opF (A.fam.R t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) :
      Submodule K _) : Set _)) =
      LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓
        LinearMap.range (opV A.fam.base.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) :=
    H.ratLev (hRZ.1 t) (goodAt ℓ.X ℓ.P ℓ.ψ) he
  rw [good_part_complex_eq_range H hv, ← key, ← goodR_eq (A.fam.R t) ℓ, ← range_toF (A.fam.R t) ℓ (X.Z t)]
  first
  | (rw [LinearMap.range_coe, ← Set.range_comp]; rfl)
  | (congr 1; rw [LinearMap.range_coe, ← Set.range_comp]; rfl)
  | (congr 1; ext y; simp)

theorem dn_at {s : ℕ} (hok : A.fam.Ok s) {gE : Representation ℂ G X.EE}
    (Hs : ∀ t, Hyp A.fam.base.v0.embedding (X.jR t) (A.fam.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t))
    (hRZ : X.RatZ) (hG2 : PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc))
    {cv : CrdV A.fam.amb} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ t, cv.v0R X.zs b t = BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hE : X.EEl b = EEg A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp A X gE P ψ) :
    X.DnLev cv b := by
  intro t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jR t '' (BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ) : Set _)) := by
    have := hu
    unfold CxData.V0C at this
    rwa [hv t] at this
  rw [good_part_complex_eq_range (Hs t) (hv t)] at hu
  rw [hE]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opC t (Sum.inr g))
          (goodAt (A.fam.lvl P ψ).X (A.fam.lvl P ψ).P (A.fam.lvl P ψ).ψ)) ≤
        LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opC t (Sum.inr g))
          (goodAt (A.fam.lvl ⊥ 1).X (A.fam.lvl ⊥ 1).P (A.fam.lvl ⊥ 1).ψ)) := by
      have e1 : goodAt (A.fam.lvl ⊥ 1).X (A.fam.lvl ⊥ 1).P (A.fam.lvl ⊥ 1).ψ = idemOf A.fam.X := goodAt_bot A.fam.X _
      rw [e1]
      exact (Hs t).range_le A.fam.X P ψ
    obtain ⟨u', hu', hΘ⟩ := (Hs t).dn _ (opF_goodAt_idem _ (A.fam.lvl ⊥ 1).X hok.irr _ _) (hle hu)
    rw [← (Hs t).ratLev (hRZ.1 t) _ (opF_goodAt_idem _ (A.fam.lvl ⊥ 1).X hok.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.Θ t))).comap (X.jR t) ⊓
          LinearMap.range (opF (A.fam.R t).r (goodAt (A.fam.lvl ⊥ 1).X (A.fam.lvl ⊥ 1).P (A.fam.lvl ⊥ 1).ψ))) =
        LinearMap.range ((A.fam.R t).toF (A.fam.lvl ⊥ 1) (X.Z t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jR t '' (LinearMap.range ((A.fam.R t).toF (A.fam.lvl ⊥ 1) (X.Z t)) : Set _)) ≤
        LinearMap.range (lin (X.uQ (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A.fam.base.v0.embedding x, X.lin_uQ_cpt (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t x⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.Θ t u ∈ LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)
    rw [← (hG2.2 t).2, ← hΘ, ← hc, ← X.iC_eq_comp]
    exact ⟨c, rfl⟩
  · show X.Θ t u ∈ typeSp A X gE P ψ
    unfold typeSp
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs t).type (h : G) ((ψ h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.irr P ψ h x hx

theorem up_at {s : ℕ} (hok : A.fam.Ok s) {gE : Representation ℂ G X.EE}
    (Hs : ∀ t, Hyp A.fam.base.v0.embedding (X.jR t) (A.fam.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t))
    {cv : CrdV A.fam.amb} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ t, cv.v0R X.zs b t = BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hE : X.EEl b = EEg A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp A X gE P ψ) :
    X.UpLev cv b := by
  intro t
  rintro _ ⟨e, he, rfl⟩
  rw [hE] at he
  obtain ⟨⟨c, rfl⟩, hty⟩ := he
  rw [good_part_complex_eq_range (Hs t) (hv t)]
  refine (Hs t).up A.fam.X P ψ _ ?_ ?_
  · rw [X.iC_eq_comp]
    have hw : lin (X.uQ (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) c ∈
        LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opC A.fam.base.μ0 (Sum.inr g))
          (goodAt (A.fam.lvl ⊥ 1).X (A.fam.lvl ⊥ 1).P (A.fam.lvl ⊥ 1).ψ)) := by
      rw [(Hs A.fam.base.μ0).range_opV, ← goodR_eq]
      refine CxData.lin_mem (fun k => ?_) c
      exact Submodule.subset_span ⟨_, BlockGood.toF_mem_goodR (A.fam.R A.fam.base.μ0)
        (A.fam.lvl ⊥ 1) (X.zs.Z A.fam.base.μ0) _, rfl⟩
    have h3 := (Hs A.fam.base.μ0).fixE _ (opF_goodAt_idem _ (A.fam.lvl ⊥ 1).X hok.irr _ _) hw
    rwa [show goodAt (A.fam.lvl ⊥ 1).X (A.fam.lvl ⊥ 1).P (A.fam.lvl ⊥ 1).ψ = idemOf A.fam.X from
      goodAt_bot A.fam.X _] at h3
  · intro h
    have h3 := (Submodule.mem_iInf _).1 hty h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3

end Conc

section ConcL

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m} {X : CxData A.fam.amb}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)} {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

open LevelOperators

theorem lift_good_part_complex_eq_range {j : A.fam.base.J} {t : A.fam.base.Tup} {ρ : G → X.FLC j t →ₗ[ℂ] X.FLC j t}
    {gW : Representation ℂ G (X.W j)}
    (H : Hyp A.fam.base.v0.embedding (X.jL j t) (A.fam.L j t).r ρ gW (X.θ' j t)) {cv : CrdV A.fam.amb} {b : Bool}
    {ℓ : Lvl K G} (hv : cv.v0L X.zs b j t = BlockGood.goodR (A.fam.L j t) ℓ) :
    X.goodPartComplexPoints cv b j t = LinearMap.range (opV A.fam.base.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have h1 : X.goodPartComplexPoints cv b j t =
      Submodule.span ℂ ((X.jL j t) '' (cv.v0L X.zs b j t : Set (A.fam.amb.FL j t))) := rfl
  rw [h1, hv, goodR_eq (A.fam.L j t) ℓ, ← H.range_opV]

theorem ratLevL_at {j : A.fam.base.J} {t : A.fam.base.Tup} {ρ : G → X.FLC j t →ₗ[ℂ] X.FLC j t}
    {gW : Representation ℂ G (X.W j)}
    (H : Hyp A.fam.base.v0.embedding (X.jL j t) (A.fam.L j t).r ρ gW (X.θ' j t)) (hRZ : X.RatZ)
    {cv : CrdV A.fam.amb} {b : Bool} (ℓ : Lvl K G) (hℓ : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)
    (hv : cv.v0L X.zs b j t = BlockGood.goodR (A.fam.L j t) ℓ) :
    Submodule.span ℂ (Set.range fun x : Fin ((A.fam.L j t).dZ ℓ (X.Zl j t)) → K =>
        X.jL j t ((A.fam.L j t).toF ℓ (X.Zl j t) x)) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓ X.goodPartComplexPoints cv b j t := by
  have he := opF_goodAt_idem (A.fam.L j t).r ℓ.X hℓ ℓ.P ℓ.ψ
  have key : Submodule.span ℂ ((X.jL j t) '' ((X.Zl j t ⊓ LinearMap.range (opF (A.fam.L j t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) :
      Submodule K _) : Set _)) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓
        LinearMap.range (opV A.fam.base.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) :=
    H.ratLev (hRZ.2 j t) (goodAt ℓ.X ℓ.P ℓ.ψ) he
  rw [lift_good_part_complex_eq_range H hv, ← key, ← goodR_eq (A.fam.L j t) ℓ, ← range_toF (A.fam.L j t) ℓ (X.Zl j t)]
  first
  | (rw [LinearMap.range_coe, ← Set.range_comp]; rfl)
  | (congr 1; rw [LinearMap.range_coe, ← Set.range_comp]; rfl)
  | (congr 1; ext y; simp)

theorem dnL_at {s : ℕ} (hok : A.fam.Ok s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A.fam.base.v0.embedding (X.jL j t) (A.fam.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : X.RatZ) {cv : CrdV A.fam.amb} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P ψ))
    (hE : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jL j t '' (BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P ψ) : Set _)) := by
    have := hu
    unfold CxData.goodPartComplexPoints at this
    rwa [hv j t] at this
  rw [lift_good_part_complex_eq_range (Hs j t) (hv j t)] at hu
  rw [hE j]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A.fam.lvlA P ψ).X (A.fam.lvlA P ψ).P (A.fam.lvlA P ψ).ψ)) ≤
        LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A.fam.lvlA ⊥ 1).X (A.fam.lvlA ⊥ 1).P (A.fam.lvlA ⊥ 1).ψ)) := by
      have e1 : goodAt (A.fam.lvlA ⊥ 1).X (A.fam.lvlA ⊥ 1).P (A.fam.lvlA ⊥ 1).ψ = idemOf A.fam.X :=
        goodAt_bot A.fam.X _
      rw [e1]
      exact (Hs j t).range_le A.fam.X P ψ⁻¹
    obtain ⟨u', hu', hΘ⟩ := (Hs j t).dn _ (opF_goodAt_idem _ (A.fam.lvlA ⊥ 1).X hok.irr _ _) (hle hu)
    rw [← (Hs j t).ratLev (hRZ.2 j t) _ (opF_goodAt_idem _ (A.fam.lvlA ⊥ 1).X hok.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
          LinearMap.range (opF (A.fam.L j t).r (goodAt (A.fam.lvlA ⊥ 1).X (A.fam.lvlA ⊥ 1).P (A.fam.lvlA ⊥ 1).ψ))) =
        LinearMap.range ((A.fam.L j t).toF (A.fam.lvlA ⊥ 1) (X.Zl j t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jL j t '' (LinearMap.range ((A.fam.L j t).toF (A.fam.lvlA ⊥ 1) (X.Zl j t)) :
          Set _)) ≤ LinearMap.range (lin (X.uL (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A.fam.base.v0.embedding x, (X.jL_toL (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.θ' j t u ∈ WgL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j
    refine Submodule.mem_iSup_of_mem t ?_
    rw [← hΘ, ← hc, ← X.tC_eq]
    exact ⟨c, rfl⟩
  · show X.θ' j t u ∈ typeSpW A X j (gW j) P ψ⁻¹
    unfold typeSpW
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs j t).type (h : G) (((ψ⁻¹) h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.irr P ψ⁻¹ h x hx

theorem upL_at {s : ℕ} (hok : A.fam.Ok s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A.fam.base.v0.embedding (X.jL j t) (A.fam.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    {cv : CrdV A.fam.amb} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A.fam.L j t) (A.fam.lvlA P ψ))
    (hE : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.UpLevL cv b := by
  intro j t
  rintro _ ⟨w, hw, rfl⟩
  rw [hE j] at hw
  obtain ⟨hwg, hty⟩ := hw
  rw [lift_good_part_complex_eq_range (Hs j t) (hv j t)]
  refine (Hs j t).up A.fam.X P ψ⁻¹ _ ?_ ?_
  · have hle : WgL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j ≤
        LinearMap.ker (opV A.fam.base.v0.embedding (fun g => gW j g) (idemOf A.fam.X) - LinearMap.id) := by
      refine iSup_le fun t' => ?_
      rintro _ ⟨c, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, X.tC_eq]
      have hw' : lin (X.uL (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t') c ∈
          LinearMap.range (opV A.fam.base.v0.embedding (fun g => X.opLC j t' (Sum.inr g))
            (goodAt (A.fam.lvlA ⊥ 1).X (A.fam.lvlA ⊥ 1).P (A.fam.lvlA ⊥ 1).ψ)) := by
        rw [(Hs j t').range_opV, ← goodR_eq]
        refine CxData.lin_mem (fun k => ?_) c
        exact Submodule.subset_span ⟨_, BlockGood.toF_mem_goodR (A.fam.L j t')
          (A.fam.lvlA ⊥ 1) (X.zs.Zl j t') _, rfl⟩
      have h3 := (Hs j t').fixE _ (opF_goodAt_idem _ (A.fam.lvlA ⊥ 1).X hok.irr _ _) hw'
      rwa [show goodAt (A.fam.lvlA ⊥ 1).X (A.fam.lvlA ⊥ 1).P (A.fam.lvlA ⊥ 1).ψ = idemOf A.fam.X from
        goodAt_bot A.fam.X _] at h3
    have h4 := hle hwg
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h4
    exact h4
  · intro h
    have h3 := (Submodule.mem_iInf _).1 hty h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h3
    exact h3

end ConcL

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m} {X : CxData A.fam.amb} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)} {Zsc : DefSub A.fam.amb → IndefScale A.fam.base} {s : ℕ}

open LevelOperators

theorem ratLev_of (hok : A.fam.Ok s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gE : Representation ℂ G X.EE} (hU : GUnit A X gE) (hG : GEquiv A X gE) (b : Bool) :
    X.RatLev (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro t
  have H := hypR hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ => rfl) hJ hU hG t
  cases b
  · exact ratLev_at H hRZ (A.fam.lvl P0 ψ0) hok.irr rfl
  · exact ratLev_at H hRZ (A.fam.lvl P1 ψ1) hok.irr rfl

theorem dnLev_of (hok : A.fam.Ok s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gE : Representation ℂ G X.EE} (hU : GUnit A X gE) (hG : GEquiv A X gE)
    (hG2 : PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc))
    (hL0 : LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0)
    (hL1 : LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1) (b : Bool) :
    X.DnLev (cvOf A P0 ψ0 P1 ψ1) b := by
  have Hs := fun t => hypR hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ => rfl) hJ hU hG t
  cases b
  · exact dn_at hok Hs hRZ hG2 P0 ψ0 (fun _ => rfl) hL0
  · exact dn_at hok Hs hRZ hG2 P1 ψ1 (fun _ => rfl) hL1

theorem upLev_of (hok : A.fam.Ok s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf A P0 ψ0 P1 ψ1))
    {gE : Representation ℂ G X.EE} (hU : GUnit A X gE) (hG : GEquiv A X gE)
    (hL0 : LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0)
    (hL1 : LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1) (b : Bool) :
    X.UpLev (cvOf A P0 ψ0 P1 ψ1) b := by
  have Hs := fun t => hypR hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ => rfl) hJ hU hG t
  cases b
  · exact up_at hok Hs P0 ψ0 (fun _ => rfl) hL0
  · exact up_at hok Hs P1 ψ1 (fun _ => rfl) hL1

theorem ratLevL_of (hok : A.fam.Ok s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : GUnitL A X gW) (hG : GEquivL A X gW) (b : Bool) :
    X.RatLevL (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf A P0 ψ0 P1 ψ1) b := by
  intro j t
  have H := hypL hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  cases b
  · exact ratLevL_at H hRZ (A.fam.lvlA P0 ψ0) hok.irr rfl
  · exact ratLevL_at H hRZ (A.fam.lvlA P1 ψ1) hok.irr rfl

theorem dnLevL_of (hok : A.fam.Ok s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : GUnitL A X gW) (hG : GEquivL A X gW)
    (hL0 : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0)
    (hL1 : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW true P1 ψ1) (b : Bool) :
    X.DnLevL (cvOf A P0 ψ0 P1 ψ1) b := by
  have Hs := fun j t => hypL hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  cases b
  · exact dnL_at hok Hs hRZ P0 ψ0 (fun _ _ => rfl) hL0
  · exact dnL_at hok Hs hRZ P1 ψ1 (fun _ _ => rfl) hL1

theorem upLevL_of (hok : A.fam.Ok s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf A P0 ψ0 P1 ψ1))
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : GUnitL A X gW) (hG : GEquivL A X gW)
    (hL0 : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0)
    (hL1 : LevTypeL A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW true P1 ψ1) (b : Bool) :
    X.UpLevL (cvOf A P0 ψ0 P1 ψ1) b := by
  have Hs := fun j t => hypL hok hK (cvOf A P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  cases b
  · exact upL_at hok Hs P0 ψ0 (fun _ _ => rfl) hL0
  · exact upL_at hok Hs P1 ψ1 (fun _ _ => rfl) hL1

theorem kerStabR_of (hK : X.KFormR) {gE : Representation ℂ G X.EE} (hG : GEquiv A X gE) (hH : KernelStableUnderHecke A X) :
    X.KerStabR := by
  intro t i u hu
  rcases i with p | g
  · exact hH t p u hu
  · have hsp : Submodule.span ℂ (Set.range (X.jR t)) = ⊤ := spR hK t
    have hcomm : X.Θ t ∘ₗ X.opC t (Sum.inr g) = gE g ∘ₗ X.Θ t := by
      apply LinearMap.ext_on_range hsp
      intro x
      simp only [LinearMap.comp_apply]
      rw [← X.jR_opR hK t (Sum.inr g) x, hG t g x]
    have h2 := LinearMap.congr_fun hcomm u
    simp only [LinearMap.comp_apply] at h2
    rw [h2, hu, map_zero]

theorem kerStabL_of (hK : X.KFormL) {gW : ∀ j, Representation ℂ G (X.W j)} (hG : GEquivL A X gW)
    (hH : KerStabLH A X) : X.KerStabL := by
  intro j t i u hu
  rcases i with p | g
  · exact hH j t p u hu
  · have hsp : Submodule.span ℂ (Set.range (X.jL j t)) = ⊤ := spL hK j t
    have hcomm : X.θ' j t ∘ₗ X.opLC j t (Sum.inr g) = gW j g ∘ₗ X.θ' j t := by
      apply LinearMap.ext_on_range hsp
      intro x
      simp only [LinearMap.comp_apply]
      rw [← X.jL_opL hK j t (Sum.inr g) x, hG j t g x]
    have h2 := LinearMap.congr_fun hcomm u
    simp only [LinearMap.comp_apply] at h2
    rw [h2, hu, map_zero]

end Final

end Formalism.IndefR.CxPass
