import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlobApprox

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csGlob_eq (g : GL n 𝒜) (Λ : Submodule (𝓞 E) (n → E)) :
    Formalism.UG.CS.globLat g Λ =
      adelstabLam F E g (latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) := rfl

theorem csGlob_lattice (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (g : GL n 𝒜) :
    Submodule.IsLattice E (Formalism.UG.CS.globLat g Λ) := by
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  obtain ⟨d, hd, c, hc, hcg, hcgi⟩ := levelaf_exists_denom (E := E) g
  have hG := adelstab_entries g d c hc hcg
  have hGi := adelstab_entries g⁻¹ d c hc hcgi
  have hf := adelstab_finite g _ c₂ d hc₂ hd h₂ hG
  have hs := adelstab_span g _ c₁ d hc₁ hd h₁ hGi
  rw [csGlob_eq]
  exact ⟨Module.Finite.iff_fg.mp hf, hs⟩

end Glob

section One

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

variable (F E) in

def csGlobN : Submodule (𝓞 F) E where
  carrier := {e | ι e ∈ 𝒮}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact zero_mem _
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E]
    exact mul_mem (adelstab_incl_int _) hx

theorem csGlob_N_fg : (csGlobN F E).FG := by
  classical
  set β := Module.finBasis F E
  obtain ⟨d₀, hd₀, -, hd₀i⟩ := sf_den (fun i => β i)
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  set W : Submodule (𝓞 F) E := Submodule.span (𝓞 F) (Set.range fun i => d₀⁻¹ * β' i)
  have hle : csGlobN F E ≤ W := by
    intro e he
    have h1 := adelstab_dual β d₀ hd₀i e (adelstab_tr_mem e he)
    let Lm : E →ₗ[𝓞 F] E := (LinearMap.mulLeft F d₀⁻¹).restrictScalars (𝓞 F)
    have h2 := Submodule.mem_map_of_mem (f := Lm) h1
    rw [Submodule.map_span] at h2
    have h3 : Lm (d₀ * e) = e := by
      simp only [Lm, LinearMap.coe_restrictScalars, LinearMap.mulLeft_apply]
      rw [← mul_assoc, inv_mul_cancel₀ hd₀, one_mul]
    rw [h3] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  have : Module.Finite (𝓞 F) W := Module.Finite.span_of_finite _ (Set.finite_range _)
  have : IsNoetherian (𝓞 F) W := inferInstance
  have : IsNoetherian (𝓞 F) (csGlobN F E) := isNoetherian_of_le hle
  exact Module.Finite.iff_fg.mp inferInstance

theorem csGlob_int (e : E) (he : ι e ∈ 𝒮) : IsIntegral ℤ e := by
  have hne : csGlobN F E ≠ ⊥ := by
    intro h
    have h1 : (1 : E) ∈ csGlobN F E := by
      show ι 1 ∈ 𝒮
      rw [map_one]; exact one_mem _
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hI : IsIntegral (𝓞 F) e := isIntegral_of_smul_mem_submodule (csGlobN F E) hne csGlob_N_fg e
    (fun m hm => by
      show ι (e * m) ∈ 𝒮
      rw [map_mul]; exact mul_mem he hm)
  exact isIntegral_trans (R := ℤ) (A := 𝓞 F) e hI

end One

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csGlob_tmul_int (x : E) (ρ : 𝓞 F) :
    x ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ = ι (algebraMap (𝓞 F) E ρ * x) := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F),
    IsScalarTower.algebraMap_apply (𝓞 F) F E,
    Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 F) F), ← TensorProduct.smul_tmul,
    ← Algebra.smul_def]
  rfl

theorem csGlob_approx (hA : Formalism.UG.CS.IntAdApprox) (D : 𝓞 F) (hD : D ≠ 0) (s : 𝒜)
    (hs : s ∈ 𝒮) : ∃ b : 𝓞 E, ∃ t ∈ 𝒮, s = ι (algebraMap (𝓞 E) E b) + levelafC E D * t := by
  classical
  obtain ⟨m, bb, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨r, hr, rfl⟩ := levelaf_decomp bb hb hs
  choose ρ y hy hρ using fun j => hA F D hD (r j) (hr j)
  refine ⟨∑ j, algebraMap (𝓞 F) (𝓞 E) (ρ j) * bb j, ∑ j, algebraMap (𝓞 E) E (bb j) ⊗ₜ[F] y j,
    sum_mem fun j _ => levelaf_tmul_mem _ (hy j), ?_⟩
  simp only [hρ, TensorProduct.tmul_add, Finset.sum_add_distrib, map_sum, Finset.mul_sum, levelafC,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [csGlob_tmul_int, map_mul (algebraMap (𝓞 E) E), ← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 E) E,
    map_mul]

end Approx

section OneMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

omit [NumberField F] [Algebra F E] in

theorem csGlob_single (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
  classical
  have hk : ∀ k : n, ∃ N : ℕ, ∃ f : Fin N → E, ∃ w : Fin N → Λ,
      ∑ j, f j • (w j : n → E) = Pi.single k 1 := by
    intro k
    have : (Pi.single k 1 : n → E) ∈ Submodule.span E (Λ : Set (n → E)) := by
      rw [hspan]; exact Submodule.mem_top
    obtain ⟨N, f, w, h⟩ := Submodule.mem_span_set'.1 this
    exact ⟨N, f, fun j => ⟨w j, (w j).2⟩, h⟩
  choose N f w hw using hk
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : Σ k : n, Fin (N k) => f p.1 p.2)
  refine ⟨m, hm0, fun k => ?_⟩
  have : (Pi.single k (m : E) : n → E) =
      ∑ j, (⟨(m : E) * f k j, hm ⟨k, j⟩⟩ : 𝓞 E) • (w k j : n → E) := by
    have h1 : (Pi.single k (m : E) : n → E) = (m : E) • (Pi.single k 1 : n → E) := by
      rw [← Pi.single_smul', smul_eq_mul, mul_one]
    rw [h1, ← hw k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul E, smul_smul]
    rfl
  rw [this]
  exact sum_mem fun j _ => Λ.smul_mem _ (w k j).2

theorem csGlob_one (hA : Formalism.UG.CS.IntAdApprox) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    Formalism.UG.CS.globLat (F := F) 1 Λ = Λ := by
  classical
  obtain ⟨m, hm0, hsingle⟩ := csGlob_single Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  set c₁ : 𝓞 F := (m : 𝓞 F)
  have hc₁ : c₁ ≠ 0 := Int.cast_ne_zero.2 hm0
  have hcE : algebraMap (𝓞 F) E c₁ = (m : E) := map_intCast _ _
  have key : ∀ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∃ y ∈ Λ, ∃ s : n → 𝒜,
      (∀ i, s i ∈ 𝒮) ∧ u = fun i => ι (y i) + levelafC E c₁ * s i := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, hx, rfl⟩ := hu
      exact ⟨x, hx, 0, fun _ => zero_mem _, by ext i; simp⟩
    | zero => exact ⟨0, zero_mem _, 0, fun _ => zero_mem _, by ext i; simp⟩
    | add u w _ _ hu hw =>
      obtain ⟨y, hy, s, hs, rfl⟩ := hu
      obtain ⟨y', hy', s', hs', rfl⟩ := hw
      refine ⟨y + y', add_mem hy hy', s + s', fun i => add_mem (hs i) (hs' i), ?_⟩
      ext i
      simp only [Pi.add_apply, map_add]
      ring
    | smul a u _ hu =>
      obtain ⟨y, hy, s, hs, rfl⟩ := hu
      obtain ⟨b, t, ht, hab⟩ := csGlob_approx (F := F) (E := E) hA (c₁ * c₂) (mul_ne_zero hc₁ hc₂) (a : 𝒜) a.2
      have hy2 : ∀ i, levelafC E c₂ * ι (y i) ∈ 𝒮 := h₂ _ (Submodule.subset_span ⟨y, hy, rfl⟩)
      refine ⟨b • y, Λ.smul_mem b hy, fun i => levelafC E c₂ * ι (y i) * t + (a : 𝒜) * s i,
        fun i => add_mem (mul_mem (hy2 i) ht) (mul_mem a.2 (hs i)), ?_⟩
      ext i
      simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
      rw [show algebraMap 𝒮 𝒜 a = (a : 𝒜) from rfl, hab, levelafC_mul]
      ring
  ext x
  constructor
  · intro hx
    have hx' : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
      have : ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
          latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hx
      rwa [inv_one, Units.val_one, one_mulVec] at this
    obtain ⟨y, hy, s, hs, he⟩ := key _ hx'
    have hmE : (m : E) ≠ 0 := Int.cast_ne_zero.2 hm0
    have hint : ∀ i, IsIntegral ℤ ((x i - y i) * (m : E)⁻¹) := by
      intro i
      apply csGlob_int (F := F)
      have hi := congrFun he i
      rw [map_mul, map_sub, hi, ← adelstab_incl_C, hcE, add_sub_cancel_left, mul_right_comm,
        ← map_mul, mul_inv_cancel₀ hmE, map_one, one_mul]
      exact hs i
    have hdiff : x - y = ∑ i, (⟨_, hint i⟩ : 𝓞 E) • (Pi.single i (m : E) : n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def]
        show (x - y) j = (x j - y j) * (m : E)⁻¹ * (m : E)
        rw [inv_mul_cancel_right₀ hmE, Pi.sub_apply]
      · intro k _ hkj
        rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hkj), smul_zero]
      · exact fun h => absurd (Finset.mem_univ j) h
    have hxy : x = y + (x - y) := by abel
    rw [hxy, hdiff]
    exact add_mem hy (sum_mem fun i _ => Λ.smul_mem _ (hsingle i))
  · intro hx
    show ((1⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ι (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ
    rw [inv_one, Units.val_one, one_mulVec]
    exact Submodule.subset_span ⟨x, hx, rfl⟩

end OneMain

theorem global_lattice_one_holds : Formalism.UG.CS.GlobLatOne := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan
  exact csGlob_one csGlob_intAdApprox Λ hfin hspan

theorem global_lattice_isLattice_holds : Formalism.UG.CS.GlobLatLattice := by
  intro F E _ _ _ _ _ n _ _ Λ hfin hspan g
  exact csGlob_lattice Λ hfin hspan g

end Formalism.UG.P
