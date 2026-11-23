import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n]

theorem csScale_hform_add_left (σ : A →+* A) (J : Matrix n n A) (x x' y : n → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem csScale_hform_add_right (σ : A →+* A) (J : Matrix n n A) (x y y' : n → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem csScale_hform_zero_left (σ : A →+* A) (J : Matrix n n A) (y : n → A) :
    hform σ J 0 y = 0 := by
  simp [hform]

theorem csScale_hform_zero_right (σ : A →+* A) (J : Matrix n n A) (x : n → A) :
    hform σ J x 0 = 0 := by
  simp [hform]

theorem csScale_hform_smul_left (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem csScale_hform_smul_right (σ : A →+* A) (J : Matrix n n A) (c : A) (x y : n → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem csScale_sigR_incl (σ : E →ₐ[F] E) (e : E) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (ιA e) = ιA ((σ : E →+* E) e) := by
  exact Algebra.TensorProduct.map_tmul σ (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) e 1

theorem csScale_sigma_int (σ : E →ₐ[F] E) (b : 𝓞 E) :
    IsIntegral ℤ ((σ : E →+* E) (algebraMap (𝓞 E) E b)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe b).map (σ : E →+* E).toIntAlgHom

theorem csScale_sigR_mem (σ : E →ₐ[F] E) {s : 𝒜} (hs : s ∈ 𝒮) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) s ∈ 𝒮 := by
  have key : 𝒮 ≤ Subring.comap (sigR σ (FiniteAdeleRing (𝓞 F) F)) 𝒮 := by
    apply Subring.closure_le.2
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨b, rfl⟩ := RingHom.mem_range.mp hx
      have h1 : sigR σ (FiniteAdeleRing (𝓞 F) F) (ιA (algebraMap (𝓞 E) E b)) =
          ιA (algebraMap (𝓞 E) E ⟨(σ : E →+* E) (algebraMap (𝓞 E) E b), csScale_sigma_int σ b⟩) :=
        csScale_sigR_incl σ _
      show sigR σ (FiniteAdeleRing (𝓞 F) F) (ιA (algebraMap (𝓞 E) E b)) ∈ 𝒮
      rw [h1]
      exact CS.incl_int _
    · have h2 : sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) = (1 : E) ⊗ₜ[F] y := by
        show Algebra.TensorProduct.map σ (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) ((1 : E) ⊗ₜ[F] y) = _
        rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
      show sigR σ (FiniteAdeleRing (𝓞 F) F) ((1 : E) ⊗ₜ[F] y) ∈ 𝒮
      rw [h2]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hs

theorem csScale_hform_incl (σ : E →ₐ[F] E) (J : Matrix n n E) (x y : n → E) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) (fun i => ιA (x i)) (fun i => ιA (y i)) =
      ιA (hform (σ : E →+* E) J x y) := by
  simp only [hform, map_sum, map_mul, Matrix.map_apply, csScale_sigR_incl]

theorem csScale_den (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y) := by
  classical
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  have hden : ∀ z : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * z) := by
    intro z
    have hq : IsAlgebraic ℚ z := (Algebra.IsIntegral.isIntegral (R := ℚ) z).isAlgebraic
    have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr hq
    obtain ⟨m, hm, hmi⟩ := hz.exists_integral_multiple
    exact ⟨m, hm, by rwa [zsmul_eq_mul] at hmi⟩
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp hfin
  choose f hf0 hfi using fun p : (n → E) × (n → E) => hden (hform (σ : E →+* E) J p.1 p.2)
  refine ⟨∏ p ∈ S ×ˢ S, f p, Finset.prod_ne_zero_iff.mpr fun p _ => hf0 p, ?_⟩
  have hgen : ∀ s ∈ S, ∀ t ∈ S,
      IsIntegral ℤ (((∏ p ∈ S ×ˢ S, f p : ℤ) : E) * hform (σ : E →+* E) J s t) := by
    intro s hs t ht
    have hp : (s, t) ∈ S ×ˢ S := Finset.mem_product.mpr ⟨hs, ht⟩
    rw [← Finset.mul_prod_erase _ _ hp, Int.cast_mul, mul_comm ((f (s, t) : ℤ) : E), mul_assoc]
    exact (hint _).mul (hfi (s, t))
  intro x hx y hy
  rw [← hS] at hx hy
  induction hx using Submodule.span_induction generalizing y with
  | mem s hs =>
    induction hy using Submodule.span_induction with
    | mem t ht => exact hgen s hs t ht
    | zero => rw [csScale_hform_zero_right, mul_zero]; exact isIntegral_zero
    | add u v _ _ hu hv => rw [csScale_hform_add_right, mul_add]; exact hu.add hv
    | smul a u _ hu =>
      rw [← algebraMap_smul E a u, csScale_hform_smul_right, mul_left_comm]
      exact (NumberField.RingOfIntegers.isIntegral_coe a).mul hu
  | zero => rw [csScale_hform_zero_left, mul_zero]; exact isIntegral_zero
  | add u v _ _ hu hv => rw [csScale_hform_add_left, mul_add]; exact (hu y hy).add (hv y hy)
  | smul a u _ hu =>
    rw [← algebraMap_smul E a u, csScale_hform_smul_left, mul_left_comm]
    exact (csScale_sigma_int σ a).mul (hu y hy)

theorem csScale_latS (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    {u w : n → 𝒜} (hu : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ)
    (hw : w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    ιA (m : E) * hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u w ∈ 𝒮 := by
  unfold latS at hu hw
  induction hu using Submodule.span_induction generalizing w with
  | mem u hu' =>
    obtain ⟨x, hx, rfl⟩ := hu'
    induction hw using Submodule.span_induction with
    | mem w hw' =>
      obtain ⟨y, hy, rfl⟩ := hw'
      show ιA (m : E) * hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA)
        (fun i => ιA (x i)) (fun i => ιA (y i)) ∈ 𝒮
      rw [csScale_hform_incl, ← map_mul]
      exact CS.incl_int ⟨_, hm x hx y hy⟩
    | zero => rw [csScale_hform_zero_right, mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [csScale_hform_add_right, mul_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [Subring.smul_def, csScale_hform_smul_right, mul_left_comm]
      exact mul_mem c.2 ha
  | zero => rw [csScale_hform_zero_left, mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [csScale_hform_add_left, mul_add]; exact add_mem (ha hw) (hb hw)
  | smul c a _ ha =>
    rw [Subring.smul_def, csScale_hform_smul_left, mul_left_comm]
    exact mul_mem (csScale_sigR_mem σ c.2) (ha hw)

private theorem hform_mulVec_mulVec' {A ι : Type} [CommRing A] [Fintype ι] (τ : A →+* A)
    (K M : Matrix ι ι A) (u w : ι → A) :
    hform τ K (M *ᵥ u) (M *ᵥ w) = hform τ (cT τ M * K * M) u w := by
  have hf : ∀ (K' : Matrix ι ι A) (x y : ι → A), hform τ K' x y = (τ ∘ x) ⬝ᵥ (K' *ᵥ y) := by
    intro K' x y
    simp only [hform, Matrix.mulVec, _root_.dotProduct, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hτ : τ ∘ (M *ᵥ u) = M.map τ *ᵥ (τ ∘ u) := funext fun i => RingHom.map_mulVec τ M u i
  rw [hf, hf, hτ, ← Matrix.vecMul_transpose (M.map τ) (τ ∘ u), ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, cT]

theorem csScale_glob (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    (g : GL n 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) {x y : n → E}
    (hx : x ∈ CS.globLat g Λ) (hy : y ∈ CS.globLat g Λ) :
    ιA ((m : E) * hform (σ : E →+* E) J x y) ∈ 𝒮 := by
  have hg0 : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (g : Matrix n n 𝒜) * J.map ιA *
      (g : Matrix n n 𝒜) = J.map ιA := hg
  have hback : ∀ v : n → 𝒜, (g : Matrix n n 𝒜) *ᵥ (((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hu : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hx
  have hw : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (y i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := hy
  rw [map_mul, ← csScale_hform_incl, ← hback (fun i => ιA (x i)), ← hback (fun i => ιA (y i)),
    hform_mulVec_mulVec', hg0]
  exact csScale_latS σ J Λ m hm hu hw

end Main

theorem scale_bound_holds : Formalism.UG.CS.ScaleBound := by
  intro F E _ _ _ _ _ n _ _ σ J Λ hfin _
  classical
  obtain ⟨m, hm0, hm⟩ := csScale_den σ J Λ hfin
  set β := Module.finBasis F E
  set β' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β
  obtain ⟨m1, hm10, hm1⟩ := adelstabL_den (fun i => β i)
  obtain ⟨m2, hm20, hm2⟩ := adelstabL_den (fun i => β' i)
  refine ⟨((m * m1 * m2 : ℤ) : 𝓞 E), ?_, fun g hg x hx y hy => ?_⟩
  · exact_mod_cast mul_ne_zero (mul_ne_zero hm0 hm10) hm20
  · set e := (m : E) * hform (σ : E →+* E) J x y with he_def
    have he : inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e ∈
        tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F) :=
      csScale_glob σ J Λ m hm g hg hx hy
    have h1 := adelstab_dual β (m1 : E) hm1 e (adelstab_tr_mem e he)
    have h2 : IsIntegral ℤ ((m2 : E) * ((m1 : E) * e)) := by
      suffices hs : ∀ z ∈ Submodule.span (𝓞 F) (Set.range β'), IsIntegral ℤ ((m2 : E) * z) from
        hs _ h1
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact hm2 i
      | zero => rw [mul_zero]; exact isIntegral_zero
      | add z z' _ _ h h' => rw [mul_add]; exact h.add h'
      | smul c z _ h =>
        rw [Algebra.smul_def, mul_left_comm]
        exact ((RingOfIntegers.isIntegral_coe c).algebraMap).mul h
    refine ⟨⟨_, h2⟩, ?_⟩
    show (m2 : E) * ((m1 : E) * e) = algebraMap (𝓞 E) E ((m * m1 * m2 : ℤ) : 𝓞 E) * _
    rw [he_def, map_intCast]
    push_cast
    ring

end Formalism.UG.P
