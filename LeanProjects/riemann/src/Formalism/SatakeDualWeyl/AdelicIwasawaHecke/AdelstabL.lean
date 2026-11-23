import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Adelstab

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section L

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

omit [NumberField F] [Algebra F E] in

theorem adelstabL_den {κ : Type} [Fintype κ] (f : κ → E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  classical
  have h1 : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors ℤ) (Rₘ := ℚ) (f i) (Algebra.IsIntegral.isIntegral (R := ℚ) (f i))
    refine ⟨m, nonZeroDivisors.ne_zero hm, ?_⟩
    simpa [Submonoid.smul_def, zsmul_eq_mul] using hint
  choose m hm0 hmi using h1
  refine ⟨∏ i, m i, Finset.prod_ne_zero_iff.mpr fun i _ => hm0 i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ i), Int.cast_mul,
    mul_comm ((m i : ℤ) : E), mul_assoc]
  refine IsIntegral.mul ?_ (hmi i)
  simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := ∏ j ∈ Finset.univ.erase i, m j)

theorem adelstabL_incl_int (e : E) (he : IsIntegral ℤ e) : ι e ∈ 𝒮 := by
  unfold inclE tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨e, ?_⟩, rfl⟩
  exact ⟨⟨e, he⟩, rfl⟩

theorem adelstabL_upper (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∀ i,
      levelafC E c * v i ∈ 𝒮 := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨(m : 𝓞 F), Int.cast_ne_zero.2 hm0, fun v hv => ?_⟩
  have hC : levelafC E (m : 𝓞 F) = ι (m : E) := by
    rw [← adelstab_incl_C, map_intCast]
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    intro i
    rw [hC, ← map_mul]
    exact adelstabL_incl_int _ (hΛ x hx i)
  | zero => intro i; simp
  | add v w _ _ hv hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hv i) (hw i)
  | smul s v _ hv =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (hv i)

theorem adelstabL_lower (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) →
      (fun i => levelafC E c * v i) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by
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
  have hsingle : ∀ k, (Pi.single k (m : E) : n → E) ∈ Λ := by
    intro k
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
  refine ⟨(m : 𝓞 F), Int.cast_ne_zero.2 hm0, fun v hv => ?_⟩
  have hC : levelafC E (m : 𝓞 F) = ι (m : E) := by
    rw [← adelstab_incl_C, map_intCast]
  have : (fun i => levelafC E (m : 𝓞 F) * v i) =
      ∑ k, (⟨v k, hv k⟩ : 𝒮) • (fun i => ι ((Pi.single k (m : E) : n → E) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show _ = (_ : 𝒮) • ι ((Pi.single i (m : E) : n → E) i)
      rw [Pi.single_eq_same, Subring.smul_def, smul_eq_mul, ← hC, mul_comm]
    · intro k _ hki
      show (_ : 𝒮) • ι ((Pi.single k (m : E) : n → E) i) = 0
      rw [Pi.single_apply, if_neg (Ne.symm hki), map_zero, smul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [this]
  exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hsingle k, rfl⟩)

end L

theorem adelic_stabilizer_finite_lattice_holds : Formalism.UG.AdelicStabFiniteL := by
  intro F E _ _ _ _ _ n _ _ σ J hτ hH hdet hdef Λ hfin hspan g
  obtain ⟨c₁, hc₁, h₁⟩ := adelstabL_lower (F := F) Λ hspan
  obtain ⟨c₂, hc₂, h₂⟩ := adelstabL_upper (F := F) Λ hfin
  exact adelstab_core σ J hτ hH hdet hdef _ (levelAfL σ J Λ) inf_le_right c₁ c₂ hc₁ hc₂ h₁ h₂ g

end Formalism.UG.P
