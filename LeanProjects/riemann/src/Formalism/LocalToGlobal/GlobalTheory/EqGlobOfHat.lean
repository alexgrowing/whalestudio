import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsDual
import Formalism.LocalRingCardinality.DataLevel

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.Comp

open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

def IsLat (Λ : Submodule (𝓞 E) (n → E)) : Prop :=
  Module.Finite (𝓞 E) Λ ∧ Submodule.span E (Λ : Set (n → E)) = ⊤

variable (F) in

abbrev hat (Λ : Submodule (𝓞 E) (n → E)) : Submodule 𝒮 (n → 𝒜) :=
  latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ

theorem hat_mono {A B : Submodule (𝓞 E) (n → E)} (h : A ≤ B) : hat F A ≤ hat F B :=
  Submodule.span_mono (Set.image_mono h)

theorem glob_mono (g : GL n 𝒜) {A B : Submodule (𝓞 E) (n → E)} (h : A ≤ B) : globLat g A ≤ globLat g B :=
  fun _ hx => hat_mono h hx

theorem isLat_glob {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) : IsLat (globLat g Λ) := by
  have := global_lattice_isLattice_holds F E n Λ h.1 h.2 g
  exact ⟨Module.Finite.iff_fg.2 this.fg, this.span_eq_top⟩

theorem glob_one {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) : globLat (F := F) 1 Λ = Λ :=
  global_lattice_one_holds F E n Λ h.1 h.2

theorem mem_hat_glob {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) (u : n → 𝒜) :
    u ∈ hat F (globLat g Λ) ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ :=
  span_recovery_of_integral_adelic_approx csGlob_intAdApprox F E n Λ h.1 h.2 g u

theorem glob_glob {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g k : GL n 𝒜) :
    globLat g (globLat k Λ) = globLat (g * k) Λ := by
  ext x
  show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F (globLat k Λ) ↔
    (((g * k)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F Λ
  rw [mem_hat_glob h, mulVec_mulVec, _root_.mul_inv_rev, Units.val_mul]

theorem glob_inv_glob {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) :
    globLat g (globLat g⁻¹ Λ) = Λ := by
  rw [glob_glob h, mul_inv_cancel, glob_one h]

theorem glob_glob_inv {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) :
    globLat g⁻¹ (globLat g Λ) = Λ := by
  rw [glob_glob h, inv_mul_cancel, glob_one h]

theorem eq_glob_of_hat {Λ M : Submodule (𝓞 E) (n → E)} (hM : IsLat M) (g : GL n 𝒜)
    (h : ∀ u : n → 𝒜, u ∈ hat F M ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ) : M = globLat g Λ := by
  rw [← glob_one (F := F) hM]
  ext x
  show (((1 : GL n 𝒜)⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F M ↔
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA (x i)) ∈ hat F Λ
  rw [inv_one, Units.val_one, one_mulVec, h]

theorem isLat_sup {A B : Submodule (𝓞 E) (n → E)} (hA : IsLat A) (hB : IsLat B) : IsLat (A ⊔ B) := by
  refine ⟨Module.Finite.iff_fg.2 ((Module.Finite.iff_fg.1 hA.1).sup (Module.Finite.iff_fg.1 hB.1)), ?_⟩
  rw [eq_top_iff, ← hA.2]
  exact Submodule.span_mono (fun x hx => (le_sup_left : A ≤ A ⊔ B) hx)

theorem glob_sup {A B : Submodule (𝓞 E) (n → E)} (hA : IsLat A) (hB : IsLat B) (g : GL n 𝒜) :
    globLat g (A ⊔ B) = globLat g A ⊔ globLat g B := by
  apply le_antisymm
  · have h1 : A ⊔ B ≤ globLat g⁻¹ (globLat g A ⊔ globLat g B) := by
      refine sup_le ?_ ?_
      · conv_lhs => rw [← glob_glob_inv hA g]
        exact glob_mono _ le_sup_left
      · conv_lhs => rw [← glob_glob_inv hB g]
        exact glob_mono _ le_sup_right
    have h2 := glob_mono g h1
    rwa [glob_inv_glob (isLat_sup (isLat_glob hA g) (isLat_glob hB g))] at h2
  · exact sup_le (glob_mono g le_sup_left) (glob_mono g le_sup_right)

theorem isLat_smul {A : Submodule (𝓞 E) (n → E)} (hA : IsLat A) {a : 𝓞 E} (ha : a ≠ 0) :
    IsLat (Ideal.span {a} • A) := by
  refine ⟨Module.Finite.iff_fg.2 (Submodule.FG.smul (Submodule.fg_span_singleton a) (Module.Finite.iff_fg.1 hA.1)), ?_⟩
  rw [eq_top_iff, ← hA.2, Submodule.span_le]
  intro x hx
  have h1 : a • x ∈ Ideal.span {a} • A := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
  have h2 : (a : E) ≠ 0 := fun h => ha (RingOfIntegers.ext h)
  have h3 : x = (a : E)⁻¹ • (a • x) := by
    rw [← algebraMap_smul E a x, smul_smul]
    show x = ((a : E)⁻¹ * (a : E)) • x
    rw [inv_mul_cancel₀ h2, one_smul]
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem smul_hat (A : Submodule (𝓞 E) (n → E)) (a : 𝓞 E) (u : n → 𝒜) (hu : u ∈ hat F A) :
    ιA (a : E) • u ∈ hat F (Ideal.span {a} • A) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    refine Submodule.subset_span ⟨a • y, Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hy, ?_⟩
    funext i
    show ιA ((a : E) * y i) = ιA (a : E) * ιA (y i)
    rw [map_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
  | smul s u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ s hu

theorem smul_glob_le (A : Submodule (𝓞 E) (n → E)) (a : 𝓞 E) (g : GL n 𝒜) :
    Ideal.span {a} • globLat g A ≤ globLat g (Ideal.span {a} • A) := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.1 hr
  rw [mul_comm, mul_smul]
  refine Submodule.smul_mem _ c ?_
  show ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ (fun i => ιA ((a • x) i)) ∈ hat F (Ideal.span {a} • A)
  have h1 : (fun i => ιA ((a • x) i)) = ιA (a : E) • (fun i => ιA (x i)) := by
    funext i
    show ιA ((a : E) * x i) = ιA (a : E) * ιA (x i)
    rw [map_mul]
  rw [h1, mulVec_smul]
  exact smul_hat A a _ hx

theorem glob_smul {A : Submodule (𝓞 E) (n → E)} (hA : IsLat A) {a : 𝓞 E} (ha : a ≠ 0) (g : GL n 𝒜) :
    globLat g (Ideal.span {a} • A) = Ideal.span {a} • globLat g A := by
  apply le_antisymm
  · have h1 := smul_glob_le (globLat g A) a g⁻¹
    rw [glob_glob_inv hA] at h1
    have h2 := glob_mono g h1
    rwa [glob_inv_glob (isLat_smul (isLat_glob hA g) ha)] at h2
  · exact smul_glob_le A a g

def dl (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) : Submodule (𝓞 E) (n → E) :=
  Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Λ)

theorem hform_add_right {A : Type} [CommRing A] (τ : A →+* A) (J : Matrix n n A) (u v w : n → A) :
    hform τ J u (v + w) = hform τ J u v + hform τ J u w := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A : Type} [CommRing A] (τ : A →+* A) (J : Matrix n n A) (s : A) (u w : n → A) :
    hform τ J u (s • w) = s * hform τ J u w := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_zero_right {A : Type} [CommRing A] (τ : A →+* A) (J : Matrix n n A) (u : n → A) :
    hform τ J u 0 = 0 := by
  simp [hform]

theorem mem_dl (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (y : n → E) :
    y ∈ dl σ J Λ ↔ ∀ x ∈ Λ, hform (σ : E →+* E) J x y ∈ (algebraMap (𝓞 E) E).range := by
  constructor
  · intro hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy => exact hy x hx
    | zero => rw [hform_zero_right]; exact zero_mem _
    | add y z _ _ hy hz => rw [hform_add_right]; exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul E a y, hform_smul_right]
      exact mul_mem ⟨a, rfl⟩ hy
  · intro h
    exact Submodule.subset_span h

theorem hform_hat (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (u w : n → 𝒜)
    (hu : u ∈ hat F Λ) (hw : w ∈ hat F (dl σ J Λ)) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u w ∈ 𝒮 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, rfl⟩ := hw
    exact csDual_span σ J Λ x ((mem_dl σ J Λ x).1 hx) u hu
  | zero => rw [hform_zero_right]; exact zero_mem _
  | add v w _ _ hv hw => rw [hform_add_right]; exact add_mem hv hw
  | smul s w _ hw =>
    rw [Subring.smul_def, hform_smul_right]
    exact mul_mem s.2 hw

theorem glob_dl_le (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : globLat g (dl σ J Λ) ≤ dl σ J (globLat g Λ) := by
  intro x hx
  rw [mem_dl]
  intro y hy
  have h1 := hform_hat σ J Λ _ _ hy hx
  have hg' : g⁻¹ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := inv_mem hg
  have h2 : cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) * J.map ιA *
      ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) = J.map ιA := hg'
  rw [hform_mulVec, h2, csDual_hform_incl] at h1
  have h3 := csGlob_int (F := F) _ h1
  exact ⟨⟨_, h3⟩, rfl⟩

theorem glob_dl (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hJ : ∀ M : Submodule (𝓞 E) (n → E), IsLat M → IsLat (dl σ J M))
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) : globLat g (dl σ J Λ) = dl σ J (globLat g Λ) := by
  apply le_antisymm (glob_dl_le σ J Λ g hg)
  have h1 := glob_dl_le σ J (globLat g Λ) g⁻¹ (inv_mem hg)
  rw [glob_glob_inv hΛ] at h1
  have h2 := glob_mono g h1
  rwa [glob_inv_glob (hJ _ (isLat_glob hΛ g))] at h2

end Formalism.L2.GlobalTheoryTheory.Comp

end
