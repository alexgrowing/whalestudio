import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimeSetBoundDataOfPrimitiveChar

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base

namespace UpperTheory.V.Chr

section Len

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def Psi (e : ℕ) (ψ : G k Ω →* Oˣ) : G k Ω →* Oˣ := chiO k Ω l O ^ (e : ℤ) * ψ

abbrev rho (e : ℕ) (ψ : G k Ω →* Oˣ) : Representation O (G k Ω) (QO l O) :=
  twist₂ l (ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)))

theorem Psi_inv (e : ℕ) (ψ : G k Ω →* Oˣ) : (Psi l e ψ)⁻¹ = ψ⁻¹ * chiO k Ω l O ^ (-(e : ℤ)) := by
  rw [Psi, mul_inv_rev, zpow_neg]

theorem rho_eq (e : ℕ) (ψ : G k Ω →* Oˣ) : rho l e ψ = twist₂ l (Psi l e ψ)⁻¹ := by rw [Psi_inv]

theorem tw_apply (e : ℕ) (ψ : G k Ω →* Oˣ) (g : G k Ω) (m : QO l O) :
    twist₂ l (chiO k Ω l O ^ (-(e : ℤ))) g m = ((ψ g : Oˣ) : O) • rho l e ψ g m := by
  simp only [rho, twist₂, scalRep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
    smul_smul, ← Units.val_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_left]

def VS (n e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := Module.length O (ShaU (rho l e ψ) n ⊤)

def V (e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := VS l l e ψ

def V' (N e : ℕ) (ψ : G k Ω →* Oˣ) : ℕ∞ := VS l (l * N) e ψ

def h0 (e : ℕ) (ψ : G k Ω →* Oˣ) (U : Subgroup (G k Ω)) : ℕ∞ := Module.length O (H0U (rho l e ψ) U)

def eigL (e : ℕ) (U : Subgroup (G k Ω)) [U.Normal] (ψ : G k Ω →* Oˣ) : ℕ∞ :=
  Module.length O (shaEig (twist₂ l (chiO k Ω l O ^ (-(e : ℤ)))) l U ⊤ (ψ.comp (⊤ : Subgroup (G k Ω)).subtype))

omit [Fact l.Prime] in
theorem shaFam_mono {m n : ℕ} (h : m ∣ n) : shaFam k Ω m ⊆ shaFam k Ω n := by
  intro U hU
  simp only [shaFam, Set.mem_setOf_eq] at hU ⊢
  rcases hU with ⟨A, hA, rfl⟩ | ⟨A, rfl⟩
  · left
    refine ⟨A, ?_, rfl⟩
    obtain ⟨c, rfl⟩ := h
    have hc : A.valuation (c : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A c)
    push_cast
    rw [map_mul]
    calc A.valuation (m : Ω) * A.valuation (c : Ω) ≤ A.valuation (m : Ω) * 1 := by gcongr
      _ = A.valuation (m : Ω) := mul_one _
      _ < 1 := hA
  · right
    exact ⟨A, rfl⟩

theorem VS_anti {m n : ℕ} (h : m ∣ n) (e : ℕ) (ψ : G k Ω →* Oˣ) : VS l n e ψ ≤ VS l m e ψ := by
  have hle : ShaU (rho l e ψ) n ⊤ ≤ ShaU (rho l e ψ) m ⊤ := by
    intro x hx
    simp only [ShaU, LocSel, Submodule.mem_iInf] at hx ⊢
    intro D hD
    exact hx D (shaFam_mono h hD)
  exact Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem V'_le_V (N e : ℕ) (ψ : G k Ω →* Oˣ) : V' l N e ψ ≤ V l e ψ := by
  exact VS_anti l (Dvd.intro N rfl) e ψ

variable (O) in

def nrm (a : ℕ∞) : ℝ := (a.toNat : ℝ) / ((eO l O).toNat : ℝ)

variable (O) in

def SumLe (f : ℕ → ℕ∞) (t : ℕ) (B : ℝ) : Prop :=
  (∀ e : ℕ, 0 < e → e < t → f e ≠ ⊤) ∧ ∑ e ∈ Finset.Ico 1 t, nrm l O (f e) ≤ B

theorem nrm_nonneg (a : ℕ∞) : 0 ≤ nrm l O a := by
  unfold nrm
  positivity

theorem nrm_mono {a b : ℕ∞} (h : a ≤ b) (hb : b ≠ ⊤) : nrm l O a ≤ nrm l O b :=
  div_le_div_of_nonneg_right (by exact_mod_cast ENat.toNat_le_toNat h hb) (Nat.cast_nonneg _)

theorem SumLe.mono {f g : ℕ → ℕ∞} {t : ℕ} {B : ℝ} (h : SumLe l O g t B) (hf : ∀ e, 0 < e → e < t → f e ≤ g e) :
    SumLe l O f t B := by
  refine ⟨fun e h1 h2 => ne_top_of_le_ne_top (h.1 e h1 h2) (hf e h1 h2), le_trans ?_ h.2⟩
  refine Finset.sum_le_sum fun e he => ?_
  rw [Finset.mem_Ico] at he
  exact nrm_mono l (hf e he.1 he.2) (h.1 e he.1 he.2)

abbrev resChar (Ω : Type) {E : Type} [Field Ω] [Algebra k Ω] [Field E] [Algebra k E] [Algebra E Ω] [IsScalarTower k E Ω] [Normal k E]
    (ψ : (E ≃ₐ[k] E) →* Oˣ) : G k Ω →* Oˣ := ψ.comp (AlgEquiv.restrictNormalHom E)

end Len

section Dir

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

include k in
theorem card_roots (N : ℕ) [NeZero N] : Nat.card (rootsOfUnity N Ω) = N := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have : NeZero ((N : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N

def cls (N : ℕ) [NeZero N] : G k Ω →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Ω (card_roots k Ω N)).comp (MulSemiringAction.toRingAut (G k Ω) Ω)

variable {k Ω} in
theorem cls_spec (N : ℕ) [NeZero N] (σ : G k Ω) (ζ : Ω) (hζ : ζ ^ N = 1) : σ ζ = ζ ^ ((cls k Ω N σ : (ZMod N)ˣ) : ZMod N).val := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp [zero_pow (NeZero.ne N)] at hζ
  have hu : Units.mk0 ζ h0 ∈ rootsOfUnity N Ω := by
    rw [mem_rootsOfUnity]
    ext
    simp [hζ]
  have := modularCyclotomicCharacter.spec Ω (card_roots k Ω N) (MulSemiringAction.toRingAut (G k Ω) Ω σ) hu
  simpa [cls] using this

def dirG {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) : G k Ω →* Oˣ :=
  χ.toUnitHom.comp (cls k Ω N)

def levH {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) : Subgroup (G k Ω) := H.comap (cls k Ω N)

instance {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ) : (levH k Ω H).Normal := Subgroup.Normal.comap inferInstance _

end Dir

section OverQ

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

instance (A : AbF) : NeZero A.m := ⟨A.pos.ne'⟩

def abU (A : AbF) : Subgroup (G ℚ Ω) := levH ℚ Ω A.H

def HasLevel (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) : Prop :=
  ∃ (j : E →ₐ[ℚ] CyclotomicField N ℚ) (ζ : CyclotomicField N ℚ), IsPrimitiveRoot ζ N ∧
    ∀ (τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ) (u : (ZMod N)ˣ), τ ζ = ζ ^ (u : ZMod N).val →
      ((∀ x : E, τ (j x) = j x) ↔ u ∈ H)

def evenSet (O : Type) [CommRing O] {N : ℕ} (H : Subgroup (ZMod N)ˣ) (e : ℕ) : Set (DirichletCharacter O N) :=
  {χ | H ≤ χ.toUnitHom.ker ∧ χ (-1) = (-1) ^ e}

def loss (l N n e : ℕ) : ℕ := (n + n ^ 2) * LDataCardLeFinrank.nuBound l N e + N.primeFactors.card * (n * n.factorization l)

end OverQ

example (N : ℕ) [NeZero N] : HasLevel ℚ N ⊤ := by
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  exact ⟨Algebra.ofId _ _, _, IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ), fun τ _ _ =>
    ⟨fun _ => trivial, fun _ x => τ.commutes x⟩⟩

example : (1 : DirichletCharacter ℤ 5) ∈ evenSet ℤ (⊤ : Subgroup (ZMod 5)ˣ) 2 :=
  ⟨fun u _ => by ext; simp, by rw [MulChar.one_apply (by simp)]; norm_num⟩

end UpperTheory.V.Chr

end
