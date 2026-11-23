import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameGenAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationApplyOfWild

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace TameWeilRepresentationIrreducibility

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem wild_inertia_isWild {σ : G E Ω} (hσ : σ ∈ GlobalTheory.WeilDeligne.Wild E A) : Formalism.MainNotions.BlochKatoReduction.IsWild A σ := by
  refine ⟨Wild_le_Ine hσ, fun x hx => ?_⟩
  have hlt := (mem_Wild.mp hσ) x hx
  have hx0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have e : σ x - x = x * (σ x / x - 1) := by
    rw [mul_sub, mul_div_cancel₀ _ hx, mul_one]
  rw [e, map_mul]
  calc A.valuation x * A.valuation (σ x / x - 1) < A.valuation x * 1 :=
        mul_lt_mul_of_pos_left hlt (zero_lt_iff.mpr hx0)
    _ = A.valuation x := mul_one _

variable [IsAlgClosure E Ω] {h : IsPlaceOver A w}

theorem mem_of_tame_generator_frobenius {M : Type*} [Monoid M] (f : Weil h →* M) (hf : GlobalTheory.WeilDeligne.IsSmooth f)
    (hw : ∀ σ : Weil h, (σ : G E Ω) ∈ GlobalTheory.WeilDeligne.Wild E A → f σ = 1)
    {γ0 : G E Ω} (hγ : Formalism.BasicNotions.TameGenAt A γ0) {φ : Weil h} (hφ : deg φ = -1)
    (S : Subgroup (Weil h)) (hS : ∀ σ, f σ = 1 → σ ∈ S)
    (h1 : (⟨γ0, GlobalTheory.WeilDeligne.Ine_le_Weil h hγ.1⟩ : Weil h) ∈ S) (h2 : φ ∈ S) (σ : Weil h) : σ ∈ S := by
  let S' : Subgroup (Ine A) := S.comap (ineIncl h)
  let K : Subgroup (Ine A) := (f.comp (ineIncl h)).ker
  have hKS : K ≤ S' := fun τ hτ => hS _ hτ
  have hKo : IsOpen (SetLike.coe K) := by
    unfold GlobalTheory.WeilDeligne.IsSmooth at hf
    exact hf
  have hcl : IsClosed (SetLike.coe S') :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hKS hKo)
  have hineS : ∀ τ : Ine A, τ ∈ S' := by
    refine GlobalTheory.TameCharUnique.mem_of_tameGen hγ S' hcl ?_ ?_
    · show ineIncl h ⟨γ0, hγ.1⟩ ∈ S
      have e : ineIncl h ⟨γ0, hγ.1⟩ = ⟨γ0, GlobalTheory.WeilDeligne.Ine_le_Weil h hγ.1⟩ :=
        Subtype.ext (coe_ineIncl h _)
      rw [e]
      exact h1
    · intro τ hτ
      show ineIncl h τ ∈ S
      apply hS
      apply hw
      rw [coe_ineIncl]
      exact mem_Wild.mpr hτ
  have hd : deg φ⁻¹ = 1 := by
    rw [deg_inv, hφ]
    rfl
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hd σ
  rw [hτ]
  exact S.mul_mem (S.zpow_mem (S.inv_mem h2) _) (hineS τ)

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem irreducible_stable_bot_or_top {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible)
    (U : Submodule ℂ V) (hU : ∀ σ, ∀ v ∈ U, ρ σ v ∈ U) : U = ⊥ ∨ U = ⊤ := by
  rcases hρ.eq_bot_or_eq_top (⟨U, fun σ v hv => hU σ v hv⟩ : Subrepresentation ρ) with h | h
  · left
    exact congrArg Subrepresentation.toSubmodule h
  · right
    exact congrArg Subrepresentation.toSubmodule h

theorem irreducible_nontrivial {ρ : Representation ℂ (Weil h) V} (hρ : ρ.IsIrreducible) :
    Nontrivial V := by
  have := hρ
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [@Subsingleton.elim _ hV x 0]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

theorem irreducible_monodromy_zero (a : WDRep h V) (ha : a.ρ.IsIrreducible) : a.N = 0 := by
  have hne : Nontrivial V := irreducible_nontrivial ha
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
    have := one_lt_normV w
    exact_mod_cast (show normV w ≠ 0 by omega)
  have hinv : ∀ σ, ∀ v ∈ LinearMap.ker a.N, a.ρ σ v ∈ LinearMap.ker a.N := by
    intro σ v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hc := congrArg (fun M : Module.End ℂ V => M v) (a.comm σ)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hv, map_zero] at hc
    exact (smul_eq_zero.mp hc.symm).resolve_left (zpow_ne_zero _ hq)
  rcases irreducible_stable_bot_or_top ha _ hinv with h | h
  · exfalso
    obtain ⟨k, hk⟩ := a.nilpotent
    have hi : Function.Injective a.N := LinearMap.ker_eq_bot.mp h
    have hk' : Function.Injective (a.N ^ k) := by
      rw [Module.End.coe_pow]
      exact hi.iterate k
    rw [hk] at hk'
    obtain ⟨x, y, hxy⟩ := hne
    exact hxy (hk' (by simp))
  · exact LinearMap.ker_eq_top.mp h

theorem mem_of_injective_maps_into {T : Module.End ℂ V} (hT : Function.Injective T) {U : Submodule ℂ V}
    (hU : ∀ v ∈ U, T v ∈ U) {v : V} (hv : T v ∈ U) : v ∈ U := by
  let T' : U →ₗ[ℂ] U := T.restrict hU
  have hinj : Function.Injective T' := fun x y hxy => by
    have e : T x = T y := congrArg Subtype.val hxy
    exact Subtype.ext (hT e)
  obtain ⟨u, hu⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨T v, hv⟩
  have e : T u = T v := congrArg Subtype.val hu
  rw [← hT e]
  exact u.2

def weilStabiliserSubgroup (ρ : Representation ℂ (Weil h) V) (U : Submodule ℂ V) : Subgroup (Weil h) where
  carrier := {σ | ∀ v, v ∈ U ↔ ρ σ v ∈ U}
  one_mem' := by
    show ∀ v, _
    intro v; simp
  mul_mem' := by
    intro σ τ hσ hτ
    have hσ' : ∀ v, v ∈ U ↔ ρ σ v ∈ U := hσ
    have hτ' : ∀ v, v ∈ U ↔ ρ τ v ∈ U := hτ
    show ∀ v, _
    intro v
    rw [map_mul, Module.End.mul_apply, ← hσ', ← hτ']
  inv_mem' := by
    intro σ hσ
    have hσ' : ∀ v, v ∈ U ↔ ρ σ v ∈ U := hσ
    show ∀ v, _
    intro v
    have e := hσ' (ρ σ⁻¹ v)
    rw [Representation.self_inv_apply] at e
    exact e.symm

theorem mem_weil_stabiliser_iff {ρ : Representation ℂ (Weil h) V} {U : Submodule ℂ V} {σ : Weil h} :
    σ ∈ weilStabiliserSubgroup ρ U ↔ ∀ v, v ∈ U ↔ ρ σ v ∈ U := Iff.rfl

def weilIntertwiningSubgroup (ρ : Representation ℂ (Weil h) V) (ρ' : Representation ℂ (Weil h) V') (e : V ≃ₗ[ℂ] V') :
    Subgroup (Weil h) where
  carrier := {σ | ∀ v, e (ρ σ v) = ρ' σ (e v)}
  one_mem' := by
    show ∀ v, _
    intro v; simp
  mul_mem' := by
    intro σ τ hσ hτ
    have hσ' : ∀ v, e (ρ σ v) = ρ' σ (e v) := hσ
    have hτ' : ∀ v, e (ρ τ v) = ρ' τ (e v) := hτ
    show ∀ v, _
    intro v
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hσ', hτ']
  inv_mem' := by
    intro σ hσ
    have hσ' : ∀ v, e (ρ σ v) = ρ' σ (e v) := hσ
    show ∀ v, _
    intro v
    have e1 := hσ' (ρ σ⁻¹ v)
    rw [Representation.self_inv_apply] at e1
    rw [e1, Representation.inv_self_apply]

theorem mem_weil_intertwining_iff {ρ : Representation ℂ (Weil h) V} {ρ' : Representation ℂ (Weil h) V'}
    {e : V ≃ₗ[ℂ] V'} {σ : Weil h} : σ ∈ weilIntertwiningSubgroup ρ ρ' e ↔ ∀ v, e (ρ σ v) = ρ' σ (e v) := Iff.rfl

end TameWeilRepresentationIrreducibility

open TameWeilRepresentationIrreducibility in
theorem st2 : St2 := by
  intro E Ω _ _ _ _ _ A w h φ hφ
  obtain ⟨γ0, hγ⟩ := GlobalTheory.MemTame.exists_tameGenAt E Ω w A h
  let γ : Weil h := ⟨γ0, GlobalTheory.WeilDeligne.Ine_le_Weil h hγ.1⟩
  have hd : deg φ⁻¹ = 1 := by
    rw [deg_inv, hφ]
    rfl
  have hfr := deg_eq_one_iff.mp hd
  let x : Weil h := (γ ^ normV w)⁻¹ * (φ⁻¹ * γ * φ⁻¹⁻¹)
  have hx : Formalism.MainNotions.BlochKatoReduction.IsWild A (x : G E Ω) := by
    apply wild_inertia_isWild
    have ht := tame_relation (γ := γ0) (q := normV w) hγ.1 hfr
    simpa [x, γ] using ht
  have hid : γ * φ = φ * γ ^ normV w * x := by
    simp only [x]
    group
  have hinj : ∀ {m : ℕ} (b : WDRep h (Fin m → ℂ)) (g : Weil h), Function.Injective (b.ρ g) :=
    fun b g u v huv => by simpa using congrArg (b.ρ g⁻¹) huv
  have hstab : ∀ {m : ℕ} (b : WDRep h (Fin m → ℂ)),
      (∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) →
      ∀ U : Submodule ℂ (Fin m → ℂ), (∀ v ∈ U, b.ρ γ v ∈ U) → (∀ v ∈ U, b.ρ φ v ∈ U) →
      ∀ σ, ∀ v ∈ U, b.ρ σ v ∈ U := by
    intro m b hb U h1 h2 σ v hv
    have hmem := mem_of_tame_generator_frobenius (S := weilStabiliserSubgroup b.ρ U) b.ρ b.smooth
      (fun τ hτ => hb τ (wild_inertia_isWild hτ)) hγ hφ ?_ ?_ ?_ σ
    · exact (mem_weil_stabiliser_iff.mp hmem v).mp hv
    · intro τ hτ
      rw [mem_weil_stabiliser_iff]
      intro u
      simp [hτ]
    · rw [mem_weil_stabiliser_iff]
      intro u
      exact ⟨h1 u, mem_of_injective_maps_into (hinj b _) h1⟩
    · rw [mem_weil_stabiliser_iff]
      intro u
      exact ⟨h2 u, mem_of_injective_maps_into (hinj b _) h2⟩
  refine ⟨γ, ?_, ?_⟩
  · intro n a ha
    refine ⟨?_, fun hirr => ⟨irreducible_nontrivial hirr, fun U h1 h2 => irreducible_stable_bot_or_top hirr U (hstab a ha U h1 h2)⟩⟩
    calc a.ρ γ * a.ρ φ = a.ρ (γ * φ) := (map_mul _ _ _).symm
      _ = a.ρ (φ * γ ^ normV w * x) := by rw [hid]
      _ = a.ρ φ * a.ρ γ ^ normV w * a.ρ x := by rw [map_mul, map_mul, map_pow]
      _ = a.ρ φ * a.ρ γ ^ normV w := by rw [ha x hx, mul_one]
  · intro n m a b ha hb hai hbi e he1 he2
    refine ⟨e, ?_, ?_⟩
    · intro σ v
      let F : Weil h →* Module.End ℂ (Fin n → ℂ) × Module.End ℂ (Fin m → ℂ) :=
        MonoidHom.prod a.ρ b.ρ
      have hF : GlobalTheory.WeilDeligne.IsSmooth F := by
        have ha' := a.smooth
        have hb' := b.smooth
        unfold GlobalTheory.WeilDeligne.IsSmooth at ha' hb' ⊢
        have hset : {τ : Ine A | F (ineIncl h τ) = 1} =
            {τ : Ine A | a.ρ (ineIncl h τ) = 1} ∩ {τ : Ine A | b.ρ (ineIncl h τ) = 1} := by
          ext τ
          simp [F, Prod.ext_iff]
        rw [hset]
        exact ha'.inter hb'
      have hmem := mem_of_tame_generator_frobenius (S := weilIntertwiningSubgroup a.ρ b.ρ e) F hF ?_ hγ hφ ?_ ?_ ?_ σ
      · exact mem_weil_intertwining_iff.mp hmem v
      · intro τ hτ
        have hw' := wild_inertia_isWild hτ
        simp [F, ha τ hw', hb τ hw']
      · intro τ hτ
        simp only [F, MonoidHom.prod_apply, Prod.ext_iff] at hτ
        rw [mem_weil_intertwining_iff]
        intro u
        rw [hτ.1, hτ.2]
        rfl
      · rw [mem_weil_intertwining_iff]
        exact he1
      · rw [mem_weil_intertwining_iff]
        exact he2
    · intro v
      rw [irreducible_monodromy_zero a hai, irreducible_monodromy_zero b hbi]
      simp

end PositivityTheory.Rg.DzCount

end
