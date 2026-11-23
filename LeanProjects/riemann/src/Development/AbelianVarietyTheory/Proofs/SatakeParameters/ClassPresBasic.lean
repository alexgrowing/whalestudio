import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresBasic

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem coef_inv (f : S.Forms) (c : S.Cl) (g : stab ι J (P.y c)) :
    (χ (stabK ι g) : ℂ) • ρ (g : Γ) (P.coef ((f : S.Cl → S.V) c)) = P.coef ((f : S.Cl → S.V) c) := by
  obtain ⟨g, rfl⟩ := (P.stabI c).surjective g
  rw [← P.coef_act, f.2 c g]

theorem ext_dec (f : S.Forms) (γ : Γ) (c : S.Cl) (k : J) :
    P.ext (f : S.Cl → S.V) (ι γ * P.y c * k) = (χ k : ℂ) • ρ γ (P.coef ((f : S.Cl → S.V) c)) := by
  have hs := P.dec_spec (ι γ * P.y c * k)
  have hc : P.decC (ι γ * P.y c * k) = c :=
    (P.reps (ι γ * P.y c * k)).unique ⟨_, _, hs⟩ ⟨γ, k, rfl⟩
  unfold ClassPres.ext
  rw [hc] at hs ⊢
  generalize P.decG (ι γ * P.y c * k) = γ' at hs ⊢
  generalize P.decK (ι γ * P.y c * k) = k' at hs ⊢
  have e : (P.y c)⁻¹ * ι (γ⁻¹ * γ') * P.y c = (k : G) * (k' : G)⁻¹ := by
    have h2 : ι γ' = ι γ * P.y c * k * (k' : G)⁻¹ * (P.y c)⁻¹ := by rw [hs]; group
    rw [map_mul, map_inv, h2]; group
  have hm : γ⁻¹ * γ' ∈ stab ι J (P.y c) := by
    rw [mem_stab, e]; exact J.mul_mem k.2 (J.inv_mem k'.2)
  have hk : stabK ι (⟨_, hm⟩ : stab ι J (P.y c)) = k' * k⁻¹ := by
    apply Subtype.ext
    simp only [stabK]
    rw [e]; simp
  have hi := coef_inv P f c ⟨_, hm⟩
  rw [hk] at hi
  conv_rhs => rw [← hi]
  rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul]
  congr 1
  · rw [map_mul, map_inv, ← Units.val_mul]
    congr 1
    rw [mul_comm, inv_mul_cancel_right]
  · simp

theorem ext_y (f : S.Forms) (c : S.Cl) :
    P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c) := by
  have := ext_dec P f 1 c 1
  simpa using this

theorem extMem : P.ExtMem := by
  intro f γ h k
  obtain ⟨c, ⟨γ', k', rfl⟩, -⟩ := P.reps h
  have e : ι γ * (ι γ' * P.y c * k') * k = ι (γ * γ') * P.y c * (k' * k : J) := by
    simp [mul_assoc]
  rw [e, ext_dec, ext_dec, map_mul, map_mul, map_smul, smul_smul, Units.val_mul, mul_comm]
  rfl

theorem isom : P.Isom := by
  intro f f'
  unfold adInner CSD.csum
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ext_y, ext_y, P.coef_pair, map_mul, map_inv₀, map_natCast, CSD.wt,
    ← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card]

def bW : Module.Basis S.ιV ℂ W := Module.Basis.mk P.coef_li (by rw [P.coef_span])

theorem bW_apply (j : S.ιV) : bW P j = P.coef (S.bV j) := by simp [bW]

theorem repr_coef (x : S.V) (j : S.ιV) : (bW P).repr (P.coef x) j = σ (S.bV.repr x j) := by
  have : P.coef x = ∑ i, σ (S.bV.repr x i) • bW P i := by
    conv_lhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ, bW_apply]
  rw [this, Module.Basis.repr_sum_self]

theorem coef_injective : Function.Injective P.coef := by
  intro x x' h
  apply S.bV.repr.injective
  ext j
  apply σ.injective
  rw [← repr_coef P, ← repr_coef P, h]

theorem extL_injective : Function.Injective P.extL := by
  intro f f' h
  apply Subtype.ext
  funext c
  apply coef_injective P
  rw [← ext_y, ← ext_y]
  exact congrFun h _

theorem eq_of_reps {F F' : G → W} (hF : F ∈ AdForms ι ρ J χ) (hF' : F' ∈ AdForms ι ρ J χ)
    (h : ∀ c, F (P.y c) = F' (P.y c)) : F = F' := by
  funext g
  obtain ⟨c, ⟨γ, k, rfl⟩, -⟩ := P.reps g
  rw [hF γ _ k, hF' γ _ k, h]

theorem ext_li : LinearIndependent ℂ (fun i => P.extL (S.basis i)) := by
  letI : Algebra K ℂ := σ.toAlgebra
  let Φ : S.Forms →ₗ[K] (S.Cl × S.ιV → K) :=
    { toFun := fun f p => S.bV.repr ((f : S.Cl → S.V) p.1) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  have hΦ : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro f f' h
    apply Subtype.ext
    funext c
    apply S.bV.repr.injective
    ext j
    exact congrFun h (c, j)
  have h1 := S.basis.linearIndependent.map' Φ hΦ
  have h2 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 h1
  let Ψ : (G → W) →ₗ[ℂ] (S.Cl × S.ιV → ℂ) :=
    { toFun := fun F p => (bW P).repr (F (P.y p.1)) p.2
      map_add' := by intro f f'; funext p; simp
      map_smul' := by intro a f; funext p; simp }
  refine LinearIndependent.of_comp Ψ ?_
  have e : (⇑Ψ ∘ fun i => P.extL (S.basis i)) = fun i => ⇑(algebraMap K ℂ) ∘ (⇑Φ ∘ ⇑S.basis) i := by
    funext i p
    show (bW P).repr (P.ext _ (P.y p.1)) p.2 = σ (S.bV.repr ((S.basis i : S.Cl → S.V) p.1) p.2)
    rw [ext_y, repr_coef]
  rw [e]
  exact h2

open Classical in

def avgForm (S : CSD K) (c : S.Cl) (x : S.V) : S.Forms :=
  ⟨Pi.single c (∑ g : S.Gam c, S.ρ c g x), by
    intro c' γ
    by_cases h : c' = c
    · subst h
      simp only [Pi.single_eq_same, map_sum]
      simp only [← Module.End.mul_apply, ← map_mul]
      exact Fintype.sum_equiv (Equiv.mulLeft γ) _ _ fun _ => rfl
    · simp [Pi.single_eq_of_ne h]⟩

theorem ext_span : Submodule.span ℂ (Set.range P.extL) = AdForms ι ρ J χ := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact extMem P f
  · intro F hF
    have hmem : ∀ M : Submodule ℂ (G → W), (∀ f, P.extL f ∈ M) →
        (∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j))) ∈ M := fun M hM =>
      M.sum_mem fun c _ => M.sum_mem fun j _ => M.smul_mem _ (hM _)
    have key : F = ∑ c, ∑ j, ((Fintype.card (S.Gam c) : ℂ)⁻¹ * (bW P).repr (F (P.y c)) j) •
          P.extL (avgForm S c (S.bV j)) := by
      refine eq_of_reps P hF (hmem _ (extMem P)) fun c => ?_
      simp only [Finset.sum_apply, Pi.smul_apply, ClassPres.extL_apply, ext_y]
      rw [Finset.sum_eq_single c]
      · have hg : ∀ g : S.Gam c, ∑ j, (bW P).repr (F (P.y c)) j • P.coef (S.ρ c g (S.bV j)) = F (P.y c) := by
          intro g
          have h1 := hF (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g))
          rw [stabK_spec] at h1
          conv_rhs => rw [h1, ← (bW P).sum_repr (F (P.y c))]
          simp only [P.coef_act, map_sum, map_smul, Finset.smul_sum, bW_apply]
          exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
        simp only [avgForm, Pi.single_eq_same, map_sum, mul_smul, ← Finset.smul_sum]
        simp only [Finset.smul_sum (s := (Finset.univ : Finset (S.Gam c)))]
        rw [Finset.sum_comm]
        simp only [hg, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
        exact_mod_cast Fintype.card_ne_zero
      · intro c' _ hc
        simp [avgForm, Pi.single_eq_of_ne (Ne.symm hc)]
      · simp
    rw [key]
    exact hmem _ fun f => Submodule.subset_span ⟨f, rfl⟩

end GlobalTheory.PresBasic

namespace GlobalTheory

theorem classPres_basic : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ), P.ExtMem ∧ P.Isom ∧ P.ExtBij ∧ (∀ (f : S.Forms) c, P.ext (f : S.Cl → S.V) (P.y c) = P.coef ((f : S.Cl → S.V) c)) ∧ Function.Injective P.extL :=
  fun _ _ _ _ _ _ P => ⟨PresBasic.extMem P, PresBasic.isom P, ⟨PresBasic.ext_li P, PresBasic.ext_span P⟩,
    PresBasic.ext_y P, PresBasic.extL_injective P⟩

end GlobalTheory
