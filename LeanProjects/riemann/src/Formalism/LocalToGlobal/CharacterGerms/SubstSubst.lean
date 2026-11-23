import Formalism.LocalToGlobal.CharacterGerms.LeafHolds
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
import Formalism.LocalToGlobal.CharacterGerms.LemmaMJet
import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace VP

section Gen

variable {C : Type} [Field C] {σ τ ρ : Type}

theorem hs [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.HasSubst a := hasSubst_of_ordGE (fun s => by
    unfold Formalism.BaseCaseIdentities.OrdGE
    intro A hA
    have h0 : A = 0 := by
      rw [← Finsupp.degree_eq_zero_iff]
      omega
    subst h0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha s)

theorem og {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    Formalism.BaseCaseIdentities.OrdGE 1 (a s) := by
  unfold Formalism.BaseCaseIdentities.OrdGE
  intro A hA
  have h0 : A = 0 := by
    rw [← Finsupp.degree_eq_zero_iff]
    omega
  subst h0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact ha s

theorem cc_subst [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have h : Formalism.BaseCaseIdentities.OrdGE 1 (MvPowerSeries.subst a f) :=
    ordGE_subst (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())
  have h0 := h 0 (by simp)
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem subst_mul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f * g) = MvPowerSeries.subst a f * MvPowerSeries.subst a g := MvPowerSeries.subst_mul (hs ha) f g

theorem subst_one [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) :
    MvPowerSeries.subst a (1 : MvPowerSeries σ C) = 1 := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_one _

theorem subst_prod [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∏ i ∈ s, F i) = ∏ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_prod _ _ _

theorem subst_sum [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, MvPowerSeries.subst a (F i) := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_sum _ _ _

theorem subst_smul [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (c : C) (f : MvPowerSeries σ C) :
    MvPowerSeries.subst a (c • f) = c • MvPowerSeries.subst a f := by
  rw [← MvPowerSeries.coe_substAlgHom (hs ha)]
  exact map_smul _ c f

theorem subst_exp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ C} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (mvExp f) = mvExp (MvPowerSeries.subst a f) := subst_mvExp (og ha) (og (a := fun _ : Unit => f) (fun _ => hf) ())

theorem subst_subst [Finite σ] [Finite τ] {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    MvPowerSeries.subst b (MvPowerSeries.subst a f) =
      MvPowerSeries.subst (fun s => MvPowerSeries.subst b (a s)) f := MvPowerSeries.subst_comp_subst_apply (hs ha) (hs hb) f

theorem subst_X [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (s : σ) :
    MvPowerSeries.subst a (MvPowerSeries.X s : MvPowerSeries σ C) = a s := MvPowerSeries.subst_X (hs ha) s

end Gen

section Exp

variable {C : Type} [Field C] [CharZero C] {n dd : ℕ}

theorem expS_eq (f : PS C n dd) (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS C f = mvExp f := by
  have hpow : ∀ (k : ℕ) (m : Fin n × Fin dd →₀ ℕ), m.degree < k → MvPowerSeries.coeff m (f ^ k) = 0 := by
    intro k m hm
    have h1 := ordGE_finsupp_prod (fun _ : Unit => f) (fun _ => og (a := fun _ : Unit => f) (fun _ => hf) ())
      (Finsupp.single () k)
    simp only [Finsupp.prod_single_index, pow_zero, Finsupp.degree_single] at h1
    exact h1 m hm
  ext m
  rw [FB.expS, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  change _ = ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (f ^ k) / (k.factorial : C)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (m.degree + 1)) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [PowerSeries.coeff_exp]
    simp only [smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro k hk
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hk (by rw [hpow k m (by omega), smul_zero])

end Exp

end VP

end Formalism.L2.FormalSeriesBounds
