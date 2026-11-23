import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MemCvOfSubstXPow

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw.FrobCurve

variable {C : Type} [Field C]

theorem sum_rescale_tyS {l : ℕ} (hl : l.Prime) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ j ∈ Finset.range l, PowerSeries.rescale (ζ ^ j) (tyS l a) := by
  ext n
  simp only [map_sum, PowerSeries.coeff_rescale, ← Finset.sum_mul]
  by_cases hn : l ∣ n
  · obtain ⟨q, rfl⟩ := hn
    have h1 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ (l * q) = (l : C) := by
      have : ∀ j, (ζ ^ j) ^ (l * q) = 1 := fun j => by
        rw [← pow_mul, mul_left_comm, pow_mul, hζ.pow_eq_one, one_pow]
      simp [this]
    rw [h1, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow hl.pos]
    by_cases hq : ∃ s, l ^ s = q
    · obtain ⟨s, rfl⟩ := hq
      rw [coeff_tyS_pow hl.two_le, ← pow_succ', coeff_tyS_pow hl.two_le]
    · push Not at hq
      rw [coeff_tyS_of_ne _ _ hq, coeff_tyS_of_ne, mul_zero]
      intro s hs
      cases s with
      | zero =>
        rw [pow_zero] at hs
        exact hl.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hs.symm)
      | succ s =>
        rw [pow_succ'] at hs
        exact hq s (Nat.eq_of_mul_eq_mul_left hl.pos hs)
  · have hc : n.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hl).2 hn).symm
    have h0 : ∑ j ∈ Finset.range l, (ζ ^ j) ^ n = 0 := by
      rw [← (hζ.pow_of_coprime n hc).geom_sum_eq_zero hl.one_lt]
      exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h0, zero_mul, Formalism.L2.FormalSeriesBounds.coeff_subst_X_pow_of_not_dvd hl.pos _ _ hn]

theorem ge_zero_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : 0 < n) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have h1 : n • V.v ζ = 0 := by rw [← V.v.map_pow, h, V.v.map_one]
  unfold VF.Ge
  induction hv : V.v ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe r =>
    rw [hv, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul] at h1
    have : r = 0 := (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn.ne')
    rw [this]

theorem rescale_smul' (s c : C) (f : PowerSeries C) :
    PowerSeries.rescale s (c • f) = c • PowerSeries.rescale s f := by
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

theorem frob_mem_tySet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g, ∀ x ∈ X.TySet V g, Fs V.l x ∈ X.TySet V g := by
  classical
  intro C _ V d _ I _ κ _ X hX g x hx
  haveI := hX.charZero
  haveI := hX.closed
  have hl := V.l_prime
  haveI : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  haveI : NeZero V.l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  obtain ⟨h0, hadd, -, hres⟩ := GlobalTheory.T.gaugedFormalGroupCurveLogarithms_addSubgroup_rescale C V d I κ X hX g
  let lo : (I g ⊕ JJ I g → PowerSeries C) → (κ → PowerSeries C) × (JJ I g → PowerSeries C) := fun A =>
    (fun i => ∑ c : I g, X.u g c i • A (Sum.inl c),
     fun q => A (Sum.inr q) - ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • A (Sum.inl c) else 0)
  have hiff : ∀ y : ℕ → I g ⊕ JJ I g → C,
      y ∈ X.TySet V g ↔ lo (fun n => tyS V.l fun s => y s n) ∈ Cv X V g := fun y => by
    constructor
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.2 (h2 q)⟩
    · rintro ⟨γ, lam, hγ, hlam, h1, h2⟩
      exact ⟨γ, lam, hγ, hlam, h1, fun q => sub_eq_iff_eq_add.1 (h2 q)⟩
  have hsum : ∀ (M : ℕ) (f : ℕ → (κ → PowerSeries C) × (JJ I g → PowerSeries C)),
      (∀ j, f j ∈ Cv X V g) → ∑ j ∈ Finset.range M, f j ∈ Cv X V g := fun M f hf =>
    Finset.sum_induction f (· ∈ Cv X V g) (fun a b ha hb => hadd a ha b hb) h0 fun j _ => hf j
  have hint : ∀ j, V.Ge 0 (ζ ^ j) := fun j => (ge_zero_of_pow_eq_one V hl.pos hζ.pow_eq_one).pow j
  have hS := hsum V.l _ fun j => hres (ζ ^ j) (hint j) _ ((hiff x).1 hx)
  rw [hiff]
  refine GlobalTheory.RowLaw.mem_Cv_of_subst_X_pow C V d I κ X hX g V.l hl.pos _ ?_
  have hsub : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ V.l) :=
    PowerSeries.HasSubst.X_pow hl.ne_zero
  have key : ∀ n, PowerSeries.substAlgHom (R := C) hsub (tyS V.l fun s => Fs V.l x s n) =
      ∑ j ∈ Finset.range V.l, PowerSeries.rescale (ζ ^ j) (tyS V.l fun s => x s n) := fun n => by
    rw [PowerSeries.coe_substAlgHom]
    exact sum_rescale_tyS hl hζ fun s => x s n
  convert hS using 1
  refine Prod.ext (funext fun i => ?_) (funext fun q => ?_)
  · simp only [lo, Prod.fst_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_smul, key,
      rescale_smul', Finset.smul_sum]
    exact Finset.sum_comm
  · simp only [lo, Prod.snd_sum, Finset.sum_apply, ← PowerSeries.coe_substAlgHom hsub, map_sum, map_sub, key,
      Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · simp only [map_smul, key, rescale_smul', Finset.smul_sum]
    · simp

end GlobalTheory.RowLaw.FrobCurve
