import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.DzGenA
import Development.DiscreteGroups.GlobalIrreducibility.ExistsCellFunctional
import Development.DiscreteGroups.GlobalIrreducibility.DzIsoKO

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker ValuativeRel

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fixed_ne_bot_of_equiv' {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} (φ : π.Equiv σ) {K : Subgroup G}
    (hπ : fixed π K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hπ
  refine (Submodule.ne_bot_iff _).2 ⟨φ v, GlobalTheory.Parabolic.mem_fixed.2 fun u hu => ?_, fun h1 => h0 ?_⟩
  · exact (φ.toIntertwiningMap.isIntertwining _ _ u v).symm.trans
      (congrArg φ (GlobalTheory.Parabolic.mem_fixed.1 hv u hu))
  · exact φ.toLinearEquiv.injective (h1.trans (map_zero _).symm)

theorem isLower_iff {g m : ℕ} [Fact g.Prime] (b : Gn g m) :
    IsLower b ↔ (b : Mt g m).BlockTriangular OrderDual.toDual := Iff.rfl

def lowZ (g m : ℕ) [Fact g.Prime] : Subgroup (GL (Fin m) ℤ_[g]) where
  carrier := {x | IsLower (GlobalTheory.GLp.red g m x)}
  one_mem' := by
    show IsLower (GlobalTheory.GLp.red g m 1)
    rw [map_one, isLower_iff, Units.val_one]
    exact Matrix.blockTriangular_one
  mul_mem' := by
    intro x y hx hy
    show IsLower (GlobalTheory.GLp.red g m (x * y))
    rw [map_mul, isLower_iff, Units.val_mul]
    exact Matrix.BlockTriangular.mul hx hy
  inv_mem' := by
    intro x hx
    show IsLower (GlobalTheory.GLp.red g m x⁻¹)
    have : Invertible ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m) := (GlobalTheory.GLp.red g m x).invertible
    rw [map_inv, isLower_iff, Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hx

theorem toZMod_eq_zero_iff {g : ℕ} [Fact g.Prime] (x : ℤ_[g]) : PadicInt.toZMod x = 0 ↔ ‖(x : ℚ_[g])‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    PadicInt.padic_norm_e_of_padicInt]

section Place

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

def lowS (m : ℕ) : Subgroup (GL (Fin m) (w.adicCompletion E)) :=
  (lowZ g m).map ((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m))

theorem lowS_apply {m : ℕ} (x : GL (Fin m) ℤ_[g]) (a b : Fin m) :
    ((((Matrix.GeneralLinearGroup.map i.toRingHom).comp (GlobalTheory.GLp.inc g m)) x : GL (Fin m) (w.adicCompletion E)) :
      Matrix (Fin m) (Fin m) (w.adicCompletion E)) a b = i ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a b : ℚ_[g]) := rfl

include hi

theorem lowS_one (m : ℕ) : KOne (w.adicCompletion E) (Fin m) ≤ lowS i m := by
  intro y hy
  obtain ⟨x, hx1, hx2⟩ := DiscreteGroups.sglob.DzIso.exists_of_mem_KOne i hi hy
  refine ⟨x, ?_, hx2⟩
  show IsLower (GlobalTheory.GLp.red g m x)
  rw [hx1, isLower_iff, Units.val_one]
  exact Matrix.blockTriangular_one

theorem lowS_KO (m : ℕ) : lowS i m ≤ KO (w.adicCompletion E) (Fin m) := by
  rintro _ ⟨x, -, rfl⟩
  exact DiscreteGroups.sglob.DzIso.map_inc_mem_KO i hi x

theorem lowS_upper (m : ℕ) : ∀ y ∈ lowS i m, ∀ a b, a < b →
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a b) < 1 := by
  rintro _ ⟨x, hx, rfl⟩ a b hab
  rw [lowS_apply, DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi, ← toZMod_eq_zero_iff]
  exact hx a b hab

theorem lowS_diag (m : ℕ) : ∀ y ∈ lowS i m, ∀ a,
    valuation (w.adicCompletion E) (((y : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) _) a a) = 1 := by
  rintro _ ⟨x, hx, rfl⟩ a
  rw [lowS_apply]
  have hdet : ((GlobalTheory.GLp.red g m x : Gn g m) : Mt g m).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [Matrix.det_of_lowerTriangular _ hx] at hdet
  have hd : PadicInt.toZMod ((x : Matrix (Fin m) (Fin m) ℤ_[g]) a a) ≠ 0 :=
    (Finset.prod_ne_zero_iff.1 hdet) a (Finset.mem_univ a)
  rw [Ne, toZMod_eq_zero_iff] at hd
  refine le_antisymm ((DiscreteGroups.sglob.DzIso.valuation_le_iff i hi _).2 ?_) (not_lt.1 fun h => hd ?_)
  · rw [PadicInt.padic_norm_e_of_padicInt]; exact PadicInt.norm_le_one _
  · exact (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi _).1 h

theorem psi_of_lifts {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle} (hL : Lifts1 i ψ₀ ψ) :
    ∀ y, valuation (w.adicCompletion E) y < 1 → ψ y = 1 := by
  intro y hy
  have hx : ‖i.symm y‖ < 1 := (DiscreteGroups.sglob.DzIso.valuation_lt_iff i hi (i.symm y)).1 (by simpa using hy)
  let z : ℤ_[g] := ⟨i.symm y, hx.le⟩
  have hz : PadicInt.toZMod z = 0 := (toZMod_eq_zero_iff z).2 hx
  have h := hL z
  rw [hz, AddChar.map_zero_eq_one] at h
  have e : i (z : ℚ_[g]) = y := by simp [z]
  rwa [e] at h

end Place

theorem lGen : LGen := by
  intro H E _ _ w g _ i hi ψ₀ _ ψ hψc hL m
  obtain ⟨hirr, hsph, hcen⟩ := genA H (w.adicCompletion E) m
  let τ₀ : IrrRep (GL (Fin m) (w.adicCompletion E)) :=
    ⟨PS (w.adicCompletion E) m, psOne (w.adicCompletion E) m, isSmooth_parInd _ _, hirr⟩
  refine ⟨τ₀, 1, ?_, hcen, ?_⟩
  · obtain ⟨φ⟩ := IrrRep.nonempty_equiv_rep τ₀
    exact fixed_ne_bot_of_equiv' φ.symm hsph
  · obtain ⟨l, hl, hlv⟩ := exists_cell_functional (lowS_one i hi m) (lowS_KO i hi m) (lowS_upper i hi m)
      (lowS_diag i hi m) ψ hψc (psi_of_lifts i hi hL)
    exact ⟨l, cellVec (lowS_one i hi m) (lowS_diag i hi m), hl, hlv, fun x hx =>
      cellVec_fixed (lowS_one i hi m) (lowS_diag i hi m) ⟨x, hx, rfl⟩⟩

end DiscreteGroups.sglob.DzType
