import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.NormOpenB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem normHom_mem (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p) (hy : y ∈ multOf p L) :
    normHom p K L y ∈ multOf p K := normHom_mem_multiplicative_group hL y hy

theorem normHom_eq_algebraNorm (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (y : KbarMult p)
    (hy : y ∈ multOf p L) :
    ((Additive.toMul (normHom p K L y) : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      ((Algebra.norm K (⟨((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p), hy⟩ :
        IntermediateField.extendScalars h) : K) : PadicAlgCl p) :=
  normHom_eq_algebra_norm hL h y hy

theorem normHom_layer (h : K ≤ L) [(subG p K L).Normal] [Fintype (GalLK p K L)] (y : (layer p K L).V) :
    normHom p K L y.1 = (∑ g, (layer p K L).rho g y).1 := normHom_layer_eq_trace_sum y

theorem normHom_trans {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') (y : KbarMult p)
    (hy : y ∈ multOf p L') : normHom p K L (normHom p L L' y) = normHom p K L' y :=
  normHom_comp_normHom_of_le hL' h h' y hy

theorem normGrp_anti {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hL' : FiniteDimensional ℚ_[p] L') (h : K ≤ L) (h' : L ≤ L') :
    normGrp p K L' ≤ normGrp p K L := normGroup_antitone hL' h h'

theorem pow_degLK_mem_normGrp (h : K ≤ L) (x : Kˣ) : x ^ degLK p K L ∈ normGrp p K L :=
  pow_degree_mem_normGroup h x

theorem normGrp_self : normGrp p K K = ⊤ := normGroup_self_eq_top

theorem finiteIndex_range_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := finiteIndex_range_pow' hK hn

theorem isOpen_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    IsOpen (normGrp p K L : Set Kˣ) :=
  Subgroup.isOpen_mono (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)
    (isOpen_range_pow' hK (degLK_pos hL))

theorem finiteIndex_normGrp (hK : FiniteDimensional ℚ_[p] K) (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) :
    (normGrp p K L).FiniteIndex := by
  have := finiteIndex_range_pow' hK (degLK_pos (K := K) hL)
  exact Subgroup.finiteIndex_of_le (H := (powMonoidHom (degLK p K L) : Kˣ →* Kˣ).range)
    (by rintro _ ⟨x, rfl⟩; exact pow_degLK_mem_normGrp h x)

end ReciprocityTheory.DiscreteGroups.LocalClassField
