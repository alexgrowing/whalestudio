import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantZmodLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicFormWeightLevelSmoothAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAutomorphicOfWeightOfNonzeroFixedFinPartFormStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSupercuspidalTypeCharacterZmodPowStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.CongSc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def zchar {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) : Multiplicative (ZMod N) →* ℂˣ where
  toFun x := ζ ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]

theorem zchar_apply {N : ℕ} [NeZero N] (ζ : ℂˣ) (hζ : ζ ^ N = 1) (x : Multiplicative (ZMod N)) :
    zchar ζ hζ x = ζ ^ (Multiplicative.toAdd x).val := rfl

theorem sum_roots {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (k : ℕ) (hk : k < N) :
    ∑ i : Fin N, (ζ ^ (i : ℕ)) ^ k = if k = 0 then (N : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ i) ^ k)]
  simp_rw [← pow_mul, mul_comm _ k, pow_mul]
  split_ifs with h
  · subst h; simp
  · have hne : ζ ^ k ≠ 1 := fun e => h (Nat.eq_zero_of_dvd_of_lt ((hζ.pow_eq_one_iff_dvd k).1 e) hk)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

def stab (W : Wt E n) (f : algForms W) : Subgroup (UA E n) where
  carrier := {x | ∀ v g, f.1 v (g * x) = f.1 v g}
  mul_mem' {x y} hx hy v g := by rw [← mul_assoc, hy, hx]
  one_mem' v g := by rw [mul_one]
  inv_mem' {x} hx v g := by
    have := hx v (g * x⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

theorem stab_level (W : Wt E n) (f : algForms W) (C : Subgroup (UA E n)) (hC : C ≤ finU E n)
    (hc : IsCompact (C : Set (UA E n))) (ho : ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ C) :
    IsCompact ((C ⊓ stab W f : Subgroup (UA E n)) : Set (UA E n)) ∧
      ∃ N : Set (UA E n), IsOpen N ∧ 1 ∈ N ∧ N ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := by
  obtain ⟨N₁, hN₁, h1, hN₁C⟩ := ho
  have hsm := isSmooth_algRep W f
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 hsm
  have hfix : ∀ x (hx : x ∈ finU E n), x ∈ t → x ∈ stab W f := by
    intro x hx hxt v g
    have : (⟨x, hx⟩ : finU E n) ∈ {k : finU E n | algRep W k f = f} := by rw [← hte]; exact hxt
    exact congrArg (fun F : algForms W => F.1 v g) this
  have h1t : (1 : UA E n) ∈ t := by
    have : (1 : finU E n) ∈ {k : finU E n | algRep W k f = f} := by simp
    rw [← hte] at this; exact this
  have hN : N₁ ∩ t ∩ finU E n ⊆ (C ⊓ stab W f : Subgroup (UA E n)) := fun x ⟨⟨hx1, hxt⟩, hxf⟩ =>
    ⟨hN₁C ⟨hx1, hxf⟩, hfix x hxf hxt⟩
  refine ⟨?_, N₁ ∩ t, hN₁.inter ht, ⟨h1, h1t⟩, hN⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hc
  have hHo : IsOpen (((C ⊓ stab W f).subgroupOf C : Subgroup C) : Set C) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      (((hN₁.inter ht).preimage continuous_subtype_val).mem_nhds ⟨h1, h1t⟩) ?_)
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hN ⟨hx, hC x.2⟩)
  have hHc := Subtype.isCompact_iff.1 (Subgroup.isClosed_of_isOpen _ hHo).isCompact
  convert hHc using 1
  ext x; constructor
  · intro hx; exact ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact Subgroup.mem_subgroupOf.1 hy

def opL (s : UA E n →₀ ℂ) : Module.End ℂ (UA E n → ℂ) where
  toFun := opOf (RU E n) s
  map_add' φ ψ := by simp [opOf, Finsupp.sum, Finset.sum_add_distrib, smul_add]
  map_smul' c φ := by simp [opOf, Finsupp.sum, Finset.smul_sum, smul_comm c]

end GlobalTheory.CongSc

namespace GlobalTheory.CongSc

end GlobalTheory.CongSc
