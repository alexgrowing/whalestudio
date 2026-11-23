import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

private theorem isOpen_subgroupOf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {C C₀ : Subgroup (UA E a)} (hC : IsLevel C) (hC₀ : IsLevel C₀) :
    IsOpen ((C₀.subgroupOf C : Subgroup C) : Set C) := by
  obtain ⟨N, hNo, h1N, hNC⟩ := hC₀.isOpen
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  refine Filter.mem_of_superset
    ((hNo.preimage continuous_subtype_val).mem_nhds (show ((1 : C) : UA E a) ∈ N from h1N)) ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, hC.fin x.2⟩)

theorem twistBd_of : Twist → TwistBd := by
  intro hT E _ _ _ l _ ι a C hC ℓ hℓ W f X b hb
  classical
  obtain ⟨C₀, hC₀, hf⟩ := UpperTheory.Gal.Gen.levelEx_holds E a W f
  have hHo := isOpen_subgroupOf hC hC₀
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  haveI : Finite (C ⧸ C₀.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hHo
  letI := Fintype.ofFinite (C ⧸ C₀.subgroupOf C)
  have hq : ∀ q : C ⧸ C₀.subgroupOf C, ∃ R : ℝ, ∀ g i,
      ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * q.out : C)))‖ ≤ R := by
    intro q
    obtain ⟨F, -, hF⟩ := hT E a C hC ℓ hℓ W f q.out
    obtain ⟨R, hR⟩ := hb F
    exact ⟨R, fun g i => by rw [← hF]; exact hR g i⟩
  choose R hR using hq
  refine ⟨1 + ∑ q, |R q|, by positivity, fun c g i => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (C₀.subgroupOf C) c
  have hhC : ((h : C) : UA E a) ∈ C₀ := Subgroup.mem_subgroupOf.1 h.2
  have e : f.1 (b g i) (g * ((ℓ g)⁻¹ * (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C).out : C)) =
      f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)) := by
    rw [hh]
    have : (((ℓ g)⁻¹ * (c * (h : C)) : C) : UA E a) = (((ℓ g)⁻¹ * c : C) : UA E a) * ((h : C) : UA E a) := by
      simp [mul_assoc]
    rw [this, ← mul_assoc]
    exact hf _ hhC _ _
  rw [← e]
  refine (hR _ g i).trans ((le_abs_self _).trans ?_)
  have := Finset.single_le_sum (f := fun q => |R q|) (fun q _ => abs_nonneg _)
    (Finset.mem_univ (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C))
  linarith

end UpperTheory.Gal.Wt

end
