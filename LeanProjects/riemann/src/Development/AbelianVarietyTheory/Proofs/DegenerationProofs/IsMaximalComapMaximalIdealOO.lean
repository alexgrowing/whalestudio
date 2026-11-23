import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

open GlobalTheory.Points IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def padicIntToOO (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* OO p :=
  (algebraMap ℤ_[p] (PadicAlgCl p)).codRestrict (OO p) fun _ =>
    (mem_OO_iff _).2 ((GlobalTheory.isIntegral_padicInt_iff_norm_le_one _).1 isIntegral_algebraMap)

theorem isIntegral_padicIntToOO : (padicIntToOO p).IsIntegral := by
  intro x
  obtain ⟨q, hq, h⟩ := (GlobalTheory.isIntegral_padicInt_iff_norm_le_one (x : PadicAlgCl p)).2 ((mem_OO_iff _).1 x.2)
  refine ⟨q, hq, Subtype.ext ?_⟩
  exact (Polynomial.hom_eval₂ q (padicIntToOO p) (OO p).subtype x).trans h

theorem natCast_residueField_OO : ((p : ℕ) : ResidueField (OO p)) = 0 := by
  rw [← map_natCast (residue (OO p)), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    not_isUnit_OO_iff]
  have h : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) p := by simp
  rw [h, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem isIntegral_int_residueField_OO : (Int.castRingHom (ResidueField (OO p))).IsIntegral := by
  intro x
  set ψ : ℤ_[p] →+* ResidueField (OO p) := (residue (OO p)).comp (padicIntToOO p)
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _ isIntegral_padicIntToOO
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  obtain ⟨q, hq, h⟩ := hψ x
  have hl : q.map ψ ∈ Polynomial.lifts (Int.castRingHom (ResidueField (OO p))) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have h1 := PadicInt.sub_zmodRepr_mem (q.coeff n)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg ψ hc
    rw [map_sub, map_mul, map_natCast, map_natCast, natCast_residueField_OO, zero_mul, sub_eq_zero] at h2
    exact ⟨((q.coeff n).zmodRepr : ℤ), by rw [h2]; simp⟩
  obtain ⟨r, hr, -, hrm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (hq.map ψ)
  refine ⟨r, hrm, ?_⟩
  rw [← Polynomial.eval_map, hr, Polynomial.eval_map, h]

theorem isMaximal_comap_maximalIdeal_OO {A : Type*} [CommRing A] (φ : A →+* OO p) :
    ((maximalIdeal (OO p)).comap φ).IsMaximal := by
  have h : ((residue (OO p)).comp φ).IsIntegral := by
    refine RingHom.IsIntegral.tower_top (Int.castRingHom A) _ ?_
    rw [RingHom.ext_int (RingHom.comp _ _) (Int.castRingHom _)]
    exact isIntegral_int_residueField_OO
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' _ h ⊥
  rwa [← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot, ker_residue] at this

theorem isClosed_singleton_cPt {X : Scheme.{0}} (y : Sp (OO p) ⟶ X) : IsClosed ({y (cPt p)} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have hs : y (cPt p) ⤳ w := specializes_iff_mem_closure.2 hw
  obtain ⟨U, hU, hwU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := w) trivial
  have hzU : y (cPt p) ∈ U := hs.mem_open U.isOpen hwU
  have hle : ⊤ ≤ y ⁻¹ᵁ U := (le_preimage_iff y U).2 hzU
  have key : ∀ f : Γ(X, U), y (cPt p) ∈ X.basicOpen f ↔
      f ∉ (maximalIdeal (OO p)).comap (valMap y U hle).hom := fun f => by
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not, ← le_preimage_iff,
      le_preimage_basicOpen_iff y hle, valR_eq y U hle]
  have hm := isMaximal_comap_maximalIdeal_OO (valMap y U hle).hom
  refine (Specializes.antisymm ?_ hs).eq
  rw [specializes_iff_forall_open]
  intro V hV hzV
  obtain ⟨f, hfV, hzf⟩ := hU.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨_, hzV⟩ hzU
  refine hfV ?_
  obtain ⟨g, c, hc, e⟩ := hm.exists_inv ((key f).1 hzf)
  have hwc : w ∉ X.basicOpen c := fun h => (key c).1 (hs.mem_open (X.basicOpen c).isOpen h) hc
  rw [X.mem_basicOpen _ _ hwU] at hwc
  show w ∈ X.basicOpen f
  rw [X.mem_basicOpen _ _ hwU]
  have e' := congrArg (X.presheaf.germ U w hwU).hom e
  rw [map_add, map_mul, map_one] at e'
  rcases isUnit_or_isUnit_of_add_one e' with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd h hwc

theorem isClosed_centre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [Algebra.FiniteType ℤ o]
    (M : RatModel o Ω) (U : Set M.Z) (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
    M.Cen U z y → IsClosed ({z} : Set M.Z) :=
  fun _ _ _ _ _ _ _ _ _ _ _ y h => h.1 ▸ isClosed_singleton_cPt y

end GlobalTheory.ZH
