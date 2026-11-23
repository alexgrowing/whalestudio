import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOrIsEmptySubschemeOfPrimeChartsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineBaseChangeOverFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChartStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

namespace GlobalTheory

theorem GenericMember.isIntegral_or_isEmpty_zeroScheme : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → ∀ (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec), ⨆ i, nonzeroLocus (b i) = ⊤ → ∃ t : (L.pull π).Sec, t ≠ 0 ∧ (IsIntegral (secIdeal (LB.isLB_pull hL π) t).subscheme ∨ IsEmpty (secIdeal (LB.isLB_pull hL π) t).subscheme) := by
  intro k _ N X X' _ _ f f' π hP L hL b hb

  have loc : ∀ x : X, ∃ (V : X.Opens) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N),
      IsAffineOpen V ∧ x ∈ V ∧ IsUnit (resG X hVc ((b j).f c)) := by
    intro x
    have hx : x ∈ (⨆ i, nonzeroLocus (b i)) := hb.ge (Set.mem_univ x)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hx
    obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hj
    obtain ⟨V, hVa, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hc
    have hVc : V ≤ L.U c := hVle.trans (X.basicOpen_le _)
    refine ⟨V, c, hVc, j, hVa, hxV, ?_⟩
    have h1 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((b j).f c)
    have h2 := h1.map (X.presheaf.map (homOfLE hVle).op).hom
    convert h2 using 1
    simp only [resG]
    erw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  choose V c hVc j hVa hxV hu using loc
  have hW : ∀ x, IsAffineOpen (π ⁻¹ᵁ V x) := fun x => (GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)).1
  have key : ∀ x, (genSec k N f' π L b).f (fun _ => c x) ≠ 0 ∧
      ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩ = ⊤ ∨
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).IsPrime ∧
        ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V x, hW x⟩).comap
          (π.app (V x)).hom = ⊥) := fun x => by
    obtain ⟨-, e, he1, he2⟩ := GlobalTheory.T.affine_base_change_over_field_extension k _ X X' f f' π hP (V x) (hVa x)
    exact GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart k N X X' f f' π L hL b (V x) ⟨x, hxV x⟩ (hW x) (c x) (hVc x) (j x) (hu x) e he1 he2
  refine ⟨genSec k N f' π L b, fun h0 => ?_, ?_⟩
  · obtain ⟨x⟩ := (inferInstance : Nonempty X)
    exact (key x).1 (by rw [h0]; rfl)
  · refine GlobalTheory.T.isIntegral_or_isEmpty_subscheme_of_prime_charts X' _ X (fun x => ⟨π ⁻¹ᵁ V x, hW x⟩) ?_ (fun x => ?_) (fun x y hx hy => ?_)
    · refine eq_top_iff.2 fun z _ => Opens.mem_iSup.2 ⟨π z, hxV (π z)⟩
    · rcases (key x).2 with h | h
      · exact Or.inl h
      · exact Or.inr h.1
    · rcases (key x).2 with h | h
      · exact absurd h hx.ne_top
      · have hg := GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint X X' π (V x) (hVa x) (hW x) _ hx h.2
        show π _ ∈ V y
        rw [hg]
        exact (genericPoint_spec X).mem_open_set_iff (V y).isOpen |>.2 ⟨y, trivial, hxV y⟩

end GlobalTheory
