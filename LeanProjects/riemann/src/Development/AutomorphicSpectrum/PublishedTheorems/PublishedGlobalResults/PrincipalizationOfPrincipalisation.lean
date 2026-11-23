import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

def ResolutionAndPrincipalisationCharZero : Prop := ResolutionCharZero ∧ PrincipalisationCharZero

def ResK : Prop := ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement

def IsSncIdeal {Y : Scheme.{0}} (I : Y.IdealSheafData) : Prop :=
  ∀ y : Y, ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (n : ℕ) (z : Fin n → Γ(Y, V.1)) (a : Fin n → ℕ),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n (fun i => Y.presheaf.germ V.1 y hy (z i)) ∧
      I.ideal V = Ideal.span {∏ i, z i ^ a i}

def ProjResolution : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (X : Scheme.{0}) (g : X ⟶ Sp K) [LocallyOfFinitePresentation g],
    IsIntegral X → IsProjOver g →
    ∃ (X' : Scheme.{0}) (f : X' ⟶ X),
      Smooth (f ≫ g) ∧ IsProjOver (f ≫ g) ∧ IsIso (f ∣_ g.smoothLocus) ∧
        Dense ((f ⁻¹ᵁ g.smoothLocus : X'.Opens) : Set X')

def Principalization : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (I : Y.IdealSheafData),
    IsIntegral Y → Smooth g → IsProjOver g → I ≠ ⊥ →
    ∃ (Y' : Scheme.{0}) (f : Y' ⟶ Y),
      Smooth (f ≫ g) ∧ IsProjOver (f ≫ g) ∧ IsIso (f ∣_ I.support.compl) ∧ IsSncIdeal (I.comap f)

theorem exists_closed_in_prod {K : Type} [Field K] {M : ℕ} {X' : Scheme.{0}} (h : X' ⟶ PSpace K M)
    (hp : IsProjOver (h ≫ PSpace.str K M)) :
    ∃ (r : ℕ) (j : X' ⟶ pullback (PSpace.str K M) (PSpace.str K r)),
      IsClosedImmersion j ∧ h = j ≫ pullback.fst _ _ := by
  obtain ⟨r, e, he, hc⟩ := hp
  have hs : IsSeparated (PSpace.str K M) := by
    unfold PSpace.str
    infer_instance
  refine ⟨r, pullback.lift h e hc.symm, ?_, (pullback.lift_fst _ _ _).symm⟩
  have h1 : IsClosedImmersion (pullback.lift h e hc.symm ≫ pullback.snd (PSpace.str K M) (PSpace.str K r)) := by
    rw [pullback.lift_snd]; exact he
  exact IsClosedImmersion.of_comp _ (pullback.snd (PSpace.str K M) (PSpace.str K r))

theorem dense_compl_of_snc {Y : Scheme.{0}} (T : TopologicalSpace.Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T)) : Dense (T : Set Y)ᶜ := by
  rw [← interior_eq_empty_iff_dense_compl, Set.eq_empty_iff_forall_notMem]
  intro y hyT
  obtain ⟨hreg, U, hy, n, f, J, hrsp, hI⟩ := h y
  have hdom : IsDomain (Y.presheaf.stalk y) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  obtain ⟨V, hV, hyV, e⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y ∈ U.1 ⊓ ⟨interior (T : Set Y), isOpen_interior⟩ from ⟨hy, hyT⟩)
  have hVU : V ≤ U.1 := e.trans inf_le_left
  have hnil : IsNilpotent (Y.presheaf.map (homOfLE hVU).op (∏ i ∈ J, f i)) := by
    rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hV.isCompact, Scheme.basicOpen_res, eq_bot_iff]
    rintro z ⟨hzV, hz⟩
    have h1 : z ∈ (Scheme.IdealSheafData.vanishingIdeal T).support := by
      rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact interior_subset (e hzV).2
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (hVU hzV), hI, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at h1
    exact (h1 hz).elim
  have h2 := (hnil.map (Y.presheaf.germ V y hyV).hom).eq_zero
  rw [TopCat.Presheaf.germ_res_apply, map_prod] at h2
  exact Finset.prod_ne_zero_iff.2 (fun i _ => (prime_of_regular_params _ hrsp.1 hrsp.2 i).ne_zero) h2

end GlobalTheory.CompanionTheory.Hypotheses₂
