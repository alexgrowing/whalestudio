import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.RedNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.GoodDelta
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LatDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.OrbTransfer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Derive
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MemTwCentConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.NormInj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbIdEqZeroOfForall

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.DZA GlobalTheory.LBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem twOrb_twConj' {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G)
    (K : Subgroup G) (δ g : G) (f : G → ℂ) :
    GlobalTheory.BCT.twOrb θ K (g⁻¹ * δ * θ g) f = GlobalTheory.BCT.twOrb θ K δ f := by
  rw [GlobalTheory.TwOrbConj.twOrb_eq, GlobalTheory.TwOrbConj.twOrb_eq,
    ← finsum_comp_equiv (GlobalTheory.TwOrbConj.dcEquiv θ K δ g)
      (f := fun x => GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out x))]
  refine finsum_congr fun q => ?_
  rw [GlobalTheory.TwOrbConj.summand_twist]
  have h : DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (g * Quotient.out q) =
      DoubleCoset.mk (GlobalTheory.BCT.twCent θ δ) K (Quotient.out (GlobalTheory.TwOrbConj.dcEquiv θ K δ g q)) := by
    rw [DoubleCoset.out_eq']
    rfl
  obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1 h
  show _ = GlobalTheory.TwOrbConj.summand θ K δ f (Quotient.out (GlobalTheory.TwOrbConj.dcEquiv θ K δ g q))
  rw [he, GlobalTheory.TwOrbConj.summand_rep θ K δ f _ ht hk]

theorem inflMatch : GlobalTheory.DZA.InflMatching := by
  unfold GlobalTheory.DZA.InflMatching
  intro k K _ _ _ _ _ _ _ _ _ hcont hchar F F' _ _ _ _ _ hdeg rk rK hk hK hinc s sb hgal hfrob n fb hfb
  have hres : IsRes rk rK s sb := ⟨hdeg, hk, hK, hinc, hgal, hfrob⟩
  obtain ⟨hVE, hFD, hGal⟩ := derive k K hcont F F' rk rK s sb hres
  have hgen := (frobFacts k K F F' rk rK s sb hres).1
  obtain ⟨hR1, hR2, hR3, hR4, hR5⟩ := redNorm k K F F' rk rK s sb hres n
  obtain ⟨hval, hinvφ⟩ := hR5 fb hfb
  obtain ⟨-, -, -, -, -, hIK⟩ := inflFacts K F' rK hK n
  obtain ⟨-, -, -, -, -, hIk⟩ := inflFacts k F rk hk n
  have suppK : ∀ x : GL (Fin n) K, infl rK (normLift sb fb) x ≠ 0 → x ∈ KO K n :=
    fun x hx => (hIK (normLift sb fb)).2.2 x hx
  have suppk : ∀ x : GL (Fin n) k, infl rk fb x ≠ 0 → x ∈ KO k n :=
    fun x hx => (hIk fb).2.2 x hx
  obtain ⟨hgalAct, hnorm, hcent, hcentr, -, hD6⟩ := dict k K s hgen n
  have hIntF : ∀ (γ x : GL (Fin n) k), infl rk fb (x⁻¹ * γ * x) ≠ 0 → IntEl γ := by
    intro γ x hx
    have h1 := (hR1 _).2 (suppk _ hx)
    rw [map_mul, map_mul, map_inv] at h1
    exact hR4 γ (incl K n x) h1
  refine ⟨fun δ hsep γ hcp => ?_, fun γ _ hne => ?_⟩
  · have hreg : PositivityTheory.Rg.Tf.Loc.IsRegSemisimple γ := by
      have hs : (Polynomial.map (algebraMap k K) (γ : Matrix (Fin n) (Fin n) k).charpoly).Separable :=
        hcp ▸ hsep
      exact (Polynomial.separable_map _).1 hs
    have hnormOf : PositivityTheory.Rg.Tf.Loc.IsNormOf s δ γ :=
      hD6 δ γ hreg (by rw [← hnorm δ]; exact hcp)
    obtain ⟨h, hh⟩ := hnormOf
    by_cases hint : IntEl γ
    · obtain ⟨δ₀, hδ₀N, -, hδ₀K⟩ := goodDelta k K F F' rk rK s sb hres n γ hint
      have hN0 : PositivityTheory.Rg.Tf.Loc.IsNormOf s δ₀ γ :=
        ⟨1, by rw [← hnorm δ₀, hδ₀N, one_mul, inv_one, mul_one]; rfl⟩
      obtain ⟨y, hy⟩ := UpperTheory.ConvolutionTheory.Loc.normInj k K s hgen n γ hreg δ₀ δ hN0 ⟨h, hh⟩
      have e1 : δ = y⁻¹ * δ₀ * (galAct s n) y := by
        rw [hy, hgalAct]
        rfl
      rw [e1, twOrb_twConj']
      have hTC := (UpperTheory.V.Z.Tf.Orb.twCentImg_holds k K s hgen n δ₀ γ hreg
        (by rw [← hnorm δ₀, hδ₀N]; rfl)).2
      rw [hcent δ₀, hcentr γ] at hTC
      refine orbTransfer (GL (Fin n) K) (GL (Fin n) k) (incl K n)
        (by exact UpperTheory.V.Z.Tf.Orb.inclClosed_holds k K n) (galAct s n) (KO K n) (KO k n) hR1 δ₀ γ
        (by rw [hgalAct]; exact hTC) _ _ (fun κ hκ y => hinvφ κ hκ y) ?_ ?_ (fun h => galAct_incl s h)
      · intro x hx
        have hβ := suppK _ hx
        have hNβ := hR2 _ hβ
        rw [hR3, hδ₀N] at hNβ
        have h2 := hδ₀K x hNβ
        apply latDesc k K F F' rk rK s sb hres n x
        have e2 : x⁻¹ * (galAct s n) x = (x⁻¹ * δ₀ * x)⁻¹ * (x⁻¹ * δ₀ * (galAct s n) x) := by group
        rw [e2]
        exact mul_mem (inv_mem h2) hβ
      · intro h
        rw [galAct_incl]
        have eN : GlobalTheory.LBC.norm k s ((incl K n h)⁻¹ * δ₀ * incl K n h) = incl K n (h⁻¹ * γ * h) := by
          have e3 := hR3 δ₀ (incl K n h)
          rw [galAct_incl] at e3
          rw [e3, hδ₀N, map_mul, map_mul, map_inv]
        by_cases hm : (incl K n h)⁻¹ * δ₀ * incl K n h ∈ KO K n
        · exact hval _ hm _ eN
        · have h0 : infl rK (normLift sb fb) ((incl K n h)⁻¹ * δ₀ * incl K n h) = 0 := by
            by_contra hc
            exact hm (suppK _ hc)
          have h1 : infl rk fb (h⁻¹ * γ * h) = 0 := by
            by_contra hc
            have hx := (hR1 _).2 (suppk _ hc)
            rw [map_mul, map_mul, map_inv] at hx
            exact hm (hδ₀K _ hx)
          rw [h0, h1]
    · have hL : GlobalTheory.BCT.twOrb (galAct s n) (KO K n) δ (infl rK (normLift sb fb)) = 0 := by
        refine GlobalTheory.DZA.OrbSupp.twOrb_eq_zero_of_forall _ _ _ _ fun x => ?_
        by_contra hc
        apply hint
        have hNβ := hR2 _ (suppK _ hc)
        rw [hR3, hnorm δ, hh] at hNβ
        change x⁻¹ * (h * incl K n γ * h⁻¹) * x ∈ KO K n at hNβ
        apply hR4 γ (h⁻¹ * x)
        have e4 : (h⁻¹ * x)⁻¹ * incl K n γ * (h⁻¹ * x) = x⁻¹ * (h * incl K n γ * h⁻¹) * x := by group
        rw [e4]
        exact hNβ
      have hR : GlobalTheory.BCT.twOrb (MonoidHom.id (GL (Fin n) k)) (KO k n) γ (infl rk fb) = 0 :=
        GlobalTheory.DZA.OrbSupp.twOrb_id_eq_zero_of_forall _ _ _ fun x => by
          by_contra hc
          exact hint (hIntF γ x hc)
      rw [hL, hR]
  · obtain ⟨x, hx⟩ := GlobalTheory.DZA.OrbSupp.exists_conj_ne_zero _ _ _ hne
    obtain ⟨δ₀, hδ₀N, -, -⟩ := goodDelta k K F F' rk rK s sb hres n γ (hIntF γ x hx)
    refine ⟨δ₀, ?_⟩
    rw [hδ₀N]
    exact (Matrix.charpoly_map (γ : Matrix (Fin n) (Fin n) k) (algebraMap k K)).symm

end UpperTheory.Gal.InertialTypesAlt.L
