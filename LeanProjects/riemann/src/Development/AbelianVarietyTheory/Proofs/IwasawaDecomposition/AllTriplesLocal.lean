import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescentMapNonzeroOfSmallFieldFormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLocalHomOfNatCast
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodRowsSameEigenvaluesSameFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRhoOfRowOfFrobeniusEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlaceDataStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem exists_sig_of_row (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hOcc : EigOcc D S θ hL Sb eig) (hall : D.nexp.sig_all) (i : D.ntw.Tw) (b : Bool) (j : ℕ) (h1 : 1 ≤ j)
    (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (hiso : D.what₂.isot j σ ≠ ⊥) (hgood : D.nd.goodRow σ) :
    ∃ s : D.ntw.Sig i, D.ntw.jS i s = j ∧ D.ntw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P →
      P ∉ D.ntw.S0 i → eig j (Bs.rowS i s) k P = eig j σ k P := by
  classical
  obtain ⟨x, hxg, hx0, hxe⟩ := hOcc j h1 h2 σ hiso hgood
  obtain ⟨Φ, hΦ0, hΦs, hΦT⟩ := GlobalTheory.T.exists_descent_map_nonzero_of_small_field_form D S _ (hKs _ h1 h2) i b x hx0
  set e := Bs.eF i j b h1 h2 with he
  have hfix : MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b))
      (G0g D.nd) (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) (D.nexp.eAlg i b)
      (e.symm (Φ x)) = e.symm (Φ x) := by
    letI : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
    have hx1 := Module.End.mem_eigenspace_iff.1 (Submodule.mem_inf.1 hxg).1
    rw [one_smul, finsum_eq_sum_of_fintype, LinearMap.sum_apply] at hx1
    apply e.injective
    rw [MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intros; simp), LinearMap.sum_apply,
      map_sum, e.apply_symm_apply]
    conv_rhs => rw [← hx1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, hΦs, D.nexp.eAlg_def]
    change readLL0 S i _ (D.nexp.eLL0 g) • e (D.nexp.actG i _ _ g (e.symm (Φ x))) = _
    rw [Bs.act i _ _ h1 h2 g, e.apply_symm_apply]
    congr 1
    have hc : ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ =
        (((chiL S _ (Bs.chiL _ h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) := by
      simp [chiL]
    change _ = Φ (((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹ •
      (S.A j).ρ (S.eG.symm g) x)
    rw [hc, hΦs, hΦT _ (Bs.rho _ h1 h2 (S.eG.symm g)), map_inv₀]
    rfl
  have hhk : ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      D.nexp.hkF i j b k P (e.symm (Φ x)) =
        (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
          (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P))) • e.symm (Φ x) := by
    intro k P hk1 hk2 hsp hP
    apply e.injective
    rw [Bs.hkEq i _ _ h1 h2 k P _ hP hsp hk2, e.apply_symm_apply, map_smul, e.apply_symm_apply]
    have h3 := hΦT (hL j k P) (Bs.hs _ h1 h2 k P) x
    rw [hxe k P hk1 hk2 hsp (fun h => hP (hSb i h)), hΦs] at h3
    rw [mul_smul]
    congr 1
    exact h3.symm
  obtain ⟨s, hj, hb, hs⟩ := hall i j b (e.symm (Φ x))
    (fun k P => algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i b P : D.ntw.O i) ^ k *
      (show FractionRing (D.ntw.O i) from readLL0 S i b (eig j σ k P)))
    (by simpa using hΦ0) hfix hhk
  refine ⟨s, hj, hb, fun k P hk1 hk2 hsp hP => ?_⟩
  have h3 := hs k P hk1 hk2 hsp hP
  rw [Bs.rowS_eig i s k P hk1 hk2 hsp hP] at h3
  subst hj hb
  have hu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (Bs.cHk i (D.ntw.side i s) P : D.ntw.O i) ^ k ≠ 0 := by
    refine pow_ne_zero _ ?_
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact (Bs.cHk i (D.ntw.side i s) P).ne_zero
  exact (readLL0 S i (D.ntw.side i s)).injective (mul_left_cancel₀ (M₀ := FractionRing (D.ntw.O i)) hu h3)

end GlobalTheory.RowTriple

namespace GlobalTheory.RowTriple

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem tripAll_of_sideB (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ)
    (Sb : Finset (PlE D.host)) (hSb : ∀ i, Sb ⊆ D.ntw.S0 i) (hKs : ∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm)
    (hT : EigTrue D cf Rw Sb eig) (hOcc : EigOcc D S θ hL Sb eig) (hP : GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw)
    (hall : D.nexp.sig_all) (hloc : ∀ a σ v, IsSplitPl D.host v → D.naut.locW a σ v = Rw.locR σ v)
    (hR : ∀ a, ReadTw D a) : GlobalTheory.IndefiniteRowSideFullHecke.TwistedTriples.TripAll D := by
  classical
  intro a σ hσ
  obtain ⟨hiso, hgood⟩ := hσ
  obtain ⟨h1, h2⟩ := D.nd.j_range a
  obtain ⟨s, hj, hb, he⟩ := exists_sig_of_row D cf Rw low Pq S hL eig θ Bs Sb hSb hKs hOcc hall (D.ntw.twOf a)
    (D.ntw.twSide a) (D.nd.j a) h1 h2 σ hiso hgood
  obtain ⟨hiso', hgood', -⟩ := Bs.rhoS _ s
  rw [hj] at hiso'
  refine ⟨s, hj, hb, GlobalTheory.T.isRhoOfRow_of_frobenius_eigenvalues D Rw Bs.rowS Bs.rhoS hP a σ s (hR a) hb hj ⟨hiso, hgood⟩ (hloc a σ) ?_⟩
  have hfin : ((Sb ∪ D.ntw.S0 (D.ntw.twOf a) : Finset (PlE D.host)) : Set (PlE D.host)).Finite := Finset.finite_toSet _
  filter_upwards [hfin.compl_mem_cofinite] with P hP' hsp
  have hP1 : P ∉ Sb := fun h => hP' (by simp [h])
  have hP2 : P ∉ D.ntw.S0 (D.ntw.twOf a) := fun h => hP' (by simp [h])
  exact GlobalTheory.T.good_rows_same_eigenvalues_same_frobenius D cf Rw Sb eig hT hP (D.nd.j a) h1 h2 σ (Bs.rowS _ s) hiso hgood hiso' hgood' P hsp hP1
    fun k hk1 hk2 => he k P hk1 hk2 hsp hP2

theorem allTriples_atMem : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c => GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.AllTriples (w.D Z) := by
  intro hP hS hL
  refine GlobalTheory.HeightCounting.Up.Model.AtMem.imp (GlobalTheory.T.galois_family_place_data hP hS hL) fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨cf, Rw, low, Pq, S, hL', eig, θ, Bs, Sb, hSb, hKs, hT, hOcc, hcp, hall, hloc, hR⟩ := h
  exact GlobalTheory.TwistedSelmerCompare.allTriples_of_tripAll _
    (tripAll_of_sideB _ cf Rw low Pq S hL' eig θ Bs Sb hSb hKs hT hOcc hcp hall hloc hR)

end GlobalTheory.RowTriple

end
