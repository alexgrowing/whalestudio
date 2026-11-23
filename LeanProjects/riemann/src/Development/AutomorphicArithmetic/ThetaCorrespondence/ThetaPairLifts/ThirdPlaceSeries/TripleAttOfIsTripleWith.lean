import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Triple
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTripleAtOfConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobMatchRho
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobMatchT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkSat

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TripleLocal
end UpperTheory.GalS
namespace GlobalTheory.TripleResidual
open NumberField IsDedekindDomain Polynomial Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open GlobalTheory.TypeLeaf (WildOne FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (OnW IsBaseChange IsGaloisRepOf IsReduction Zbar GaloisReps GalE toFb)
open scoped Pointwise
variable {D : D7} (Y : NTw D.R D.host D.what₂ D.LL0 D.nd)
end GlobalTheory.TripleResidual
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
namespace GlobalTheory.TripleLocal
end GlobalTheory.TripleLocal
namespace GlobalTheory.GoodRowMono
variable {D : D7}
end GlobalTheory.GoodRowMono
end
namespace GlobalTheory.TripleLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleGal
open GlobalTheory.TypeLeaf (FrobDense)
variable {D : D7} {T : WDTie D.nd D.naut} {i : D.ntw.Tw} {j : FractionRing (D.ntw.O0 i) →+* ℂ}
  {ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.ntw.O0 i)} {π : D.naut.CG D.R.r} {s : ℝ}
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Formalism.L2.Host Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.HeightCounting (CharSide)
open GlobalTheory.GalOfCusp GlobalTheory.TripleGal GlobalTheory.Triple
open GlobalTheory.TypeLeaf (FrobDense)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)
open GlobalTheory.JumpDictionaryFoundation (exists_embOver embOver_true_apply)
variable {D : D7} {T : WDTie D.nd D.naut} {C₀ C : CharFrame D} (S : CharSide D C₀)
  {art : Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om} {i : D.ntw.Tw} {s : D.ntw.Sig i}
  {ρ : Reading D.ntw i (D.ntw.side i s)} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))} {ν : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* (D.ntw.O0 i)ˣ}
  {w : D.what₂.places.Pl} {red : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.Zbar (D.ntw.l i) →+* FbAt D w}
theorem triple_att_n_of_is_triple_with (hF : FrobDense D) (hG : UpperTheory.GalS.GalHodgeN D T) (ha : GlobalTheory.HeckeGal.IsGlobalArtin art)
    (hχ : IsChars C art ρ) (h : _root_.GlobalTheory.Triple.IsGaloisTripleWithReduction C art ρ s σ π r ν w red) (S : CharSide D C₀) :
    TripleAttN D.naut (bk0 D) i s := by
  have hsep := fun k w hk => GlobalTheory.GoodRowMono.sep_over_g hG h.good h.param.csd h.param.lab k (w := w) hk
  have hthr : ∀ k w, w ∈ placesOver D.host.E (D.host.g k) → UpperTheory.GalS.thr w D.R.r = 2 := fun k w hk =>
    UpperTheory.GalS.thr_split (D.host.g_prime k) hk (D.nd.g_split k)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega))
  have hR := rowFacts (C := C) (i := i) S h.param (fun v => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact D.naut.unr_mono0 _ (h.param.unr v hv)
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact (UpperTheory.GalS.nc_of_sep T (by rw [D.naut.locG_dim]; exact hthr k v hk) (hsep k v hk)).2.1) (jIdx s)
  have htw : ∀ {ξ : HChar D.host.E} (hξ : ξ.IsUnitary) k v, v ∈ placesOver D.host.E (D.host.g k) → ξ.TameAt v →
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π hξ) v) := fun hξ k v hk ht => by
    rw [twBy, D.naut.locG_tw]
    exact UpperTheory.GalS.nc_of_sep T (by rw [D.naut.lpDim_char _ _ (D.naut.locG_dim _ _), D.naut.locG_dim]; exact hthr k v hk)
      (UpperTheory.GalS.sep_char (GlobalTheory.RowTieLP.main D T) (D.naut.locG_dim _ _)
      (hG.2.2.2 _ S _ v (by rwa [rankOneCuspidal_unitaryChar_equiv_apply_symm])) (UpperTheory.GalS.inePol_coeff_zero T _) (hsep k v hk))
  have tinv : ∀ {ξ : HChar D.host.E} v, ξ.TameAt v → ξ⁻¹.TameAt v := fun v ht x h1 h2 => by
    rw [Formalism.L2.Host.HChar.loc_inv, ht x h1 h2, inv_one]
  have n1 : ∀ v ∈ placesOver D.host.E (D.ntw.l i),
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π C.isEta.unitary.inv) v) := fun v _ => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact .of_unr (hR.unr₁ v hv)
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact htw _ k v hk (tinv v fun x h1 _ => C.isEta.unr v x h1)
  have n2 : ∀ v ∈ placesOver D.host.E (D.ntw.l i),
      UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG (twBy S π (mu_unitary C (D.ntw.l i) (jIdx s))) v) := fun v hl => by
    by_cases hv : ∀ k, v ∉ placesOver D.host.E (D.host.g k)
    · exact .of_unr (hR.unr v hv (by simpa using GlobalTheory.TripleGal.HodgeOfAtt.not_mem_pD D i hl))
    · push Not at hv
      obtain ⟨k, hk⟩ := hv
      exact htw _ k v hk (tinv v (GlobalTheory.MuTameQS.tameAt_mul ((C.isMu0 _).tame v) ((isDelta_delAt C _).tame v)))
  have hφ := (GlobalTheory.GalChar.isEmbedding_toQ (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg).continuous
  have hne : ∀ u : (D.ntw.O0 i)ˣ, GlobalTheory.GalChar.toQ ρ.κ u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
  have s1 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (D.ntw.rhoS i s)) := isSSRep_of_smul _ (fun g => hne (ν g)) h.rho (_root_.UpperTheory.GalS.galW' h.gal).2.1
  have s2 : IsSSRep (mapRep (GlobalTheory.GalChar.toQ ρ.κ) (Tgl i s)) :=
    isSSRep_of_smul _ (fun g => hne (chiS i s g)⁻¹) (fun g => by
      change ((Tgl i s g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map _ = _
      rw [Tgl_coe]
      ext x y
      exact map_mul (GlobalTheory.GalChar.toQ ρ.κ) _ _) s1
  have c2 : Continuous fun g => (Tgl i s g : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) := by
    simp only [Tgl_coe, Tmat]
    exact (Units.continuous_coe_inv.comp (GlobalTheory.GalChar.continuous_units _ (D.ntw.twistCharacterFamily_continuous i _ _))).smul (D.ntw.rhoS_cont i s)
  obtain ⟨c, hc⟩ := GlobalTheory.GalChar.odd_r D.R
  obtain ⟨d, hd⟩ := D.R.t_odd
  have a1 := attN_of_isSSRep_mapRep_of_nc_locG hF hG (twBy_csd S _ h.param.csd (isCSD_inv (GlobalTheory.EtaSelfDual.isCSD_of_isEtaT _ _ _ C.isEta)))
    (twBy_regAlg S _ h.param.ralg (eta_inf C) fun g =>
      ⟨⟨-d - 1, by rw [hd]; push_cast; ring⟩, -d, by rw [hd]; push_cast; ring⟩)
    (D.ntw.rhoS_cont i s) (_root_.GlobalTheory.TripleLocal.frobMatch_rhoS_of_isTripleWith S ha h) hφ ρ.κ_alg (fun _ => rfl) s1 n1
  have a2 := attN_of_isSSRep_mapRep_of_nc_locG hF hG hR.csd
    (twBy_regAlg S _ h.param.ralg (mu_inf C _ (jIdx s)) fun g => by
      obtain ⟨z, hz⟩ := eExp_int (jIdx s) g
      exact ⟨⟨z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩, -z + c - d, by rw [hz, hc, hd]; push_cast; ring⟩)
    c2 (_root_.GlobalTheory.TripleLocal.frobMatch_Tgl_of_isTripleWith S ha hχ h) hφ ρ.κ_alg (fun _ => rfl) s2 n2
  refine ⟨_, _, _, ?_, ?_, hR, _root_.GlobalTheory.TripleLocal.hkSat_of_isTripleWith S h⟩
  · convert a1 using 1
    ring
  · convert a2 using 1
    ring
end
end GlobalTheory.TripleLocal
end
end
