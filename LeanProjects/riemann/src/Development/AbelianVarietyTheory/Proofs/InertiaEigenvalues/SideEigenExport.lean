import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstTwistCharactersEqLadicCharactersAllReadingsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTripleEigenvectorInGoodPartStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallRingElemOfFractionMapIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyFinOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isInv_twGL_iff {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (W : Submodule K (Fin a → K)) : IsInv (twGL χ r) W ↔ IsInv r W := by
  constructor
  · intro h g v hv
    have := W.smul_mem (((χ g)⁻¹ : Kˣ) : K) (h g v hv)
    rwa [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_smul] at this
  · intro h g v hv
    rw [GlobalTheory.TwistAbove.twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem isSSRep_twGL {Γ K : Type} [Group Γ] [Field K] {a : ℕ} (χ : Γ →* Kˣ) (r : Γ →* GL (Fin a) K)
    (h : IsSSRep r) : IsSSRep (twGL χ r) := fun W hW =>
  let ⟨W', h1, h2⟩ := h W ((isInv_twGL_iff χ r W).1 hW)
  ⟨W', (isInv_twGL_iff χ r W').2 h1, h2⟩

variable {D : D7} {C : CharFrame D} {art : Neutral.B1.Ideles D.host.E →* GlobalTheory.HeckeGal.Gab D.host.E D.nd.Om}

theorem isRepOf_twist (ha : GlobalTheory.HeckeGal.IsGlobalArtin art) (hCS : CharSide D C) {i : D.ntw.Tw} {b : Bool}
    (ρ : Reading D.ntw i b) {π : D.naut.CG D.R.r} {r : GalE D →* GL (Fin D.R.r) (Qbar (D.ntw.l i))}
    (hr : IsGaloisRepOf D π (D.ntw.l i) ρ.ι r) {ν : GalE D →* (D.ntw.O0 i)ˣ} {n : _}
    (hν : IsGal art ρ.κ ρ.ι (shiftChar C) n ν) :
    IsRepOf D (D.ntw.l i) ρ.ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) (twGL (inQ ρ.κ ν) r) := by
  refine ⟨(Units.continuous_val.comp (hν.cont (D.ntw.twistBaseCoefficientRing_isAdic i) ρ.κ_alg)).smul hr.1,
    isSSRep_twGL _ _ hr.2.1, ?_⟩
  have hfin := Formalism.L2.NR.placesOver_finite D.host.E (D.ntw.l i) (D.ntw.lPrime i).out.ne_zero
  filter_upwards [D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hu hwl
  intro B σ hB hσ
  have hl : w ∉ placesOver D.host.E (D.ntw.l i) := hwl
  have e1 := (hr.2.2 w hl).2.2 hu B σ hB hσ
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e2 := hν.frob ha (Or.inl hl) (shiftChar_unr C w) hB hσ

  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hfe : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {((C.eta.val w : ℂˣ) : ℂ)} := by
    rw [hCS.frob _ w ((hCS.unr_iff _ w).1 hue), hCS.etaTinv, HChar.val_inv, inv_inv]
  have hd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ w
  have hM : ((((twGL (inQ ρ.κ ν) r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))).map ρ.ι.toRingHom) =
      ρ.ι (toQ ρ.κ ((ν σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) •
        ((r σ : GL (Fin D.R.r) (Qbar (D.ntw.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i))).map
          ρ.ι.toRingHom := by
    ext x y
    simp [GlobalTheory.TwistAbove.twGL_val, GlobalTheory.GalChar.inQ_val]
  rw [← Matrix.charpoly_map, hM, charpoly_smul_of_prod _ _ _ e1, galPol, D.naut.locG_tw,
    D.naut.frobEig_tw _ _ (D.naut.unr_char _ _ hd hu hue), D.naut.frobEig_char _ _ _ hu hue hd hfe]
  simp only [Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
  simp only [Function.comp_apply]
  congr 2
  rw [e2, shiftChar_val]
  have hq := normV_ne_zero (D := D) w
  have h0 := (C.eta.val w).ne_zero
  have e3 : ((D.R.nV : ℕ) : ℝ) = (D.R.r : ℝ) + (D.R.t : ℝ) := by
    rw [show D.R.nV = D.R.r + D.R.t from rfl]; push_cast; ring
  have e4 : ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.nV : ℝ)) / 2 : ℝ)) : ℂ) =
      ((normV w : ℕ) : ℂ) ^ ((((1 - (D.R.r : ℝ)) / 2 : ℝ)) : ℂ) *
        (((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) / 2 : ℝ)) : ℂ))⁻¹ := by
    rw [← Complex.cpow_neg, ← Complex.cpow_add _ _ hq, e3]
    congr 1
    push_cast
    ring
  rw [e4, mul_inv, inv_inv]
  ring

end GlobalTheory.TripInhab

namespace GlobalTheory.TripInhab

open GlobalTheory.Triple GlobalTheory.EigTie
open GlobalTheory.GalChar (IsGal toQ inQ)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf GalE)
open GlobalTheory.TwistAbove (twGL)

theorem isTriple_of_sideB : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → (∀ j, 1 ≤ j → j ≤ D.R.m → (S.A j).IsKsForm) → ChiTOk D cf → GrpSide D → CharSide D cf → ValLL0 D cf → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → EigTrue D cf Rw Sb eig → EigOcc D S θ hL Sb eig → RowParam D Rw → GlobalTheory.EigTie.ResTied D Rw → GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D → D.nexp.sig_all → GlobalTheory.Triple.IsTriple D := by
  intro hCheb hArt D cf Rw low Pq S hL eig θ Bs Sb hSb hks hT hG hCS hV hroot hstar hET hEO hRP hRT hGR hall
  obtain ⟨art, ha⟩ := hArt D.host.E D.nd.Om
  refine ⟨cf, art, ha, fun i hi b => ?_,
    fun i _ s => GlobalTheory.T.twistTriple_eigenvector_in_good_part D cf Rw low Pq S hL eig θ Bs Sb hSb hks hEO i s, hall⟩
  obtain ⟨ρ, w, red, hind, hres⟩ := hRT.exists_reading hstar hi b
  have hc : IsChars cf art ρ := GlobalTheory.T.firstTwistCharacters_eq_ladic_characters_allReadings hCheb hArt D cf Rw low Pq S hL eig θ Bs hT hG hCS hV hroot art ha i b ρ
  refine ⟨ρ, hc, fun s hs => ?_⟩
  subst hs
  obtain ⟨hocc, hgood, hspec⟩ := Bs.rhoS i s
  obtain ⟨π, hpar⟩ := hRP _ (D.ntw.jS_range i s).1 (D.ntw.jS_range i s).2 _ hocc hgood
  obtain ⟨r, hr⟩ := hGR π hpar.1.csd hpar.1.ralg (D.ntw.l i) ρ.ι
  obtain ⟨ν, n, hν⟩ := exists_shift ha hV ρ
  have hR1 := hspec π hpar.1.csd hpar.1.ralg hpar.2 ρ.κ ρ.ι ρ.κ_alg (fun x => ρ.read x)
  have hR2 := isRepOf_twist ha hCS ρ hr hν
  obtain ⟨A, hA⟩ := GlobalTheory.HeightCounting.FitRho.conj_of_isRepOf D ρ.ι _ _ (GlobalTheory.ChebSplitDense.chebSplit_nd hCheb D) _ _ hR1 hR2
  have hhk := GlobalTheory.TwInputs.HEig.hEig_eq_heckeVal D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hpar
  refine isTripleAt_of_conj hgood hocc hpar.1 hr ⟨n, hν⟩ A (fun g => ?_) hhk hind
    (hres.2.2 _ π r hgood ⟨_, (D.ntw.jS_range i s).1, (D.ntw.jS_range i s).2, hocc⟩ hpar hr)
  have := congrArg (fun M : GL (Fin D.R.r) (Qbar (D.ntw.l i)) => (M : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.ntw.l i)))) (hA g)
  simp only [Units.val_mul, GlobalTheory.TwistAbove.twGL_val, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [Units.val_mul, Units.val_mul]
  exact this

end GlobalTheory.TripInhab

end
