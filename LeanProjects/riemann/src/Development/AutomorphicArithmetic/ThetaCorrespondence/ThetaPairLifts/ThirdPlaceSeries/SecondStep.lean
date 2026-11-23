import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCuspMultiplicityInput
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpecStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeightsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAllStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SigDataExistsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevDatumFormsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkBCharpolySplitsStatement

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
attribute [local instance] algKkT
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem second_step_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw) (In : RatIn D S) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)), MtInput D M tup Q → (∀ v, NG.OverPl (Pq v) v) → GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ∃ c0 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T), (∀ (l : ℕ) [Fact l.Prime] j, (c0 l j).1 ≤ (b0 l j).1) → In.Sb ⊆ Sx → (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) → (∀ p ∈ low, placesOver D.host.E p ⊆ ↑Sx) → ∃ (F : TwF T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw A.bare F (TwL.empty T))) (h0 : _), (∀ i j b, (ex.Bsup i j b).FG ∧ Submodule.span (FractionRing ((T.ntw A.bare F (TwL.empty T)).O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) ∧ ∀ th, Nonempty (SideB (⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row A.row) low Pq ((⟨T.ntw A.bare F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) In.hL In.eig In.θ) := by
  intro hGAR D cf jE A S In low Pq M tup Q hM hPq hGal hRC hCh hstar hexp hsplit
  obtain ⟨c1, hc1⟩ := _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt hGAR D cf jE A hGal hRC hCh hstar
  obtain ⟨c2, hc2⟩ := _root_.GlobalTheory.T.exists_weight_data_integral_alt hGAR D cf jE A hstar hexp
  refine ⟨fun l _ j => ⟨(c1 l j).1 ⊔ (c2 l j).1, by haveI := (c1 l j).2; haveI := (c2 l j).2; infer_instance⟩,
    fun b0 b1 Sx T Sp hc0 hSb hconj hlow => ?_⟩
  have hb1 : ∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_left (hc0 l j)
  have hb2 : ∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1 := fun l _ j => le_trans le_sup_right (hc0 l j)
  obtain ⟨rho, hrho, hrhoS⟩ := hc1 b0 b1 Sx T Sp hb1
  obtain ⟨wt, hwt⟩ := hc2 b0 b1 Sx T Sp hb2
  have hfg := GlobalTheory.T.twisted_lattice_finitely_generated_spanning D S In T
  have hfg' : ∀ i j b, (BsupT D T S i j b).FG := fun i j b => (hfg i j b).1
  have hst := _root_.GlobalTheory.T.hkStab_of_subset_of_star_closed D cf jE A S In b0 b1 Sx T Sp hSb hstar
  obtain ⟨sd, hsd1, hsd2, hsd3, hsd4, hsd5⟩ := _root_.GlobalTheory.T.exists_signature_data_span_alt D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  have he := GlobalTheory.T.isCentralGroupAlgebraIdempotent_universal D
  have hpsi := GlobalTheory.T.genericUnipotentCharacterAtSide_eq_thetaSide D S In T hstar
  refine ⟨mkF D T S In hfg' hst sd rho hrho, mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq,
    fun i j b => hfg i j b, fun th => ⟨?_⟩⟩
  let N : TwNew D := ⟨T.ntw A.bare (mkF D T S In hfg' hst sd rho hrho) (TwL.empty T),
    mkEx D T S In A.bare hfg' hst sd rho hrho he Pq wt, D.nStage_trivialCharacter_coeff_eq, th, Sp.br, Sp.br_ind⟩
  have hU := tied_U_clauses N.toD7 (fun (i : T.Tw) k => (Units.map (readT D T i true).toMonoidHom).comp (In.θ k))
    (fun _ => xiRedNZ N.toD7) (fun h i k => hpsi.2 h i k) rfl (fun i b u => hpsi.1 i b u)
  have hLev : ∀ (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
      (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ), 1 ≤ j → j ≤ D.R.m → NX.AdmTw N.toD7 i k Q ψ →
      ∃ L : LevT D T i k, LevLawsT D T Pq In.θ i j b k Q ψ L ∧
        FiniteDimensional (FractionRing (T.Ok i k))
          ↥(NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k) L.J L.χ) :=
    fun i j b k Q ψ h1 h2 hadm => _root_.GlobalTheory.T.places_over_real_subfield_split_alt hGAR D cf jE A S In Pq b0 b1 Sx T Sp hPq hsplit wt
      (fun i j b h1 h2 => ⟨(hwt i j b h1 h2).1, (hwt i j b h1 h2).2.1⟩) A.bare (mkF D T S In hfg' hst sd rho hrho)
      i j b k Q ψ h1 h2 hadm.1 hadm.2.1 hadm.2.2.1 hadm.2.2.2.1 hadm.2.2.2.2.1 hadm.2.2.2.2.2
  let E : NExpTied N.toD7 :=
    { U_eq := hU.1
      psiU_gen := hU.2.1
      psiU_side := hU.2.2.1
      psiU_xi := hU.2.2.2
      delU_cont := fun (i : T.Tw) Q M => (GlobalTheory.GalChar.universal_anticyclotomic_character_laws D.host T.cc (T.l i)).2.2.2.1 Q M
      delU_ine := fun i Q M hQ P hP =>
        GlobalTheory.T.inertia_surjective_of_admQ hGAR D cf b0 b1 Sx T Sp A.bare (mkF D T S In hfg' hst sd rho hrho) i Q M hQ P hP
      thU_empty := fun i j b M d => PEmpty.elim d
      sgnT := 1
      sgnT_one := rfl
      Wt := wt.Wt
      acgWt := fun (i : T.Tw) j b => wt.acg i j b
      modWt := fun (i : T.Tw) j b => wt.mod i j b
      fdWt := fun (i : T.Tw) j b => wt.fd i j b
      rhoW := fun (i : T.Tw) j b => wt.rhoW i j b
      rhoW_irr := fun i j b h1 h2 => (hwt i j b h1 h2).1
      rhoW_alg := fun i j b h1 h2 => (hwt i j b h1 h2).2.1
      tauG := fun (i : T.Tw) j b kv => tauT D T i j b kv
      sgnG := 1
      sgnG_one := rfl
      tau_galois_first_character := fun (i : T.Tw) j b kv x u h1 h2 hl hu => by
        have h := GlobalTheory.T.hasTameBlockCharacter_typePlace_not_over_l hGAR D cf b0 b1 Sx T Sp i j b kv h1 h2 hl
        show ((tauT D T i j b kv x : (FractionRing (T.O i))ˣ) : FractionRing (T.O i)) =
          baseCoeffToFractionRing D T i (NX.tameVal (T.chi1 i j b) (NX.pG D kv) ((1 : ℤ) * 1) u).1
        rw [show ((1 : ℤ) * 1) = 1 from rfl]
        unfold tauT
        rw [dif_pos h]
        exact h.choose_spec x u hu
      mtV := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        @NX.MtVReal.mk N.toD7 i j b k Q ψ 1 (wt.Wt i j b) (wt.acg i j b) (wt.mod i j b) (wt.rhoW i j b) (tauT D T i j b)
          (WkT D T wt i j b k)
          (inferInstance : AddCommGroup (WkT D T wt i j b k))
          (inferInstance : Module (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (inferInstance : FiniteDimensional (FractionRing (T.Ok i k)) (WkT D T wt i j b k))
          (rhoKT D T wt i j b k)
          ((hwt i j b h1 h2).2.2.1 k)
          (isAlgWeightF_bc (K' := FractionRing (T.Ok i k)) (wt.rhoW i j b) (hwt i j b h1 h2).2.1)
          ⟨_, inferInstance, inferInstance, Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b),
            Algebra.TensorProduct.basis (FractionRing (T.Ok i k)) (Module.finBasis (FractionRing (T.O i)) (wt.Wt i j b)),
            fun γ => toMatrix_bcRep (K' := FractionRing (T.Ok i k)) _ (wt.rhoW i j b) γ⟩
          (hLev i j b k Q ψ h1 h2 hadm).choose.J
          (hLev i j b k Q ψ h1 h2 hadm).choose.χ
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.QP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.DP
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.sp
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose.redG
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.1
          (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.2.2.2.2.2.2.2.2.2
          (LinearEquiv.ofEq (MtSubT D T wt i j b k (LevLawsT D T Pq In.θ i j b k Q ψ))
            (NX.TypeSpF D.host.E D.R.nV (FractionRing (T.Ok i k)) (rhoKT D T wt i j b k)
              (hLev i j b k Q ψ h1 h2 hadm).choose.J (hLev i j b k Q ψ h1 h2 hadm).choose.χ)
            (by rw [MtSubT, dif_pos (hLev i j b k Q ψ h1 h2 hadm)]))
      rhoW_hw := fun i j b t h1 h2 => (hwt i j b h1 h2).2.2.2.1 t
      rhoW_wt := fun i j b t hj hjm sh lam h1 h2 => (hwt i j b hj hjm).2.2.2.2 t sh lam h1 h2 }
  exact
    { twF := { K0 := Sp.K0, eO0 := Sp.eO0, j0 := Sp.j0, Lw := Sp.Lw, eO := Sp.eO, eOk := Sp.eOk, iCq := Sp.iCq,
               S0x := fun _ => Sx }
      tw := { pl_emb := fun i => ⟨Sp.eTw i, Sp.pl_emb i⟩
              ringSpec_baseIntegersEquiv_algebraMap := Sp.ringSpec_baseIntegersEquiv_algebraMap
              ringSpec_baseEmbedding_compatible := Sp.ringSpec_baseEmbedding_compatible
              eO_alg := Sp.eO_alg
              eOk_alg := Sp.eOk_alg
              mu_g := Sp.mu_g
              hk_split := fun i j b k P hP => _root_.GlobalTheory.T.lattice_basis_free_module_place_alt D cf jE A S In b0 b1 Sx T Sp hSb hstar hst i j b k P
                (hfr := (mkF D T S In hfg' hst sd rho hrho).freeB i j b)
                (hfi := (mkF D T S In hfg' hst sd rho hrho).finB i j b) hP
              ringSpec_excludedPlaces_eq := Sp.ringSpec_excludedPlaces_eq
              concreteTwistFrame_extraExcludedPlaces_conj := fun i P P' h h' => hconj P P' h h'
              B_range := fun (i : T.Tw) j b => by
                show LinearMap.range (BI D T S In i j b).subtype = _
                rw [Submodule.range_subtype]
                rfl
              sig_inj := hsd2
              qs_pos := fun i lam => PEmpty.elim lam
              concreteTwistFrame_extraExcluded_over_smallPrimes := fun i => hlow }
      cover := fun w => GlobalTheory.T.exists_twistIndex_of_coefficientField_place D cf b0 b1 Sx T Sp w
      chiD := { mu0 := Sp.mu0H, etaT := Sp.etaH, del := Sp.delH, psi := fun a => A.bare.elim a,
                chiI := fun s lam => PEmpty.elim lam, embO := Sp.embO }
      chi := { psi := fun a => A.bare.elim a, del_fix := Sp.del_fix, delta := Sp.delta, chi1 := Sp.chi1,
               ringSpec_sidedEmbedding_fixedField := Sp.ringSpec_sidedEmbedding_fixedField, etaT_unr := Sp.etaT_unr, etaT_inf := Sp.etaT_inf,
               lamG := fun s lam => PEmpty.elim lam }
      eta_eq := Sp.eta_eq
      ringSpec_normalisedCharacter_eq := Sp.ringSpec_normalisedCharacter_eq
      del_eq := Sp.del_eq
      iCq_embO := Sp.iCq_embO
      embO_star := Sp.embO_star
      deltaRead := Sp.deltaRead
      exp := E
      pq := fun (i : T.Tw) j b k Q ψ h1 h2 hadm =>
        ⟨(hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.1, (hLev i j b k Q ψ h1 h2 hadm).choose_spec.1.2.2.2.1⟩
      psiU := fun i b u hu hu' => rfl
      rho := In.rho
      chiL := In.chi
      hs := In.hs
      eF := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose
      bsup := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.1
      act := fun i j b h1 h2 => (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.1
      cHk := fun (i : T.Tw) b P => cHkT D T i b P
      hkEq := fun i j b h1 h2 k P x _ _ _ =>
        (GlobalTheory.T.twistLiftForms_eq_baseChange_rationalDatumForms D S In T A.bare hfg' hst sd rho hrho he Pq wt i j b h1 h2).choose_spec.2.2 k P x
      cHk_del := fun i b P hP σ hσ => GlobalTheory.T.heckeComparisonUnitAtFrobenius_eq_delta D T i b P hP σ hσ
      hk_emb := fun (i : T.Tw) j b k P x h1 h2 hP hs hk => by
        rcases Nat.eq_zero_or_pos k with rfl | hk0
        · show ((hkB D T S In hst i j b 0 P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b 0 P (x : ↥(BI D T S In i j b)).1
          rw [show hkB D T S In hst i j b 0 P = 1 from hkB_zero D T S In hst i j b P,
            show hkT D T S In i j b 0 P = 1 from hkT_zero D T S In i j b P]
          rfl
        · show ((hkB D T S In hst i j b k P x : ↥(BI D T S In i j b)) : FmT D T S i j b) =
            hkT D T S In i j b k P (x : ↥(BI D T S In i j b)).1
          unfold hkB
          rw [dif_pos ⟨h1, h2, hk0, hk, hs, hP⟩]
          rfl
      sigSpan := fun i j b h1 h2 => hsd1 i j b h1 h2
      rowS := sd.rowS
      rowS_eig := hsd4
      hEig_zero := hsd5
      rhoS := fun i s => ⟨(hsd3 i s).1, (hsd3 i s).2, fun π hc hr hl φ ι hz hι =>
        hrhoS i (sd.rowS i s) (sd.side i s) ⟨sd.jS i s, (sd.jS_range i s).1, (sd.jS_range i s).2, (hsd3 i s).1⟩
          (hsd3 i s).2 π hc hr hl φ ι hz hι⟩ }
end GlobalTheory.HeightCounting.FormsStep
end
end
