import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbarStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoupledTameInertiaGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspParamOfGreenParametrisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivariantLabelMapTwistCuspidalLabelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GreenSeriesIdempotentEqClassFunctionIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaTwoPlacesOverSamePrimeTrivialMeetStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalIntegerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting.TameGrp

theorem isGenSys_gen {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) : IsGenSys L.gen := by
  intro d hd
  refine ⟨L.gen_order d hd, fun d' hdd hd' => ?_⟩
  obtain ⟨e, rfl⟩ := hdd
  have he : 0 < e := Nat.pos_of_mul_pos_left hd'
  exact L.gen_norm d e hd he

theorem prod_rootsBar_X_sub_one_pow {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (n : ℕ) :
    ((Formalism.CyclotomicNorms.rootsBar ((X - 1 : (ZMod g)[X]) ^ n)).map fun x => X - Polynomial.C (t x)).prod = (X - 1 : ℂ[X]) ^ n := by
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.roots_pow,
    ← Polynomial.C_1, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.prod_nsmul, Multiset.map_singleton,
    Multiset.prod_singleton, map_one, Polynomial.C_1]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_tame_generators_cuspidal_labelling : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D), (∀ j g, ∃ z : ℤ, eExp D j g = z) → GlobalTheory.Mem.Top.TypesTrue D.ntypes cf.P cf.W → ∃ (L : Lay0 D) (hZ : L.ZOk) (hη : L.EtaOk), IsEmpty L.nd.Loc ∧ GlobalTheory.Mem.Top.TypesTrue L.ntypes cf.P cf.W ∧ L.nd.PlG = D.nd.PlG ∧ HEq L.naut.plGw D.naut.plGw ∧ HEq L.ntypes.cenAmb D.ntypes.cenAmb ∧ HEq L.ntypes.cenMt D.ntypes.cenMt ∧ (∃ Gs : GrpSide (setK D L hZ hη), ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; Gs.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen) ∧ ChiTOk (setK D L hZ hη) (cfK L hZ hη cf) ∧ L.loc = D.loc ∧ HEq (@NData.Om _ _ _ L.nd) (@NData.Om _ _ _ D.nd) ∧ HEq (@NData.instOm _ _ _ L.nd) (@NData.instOm _ _ _ D.nd) ∧ HEq (@NData.algOm _ _ _ L.nd) (@NData.algOm _ _ _ D.nd) ∧ HEq (@NData.plOm _ _ _ L.nd) (@NData.plOm _ _ _ D.nd) := by
  intro hG _ D hE cf _ hT
  haveI : IsEmpty D.nd.Loc := hE

  have htame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
        ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)),
          TameGenAt (D.nd.plOm.1 (D.naut.plGw k v)) σ ∧
            TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ σ (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen := by
    intro k v
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    exact GlobalTheory.T.exists_coupled_tame_inertia_generator D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.nd.plOm.2 _)
      (D.host.g k) (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      _ (isGenSys_gen _)
  choose kv tg tg_mem tg_gen tg_coup using htame

  let N1 := ndLab D.nd D.nd.lab D.nd.lab_monic
  haveI : IsEmpty N1.Loc := hE
  let A : NAut N1 := GlobalTheory.Mem.GaloisStage.nAut N1 D.naut.plGw D.naut.plGw_over D.naut.plGw_inj D.naut.plGw_nconj
  obtain ⟨C⟩ := GlobalTheory.MemN.nonempty_nbc_of_isEmpty_loc _ _ _ N1 A hE
  have hl1 : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod :=
    fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
  let D1 := setAut D hE D.nd.lab D.nd.lab_monic A C D.ntypes.tg_mem D.ntypes.tg_gen hl1
  let X1 : NTypes D1.naut :=
    { D1.ntypes with
      tg := tg
      tg_mem := tg_mem
      tg_gen := tg_gen
      heckeLoc_gamma_places := fun i => hE.elim i
      inertiaCharpoly_type := fun k v L _ => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        (prod_rootsBar_X_sub_one_pow (D.ntypes.teichC k) _).symm
      chiT_tg := fun i => hE.elim i }
  let D2 := setTy D1 hE X1 D1.nStage_trivialCharacter_compat D1.nStage_trivialCharacter_coeff_eq
  let L : Lay0 D := lay0 D2
  have hZ : L.ZOk := ⟨fun i => hE.elim i, fun i => hE.elim i⟩
  have hη : L.EtaOk := D.etaJ_tie
  refine ⟨L, hZ, hη, hE, ⟨hT.pl, hT.teich, hT.chi, hT.ser⟩, rfl, HEq.rfl, HEq.rfl, HEq.rfl, ?_, ?_, rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · have hteich := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
    choose tA tκ hTe using hteich
    have hlab : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        ∃ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k))
          (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _)),
          Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O ∧ LabTwLawO O ∧
            ∀ f, D.ntypes.eSer k f = eSerO O D.R.r f := by
      intro k
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      obtain ⟨O, hO1, hO2, hO3⟩ := GlobalTheory.T.exists_equivariant_labelMap_twist_cuspidalLabel (ZMod (D.host.g k)) _
        (GlobalTheory.T.cuspParam_of_greenParametrisation hG (D.host.g k) (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
          (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen (isGenSys_gen _))
      have hr : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
      exact ⟨O, hO1, hO2, fun f => (hT.ser k f).trans
        (GlobalTheory.T.greenSeriesIdempotent_eq_classFunctionIdempotent hG _ _ _ _ _ (hT.teich k) O hO3 D.R.r f hr)⟩
    choose O hOe hOt hOs using hlab
    exact ⟨{ tA := tA, tκ := tκ, teichC_def := hTe
             ζ := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
             ζ_gen := fun k => haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; isGenSys_gen _
             O := O, eSer_def := hOs, kv := kv, tg_tame := tg_coup, O_equiv := hOe, O_tw := hOt }, fun _ => rfl⟩
  · intro k v j u hu hrep
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    haveI := D.nd.acOm
    have hP := D.nd.plOm.2 (D.naut.plGw k v)
    obtain ⟨a, ha, hua, hga⟩ := GlobalTheory.T.tameInertia_representative_residue D.host.E D.nd.Om (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v)
      (D.host.g k) hP (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v))
      (D.naut.plGw_over k v)
      (Formalism.MainNotions.Gaps.LevGap.natCast_notMem_sq_of_split _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v))
      (kv k v) (tg k v) _ (tg_mem k v) (isGenSys_gen _) (tg_coup k v)
      (fun A' hA' hσ hne => GlobalTheory.T.inertia_two_places_over_same_prime_trivial_meet D.host.E D.nd.Om _ _ _ hP hA' (tg k v) (tg_mem k v) hσ hne) u hrep
    refine ⟨(D.nd.chiT k v j)⁻¹, Or.inr rfl, ?_⟩
    change ((((cf.mu0 j).locK (D.naut.plGw k v)) (Units.mk0 (((show 𝓞 D.host.E from u) : 𝓞 D.host.E) : D.host.E) hu) : ℂˣ) : ℂ) =
      (D.ntypes.teichC k) ((algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
        (((D.nd.chiT k v j)⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))
    rw [GlobalTheory.T.muZeroChar_locK_congruent_rational_integer cf.P cf.W _ _ _ (cf.isMu0 j) k _ (hT.pl k v) u hu a ha hua, hT.teich k, hT.chi k v j]
    have hlabel := (GlobalTheory.Mem.Top.isCharLab_omLab cf.W k).2 (ZMod.unitOfCoprime a ha) (by simpa using hga)
    have key : ∀ z : Formalism.CyclotomicNorms.Fbar (D.host.g k), z ≠ 0 →
        (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z⁻¹ = ((GlobalTheory.Mem.TypePl.labDat (D.host.g k)).teich z)⁻¹ :=
      fun z hz => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ hz, map_one])
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, hlabel, Units.val_inv_eq_inv_val, map_inv₀, key _ (by
      rw [Units.val_pow_eq_pow_val, map_pow]
      exact pow_ne_zero _ ((_root_.map_ne_zero _).2 (Units.ne_zero _))), Units.val_pow_eq_pow_val, map_pow, map_pow]

end GlobalTheory.HeightCounting.TameGrp

end
