import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalEigenData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
noncomputable section
namespace GlobalTheory.HeckeLocN
set_option synthInstance.maxHeartbeats 400000
section Psi
variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)
end Psi
set_option maxHeartbeats 2000000 in
theorem ndSpec_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  intro hArt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI _ _ hpd hCheb hOS hVal big
  obtain ⟨hO, hc⟩ := GlobalTheory.T.twistConductors_over_real_places_and_conj_stable D cf C tp hCS.off
  have hG := GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable D cf M C tp hMI hO
  have hX := GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer D
  have hR := GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators D M C tp.tup hStd hG hMI
  have hCm := GlobalTheory.T.liftedHeckeOperators_at_generators_commute D M C hR hStd hG hX
  choose F1 hF1 using GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues D M C hR (plEmb A.pl) hCm
  choose F2 hF2 hF2' using GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers D A.pl big
  choose F3 hF3 using GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff D
  choose F4 hF4 using GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings D C Bs.twF low (plEmb A.pl) Bs.tw hCS.choice
  obtain ⟨X, hXE, h1, h2, h3, h4⟩ : ∃ X : CoefIn D.what₂, X.E = plEmb A.pl ∧ (∀ j w, (F1 j w).1 ≤ (X.Kx j w).1) ∧
      (∀ j w, (F2 w).1 ≤ (X.Kx j w).1) ∧ (∀ j w, (F3 w).1 ≤ (X.Kx j w).1) ∧ ∀ j w, (F4 w).1 ≤ (X.Kx j w).1 :=
    ⟨coefIn A.pl (fun j w => feSup (feSup (F1 j w) (F2 w)) (feSup (F3 w) (F4 w)))
      (fun j w x => (le_sup_of_le_left le_sup_right : (F2 w).1 ≤ ((F1 j w).1 ⊔ (F2 w).1) ⊔ ((F3 w).1 ⊔ (F4 w).1)) (hF2 w x)), rfl,
      fun _ _ => le_sup_of_le_left le_sup_left, fun _ _ => le_sup_of_le_left le_sup_right,
      fun _ _ => le_sup_of_le_right le_sup_left, fun _ _ => le_sup_of_le_right le_sup_right⟩
  have hS : SplitK (mt0 M) C.Q hR X := fun j w => hF1 j w X hXE (h1 j w)
  choose twC hTwA hTwR hTwE using fun j w => hF4 w X j hXE (h4 j w)
  obtain ⟨ψ0, -, hψ0, -⟩ := hCS.nct.psi_eq
  have hP := GlobalTheory.T.twistCharacterValues_integral_units_at_place D C X ψ0 hψ0
  have hs := GlobalTheory.T.heckeStandardFacts_on_localisation_base D M C hR X hS hStd hG hX hCm
  have hd := GlobalTheory.T.finiteDimensional_localisation_space_all (base M C hR X hS)
  have hML := LatticeFinitenessFree.mtLoc_holds (partCompl_of hs hd)
  have hAct := GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice _ hs hd hML (GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places D M C hR X hS tp.tup hMI hX)
    (GlobalTheory.T.heckeOperators_on_localisation_space_semisimple D M C hR X hS hStd GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace hG hX)
  have hAHK := GlobalTheory.T.heckeRing_acts_on_lattice_as_operators _ hs hd hML hAct
  have hI := osInt D (base M C hR X hS)
  have hGal := fun w (hw : TwistedAt D w) => GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l D cf C tp w hArt hCheb hCS.psi hw (hVal w hw) (hCS.adm w hw)
  have htw : ∀ w v, v ∈ C.Q w → TwistedAt D w := fun w v hv => by
    by_contra hw
    rw [hCS.off w hw] at hv
    exact absurd hv (Finset.notMem_empty v)
  have hQl : ∀ w v, v ∈ C.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun w v hv =>
    C.twI_l w ▸ ((hCS.adm w (htw w v hv)).1 v hv).2
  have hQS : ∀ w v, v ∈ C.Q w → v ∉ exceptionalPlaces D.host (D.what₂.places.resChar w) := fun w v hv h => by
    have ha := (hCS.adm w (htw w v hv)).2.1 v hv
    rcases h.1 with h | h | h
    · exact ha.2 0 h
    · exact ha.2 1 h
    · refine ha.1 (Finset.mem_coe.1 ?_)
      rw [D.ntw.pD_eq, C.twI_l]
      exact h
  have hSs : ∀ l v, v ∈ exceptionalPlaces D.host l → IsSplitPl D.host v := fun l v h => by
    rcases h.1 with h | h | h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 0 v h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 1 v h
    · split_ifs at h
      · exact hpd v (Or.inr h)
      · exact hpd v (Or.inl h)
  have hRP := fun j w (hw : TwistedAt D w) => psN_ram hψ0 hP j w (hGal w hw).1
  refine ⟨_, _, nonempty_spec (base M C hR X hS) C hs hd hML (LatticeFinitenessFree.mtSub_free _) (LatticeFinitenessFree.mtSub_finite _) (GlobalTheory.T.localisation_heckeRing_isLocalRing _ hs hd) hAct
    (GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point _ hs hd hML hAct hAHK) (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i))
    (GlobalTheory.T.localisation_galoisCharacter_continuous D M C hR X hS twC ψ0 hP hTwA (psN_open hψ0 hP))
    (fun i v hv => hv.elim (fun h => hSs _ v ((Set.Finite.mem_toFinset _).1 h))
      (fun h => ((hCS.adm _ (htw _ v h)).1 v h).1))
    (fun i => Finset.disjoint_left.2 fun v h h' => hQS _ v h' ((Set.Finite.mem_toFinset _).1 h)) hQl ?_ hI
    (GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing D _ hI hOS) (fun a => hTwE _ _ a.2.2.2.2.2) (fun a => psN_ord hψ0 hP _ _) (fun a => psN_open hψ0 hP _ _)
    (fun a => psN_anti hψ0 hP _ _) (fun a => hRP _ _ a.2.2.2.2.2)
    (fun a v hv B hB σ hσ => (psN_eq_one hψ0 hP _ _ σ).2 ((hGal _ a.2.2.2.2.2).2 v hv B hB σ hσ))
    A.pl M big (fun j w h1 h2 v k s ϖ hg hcj hu x => hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x) hO hc
    (fun _ => rfl) (iqC X) (fun j w z => (iqC_alg X j w _).trans rfl) ?_ ?_ hAHK (plGwDisj D) ?_ (fun a => hTwA _ _)
    (fun a => hTwR _ _) (fun j w => hF3 w X j (h3 j w))⟩
  · intro i v hv
    have hw : TwistedAt D (wOf _ i) := i.2.2.2.2.2
    obtain ⟨σ, hσ, hne⟩ := (hRP (jOf _ i) _ hw v _ (D.nd.plOm.2 v)).2 hv
    have ha := hCS.adm _ hw
    have h1 := D.ntw.twistCharacterFamily_unramified (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) v (ha.1 v hv).2 (ha.2.1 v hv).2 (ha.2.1 v hv).1 _
      (D.nd.plOm.2 v) σ hσ
    refine ⟨σ, hσ, fun e => hne ?_⟩
    have e' : Units.map (twC (jOf _ i) (wOf _ i)).toMonoidHom (D.ntw.chi1 (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) σ) *
        psN X ψ0 hP (jOf _ i) (wOf _ i) σ = 1 := e
    rwa [h1, map_one, one_mul] at e'
  · intro j w x
    change A.pl.ι w (iqC X j w (ecC X j w x)) = _
    rw [iqC_ec, hXE]
    exact (A.pl.ι w).apply_symm_apply _
  · intro j w z hz
    obtain ⟨x, hx⟩ := iqC_surj X j w _ (h2 j w (hF2' w z hz))
    exact ⟨x, (congrArg (A.pl.ι w) hx).trans ((A.pl.ι w).apply_symm_apply z)⟩
  · intro a g y hy
    obtain rfl := (C.embW _).injective (hy.trans (hψ0 _ g).symm)
    exact (psN_spec hP _ _ g).symm
end GlobalTheory.HeckeLocN
end
end
