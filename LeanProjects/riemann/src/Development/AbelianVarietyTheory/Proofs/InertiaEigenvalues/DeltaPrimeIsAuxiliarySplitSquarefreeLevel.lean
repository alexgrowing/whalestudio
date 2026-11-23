import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverLevelOneOverSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLevelDatumReferenceTupleSmallField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DictionaryCharacterRightInvariantCoreLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSelfDualLatticeIffIntegralFrameMatricesHalfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfOfAuxiliarySplitLevel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootInRayClassFieldNatModulus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompatStatement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.SeriesTie.BaseRat

variable {D : D7}

open Classical in

theorem isIdemSum_halfIdem {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : PlacesOK Pg Q) :
    IsIdemSum (halfIdem Pg Q) (Pg.image Formalism.L2.DIV.conjPl ∪ Q) := by
  obtain ⟨he, hR⟩ := GlobalTheory.ExportSeries.LatHalf.conj_placesOK h
  obtain ⟨P, h1, h2, hP⟩ := h.split
  obtain ⟨P', -, h3, hP'⟩ := hR.split
  have hdis : Disjoint (Pg.image Formalism.L2.DIV.conjPl) Q := by
    refine Finset.disjoint_left.2 fun PP hPP hQ => ?_
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    exact GlobalTheory.ExportType.not_isConjPl_of_splitSet hP (h1 hP0) (h2 hQ) (GlobalTheory.ExportSeries.LatHalf.levConj_conjPl P0)
  refine ⟨⟨idemAt, fun PP hPP => ?_, ?_⟩, h.isOrthSum.2⟩
  · rcases Finset.mem_union.1 hPP with k | k
    · exact hP'.isIdemAt (h3 k)
    · exact hP.isIdemAt (h2 k)
  · rw [Finset.sum_union hdis, halfIdem, ← he]
    rfl

theorem frMapO_nsmul {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ) (x : WO S T) :
    frMapO S T βS βT (k • x) = k • frMapO S T βS βT x := by
  induction k with
  | zero => simp [frMapO]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.ExportSeries.LatHalf.frMapO_add, ih]

theorem isLevDatum_vec {S T : HSp D} {F : Frame S T} (hF : F.Good) {G : TypeDat D T.rank} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : PlacesOK G.Pg Q)
    (hP : ∀ PP, PP ∈ G.Pg ∨ PP ∈ Q → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    {ω : Reds D T.rank S.rank → ℂ} (hω : ∀ y y', (∀ PP ∈ Q, y PP = y' PP) → ω y = ω y') {N : ℕ}
    (hN : ∀ PP, PP ∈ G.Pg ∨ PP ∈ Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) {k : Subfield ℂ}
    (h1 : ∀ y : Reds D S.rank T.rank, omegaG G.levT G.muC y ∈ k) (h2 : ∀ y, ω y ∈ k) :
    IsLevDatum F.ψ S T F.ΛS F.ΛT N k F.f₀ (F.vec G Q ω) := by
  classical
  refine ⟨_, halfIdem G.Pg Q, F.datumFn G Q ω, isIdemSum_halfIdem h, ?_, ?_, ?_, ?_, Frame.isThetaAt_vec hF h hω⟩
  · intro PP hPP
    rcases Finset.mem_union.1 hPP with hk | hk
    · obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hk
      show Formalism.L2.DIV.starOHom ((N : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
      rw [map_natCast]
      exact hN P0 (Or.inl hP0)
    · exact hN PP (Or.inr hk)
  · intro t ht
    unfold Frame.datumFn at ht
    have a1 : IsHalf (halfIdem G.Pg Q) t ∧ IsIntM (frMapAdj S T F.βS F.βT t) := by
      by_contra hc
      exact left_ne_zero_of_mul ht (if_neg hc)
    have a2 : IsHalf (halfIdem G.Pg Q) t ∧ IsIntM (frMapO S T F.βS F.βT t) := by
      by_contra hc
      exact right_ne_zero_of_mul ht (if_neg hc)
    exact ⟨(GlobalTheory.T.mem_selfDualLattice_iff_integral_frameMatrices_half hF h hP a1.1).2 ⟨a1.2, a2.2⟩, a1.1⟩
  · intro u hu hue t
    obtain ⟨i1, i2⟩ := (GlobalTheory.T.mem_selfDualLattice_iff_integral_frameMatrices_half hF h hP hue).1 hu
    have f1 : frMapAdj S T F.βS F.βT (t + N • u) = frMapAdj S T F.βS F.βT t + N • frMapAdj S T F.βS F.βT u := by
      rw [GlobalTheory.RefDatumLev.frMapAdj_add', GlobalTheory.RefDatumLev.frMapAdj_nsmul']
    have f2 : frMapO S T F.βS F.βT (t + N • u) = frMapO S T F.βS F.βT t + N • frMapO S T F.βS F.βT u := by
      rw [GlobalTheory.ExportSeries.LatHalf.frMapO_add, frMapO_nsmul]
    have hKu : IsHalf (halfIdem G.Pg Q) (N • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hh : IsHalf (halfIdem G.Pg Q) (t + N • u) ↔ IsHalf (halfIdem G.Pg Q) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    unfold Frame.datumFn
    rw [f1, f2]
    congr 1
    · by_cases hc : IsHalf (halfIdem G.Pg Q) t ∧ IsIntM (frMapAdj S T F.βS F.βT t)
      · rw [if_pos ⟨hh.2 hc.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i1 _).2 hc.2⟩, if_pos hc]
        exact GlobalTheory.PlaceDatum.omegaG_congr _ _ _ _ fun PP hPP => GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i1 _ (hN PP (Or.inl hPP))
      · rw [if_neg hc, if_neg fun h' => hc ⟨hh.1 h'.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i1 _).1 h'.2⟩]
    · by_cases hc : IsHalf (halfIdem G.Pg Q) t ∧ IsIntM (frMapO S T F.βS F.βT t)
      · rw [if_pos ⟨hh.2 hc.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i2 _).2 hc.2⟩, if_pos hc]
        exact hω _ _ fun PP hPP => GlobalTheory.RefDatumLev.redM_add_nsmul PP hc.2 i2 _ (hN PP (Or.inr hPP))
      · rw [if_neg hc, if_neg fun h' => hc ⟨hh.1 h'.1, (GlobalTheory.RefDatumLev.isIntM_add_nsmul_iff i2 _).1 h'.2⟩]
  · intro t
    unfold Frame.datumFn
    refine mul_mem ?_ ?_ <;> split_ifs
    exacts [h1 _, zero_mem _, h2 _, zero_mem _]

theorem omegaG_mem {r n : ℕ} (G : TypeDat D r) {k : Subfield ℂ} (h1 : ∀ p, ((G.P.chi p : ℂˣ) : ℂ) ∈ k)
    (h2 : ∀ PP ∈ G.Pg, ∀ u, ((G.muC PP u : ℂˣ) : ℂ) ∈ k) (y : Reds D n r) : omegaG G.levT G.muC y ∈ k := by
  unfold omegaG
  split_ifs with h
  · refine mul_mem (mul_mem (h1 _) (prod_mem fun PP _ => prod_mem fun c hc => absurd hc (by simp [TypeDat.levT]))) ?_
    exact prod_mem fun PP _ => inv_mem (h2 _ PP.2 _)
  · exact zero_mem _

theorem exists_normal_roots (L₀ : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L₀] [Normal ℚ L₀] {k : Subfield ℂ}
    (h : L₀.toSubfield ≤ k) {n : ℕ} (hn : n ≠ 0) :
    ∃ L : IntermediateField ℚ ℂ, FiniteDimensional ℚ L ∧ Normal ℚ L ∧ L₀ ≤ L ∧ L.toSubfield ≤ k ∧
      ∀ z ∈ k, z ^ n = 1 → z ∈ L := by
  let I := {z : ℂ // z ∈ k ∧ z ^ n = 1}
  haveI : Finite I := by
    refine Set.Finite.to_subtype (s := {z : ℂ | z ∈ k ∧ z ^ n = 1})
      ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => ?_)
    simpa [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)] using hz.2
  have hcyc : ∀ z : I, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z.1}) ∧ Normal ℚ (IntermediateField.adjoin ℚ {z.1}) := by
    intro z
    have ho : IsOfFinOrder z.1 := isOfFinOrder_iff_pow_eq_one.2 ⟨n, Nat.pos_of_ne_zero hn, z.2.2⟩
    haveI : NeZero (orderOf z.1) := ⟨ho.orderOf_pos.ne'⟩
    have hζ := IsPrimitiveRoot.orderOf z.1
    haveI : IsCyclotomicExtension {orderOf z.1} ℚ (IntermediateField.adjoin ℚ {z.1}) := by
      change IsCyclotomicExtension {orderOf z.1} ℚ (IntermediateField.adjoin ℚ {z.1}).toSubalgebra
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        ((hζ.isIntegral ho.orderOf_pos).tower_top (A := ℚ)).isAlgebraic]
      exact hζ.adjoin_isCyclotomicExtension ℚ
    haveI := IsCyclotomicExtension.isGalois {orderOf z.1} ℚ (IntermediateField.adjoin ℚ {z.1})
    exact ⟨IsCyclotomicExtension.finiteDimensional {orderOf z.1} ℚ _, inferInstance⟩
  haveI := fun z => (hcyc z).1
  haveI := fun z => (hcyc z).2
  let k' : IntermediateField ℚ ℂ := k.toIntermediateField fun q => SubfieldClass.ratCast_mem k q
  refine ⟨L₀ ⊔ ⨆ z : I, IntermediateField.adjoin ℚ {z.1}, inferInstance,
    @IntermediateField.normal_sup ℚ ℂ _ _ _ _ _ ‹_› (@IntermediateField.normal_iSup ℚ ℂ _ _ _ _ _ fun z => (hcyc z).2),
    le_sup_left, ?_, fun z hz hzn => ?_⟩
  · have : L₀ ⊔ ⨆ z : I, IntermediateField.adjoin ℚ {z.1} ≤ k' :=
      sup_le h (iSup_le fun z => IntermediateField.adjoin_simple_le_iff.2 z.2.1)
    exact this
  · exact (le_sup_right : _ ≤ L₀ ⊔ _) (le_iSup (fun z : I => IntermediateField.adjoin ℚ {z.1}) ⟨z, hz, hzn⟩
      (IntermediateField.mem_adjoin_simple_self ℚ z))

abbrev pdAt (D : D7) (l : ℕ) : ℕ := if l = D.host.pde then D.host.pde' else D.host.pde

theorem mem_pD_iff (i : D.ntw.Tw) (P : Formalism.L2.DIV.Pl D.host.E) :
    P ∈ D.ntw.pD i ↔ ((pdAt D (D.ntw.l i) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := Set.ext_iff.1 (D.ntw.pD_eq i) P

theorem deltaPrime_isAuxiliarySplitSquarefreeLevel (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) (l : ℕ) :
    IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) (pdAt D l) := by
  have key : ∀ p : ℕ, p.Prime → p % 15 = 1 → D.host.cls p = PrimeClass.splitK → p ∈ D.host.levelPrimes → (∀ k, p ≠ D.host.g k) →
      IsAuxiliarySplitSquarefreeLevel D (D.host.g 0 * D.host.g 1) p := by
    intro p hp _ hc hl hg
    have s : p ∉ D.host.small ∧ p ≠ D.host.q ∧ jacobiSym (-(D.host.d : ℤ)) p = 1 := by
      unfold Formalism.BasicNotions.Host.cls primeClass at hc
      split_ifs at hc with h1 h2 h3 h4 <;> first | exact ⟨h1, h2, h4⟩ | cases hc
    refine ⟨hp.odd_of_ne_two (UpperTheory.Small.ne_two D.host s.1), hp.prime.squarefree, fun p' hp' hd => ?_,
      Nat.Coprime.mul_right ((Nat.coprime_primes hp (D.host.g_prime 0)).2 (hg 0))
        ((Nat.coprime_primes hp (D.host.g_prime 1)).2 (hg 1)),
      (GlobalTheory.SeriesTie.PlacesGood.coprime_of_level hp s.1 s.2.1 hl).symm⟩
    rw [(Nat.prime_dvd_prime_iff_eq hp' hp).1 hd]
    exact s.2.2
  unfold pdAt
  split_ifs
  · exact key _ D.host.pde'_prime D.host.pde_mod.2 hsp.2 D.host.pde_level.2 fun k => (D.host.pde_ne_g k).2
  · exact key _ D.host.pde_prime D.host.pde_mod.1 hsp.1 D.host.pde_level.1 fun k => (D.host.pde_ne_g k).1

theorem zeta_mem_of_rayIn {N : ℕ} (hN : N ≠ 0) {k : Subfield ℂ} (h : RayIn D N k) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N ∈ k := by
  obtain ⟨L, i1, i2, i3, i4, hL, j, -, hk⟩ := h
  obtain ⟨ζ, hζ⟩ := GlobalTheory.RayRootOfUnity.exists_isPrimitiveRoot_of_isRay hN hL
  haveI : NeZero N := ⟨hN⟩
  obtain ⟨a, -, ha⟩ := (hζ.map_of_injective j.injective).eq_pow_of_pow_eq_one (Complex.isPrimitiveRoot_exp N hN).pow_eq_one
  have : ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = j ζ ^ a := ha.symm
  rw [this]
  exact pow_mem (hk ζ) a

theorem RayIn_mono {N : ℕ} {k k' : Subfield ℂ} (hk : k ≤ k') (h : RayIn D N k) : RayIn D N k' := by
  obtain ⟨L, i1, i2, i3, i4, hL, j, hj, hm⟩ := h
  exact ⟨L, i1, i2, i3, i4, hL, j, hj, fun x => hk (hm x)⟩

theorem valuesIn_of_le {χ : Formalism.L2.Host.HChar D.host.E} {s : ℝ} (h : χ.ValuesIn s (embLL0 D)) {k : Type} [Field k] {σ : k →+* ℂ}
    (hk : (embLL0 D).fieldRange ≤ σ.fieldRange) : χ.ValuesIn s σ := fun v hv => by
  obtain ⟨y, hy⟩ := h v hv
  obtain ⟨z, hz⟩ := hk ⟨y, rfl⟩
  exact ⟨z, hz.trans hy⟩

theorem isTwist_delAt (C : Formalism.L2.Host.CharFrame D) (hval : Formalism.L2.Host.ValLL0 D C) (l : ℕ) {δc : (AE D)ˣ →* Circle}
    (h : ChrEq δc (C.delAt l)) {k : Type} [Field k] {σ : k →+* ℂ} (hk : (embLL0 D).fieldRange ≤ σ.fieldRange) :
    IsTwist (pdAt D l) σ (C.delAt l) δc := by
  refine ⟨h, ?_⟩
  unfold Formalism.L2.Host.CharFrame.delAt pdAt
  split_ifs
  · exact ⟨C.isDel'.fin, C.isDel'.triv, C.isDel'.tame, C.isDel'.unr, valuesIn_of_le hval.del' hk⟩
  · exact ⟨C.isDel.fin, C.isDel.triv, C.isDel.tame, C.isDel.unr, valuesIn_of_le hval.del hk⟩

theorem de_values {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ x, (((ρ.B i j b).de.chi x : Circle) : ℂ) ^ n = 1 ∧
      (((ρ.B i j b).de.chi x : Circle) : ℂ) ∈ (ρ.e i b).fieldRange := by
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) with hψ
  have hopen : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have : ψ.ker = (D.ntw.delta i).ker := by
      ext σ
      cases b <;> simp [hψ, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [this]; exact D.ntw.delta_open i
  haveI : ψ.ker.FiniteIndex := @Subgroup.finiteIndex_of_finite_quotient _ _ _ (Subgroup.quotient_finite_of_isOpen _ hopen)
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  refine ⟨ψ.ker.index, Subgroup.FiniteIndex.index_ne_zero, fun x => ?_⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have e : (((ρ.B i j b).de.chi x : Circle) : ℂ) =
      ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ψ σ : (D.ntw.O0 i)ˣ) := by
    rw [hρ.delta i j b]
    exact charOf_eq _ _ hopen hσ Subgroup.FiniteIndex.index_ne_zero (hpow σ)
  rw [e]
  exact ⟨by rw [← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one], _, rfl⟩

theorem eq_one_of_full_upper_block_eq_one {κ : Type} [CommRing κ] {r n : ℕ} (hr : r ≤ n) (e : n = r) {g : GL (Fin n) κ} (h : upperLeftBlock hr g = 1) :
    g = 1 := by
  subst e
  rwa [GlobalTheory.AdjDatumMove.restrictedBlock_self_apply] at h

section Core

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem tieIn_of_fw (fw : FWTie T Rl.toRealDat κ v₀) : TieIn T Rl.toRealDat κ v₀ :=
  ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

include YS in

theorem exists_goodCover_pdAt (hRF : GlobalTheory.NT.RayField) (hT : LawsJ T) (ha : AlgTie T) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) (l : ℕ) (j : Fin D.R.m) (n : ℕ)
    (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] [Normal ℚ L] (hL : GlobalTheory.CoverSmall.smallF D ≤ L) :
    ∃ C : Cover T ((j : ℕ) + 1) T.σ₀, C.d.pd = pdAt D l ∧ C.σ₂.fieldRange = L.toSubfield ∧ GoodCover T Rl.toRealDat j C n := by
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have haux : IsAuxiliarySplitSquarefreeLevel D T.Q.l.M (pdAt D l) := hMg ▸ deltaPrime_isAuxiliarySplitSquarefreeLevel hsp l
  obtain ⟨I, hK, hprod, hsup⟩ := GlobalTheory.HalfCharacter.exists_half_of_auxiliary_split_level D T hT _ haux
  have hLL : (embLL0 D).fieldRange ≤ L.toSubfield := fun z hz => hL hz
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  have h2 := D.host.pde_prime.ne_zero
  have h3 := D.host.pde'_prime.ne_zero
  have hN : T.Q.l.M * pdAt D l ≠ 0 := mul_ne_zero (by rw [hMg]; positivity) haux.1.pos.ne'
  have hray' : RayIn D (T.Q.l.M * pdAt D l) L.toSubfield := by
    refine RayIn_mono hLL (GlobalTheory.CoverSmall.rayIn_of_dvd hRF D hN (by positivity) ?_ hray)
    rw [hMg]
    unfold pdAt
    split_ifs
    · exact ⟨D.host.pde, by ring⟩
    · exact ⟨D.host.pde', rfl⟩
  have hLv : (embLL0 D).fieldRange ≤ (L.val : L →+* ℂ).fieldRange := fun z hz => ⟨⟨z, hLL hz⟩, rfl⟩
  obtain ⟨C, hpd, -, hfr, hG⟩ := GlobalTheory.CoverGalois.exists_goodCover_galois D T Rl.toRealDat hT j (inR j) n _ I haux hK hprod hsup L
    ((GlobalTheory.CoverSmall.core_le_small T Rl cG S YS hT ha j).trans hL) (zeta_mem_of_rayIn hN hray')
    ⟨valuesIn_of_le (hval.mu0 j) hLv, valuesIn_of_le hval.eta hLv⟩ hray'
  exact ⟨C, hpd, hfr, hG⟩

theorem mu_level (hlev : Rl.toLevCh.Is A3.A.μ0) (hT : TieIn T Rl.toRealDat κ v₀) (j : Fin D.R.m) :
    ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, T.mu ((j : ℕ) + 1) T.σ₀ (g * k) = T.mu ((j : ℕ) + 1) T.σ₀ g := by
  intro k hk g
  have hJ := hT.laws
  have hj := inR j
  have hσ : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  obtain ⟨τ, hτ⟩ := GlobalTheory.MuLevel.exists_ext (L := D.what₂.LL) T.σ₀
  obtain ⟨hf, hk'⟩ := (hJ.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := hJ.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨y, hy, hu, hc⟩ := GlobalTheory.MuLevel.exists_root_of_level _ _ hodd k hf hk'
  have hm := Rl.C.isMu0 j
  have h1 : Rl.mu0 ((j : ℕ) + 1) y = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hlev.mu0 j) hm.tame _
      (fun P hP => hm.unr P fun a ha => hP ?_) y hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  have hg : GoodEmb T.Q.c (τ.comp (algebraMap T.Q.c.F D.what₂.LL)) := hτ ▸ hσ
  obtain ⟨z, hz1, hz2⟩ := (hT.chiR j τ hg).2.2.2.1 y hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL z = 1 :=
    D.what₂.embLL.injective (by rw [← hz1, h1, map_one, Circle.coe_one])
  have hχ : T.chiW ((j : ℕ) + 1) T.σ₀ y = 1 := by
    rw [hτ] at hz2
    apply Subtype.ext
    rw [hz2, h2, map_one, Circle.coe_one]
  have hMV := hJ.muVal _ hj _ hσ
  obtain ⟨x, hx⟩ := hMV.1 g
  have hxy : IsDetRoot _ (g * k) (x * y) := (GlobalTheory.Member.isDetRoot_laws D _).2.2.2 g k x y hx hy
  rw [hMV.2 _ _ hxy, hMV.2 g x hx, map_mul, hχ, mul_one]

variable (T κ v₀) in

def ReadsAs {j : Fin D.R.m} (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) (c : ℂ) : Prop :=
  ∀ f : Cu T κ j, ∃ x : NX.FmK S ((j : ℕ) + 1),
    castDict hV (T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) (f : T.R ((j : ℕ) + 1))) = c • evW YS v₀ j (Subtype.val x)

theorem readsAs_one (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates) {j : Fin D.R.m}
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j) : ReadsAs T YS κ v₀ hV 1 := fun f => by
  have hres : res T (sg0 D A3.A) = T.σ₀ := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ Rl.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  have hV' : T.V ((j : ℕ) + 1) (res T (sg0 D A3.A)) = Wc D j := by rw [hres]; exact hV
  obtain ⟨x, hx⟩ := exists_evW_eq_phiC YS fw hev j (hres ▸ T.toCore.good_σ₀) hV' f
  refine ⟨x, funext fun g => ?_⟩
  rw [one_smul, hx]
  exact (RatExpand.castDict_phiJ hres hV' hV _ _ g).symm

theorem exists_sum_evW (hti : TieIn T Rl.toRealDat κ v₀) (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hlev : Rl.toLevCh.Is A3.A.μ0) (hpb : T.pb = Rl.C.P.pb) {j : Fin D.R.m} {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j}
    {c : ℂ} (hrd : ReadsAs T YS κ v₀ hV c) {C : Cover T ((j : ℕ) + 1) T.σ₀} (hC : GoodCover T Rl.toRealDat j C (κ j).n) {φ : GA D (Wc D j) → ℂ}
    (hφ : IsRat T j hV C (κ j) φ)
    (hinv : ∀ k, Lev.IsLevelLift (Wc D j) (Rl.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k → ∀ g, φ (g * k) = φ g) :
    ∃ (n : ℕ) (z : Fin n → ℂ) (x : Fin n → NX.FmK S ((j : ℕ) + 1)), (∀ k, z k ∈ C.σ₂.fieldRange) ∧
      φ = c • ∑ k, z k • evW YS v₀ j (Subtype.val (x k)) := by
  have hT := hti.laws
  have hInR := inR j
  have hlast : (κ j).LastPos := fun τ i hi => by
    rw [(hti.kap j τ).1 i]
    exact GlobalTheory.LiftWeight.kapTop_lastPos D j τ i hi
  have hn : 8 * D.R.f * D.R.r + 4 ≤ (κ j).n := by
    rw [(hti.kap j (D.eTau.symm 1)).2.2]
    exact hnV
  obtain ⟨φ', hφ'm, rfl⟩ := hφ
  have hspan : Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n) ≤
      Submodule.span ℂ (rdU (T.U ((j : ℕ) + 1) T.σ₀) '' {f | f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
        rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
          (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)}) := by
    refine (GlobalTheory.OntoCore.holSub0_le_span_cuspA D T hT _ hInR (κ j) hlast hn T.σ₀ T.toCore.good_σ₀).trans
      (Submodule.span_mono (Set.image_mono fun f hf => ⟨Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf, ?_, ?_⟩))
    · exact ((Formalism.L2.Pj.mem_cusp _ _ _ _ _ f).1 hf).2 T.σ₀ T.toCore.good_σ₀
    · exact Formalism.L2.Pj.rdU_mem_offZero _ _
  have hinv' : ∀ k ∈ T.Kf ((j : ℕ) + 1) T.σ₀, ∀ g, φ' (g * k) = φ' g := fun k hk g => by
    have hkk : cast (congrArg (GA D) hV.symm) (cast (congrArg (GA D) hV) k) = k := by simp
    have key : ∀ {V W : HSp D} (e : V = W) (ψ : GA D V → ℂ) (a c : GA D V),
        castDict e ψ (cast (congrArg (GA D) e) a * cast (congrArg (GA D) e) c) = castDict e ψ (cast (congrArg (GA D) e) a) →
          ψ (a * c) = ψ a := by
      rintro V _ rfl ψ a c h
      exact h
    exact key hV φ' g k (hinv _ ((GlobalTheory.T.level_character_embedding_compat T Rl.toRealDat κ v₀ hlev hti hpb j T.σ₀ T.toCore.good_σ₀ hV _).2
      (by rw [hkk]; exact hk)) _)
  obtain ⟨m, xs, ψ, hψ, hφeq⟩ := GlobalTheory.CoverFormDesc.cover_form_desc D T hT _ hInR T.σ₀ T.toCore.good_σ₀ C hC.1 (wtA (κ j)) (κ j).n
    (dom_wtA _) (hC.2.1 _ (dom_wtA _)) hspan (mu_level hlev hti j) φ' hφ'm hinv'
  have hψ' : ∀ k, ∃ f, (f ∈ sec (T.Q.Xo ((j : ℕ) + 1)) T.Q.c (wtA (κ j)) (κ j).n ∧
      rdU (T.U ((j : ℕ) + 1) T.σ₀) f ∈ Formalism.L2.Pj.holSub0 (T.U ((j : ℕ) + 1) T.σ₀).X
        (laU (T.U ((j : ℕ) + 1) T.σ₀) (wtA (κ j)) (κ j).n)) ∧ T.phiJ ((j : ℕ) + 1) T.σ₀ (wtA (κ j)) f = ψ k := hψ
  choose fs hfs using hψ'
  choose x hx using fun k => hrd ⟨fs k, GlobalTheory.T.mem_cuspForms_of_reading_bounded_cuspidal_holomorphic D T hT _ hInR (κ j) hlast hn (fs k) (hfs k).1.1 (hfs k).1.2⟩
  refine ⟨m, fun k => C.σ₂ (xs k), x, fun k => ⟨xs k, rfl⟩, funext fun g => ?_⟩
  rw [hφeq, RatExpand.castDict_sum_smul, Finset.smul_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm, Pi.smul_apply, smul_eq_mul, ← hx k]
  exact congrArg _ (congrArg (fun ψ' => castDict hV ψ' g) (hfs k).2).symm

theorem ioP_mem_valSpace {F : Face D A3.A} (hC : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) {j : Fin D.R.m}
    (hv : IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) {B : Base (Vc D j) (Wc D j)} (hB : B.Good) (hBo : BaseOf Rl.toRealDat j B)
    {u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ} (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) (w : (Rl.cV j).W) :
    Rl.ioP j (PiTensorProduct.tprod ℂ u) w ∈ B.valSpace := by
  have hcV : (Rl.cV j).Is := hC.models.cV j
  obtain ⟨u', w₀, hu', -, hw⟩ := FWT.IsChosenExtremalVector.io _ hv hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw
  have hT := Scale.io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  rcases hcV.2.2.2.2 ((harm (Wc D j).rank B.w B.F.BS).comap (Rl.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT a ha]
      exact fockGL_mem_harm _ _ _ hw') with h | h
  · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (Rl.ioP j (PiTensorProduct.tprod ℂ u)) := by
      rw [Submodule.mem_comap, hw, ← hBo.delta]
      exact delta_mem_harm _ _
    rw [h, Submodule.mem_bot] at h0
    rw [h0, map_zero] at hw
    exact absurd hw.symm hΔ0
  · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (Rl.ioP j (PiTensorProduct.tprod ℂ u)))

theorem baseOf_of_realPin (hL : Rl.toLevCh.Is A3.A.μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) : BaseOf Rl.toRealDat j (ρ.B i j b) := by
  have hB := hρ.base i j b
  have hlam := GlobalTheory.BaseLiftWeight.lam_eq D _ Rl.toLevCh A3.A.μ0 j (ρ.B i j b) hL hB (hp.mu0 i j b) (hp.ap i j b) (hp.am i j b)
  have hc : ∀ τ, (ρ.B i j b).w.c τ = liftC D j τ := fun τ => GlobalTheory.BaseLiftWeight.c_eq hL hB (hp.mu0 i j b) τ
  have hP : (ρ.B i j b).w.p = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS D j := funext fun τ => congrArg Prod.fst (hB.sig τ)
  have hQ : (ρ.B i j b).w.q = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS D j := funext fun τ => congrArg Prod.snd (hB.sig τ)
  have hAP : (ρ.B i j b).w.ap = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aP D j := funext fun τ => hp.ap i j b τ
  have hAM : (ρ.B i j b).w.am = GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.aM D j := funext fun τ => hp.am i j b τ
  refine
    { ψ := hp.psi i j b, θ := hp.inf i j b, sT := hp.cartT i j b, BS := hp.onbS i j b, BT := hp.onbT i j b,
      ΛS := hp.latS i j b, ΛT := hp.latT i j b, βS := hp.frS i j b, βT := hp.frT i j b, vac := hp.vac i j b,
      Pg := hp.Pg i j b, mu0 := hp.mu0 i j b, eta := hp.eta i j b, lam := hlam, delta := ?_, p := hP, q := hQ,
      c := funext hc }
  rw [← liftWeight_delta, Weight.delta, Weight.delta, hP, hQ, hAP, hAM]
  rfl

theorem lifts_one {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} (hBo : BaseOf Rl.toRealDat j B) {k : GA D (Wc D j)}
    (hk : Lev.IsLevelLift (Wc D j) (Rl.βW j) (Rl.toRealDat.datWp j Rl.toRealDat.triv) 1 k) : GlobalTheory.ExportType.Lifts B 1 k := by
  refine ⟨hk.1, by rw [hBo.βT]; exact parLev_St hk.2.1, fun PP => ?_⟩
  rw [hBo.βT]
  exact (eq_one_of_full_upper_block_eq_one _ (FWT.rank_Wc j) (congrFun hk.2.2 ⟨PP.1, (Finset.ext_iff.1 hBo.Pg PP.1).1 PP.2⟩)).symm

end Core

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

include YS in

theorem isLevDatum_vecBase {F : Face D A3.A} (hT : LawsJ T) (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hgal : IsGalois ℚ D.LL0)
    (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {k : Subfield ℂ}
    (hk : (embLL0 D).fieldRange ≤ k) (hχ : ∀ p, (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ k)
    (hδ : ∀ x, (((ρ.B i j b).de.chi x : Circle) : ℂ) ∈ k) :
    IsLevDatum Rl.ψ (Vc D j) (Wc D j) (Rl.ΛV j) (Rl.ΛW j) (T.Q.l.M * pdAt D (D.ntw.l i)) k (Rl.vacP j) (ρ.B i j b).vecBase := by
  classical
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := hT.toLawsM.pins.2.1.1
  have hQ : ∀ PP ∈ (ρ.B i j b).de.Q, ((pdAt D (D.ntw.l i) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => by
    rw [hρ.delta i j b] at hPP
    exact (mem_pD_iff i PP).1 (mem_half.1 hPP).1
  rw [← hBo.ψ, ← hBo.ΛS, ← hBo.ΛT, ← hBo.vac]
  refine isLevDatum_vec hB.frame (Base.admissible_empty_of_good hB).1 ?_ ?_ ?_ (omegaG_mem _ hχ fun PP hPP u => ?_) fun y => ?_
  · rintro PP (hPP | hPP)
    · obtain ⟨a, ha⟩ := hρ.Pg i j b PP hPP
      exact GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (GlobalTheory.CoverHalf.g_coprime D a) ha
    · exact GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (deltaPrime_isAuxiliarySplitSquarefreeLevel hsp _).2.2.2.2 (hQ PP (by simpa using hPP))
  · intro y y' hy
    unfold Base.locFn
    rw [Finset.prod_congr rfl fun PP hPP => by rw [hy PP (by simpa using hPP)]]
  · rintro PP (hPP | hPP)
    · obtain ⟨a, ha⟩ := hρ.Pg i j b PP hPP
      rw [hMg, Nat.cast_mul, Nat.cast_mul]
      refine Ideal.mul_mem_right _ _ ?_
      fin_cases a
      · exact Ideal.mul_mem_right _ _ ha
      · exact Ideal.mul_mem_left _ _ ha
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (hQ PP (by simpa using hPP))
  · have hP : PP ∈ Rl.Pg := (Finset.ext_iff.1 hBo.Pg PP).1 hPP
    rw [hBo.muC_eq hcore.lev hB hP, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact inv_mem (hk (GlobalTheory.T.typePlace_residueCharacters_values_mem_smallField D Γ Pl0 I0 T0 A3 T Rl cG S YS F hT hcore hgal hval hroots j PP hP u))
  · unfold Base.locFn
    refine mul_mem (prod_mem fun PP hPP => ?_) (prod_mem fun _ _ => one_mem _)
    unfold flat
    split_ifs with h
    · obtain ⟨x, hx⟩ := exists_isLocUnit (hB.de.split.isIdemAt hPP) h.unit
      have e := hx.eq (hB.de.res PP hPP)
      have := hδ x
      rw [e] at this
      exact this
    · exact zero_mem _

theorem ratBase_of_readsAs (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (hti : TieIn T Rl.toRealDat κ v₀)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} {c₁ : ℂ} (hc₁ : c₁ ≠ 0) (hrd : ReadsAs T YS κ v₀ hV c₁)
    (hχ : ∀ p, (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ (ρ.e i b).fieldRange)
    {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν) : RatBase (realRd YS v₀ hρ i j b (c₁⁻¹ * ν)) := by
  have hν0 := mul_ne_zero (inv_ne_zero hc₁) hν.ne_zero
  obtain ⟨gR, cR, cL, -, u, hu, c, ph, -, -, rfl, hsc, hrat⟩ := hν
  have hT := hti.laws
  have hB := hρ.base i j b
  have hBo := baseOf_of_realPin hcore.lev hρ hpin i j b

  obtain ⟨nδ, hnδ, hδ⟩ := de_values hρ i j b
  have hcard : Nat.card (ρ.B i j b).G.P.H ≠ 0 := Nat.card_pos.ne'
  haveI := GlobalTheory.CoverSmall.smallF_normal D hgal
  obtain ⟨L, _, _, hL0, hLe, hLr⟩ := exists_normal_roots (GlobalTheory.CoverSmall.smallF D) (k := (ρ.e i b).fieldRange)
    (by rintro _ ⟨x, rfl⟩; exact ⟨_, hρ.e_LL0 i b x⟩) (mul_ne_zero hcard hnδ)
  obtain ⟨C, hpd, hfr, hC⟩ := exists_goodCover_pdAt YS hRF hT hti.alg hval hray hsp (D.ntw.l i) j (κ j).n L hL0
  have hLL : (embLL0 D).fieldRange ≤ C.σ₂.fieldRange := by
    rw [hfr]; exact fun z hz => hL0 hz
  have hdat := isLevDatum_vecBase YS hT hcore hgal hval hroots hsp hρ hpin i j b hLL
    (fun p => by
      rw [hfr]
      refine hLr _ (hχ p) ?_
      rw [pow_mul, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one, one_pow])
    (fun x => by
      rw [hfr]
      exact hLr _ (hδ x).2 (by rw [pow_mul', (hδ x).1, one_pow]))
  rw [← hpd] at hdat
  have htw : IsTwist C.d.pd C.σ₂ (Rl.C.delAt (D.ntw.l i)) (ρ.B i j b).de.chi := by
    rw [hpd]; exact isTwist_delAt Rl.C hval _ (hpin.delta i j b) hLL
  have hω := hρ.weil_base i j b
  have hω' : IsWeilDatumO Rl.ψ (Vc D j) (Wc D j) (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup Rl.mu0 (ρ.B i j b).de.chi) Rl.eta ((j : ℕ) + 1)).2 (ρ.om i j b 1) := by
    have h1 := hω
    rw [Base.IsWeil, mul_one, Base.mu, hBo.ψ, hBo.mu0, hBo.eta] at h1
    exact h1

  have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
    have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at h2
    exact h2.le
  have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ (ρ.B i j b).w (ρ.B i j b).F.BS hB.wt hm
  intro s h P hd
  refine mem_range_of_small _ ((ρ.B i j b).theta (ρ.om i j b 1) h) hinj (fun G => ?_) (fun P hP G hPG => ?_) hd.mem
  · have h3 : coefFn (embLL0 D) (ρ.B i j b).w.lam (G : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) ∈
        (harm (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS).map (harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS) := by
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ _ _ hB.wt hm]
      exact Submodule.subset_span ⟨GlobalTheory.CoefModel.mapVV (embLL0 D) _ G, (Scale.coefFn_map _ _ _).symm⟩
    exact h3
  · obtain ⟨G', hG', hPG'⟩ : ∃ G' : VV D.what₂.LL (FWT.lamV D j),
        (∀ m, D.what₂.embLL (MvPolynomial.coeff m (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) ∈ (embLL0 D).fieldRange) ∧
        harmFn (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS P =
          coefFn D.what₂.embLL (FWT.lamV D j) (G' : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
      rw [hPG]
      have hlam := hBo.lam
      generalize (ρ.B i j b).w.lam = lam at G hlam
      subst hlam
      refine ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV D.LL0.val.toRingHom _ _ G.2⟩, fun m => ⟨MvPolynomial.coeff m G.1, ?_⟩, ?_⟩
      · exact congrArg D.what₂.embLL (MvPolynomial.coeff_map D.LL0.val.toRingHom G.1 m).symm
      · rw [← Scale.coefFn_map, ← Scale.coefFn_map D.what₂.embLL]
        exact congrArg _ (MvPolynomial.map_map _ _ _).symm
    have hP' := hsc.ioP_eq hinj hP (ioP_mem_valSpace hcore hio (hti.hv₀ j _) hB hBo hu _) hPG'
    have hR := ((hrat C hC hLL h hd.fin _ hdat (cL j G') (Submodule.subset_span ⟨G', fun m => hLL (hG' m), rfl⟩)).2 _ _ htw).2 _ hω'
    replace hR : IsRat T j hV C (κ j) ((ph * c) • (ρ.B i j b).theta (ρ.om i j b 1) h P) :=
      (congrArg (IsRat T j hV C (κ j)) (hpin.phase_mul_thetaKO i b hP' ph (ρ.om i j b 1) h (ρ.B i j b).vecBase)).mp hR
    obtain ⟨n, z, x, hz, e⟩ := exists_sum_evW YS hti hnV hcore.lev hpb hrd hC hR fun k hk g => by
      have := GlobalTheory.ExportType.theta_type hB (D.sp.V_sig _) hω (one_mem _) (lifts_one hBo hk) h P g
      rw [show (⟨1, one_mem _⟩ : (ρ.B i j b).G.P.H) = 1 from rfl, map_one, Units.val_one, one_mul] at this
      exact congrArg ((ph * c) * ·) this
    exact mem_range_realRd_of_sum hρ hν0 z (fun k => hLe (hfr ▸ hz k)) x (by rw [mul_smul, e, inv_smul_smul₀ hc₁])

theorem ratBase (hRF : GlobalTheory.NT.RayField) {F : Face D A3.A} (fw : FWTie T Rl.toRealDat κ v₀) (hev : fw.Evaluates)
    (hcore : GlobalTheory.Hk3.Core Rl.toRealDat F) (hio : IoExt Rl.toRealDat) (hpb : T.pb = Rl.C.P.pb)
    (hnV : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hgal : IsGalois ℚ D.LL0) (hval : Formalism.L2.Host.ValLL0 D Rl.C)
    (hray : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (hroots : ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j)
    (hχ : ∀ p, (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ (ρ.e i b).fieldRange)
    {ν : ℂ} (hν : IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν) : RatBase (realRd YS v₀ hρ i j b ν) := by
  have h := ratBase_of_readsAs YS hRF (tieIn_of_fw fw) hcore hio hpb hnV hgal hval hray hroots hsp hρ hpin i j b one_ne_zero
    (readsAs_one YS fw hev hV) hχ hν
  rwa [inv_one, one_mul] at h

theorem chi_mem_of_levelOf {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} (t : ρ.LevelOf Y) (i : X.Tw) (j : Fin D.R.m) (b : Bool)
    (p : (ρ.B i j b).G.P.H) : (((ρ.B i j b).G.P.chi p : ℂˣ) : ℂ) ∈ (ρ.e i b).fieldRange := by
  have h1 : ρ.eG i j b ((ρ.eG i j b).symm p) ∈ (ρ.B i j b).G.P.H := by
    rw [MulEquiv.apply_symm_apply]; exact p.2
  have h2 := t.psiU_eq i j b ⟨_, (t.U_eq i j b _).1 h1⟩ h1
  have h3 : (⟨_, h1⟩ : (ρ.B i j b).G.P.H) = p := Subtype.ext (MulEquiv.apply_symm_apply _ _)
  rw [← h3]
  exact ⟨_, h2.symm⟩

end Main

open GlobalTheory.BigOn.Exp in

theorem ratBase_of_ratHyp : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RealPin Rl cG ρ → ρ.LevelOf D.nexp → RatHyp T Rl F κ v₀ O i j hV → (D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) → ∀ ν, IsRatScalar T Rl κ v₀ hV (ρ.B i j b) ν → RatBase (realRd YS v₀ hρ i j b ν) := by
  intro _ hRF _ D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin hχ H hsp ν hν
  obtain ⟨fw⟩ := H.fw
  exact ratBase YS hRF fw (fw.evaluates_of_lUnif H.unif) H.core H.io
    (GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat H.laws.toLawsM H.core.lev (H.pins.2.tuple ()).half)
    H.size H.galois H.small.val H.small.ray H.small.roots hsp hρ hpin i j b hV (chi_mem_of_levelOf hχ i j b) hν

end GlobalTheory.SeriesTie.BaseRat

end
