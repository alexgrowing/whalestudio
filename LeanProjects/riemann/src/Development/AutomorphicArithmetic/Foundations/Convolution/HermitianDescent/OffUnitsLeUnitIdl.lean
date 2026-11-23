import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTriStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharCMEtaLocalEqNegOnePowValInertStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOtherSplitPlaceWithDistinctRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.ConvolutionTheory.D.MultiplierQuotient

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj conj finiteCompletionMap)
open Neutral.B1 (Ideles diagUnits localIdele)
open GlobalTheory.ConsEta (unitDir infSign conjQuot)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_split_avoid (S : Set (HeightOneSpectrum (𝓞 E))) (hS : S.Finite) :
    ∃ w₀ : HeightOneSpectrum (𝓞 E), IsSplitAt w₀ ∧
      ∀ w ∈ S, w.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  classical
  obtain ⟨p, hp, hmp, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E
    (∑ w ∈ hS.toFinset, Ideal.absNorm w.asIdeal)
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hsplit : ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
    intro w hw
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      rwa [map_natCast]
    obtain ⟨a, b, hab, ha, hb⟩ :=
      GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
    by_cases h : a = w
    · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
    · exact ⟨a, h, HeightOneSpectrum.ext ha⟩
  haveI hPmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hinj : Function.Injective (algebraMap ℤ (𝓞 E)) := (algebraMap ℤ (𝓞 E)).injective_int
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E)
    (Ideal.span {(p : ℤ)}) (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := hQ ▸ Ideal.subset_span rfl
    simpa using this
  have hp0 : (p : 𝓞 E) ≠ 0 := by exact_mod_cast hp.ne_zero
  let w₁ : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, fun h => hp0 (by rw [h] at hpQ; simpa using hpQ)⟩
  refine ⟨w₁, hsplit w₁ hpQ, fun w hw heq => ?_⟩
  have hlt : Ideal.absNorm w.asIdeal < p :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun w : HeightOneSpectrum (𝓞 E) => Ideal.absNorm w.asIdeal)
      (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.2 hw)) hmp
  have hpw : (p : 𝓞 E) ∈ w.asIdeal := by
    have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w₁.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w₁.asIdeal
      rw [map_natCast]; exact hpQ
    rw [← heq] at hv
    have : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  have hN : ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hN0 : 0 < Ideal.absNorm w.asIdeal :=
    Nat.pos_of_ne_zero (fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hcop : Nat.Coprime p (Ideal.absNorm w.asIdeal) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => absurd (Nat.le_of_dvd hN0 h) (not_le.mpr hlt))
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom (𝓞 E))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hpw
  · simpa using hN

private noncomputable def offUnits (w₀ : HeightOneSpectrum (𝓞 E)) : Subgroup (Ideles E) :=
  Subgroup.closure {x | ∃ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ),
    w.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) ∧
      Valued.v (u : w.adicCompletion E) = 1 ∧ x = localIdele E w u}

private theorem offUnits_le_unitIdl (w₀ : HeightOneSpectrum (𝓞 E)) : offUnits w₀ ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, u, -, hu, rfl⟩ v
  by_cases hv : v = w
  · subst hv
    rw [Neutral.B1.localIdele_snd_self]; exact hu
  · rw [((Neutral.B1.localIdele_isSupportedAt E w u).2 v hv)]; exact map_one _

private theorem conjQuot_off (w₀ : HeightOneSpectrum (𝓞 E)) {u : Ideles E} (hu : u ∈ offUnits w₀) :
    conjQuot E w₀ u = 1 := by
  have key : offUnits w₀ ≤ (conjQuot E w₀).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w', a, hunder, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    have hne : w' ≠ w₀ := fun h => hunder (h ▸ rfl)
    have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (localIdele E w' a) = 1 :=
      Units.ext ((Neutral.B1.localIdele_isSupportedAt E w' a).2 w₀ hne.symm)
    have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w₀)
        (ideleConj (maximalRealSubfield E) E (localIdele E w' a)) = 1 :=
      GlobalTheory.ConsEta.finEval_ideleMap_localIdele (F := maximalRealSubfield E)
        (alg := (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra)
        (fun x => (conj (maximalRealSubfield E) E).commutes x) w₀ w' hunder a
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  exact key hu

private noncomputable def dirAt (w : InfinitePlace E) : Ideles E →* ℂˣ :=
  unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
    (Units.map (GlobalTheory.IdeleNormChar.infEval w)))

private noncomputable def psi (e : InfinitePlace E → ℤ) : Ideles E →* ℂˣ := ∏ w, dirAt w ^ e w

private theorem psi_apply (e : InfinitePlace E → ℤ) (x : Ideles E) : psi e x = ∏ w, dirAt w x ^ e w := by
  rw [psi, MonoidHom.finset_prod_apply]
  rfl

private theorem continuous_dirAt (w : InfinitePlace E) : Continuous (dirAt (E := E) w) := by
  refine GlobalTheory.ConsEta.continuous_unitDir.comp ((Continuous.units_map _ ?_).comp (Continuous.units_map _ ?_))
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · exact (continuous_apply w).comp continuous_fst

private theorem continuous_psi (e : InfinitePlace E → ℤ) : Continuous (psi e) := by
  have : ⇑(psi e) = fun x => ∏ w, dirAt w x ^ e w := funext (psi_apply e)
  rw [this]
  exact continuous_finset_prod _ fun w _ => (continuous_dirAt w).zpow _

private theorem norm_psi (e : InfinitePlace E → ℤ) (x : Ideles E) : ‖((psi e x : ℂˣ) : ℂ)‖ = 1 := by
  rw [psi_apply, Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [Units.val_zpow_eq_zpow_val, norm_zpow]
  have : ‖((dirAt w x : ℂˣ) : ℂ)‖ = 1 := GlobalTheory.ConsEta.norm_unitDir _
  rw [this, one_zpow]

private theorem psi_off (e : InfinitePlace E → ℤ) (w₀ : HeightOneSpectrum (𝓞 E)) {u : Ideles E}
    (hu : u ∈ offUnits w₀) : psi e u = 1 := by
  have key : offUnits w₀ ≤ (psi e).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w, a, -, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, psi_apply]
    refine Finset.prod_eq_one fun v _ => ?_
    have : Units.map (GlobalTheory.IdeleNormChar.infEval v) (localIdele E w a) = 1 := Units.ext rfl
    simp only [dirAt, MonoidHom.comp_apply, this, map_one, one_zpow]
  exact key hu

private theorem psi_ideleMap (e : InfinitePlace E → ℤ) (he : ∀ v, Odd (e v))
    (b : Ideles (maximalRealSubfield E)) :
    psi e (ideleMap (maximalRealSubfield E) E b) = infSign E (ideleMap (maximalRealSubfield E) E b) := by
  rw [psi_apply, infSign, MonoidHom.finset_prod_apply]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  have hs : dirAt w (ideleMap (maximalRealSubfield E) E b) = Units.map (Int.castRingHom ℂ).toMonoidHom
      (if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        ((GlobalTheory.IdeleNormChar.infComp b (w.comap (algebraMap (maximalRealSubfield E) E)) : _) : _) then 1 else -1) := by
    refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
    · intro h'
      exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
        ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
    · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
  change dirAt w _ ^ e w = dirAt w _
  rw [hs]
  split_ifs
  · simp
  · rw [← map_zpow, (he w).neg_one_zpow]

private theorem quadChar_unr (w : HeightOneSpectrum (𝓞 E))
    (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (GlobalTheory.GalOfCusp.quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      have := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

private theorem quadChar_finPart (hU : GlobalTheory.BCT.Unr E) (b : Ideles (maximalRealSubfield E))
    (hb : b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E)) :
    (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    have := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) (GlobalTheory.GalOfCusp.quadChar E).1
    (GlobalTheory.GalOfCusp.quadChar E).2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hb) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hb v
  obtain ⟨w, rfl⟩ := hs v
  exact quadChar_unr w (hU w) x hxu

private theorem infSign_finPart (b : Ideles (maximalRealSubfield E)) :
    infSign E (ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
  rw [infSign, MonoidHom.finset_prod_apply]
  refine Finset.prod_eq_one fun w _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval w)
      (ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
    refine Units.ext ?_
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E 1) w = 1
    rw [map_one]; rfl
  simp only [MonoidHom.comp_apply, this, map_one]

private theorem eta_eq_infSign (hU : GlobalTheory.BCT.Unr E) (b : Ideles (maximalRealSubfield E))
    (hb : b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E)) :
    (GlobalTheory.GalOfCusp.quadChar E).1 b = infSign E (ideleMap (maximalRealSubfield E) E b) := by
  set f := GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b
  have h1 : ∀ v, ((b * f⁻¹ : Ideles _) : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1 := by
    intro v
    have e : f⁻¹ = GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b⁻¹ := (map_inv _ b).symm
    rw [e]
    exact congrArg (fun z : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) => z.2 v) b.mul_inv
  have h2 := GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial E _ h1
  have h3 := quadChar_finPart hU b hb
  have e1 : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 (b * f⁻¹) * (GlobalTheory.GalOfCusp.quadChar E).1 f := by
    rw [← map_mul, inv_mul_cancel_right]
  have e2 : infSign E (ideleMap (maximalRealSubfield E) E b) =
      infSign E (ideleMap (maximalRealSubfield E) E (b * f⁻¹)) *
        infSign E (ideleMap (maximalRealSubfield E) E f) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [e1, e2, h2, h3, infSign_finPart, mul_one]

private noncomputable def opn (w₀ : HeightOneSpectrum (𝓞 E)) (V : Subgroup (w₀.adicCompletion E)ˣ) :
    Subgroup (Ideles E) :=
  GlobalTheory.Mem.Chr.unitIdl E ⊓ (GlobalTheory.Mem.Chr.unitIdl E).comap (ideleConj (maximalRealSubfield E) E) ⊓
    V.comap (conjQuot E w₀)

private theorem isOpen_opn (w₀ : HeightOneSpectrum (𝓞 E)) (V : Subgroup (w₀.adicCompletion E)ˣ)
    (hV : IsOpen (V : Set (w₀.adicCompletion E)ˣ)) : IsOpen (opn w₀ V : Set (Ideles E)) := by
  have hC : Continuous (ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.preimage hC)).inter
    (hV.preimage (GlobalTheory.ConsEta.continuous_conjQuot w₀))

private theorem consistent (hU : GlobalTheory.BCT.Unr E) (w₀ : HeightOneSpectrum (𝓞 E)) (V : Subgroup (w₀.adicCompletion E)ˣ)
    (hV : ∀ t : Eˣ, (∃ n : ℕ, 0 < n ∧ t ^ n = 1) →
      Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom t ∈ V → t = 1)
    (e : InfinitePlace E → ℤ) (he : ∀ v, Odd (e v)) (k : Eˣ) (b : Ideles (maximalRealSubfield E)) (u : Ideles E)
    (hu : u ∈ offUnits w₀) (hx : diagUnits E k * ideleMap (maximalRealSubfield E) E b * u ∈ opn w₀ V) :
    (GlobalTheory.GalOfCusp.quadChar E).1 b = psi e (diagUnits E k * ideleMap (maximalRealSubfield E) E b * u) := by
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hu1 := offUnits_le_unitIdl w₀ hu
  have hCu := GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles E u hu1
  set C := ideleConj (maximalRealSubfield E) E with hCdef
  set I := ideleMap (maximalRealSubfield E) E b with hI
  set c : Eˣ →* Eˣ := Units.map (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toMonoidHom with hc
  have hCx : C (diagUnits E k * I * u) = diagUnits E (c k) * I * C u := by
    rw [map_mul, map_mul, hI, GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield]
    congr 2
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (maximalRealSubfield E) E k
  set x := diagUnits E k * I * u with hxdef
  set t : Eˣ := k / c k with ht
  have hdt : diagUnits E t = (x / C x) * (u / C u)⁻¹ := by
    rw [hCx, hxdef, ht, _root_.map_div]
    exact GlobalTheory.ConsEta.commGroup_div_eq_mul_div_mul_inv_div _ _ _ _ _
  have htu : diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    rw [hdt]; exact mul_mem (div_mem hx1 hx2) (inv_mem (div_mem hu1 hCu))
  have hnorm : ∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1 := by
    intro φ
    have h0 : φ (k : E) ≠ 0 := by simp
    have e : φ ((c k : Eˣ) : E) = starRingEnd ℂ (φ k) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
    rw [ht, Units.val_div_eq_div_val, map_div₀, e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]
  have htor := GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one E t htu hnorm
  have hcqu := conjQuot_off w₀ hu
  have hmem : Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom t ∈ V := by
    have e1 : Units.map (algebraMap E (w₀.adicCompletion E)).toMonoidHom t =
        Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (diagUnits E t) := Units.ext rfl
    have e2 : conjQuot E w₀ x = Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (x / C x) := rfl
    have e3 : conjQuot E w₀ u = Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (u / C u) := rfl
    rw [e1, hdt, map_mul, map_inv, ← e2, ← e3, hcqu, inv_one, mul_one]
    exact hx3
  have ht1 := hV t htor hmem
  have hck : c k = k := (div_eq_one.1 ht1).symm
  have hkF : (k : E) ∈ maximalRealSubfield E := by
    refine (IsCMField.complexConj_eq_self_iff E _).1 ?_
    exact congrArg Units.val hck
  set k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨(k : E), hkF⟩ (fun h => k.ne_zero (congrArg Subtype.val h)) with hk'
  have hdk : diagUnits E k = ideleMap (maximalRealSubfield E) E (diagUnits (maximalRealSubfield E) k') := by
    refine (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (maximalRealSubfield E) E k').trans ?_ |>.symm
    exact congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E) (Units.ext rfl)
  set b' := diagUnits (maximalRealSubfield E) k' * b with hb'
  have hxb : x = ideleMap (maximalRealSubfield E) E b' * u := by
    rw [hxdef, hdk, hb', map_mul]
  have hηb : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 b' := by
    rw [hb', map_mul, (GlobalTheory.GalOfCusp.quadChar E).2.2 k', one_mul]
  have hb'E : ideleMap (maximalRealSubfield E) E b' ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    have : ideleMap (maximalRealSubfield E) E b' = x * u⁻¹ := by rw [hxb, mul_inv_cancel_right]
    rw [this]; exact mul_mem hx1 (inv_mem hu1)
  rw [hηb, eta_eq_infSign hU b' (GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield E b' hb'E), hxb, (psi e).map_mul _ u, psi_off e w₀ hu, mul_one,
    psi_ideleMap e he]

private theorem quadChar_norm (b : Ideles (maximalRealSubfield E)) :
    ‖(((GlobalTheory.GalOfCusp.quadChar E).1 b : ℂˣ) : ℂ)‖ = 1 := by
  change ‖((Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E b) : ℂˣ) : ℂ)‖ = 1
  rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E b) with h | h <;> rw [h] <;> simp

private theorem infId_snd (z : (Cinf E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((infId E z : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  have h : pFin E (infId E z).val = (1 : Af E) := by
    change (1 - 0 + 0 : Af E) = 1
    simp
  exact congrArg (fun a : FiniteAdeleRing (𝓞 E) E => a w) h

private theorem ext_infId (z : (Cinf E)ˣ) (v : InfinitePlace E) :
    InfinitePlace.Completion.extensionEmbedding v (((infId E z : Ideles E) : AdeleRing (𝓞 E) E).1 v) = z.1 v := by
  have h1 : pInf E (infId E z).val = z.val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E z.val) = _
    simp
  exact congrFun h1 v

private theorem infId_mem (w₀ : HeightOneSpectrum (𝓞 E)) (V : Subgroup (w₀.adicCompletion E)ˣ) (z : (Cinf E)ˣ) :
    infId E z ∈ opn w₀ V := by
  have hsnd : ((infId E z : Ideles E) : AdeleRing (𝓞 E) E).2 = 1 := FiniteAdeleRing.ext _ (infId_snd z)
  have hC : ∀ w, ((ideleConj (maximalRealSubfield E) E (infId E z) : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := fun w => by
    have e : ((ideleConj (maximalRealSubfield E) E (infId E z) : Ideles E) : AdeleRing (𝓞 E) E).2 =
        @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap E E _ _ _ _ (conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
          ((infId E z : Ideles E) : AdeleRing (𝓞 E) E).2 := rfl
    rw [e, hsnd, map_one]
    rfl
  have h1 : Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (infId E z) = 1 := Units.ext (infId_snd z w₀)
  have h2 : Units.map (GlobalTheory.IdeleNormChar.finEval w₀) (ideleConj (maximalRealSubfield E) E (infId E z)) = 1 :=
    Units.ext (hC w₀)
  have h3 : conjQuot E w₀ (infId E z) = 1 := by
    simp only [conjQuot, MonoidHom.comp_apply, MonoidHom.div_apply, MonoidHom.id_apply, _root_.map_div, h1, h2, div_one]
  refine ⟨⟨fun w => ?_, fun w => ?_⟩, ?_⟩
  · show Valued.v (((infId E z : Ideles E) : AdeleRing (𝓞 E) E).2 w) = 1
    rw [infId_snd, map_one]
  · show Valued.v (((ideleConj (maximalRealSubfield E) E (infId E z) : Ideles E) : AdeleRing (𝓞 E) E).2 w) = 1
    rw [hC, map_one]
  · show conjQuot E w₀ (infId E z) ∈ V
    rw [h3]
    exact one_mem _

private theorem psi_infId (e : InfinitePlace E → ℤ) (z : (Cinf E)ˣ) :
    ((psi e (infId E z) : ℂˣ) : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v := by
  rw [psi_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  congr 1
  change (InfinitePlace.Completion.extensionEmbedding v (((infId E z : Ideles E) : AdeleRing (𝓞 E) E).1 v)) /
    (‖InfinitePlace.Completion.extensionEmbedding v (((infId E z : Ideles E) : AdeleRing (𝓞 E) E).1 v)‖ : ℂ) = _
  rw [ext_infId]

end UpperTheory.ConvolutionTheory.D.MultiplierQuotient

open UpperTheory.ConvolutionTheory.D.MultiplierQuotient in
theorem UpperTheory.ConvolutionTheory.D.muEx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → ∀ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) →
    ∃ μ : HChar E, (μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
      (∀ w : HeightOneSpectrum (𝓞 E), ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
      ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v) ∧ ∀ w ∈ S, μ.UnrAt w := by
  intro E _ _ _ hU S hS e he
  obtain ⟨w₀, hw₀, hSw⟩ := exists_split_avoid S hS
  obtain ⟨V, hVo, hV⟩ := GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity E w₀
  let α : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × offUnits w₀) →* Neutral.B1.Ideles E :=
    (Neutral.B1.diagUnits E).coprod ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E).coprod (offUnits w₀).subtype)
  let a : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × offUnits w₀) →* ℂˣ :=
    (GlobalTheory.GalOfCusp.quadChar E).1.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))
  have hα : ∀ y, α y = Neutral.B1.diagUnits E y.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E y.2.1 *
      (y.2.2 : Neutral.B1.Ideles E) := fun y => by
    simp only [α, MonoidHom.coprod_apply, Subgroup.coe_subtype, mul_assoc]
  obtain ⟨χ, hχc, hχu, hχU, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) _
    (opn w₀ V) (isOpen_opn w₀ V hVo) α a (psi e) (continuous_psi e) (norm_psi e)
    (fun y => quadChar_norm y.2.1) (fun y hy => by
      rw [hα] at hy ⊢
      exact consistent hU w₀ V hV e he y.1 y.2.1 y.2.2 y.2.2.2 hy)
  have hk : ∀ k : Eˣ, χ (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have h := hχα (k, 1, 1)
    rw [hα] at h
    simpa [a] using h
  let μ : HChar E := ⟨χ, hχc, hk⟩
  have hres : ∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x :=
    fun x => by
      have h := hχα (1, x, 1)
      rw [hα] at h
      simpa [a] using h
  have hoff : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ),
      w.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) →
      Valued.v (u : w.adicCompletion E) = 1 → μ.1 (Neutral.B1.localIdele E w u) = 1 := fun w u hw hu => by
    have h := hχα (1, 1, ⟨_, Subgroup.subset_closure ⟨w, u, hw, hu, rfl⟩⟩)
    rw [hα] at h
    simpa [a] using h
  have hns : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w →
      Valued.v (u : w.adicCompletion E) = 1 → μ.1 (Neutral.B1.localIdele E w u) = 1 := fun w u hw hu =>
    hoff w u (fun h => hw (GlobalTheory.ConsEta.isSplitAt_of_under_eq hw₀ h)) hu
  refine ⟨μ, ⟨hχu, hres, GlobalTheory.T.heckeCharCM_eta_local_eq_neg_one_pow_val_inert E hU μ hres hns, he, fun z => ?_⟩, fun w hw x hx => hoff w x (hSw w hw) hx⟩
  have h := hχU _ (infId_mem w₀ V z)
  change ((χ (infId E z) : ℂˣ) : ℂ) = _
  rw [h, psi_infId]
