import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagVecMemAndSpanStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticeFrameLiftingSpanningVectorsModStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagBasisLiftGramSignedPermutationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCongruenceIffFlagConditionsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterArgumentCongrRootEntrySumModStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLiftedFlagBasisReduceModLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagBasisDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricUnipotentMemOfFlagCongruenceDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagRootSumDualEqSymmetricEdgeSumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralAdeleCongrZeroOfResiduesSquarefreeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimesProductNotMemSqPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePrimePlaceMemOrConjGenusTypePlaceSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConjStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairSlotStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CharacterResidueFieldsEqProdGenericShiftStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdgesStatement

noncomputable section

namespace GlobalTheory.FlagBasis

section Alg
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV
open scoped TensorProduct

theorem flagCond_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (P : B → Prop) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) :
    FlagCond P ρ k (f ε) (m.map f) ↔ FlagCond (fun a => P (f a)) ρ k ε m := by
  have e : ∀ i j, (m.map f - 1) i j = f ((m - 1) i j) := fun i j => by
    simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
    split_ifs <;> simp
  simp only [FlagCond, e, ← map_mul]

theorem rootSum_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (ρ k : ℕ) (ε : A)
    (m : Matrix (Fin n) (Fin n) A) : rootSum ρ k (f ε) (m.map f) = f (rootSum ρ k ε m) := by
  simp only [rootSum, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem flagGram_transpose (K : Type) [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) :
    (flagGram K n ρ k)ᵀ = flagGram K n ρ k := by
  ext i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.transpose_apply, flagGram, dualIdx]
  split_ifs <;> first | rfl | omega

theorem flagCond_of_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (ε : K) {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) := by
  have low : ∀ i j : Fin n, j.val ≤ i.val → ((M : Matrix (Fin n) (Fin n) K) - 1) i j = 0 := by
    intro i j h
    rcases eq_or_lt_of_le h with h | h
    · obtain rfl : j = i := Fin.ext h
      simp [unip_diag hM.1]
    · rw [Matrix.sub_apply, unip_lower hM.1 (show j < i from h), Matrix.one_apply_ne (ne_of_gt (show j < i from h)), sub_zero]
  refine ⟨fun i j _ h => low i j h, fun i j hj hi => ?_, fun i j _ _ h => by rw [low i j h, mul_zero]⟩
  by_cases h : j.val ≤ i.val
  · exact low i j h
  · rw [Matrix.sub_apply, hM.2 i j hi (by omega) hj, Matrix.one_apply_ne (fun e => h (by rw [e])), sub_zero]

theorem flagCond_iff_unipSym {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) {ε ε' : K}
    (hε : (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1)) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k) :
    FlagCond (fun c : K => c = 0) ρ k ε (M : Matrix (Fin n) (Fin n) K) ∧
      FlagCond (fun c : K => c = 0) ρ k ε' (M' : Matrix (Fin n) (Fin n) K) ↔ M ∈ unipSym K n ρ k := by
  have h' : (M : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M' : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k := by
    have := congrArg Matrix.transpose h
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, flagGram_transpose K hn,
      ← Matrix.mul_assoc] at this
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hM => ⟨flagCond_of_unipSym _ hM, flagCond_of_unipSym _ (GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M M' h hM)⟩⟩
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M M' h h1 h2
  · exact GlobalTheory.T.symmetricUnipotent_mem_of_flagBasisDual K n ρ k hn M' M h' (GlobalTheory.T.symmetricUnipotent_mem_of_flagCongruence_dual K n ρ k hn M' M h' h2 h1)

theorem map_eq_zero_of_zmod (I : AutInst) {g : ℕ} {K : Type} [CommRing K] (p : Formalism.L2.Herm.intAf I.F I.E →+* K)
    (hg : (g : K) = 0) {s : Formalism.L2.Herm.intAf I.F I.E} (hs : ZMod' I g s) : p s = 0 := by
  obtain ⟨t, ht, e⟩ := hs
  have : s = (g : Formalism.L2.Herm.intAf I.F I.E) * ⟨t, ht⟩ := Subtype.ext (by simpa using e)
  rw [this, map_mul, map_natCast, hg, zero_mul]

theorem kset_iff (I : AutInst) {β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)} (hβ : IsFrame β I.L) (x : I.Gf) :
    x ∈ I.Kset ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [GlobalTheory.LevSplit.mem_St_iff β I.L hβ, e]
  refine ⟨fun h => ⟨fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I h hy,
    fun y hy => Formalism.L2.SG.Pf.unitaryCongruence.K_mv I (Formalism.L2.SG.Pf.unitaryCongruence.K_inv I h) hy⟩, fun h y => ⟨h.1 y, fun hy => ?_⟩⟩
  have := h.2 _ hy
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

theorem read_in_frame (I : AutInst) (g : ℕ) (hg : g ≠ 0) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (hF : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = 2 * ρ + k + 1)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β)
    (Pg : Finset (Pl I.E)) (hdiv : ∀ PP ∈ Pg, (g : 𝓞 I.E) ∈ PP.asIdeal)
    (hN : ∀ s : Formalism.L2.Herm.intAf I.F I.E,
      (∀ PP ∈ Pg, resS I.F PP s = 0 ∧ resS I.F PP (sigInt I s) = 0) → ZMod' I g s)
    (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (ψ0 : ∀ PP : Pl I.E, AddChar (kP PP) ℂ) (a₁ a₂ : ∀ PP : Pl I.E, kP PP) (ha : ∀ PP ∈ Pg, a₁ PP ≠ 0 ∧ a₂ PP ≠ 0)
    (hχ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, star (psiEf (divN I g s.1)) =
      ∏ PP ∈ Pg, ψ0 PP (a₁ PP * resS I.F PP s + a₂ PP * resS I.F PP (sigInt I s))) :
    ∃ a : ∀ PP : Pl I.E, Fin I.n → Fin I.n → kP PP, (∀ PP ∈ Pg, ∀ i j, symEdge ρ k i j → a PP i j ≠ 0) ∧
      ∀ x : I.Gf, (x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k) ∧
        (x ∈ K2set I g e0 z0 bw → star (chi2f I psiEf g e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (∑ i, ∑ j, if symEdge ρ k i j then
            a PP i j * ((redFn β PP x : GL (Fin I.n) (kP PP)) : Matrix (Fin I.n) (Fin I.n) (kP PP)) i j else 0)) := by
  classical
  obtain ⟨hew, hG⟩ := GlobalTheory.T.liftFrame_gram_congr_flagGram I g e0 f0 z0 bw bwd ew hF hn β hβ
  have hpg : ∀ PP ∈ Pg, (g : kP PP) = 0 := fun PP hPP => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)
  let ewS : Formalism.L2.Herm.intAf I.F I.E := ⟨ew, hF.2.2.2.2.1.2.2.1⟩
  let p' : ∀ PP : Pl I.E, Formalism.L2.Herm.intAf I.F I.E →+* kP PP := fun PP => (resS I.F PP).comp (sigInt I)
  have hε : ∀ PP ∈ Pg, (resS I.F PP ewS = 1 ∧ p' PP ewS = 0) ∨ (resS I.F PP ewS = 0 ∧ p' PP ewS = 1) := by
    intro PP hPP
    have h1 : resS I.F PP (1 - ewS - sigInt I ewS) = 0 := map_eq_zero_of_zmod I _ (hpg PP hPP) hew
    have h2 : ewS * sigInt I ewS = 0 := Subtype.ext hF.2.2.2.2.1.2.1
    have h3 : resS I.F PP ewS * p' PP ewS = 0 := by
      show _ * resS I.F PP (sigInt I ewS) = 0
      rw [← map_mul, h2, map_zero]
    rw [map_sub, map_sub, map_one] at h1
    have h1' : 1 - resS I.F PP ewS - p' PP ewS = 0 := h1
    haveI := PP.isPrime
    rcases mul_eq_zero.1 h3 with h | h
    · exact Or.inr ⟨h, by rw [h] at h1'; linear_combination -h1'⟩
    · exact Or.inl ⟨by rw [h] at h1'; linear_combination -h1', h⟩
  have hZ : ∀ s : Formalism.L2.Herm.intAf I.F I.E, ZMod' I g s ↔ ∀ PP ∈ Pg, resS I.F PP s = 0 ∧ p' PP s = 0 :=
    fun s => ⟨fun h PP hPP => ⟨map_eq_zero_of_zmod I _ (hpg PP hPP) h, map_eq_zero_of_zmod I _ (hpg PP hPP) h⟩, hN s⟩
  have hroot := fun (PP : Pl I.E) (hPP : PP ∈ Pg) => GlobalTheory.T.flagRootSum_dual_eq_symmetricEdge_sum (kP PP) I.n ρ k hn _ _ (a₁ PP) (a₂ PP) (hε PP hPP)
    (ha PP hPP).1 (ha PP hPP).2
  choose! a ha1 ha2 using hroot
  have hmat : ∀ (x : I.Gf) (m : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
      frGL β m = (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
      matIn I β x = (m : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)).map (Formalism.L2.Herm.intAf I.F I.E).subtype := by
    intro x m hm
    unfold matIn
    rw [← hm]
    have : β⁻¹ * frGL β m * β = intGL I.F I.E I.n m := by
      simp only [frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    rfl
  have hrel := fun (x : I.Gf) m hm (PP : Pl I.E) (hPP : PP ∈ Pg) =>
    GlobalTheory.T.unitary_liftedFlagBasis_reduce_mod_level I g ρ k β hG (kP PP) (resS I.F PP) (hpg PP hPP) x m hm
  have main : ∀ x : I.Gf, x ∈ K2set I g e0 z0 bw ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
      ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ k := by
    intro x
    show x ∈ I.Kset ∧ _ ↔ _
    rw [kset_iff I hβ.1]
    refine and_congr_right fun hS => ?_
    rw [GlobalTheory.T.levelCongruence_iff_flag_conditions I g e0 f0 z0 bw bwd ew hF hn β hβ x hS]
    obtain ⟨m, hm⟩ := hS
    rw [hmat x m hm, ← hm]
    refine (flagCond_map (Formalism.L2.Herm.intAf I.F I.E).subtype (ZMod' I g) ρ k ewS _).trans ?_
    have e : ∀ PP ∈ Pg, (redFn β PP (frGL β m) ∈ unipSym (kP PP) I.n ρ k ↔
        FlagCond (fun s => resS I.F PP s = 0) ρ k ewS m.1 ∧ FlagCond (fun s => p' PP s = 0) ρ k ewS m.1) := by
      intro PP hPP
      rw [redFn_frGL, ← flagCond_iff_unipSym hn (hε PP hPP) (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP)]
      exact and_congr (flagCond_map (resS I.F PP) (fun c => c = 0) ρ k ewS m.1) (flagCond_map (p' PP) (fun c => c = 0) ρ k ewS m.1)
    rw [forall₂_congr e]
    constructor
    · rintro ⟨h1, h2, h3⟩ PP hPP
      exact ⟨⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).1, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).1,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).1⟩,
        ⟨fun i j a b => ((hZ _).1 (h1 i j a b) PP hPP).2, fun i j a b => ((hZ _).1 (h2 i j a b) PP hPP).2,
          fun i j a b c => ((hZ _).1 (h3 i j a b c) PP hPP).2⟩⟩
    · intro h
      exact ⟨fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.1 i j a b, (h PP hPP).2.1 i j a b⟩,
        fun i j a b => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.1 i j a b, (h PP hPP).2.2.1 i j a b⟩,
        fun i j a b c => (hZ _).2 fun PP hPP => ⟨(h PP hPP).1.2.2 i j a b c, (h PP hPP).2.2.2 i j a b c⟩⟩
  refine ⟨a, ha1, fun x => ⟨main x, fun hx => ?_⟩⟩
  obtain ⟨hS, hU⟩ := (main x).1 hx
  have hc := GlobalTheory.T.characterArgument_congr_rootEntrySum_mod I g e0 f0 z0 bw bwd ew hF hn β hβ hG x hS
  obtain ⟨m, hm⟩ := hS
  rw [hmat x m hm] at hc
  have hr := rootSum_map (Formalism.L2.Herm.intAf I.F I.E).subtype ρ k ewS m.1
  have hc' : ZMod' I g (chiArg I e0 f0 z0 bw bwd x - (rootSum ρ k ewS m.1).1) := by
    have hr' : rootSum ρ k ew (m.1.map (Formalism.L2.Herm.intAf I.F I.E).subtype) = (rootSum ρ k ewS m.1).1 := hr
    rwa [hr'] at hc
  have e1 : chi2f I psiEf g e0 f0 z0 bw bwd x = psiEf (divN I g (rootSum ρ k ewS m.1).1) := by
    obtain ⟨t, ht, e⟩ := hc'
    rw [flagLevelCharacter_eq_psi_divN, eq_add_of_sub_eq e, Formalism.L2.SG.Pf.unitaryCongruence.divN_add, hadd, Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg, hint t ht, one_mul]
  rw [e1, hχ]
  refine Finset.prod_congr rfl fun PP hPP => congrArg _ ?_
  have hU' := hU PP hPP
  rw [← hm, redFn_frGL] at hU' ⊢
  rw [← ha2 PP hPP (Formalism.UG.bc (resS I.F PP) m) (Formalism.UG.bc (p' PP) m) (hrel x m hm PP hPP) hU']
  exact congrArg₂ (· + ·) (congrArg _ (rootSum_map (resS I.F PP) ρ k ewS m.1).symm)
    (congrArg _ (rootSum_map (p' PP) ρ k ewS m.1).symm)

end Alg

end GlobalTheory.FlagBasis

section Host
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FlagBasis.read_inst (D : D7) (e0 f0 : Fin D.R.rS → VA (instOf D)) (z0 : VA (instOf D))
    (bw bwd : Fin D.R.k → VA (instOf D)) (ew : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F)
    (hF : IsRefFrame (instOf D) (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd ew) (hn : (instOf D).n = D.R.r)
    (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ) (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y)
    (hint : ∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1)
    (hrat : ∀ x : (instOf D).E,
      psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D),
      IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ x : (instOf D).Gf, (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw ↔
          (x.1 : GL (Fin (D.sp.Y 0).rank) (Formalism.IndefR.Lev.EAf D)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x.1 ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        (x ∈ K2set (instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw →
          star (chi2f (instOf D) psiEf (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd x) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP x.1))) := by
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1 := by
    rw [hn]
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | h⟩ := GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ
    · exact (hs _ hPP).1
    · exact (h s).2 (hs _ hPP).2
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ
    (fun s t => (congrArg (fun z => star (psiEf z))
        (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans (by rw [hadd, star_mul']))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1
      rw [this, hint t ht, star_one])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by
      obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ
      exact ⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)
  obtain ⟨a, ha1, hK⟩ := read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ
  have hL : (instOf D).L = Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := Lv_eq_map D
  obtain ⟨β, hβ, hSt, hred⟩ := GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges (D := D) (n := (D.sp.Y 0).rank) D.R.rS D.R.k Pg _ β₀ hβ₀.1 a ha1
  refine ⟨β, hL ▸ hβ, fun x => ⟨?_, fun hx => ?_⟩⟩
  · rw [hSt]
    exact (hK x).1.trans (and_congr_right fun hS => forall₂_congr fun PP hPP => (hred PP hPP _ hS).1.symm)
  · exact ((hK x).2 hx).trans
      (Finset.prod_congr rfl fun PP hPP => congrArg _ (hred PP hPP _ ((hK x).1.1 hx).1).2)

end Host

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjRead

open Formalism.L2.DIV

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (hr : n ≤ n) (g : GL (Fin n) κ) : upperLeftBlock hr g = g := by
  have hg : g ∈ blockTri (κ := κ) (blk2 n) := fun i j h => by
    simp [blk2, i.2, j.2] at h
  apply Units.ext
  rw [upper_block_val_submatrix hr hg]
  ext i j
  simp

theorem blockTri_blkOf_top {κ : Type} [CommRing κ] {n r : ℕ} (t : ℕ) (hn : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ blockTri (κ := κ) (blkOf r t) := fun i j h => by
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blkOf, hi, hj] at h

theorem iotaX_fst_eq_one_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) : (iotaX X h κ).1 = 1 ↔ κ ∈ GfC (D.sp.Y 0) := by
  have key : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
      (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA), ((castGA hI.symm) y).1 = 1 ↔ y.1 = 1 := by
    intro I hI y
    subst hI
    exact Iff.rfl
  show ((castGA h.symm) (Formalism.IndefR.RationalEmbedding.iota D κ)).1 = 1 ↔ _
  rw [key X.B.I h, ← Formalism.L2.SG.EvalTIota.brg_mem_GfC_i, ContinuousMulEquiv.symm_apply_apply]

theorem eq_symm_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (D.sp.Y 0)) (h1 : (iotaX X h κ).1 = 1) : (iotaX X h).symm (1, (iotaX X h κ).2) = κ := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact Prod.ext h1.symm rfl

end GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjRead.read_fin {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (Pg : Finset (Pl D.host.E)) (hPg : GlobalTheory.Core.Mi.IsTypePlaces Pg)
    (hnc : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (hψ : IsGenericPsi Pg ψ0) :
    ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((iotaX X h κ).2 ∈ X.K2 ↔ Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((iotaX X h κ).2 ∈ X.K2 → star (X.chi2 (iotaX X h κ).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
  have key : ∀ (I : AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (g : ℕ) (_ : g = D.host.g 0 * D.host.g 1)
      (e0 f0 : Fin D.R.rS → VA I) (z0 : VA I) (bw bwd : Fin D.R.k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
      (_ : GlobalTheory.FlagBasis.IsRefFrame I g e0 f0 z0 bw bwd ew) (_ : I.n = D.R.r) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
      (_ : ∀ x y, psiEf (x + y) = psiEf x * psiEf y) (_ : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
      (_ : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1),
      ∃ β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0) ∧
      ∀ κ : GA D (D.sp.Y 0), ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw ↔
          Lev.finE (D.sp.Y 0) κ ∈ Formalism.L2.DIV.St β ∧
          ∀ PP ∈ Pg, redFn β PP (Lev.finE (D.sp.Y 0) κ) ∈ unipSym (kP PP) (D.sp.Y 0).rank D.R.rS D.R.k) ∧
        ((castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2 ∈ K2set I g e0 z0 bw →
          star (chi2f I psiEf g e0 f0 z0 bw bwd (castGA hI.symm (Formalism.IndefR.RationalEmbedding.iota D κ)).2) =
          ∏ PP ∈ Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (redFn β PP (Lev.finE (D.sp.Y 0) κ)))) := by
    intro I hI g hg e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat
    subst hI hg
    obtain ⟨β, hβ, hK⟩ := GlobalTheory.FlagBasis.read_inst D e0 f0 z0 bw bwd ew hF hn psiEf hadd hint hrat Pg hPg hnc ψ0 hψ
    refine ⟨β, hβ, fun κ => ?_⟩
    have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    have e2 : Lev.finE (D.sp.Y 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) :=
      (congrArg (Lev.finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
    have hx := hK (Formalism.IndefR.RationalEmbedding.iota D κ).2
    generalize Lev.finE (D.sp.Y 0) κ = y at e2 ⊢
    subst e2
    exact hx
  exact key X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew (GlobalTheory.FlagBasis.isRefFrame_setting X) X.n_eq X.psiEf
    X.psiEf_add X.psiEf_int X.psiEf_rat

end Main

end
