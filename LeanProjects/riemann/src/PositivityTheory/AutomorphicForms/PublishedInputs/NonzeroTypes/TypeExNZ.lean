import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsTypeWeilDeligneIffMonodromyZeroCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PiFamilyProdHomBijectiveCharacterization
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem te_unr {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {w : Plc L}
    {A : ValuationSubring Ω} {h : IsPlaceOver A w} (x : WD h) (t : ℝ) :
    ((x.lpTw t).mono0 ↔ x.mono0) ∧ ∀ s, (x.lpTw t).charPol (ineIncl h s) = x.charPol (ineIncl h s) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk]
  exact ⟨by simp, fun s => by simp⟩

private theorem te_loc (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) (NZ : UpperTheory.NonzeroTypeTheory.NZ) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ)
    {w : Plc L} {A : ValuationSubring Ω} (h : IsPlaceOver A w) (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (χ : Fin n → Dec (F := L) A →* ℂˣ)
    (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := L) A))) (hv : ∀ i g, (χ i g : ℂ) ∈ (algebraMap O ℂ).range) :
    ∃ (m : ℕ) (τ : KO (w.adicCompletion L) (Fin n) →* GL (Fin m) O), IsOpen (τ.ker : Set (KO (w.adicCompletion L) (Fin n))) ∧
      ∀ π : SmIrr (GLw n w), (∃ y : Fin m → π.V, y ≠ 0 ∧ ∀ (k : KO (w.adicCompletion L) (Fin n)) i,
        ∑ a, algebraMap O ℂ (τ k i a) • π.ρ k (y a) = y i) ↔
        ∀ rc, IsRec h rc → IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm π)) := by
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.loc.llc P.loc.conv P.loc.dzc P.loc.dzi
      P.loc.brauer P.loc.chev P.aut.art P.loc.exh P.loc.multi P.loc.cos P.loc.zel
      P.loc.geo P.loc.bz
  obtain ⟨rc, hrc, hu⟩ := hL.1 L Ω A w h
  have hsm : ∀ i, IsSmooth (h := h) ((χ i).comp (Subgroup.inclusion (Weil_le_Dec h))) := fun i =>
    (ho i).preimage (f := Subgroup.inclusion (Ine_le_Dec (F := L) A)) (continuous_inclusion (Ine_le_Dec (F := L) A))
  have hT := NZ L Ω A w h rc hrc n χ ho
  rw [← show KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w n from SphCompletion.KO_completion w n] at hT
  obtain ⟨d, ξ, -, hξ, hπ⟩ := hT
  refine typeLoc O _ _ GlobalTheory.SplitFlip.isCompact_KO _ d ξ hξ (fun π => ?_) fun γ σ σ' f h1 h2 hσ rc' hrc' => ?_
  · rw [hπ π, UpperTheory.NonzeroTypeTheory.Cond]
    have e : IsTypeWD h (fun i => (χ i).comp (Subgroup.inclusion (Ine_le_Dec A))) (rc (algNorm π)) ↔ _ :=
      UpperTheory.isTypeWeilDeligne_iff_monodromy_zero_charpoly L Ω n w A h _ _
    obtain ⟨a, ha, ε, -, H⟩ := id hrc
    rw [algNorm, H.nu_eq, (te_unr _ _).1] at e
    simp only [(te_unr _ _).2] at e
    simp only [WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    refine Iff.trans e.symm ⟨fun h0 rc' hrc' => ?_, fun h0 => ?_⟩
    · rw [hu rc' hrc', algNorm, H.nu_eq]
      exact h0
    · have := h0 rc hrc
      rwa [algNorm, H.nu_eq] at this
  · have := typeConj P L Ω n w A h rc' hrc' γ.toRingEquiv σ σ' f h1 h2 χ ho (hσ rc' hrc')
    convert this using 2 with i
    ext s
    obtain ⟨z, hz⟩ := hv i (Subgroup.inclusion (Ine_le_Dec A) s)
    change (χ i _ : ℂ) = γ (χ i _ : ℂ)
    rw [← hz, γ.commutes]

private theorem te_root {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Finite (ResidueField O)] {a b : Oˣ}
    (ha : a ^ (Nat.card (ResidueField O) - 1) = 1) (hb : b ^ (Nat.card (ResidueField O) - 1) = 1)
    (h : residue O a = residue O b) : a = b := by
  letI := Fintype.ofFinite (ResidueField O)
  have hu : ((a * b⁻¹ : Oˣ) : O) ^ (Nat.card (ResidueField O) - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ha, hb]; simp
  have hr : residue O (a * b⁻¹ : Oˣ) = 1 := by
    rw [Units.val_mul, map_mul, h, ← map_mul, Units.mul_inv, map_one]
  have h1 := geom_sum_mul ((a * b⁻¹ : Oˣ) : O) (Nat.card (ResidueField O) - 1)
  rw [hu, sub_self] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · have h3 := congrArg (residue O) h2
    simp only [map_sum, map_pow, hr, one_pow, Finset.sum_const, Finset.card_range, map_zero, nsmul_eq_mul, mul_one] at h3
    rw [Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero] at h3
    simp at h3
  · exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h2))

theorem UpperTheory.NonzeroTypeTheory.typeEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → UpperTheory.NonzeroTypeTheory.NZ → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ := by
  intro P NZ l _ L Ω _ _ _ _ _ _ s n _ V _ c r ι
  by_cases hex : ∃ t, r.IsTeich t
  swap
  · exact ⟨0, 1, fun t ht => absurd ⟨t, ht⟩ hex⟩
  obtain ⟨t, ht⟩ := hex
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  let j : c.O →+* ℂ := ι.toRingHom.comp (algebraMap c.O (Qbar l))
  letI : Algebra c.O ℂ := j.toAlgebra
  have hj : Function.Injective j := ι.injective.comp Subtype.val_injective
  haveI : FaithfulSMul c.O ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
  haveI : Algebra.IsAlgebraic c.O ℂ := by
    haveI : Algebra.IsAlgebraic ℤ_[l] (Qbar l) := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ_[l])).2 inferInstance
    haveI : Algebra.IsAlgebraic c.O (Qbar l) := Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (FaithfulSMul.algebraMap_injective ℤ_[l] c.O)
    exact (AlgEquiv.ofRingEquiv (f := ι) fun _ => rfl : Qbar l ≃ₐ[c.O] ℂ).isAlgebraic
  have hker : ∀ i, (t i).ker = (r.chib i).ker := fun i => Subgroup.ext fun g => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    refine ⟨fun h => Units.ext ?_, fun h => te_root (ht i g).2 (one_pow _) ?_⟩
    · rw [← (ht i g).1, h]; simp
    · rw [(ht i g).1, h]; simp
  have hloc := fun u : s.St => te_loc P NZ n (s.hw u) c.O
    (fun i => W.pushCh j ((t i).comp (V.pr.comp (Dec (F := L) (s.A u)).subtype)))
    (fun i => Subgroup.isOpen_mono (H₁ := (r.chib i).ker.comap (V.pr.comp (Dec (F := L) (s.A u)).subtype))
      (fun g hg => by
        have h1 : t i (V.pr g) = 1 := by
          rw [← hker] at hg
          exact hg
        change Units.map _ (t i (V.pr g)) = 1
        rw [h1, map_one])
      ((r.chib_open i).preimage ((V.pr_cont W.continuous_resP).comp continuous_subtype_val)))
    fun i g => ⟨_, rfl⟩
  choose m τ ho hτ using hloc
  obtain ⟨m', τ', hk, hM⟩ := @UpperTheory.piFamilyProdHom_bijective_characterization c.O _ j s.St _ (fun _ _ => Classical.propDecidable _) (fun u => GLw n (wt s u)) _ _ _
    (fun u => KO ((wt s u).adicCompletion L) (Fin n)) m τ
  refine ⟨m', τ', fun t' ht' => ?_⟩
  obtain rfl : t = t' := funext fun i => MonoidHom.ext fun g =>
    te_root (ht i g).2 (ht' i g).2 ((ht i g).1.trans (ht' i g).1.symm)
  refine ⟨?_, fun M _ _ _ ρ σ hσ => ?_⟩
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (IsOpen.mem_nhds
      (isOpen_iInter_of_finite fun u => (ho u).preimage
        (f := fun k : KT n (wt s) => (⟨k.1 u, k.2 u trivial⟩ : KO ((wt s u).adicCompletion L) (Fin n)))
        (((continuous_apply u).comp continuous_subtype_val).subtype_mk _)) ?_) fun k hk' => ?_)
    · exact Set.mem_iInter.2 fun u => (τ u).ker.one_mem
    · change Matrix.GeneralLinearGroup.map _ (τ' k) = 1
      rw [hk k (Set.mem_iInter.1 hk'), map_one]
  · exact (hM M ρ σ hσ).trans (forall_congr' fun u => hτ u (σ u))
