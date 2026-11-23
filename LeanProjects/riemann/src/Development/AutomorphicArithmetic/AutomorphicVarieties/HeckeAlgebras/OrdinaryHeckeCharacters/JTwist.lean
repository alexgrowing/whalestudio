import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UpU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreH
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaCharEqSelfOfConjugateDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterKerOpenTrivialRationalArchimedean
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DetCharacterEqLocalDetSplitNonsplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicRepTwistByCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterOfAlgebraicHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FlagAb
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
attribute [-instance] UpperTheory.V.GradeZeroInterpolatingElement.instIsLocalRingSubtypePadicAlgClMemSubalgebraPadicIntO

private theorem twRep_one {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) :
    twRep ρ 1 = ρ := by
  ext g v
  simp [twRep]

private theorem twRep_inv {H M : Type} [Group H] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ H M) (η : H →* ℂˣ) :
    twRep (twRep ρ η⁻¹) η = ρ := by
  ext g v
  simp [twRep, smul_smul]

private theorem locDet_KGL {E : Type} [Field E] [NumberField E] {n : ℕ} {χ : Formalism.L2.Host.HChar E} {w : Plc E}
    (h : χ.UnrAt w) {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL w n) : CuspSub.locDet n χ w g = 1 :=
  h _ (GlobalTheory.SphGal.isUnitAt_det_of_mem hg)

private theorem det_tw {n : ℕ} {k Γ H : Type} [Field k] [Group Γ] [Group H] {D D' : W.GDet n k Γ} {β : Γ →* kˣ}
    {ρ : Γ →* GL (Fin n) k} (φ : H →* Γ) (hD : D = W.GDet.ofRep (W.mat ρ)) (h : D.IsTwist β D') :
    D'.comap φ = W.GDet.ofRep (W.mat (Af.tw (ρ.comp φ) (β.comp φ))) := by
  subst hD
  refine W.GDet.ext fun B _ _ y => (h B _).trans ?_
  change (W.GDet.repAlg _ B _).det = (W.GDet.repAlg _ B y).det
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add (W.GDet.repAlg _ B), ← ha, ← hb, ← map_add, ← map_add]
    congr 2
    exact map_add (MonoidAlgebra.mapDomainRingHom B φ) a b
  | single g r =>
    ext i j
    simp [W.GDet.repAlg, W.mat, Af.tw_val, mul_assoc]

private theorem tw_aut (P : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} {β : G L Ω →* (Qbar l)ˣ} (hβ : Continuous β)
    {N : ℕ} (hN : β ^ (2 * N + 1) = 1) {c : G (Lp L) Ω} (hc : Af.IsConjEl c)
    (hcβ : ∀ s s' : G L Ω, s'.restrictScalars (Lp L) = c * s.restrictScalars (Lp L) * c⁻¹ → β s' = (β s)⁻¹)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) {ρ : G L Ω →* GL (Fin n) (Qbar l)} (hρ : Continuous ρ)
    (hH : ∃ HT, Af.HasHT ρ HT)
    (hL : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι ρ w τ) :
    ∃ σ' : Submodule ℂ (UA L n → ℂ), IsAutRepU σ' ∧ (∃ HT, Af.HasHT (Af.tw ρ β) HT) ∧
      (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w),
        IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι (Af.tw ρ β) w τ) ∧
      (∀ φ lam, HasWeightAt σ φ lam → HasWeightAt σ' φ lam) ∧
      (∀ (w : Plc L) (A : ValuationSubring Ω), IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
        IsUnramU σ w → IsUnramU σ' w) ∧
      ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
        ∃ τ' : SmIrr (GLw n w), IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ'.ρ ∧
          ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
            ∀ U ≤ GlobalTheory.LFun.KGL w n, fixd τ.ρ U ≠ ⊥ → fixd τ'.ρ U ≠ ⊥ := by
  obtain ⟨art, ha⟩ := P.aut.art L Ω
  have hm : 0 < 2 * N + 1 := Nat.succ_pos _
  have h0 : Continuous (β ^ (N + 1) :) := hβ.pow (N + 1)
  have h1 : (β ^ (N + 1)) ^ (2 * N + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
  have h2 : β ^ (N + 1) * β ^ (N + 1) = β := by
    rw [← pow_add, show N + 1 + (N + 1) = 2 * N + 1 + 1 by ring, pow_succ, hN, one_mul]
  obtain ⟨ν, ⟨hν, hνβ⟩, -⟩ := GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order ha ι _ h0 hm h1
  have hκ : GlobalTheory.HeckeGal.IsLAdicOf art ι (ν * ν) 0 β := by simpa only [h2, add_zero] using hνβ.mul hνβ
  have hκo : (ν * ν).OrderDvd (2 * N + 1) := by
    have e : ν ^ (2 * N + 1) = 1 := hν
    change (ν * ν) ^ (2 * N + 1) = 1
    rw [mul_pow, e, one_mul]
  have hθ := UpperTheory.thetaChar_eq_self_of_conjugate_dual L Ω l ι art ha ν _ hm hν _ h0 hνβ c hc fun s s' e => by
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, hcβ s s' e, inv_pow]
  obtain ⟨g1, g2, g3⟩ := UpperTheory.detCharacter_ker_open_trivial_rational_archimedean L n ν _ hm hν
  have g4 := UpperTheory.detCharacter_eq_localDet_split_nonsplit L n ν hθ
  obtain ⟨σ', a1, a2, a3⟩ := UpperTheory.exists_automorphicRep_twist_by_character L n _ g1 g2 σ hσ
  obtain ⟨b1, b2⟩ := UpperTheory.galois_character_of_algebraic_hecke P L Ω l ι n ρ hρ hH art (ν * ν) 0 β ha
    (GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd hm hκo) hβ hκ
  have a4 : ∀ w, IsSplitAt w → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ (GLw n w) M),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ ↔
        IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) (twRep τ (CuspSub.locDet n (ν * ν) w)) :=
    fun w hw M _ _ τ => a3 _ _ _ _ τ _ fun x => (g4 w x x.2).1 hw
  refine ⟨σ', a1, b1, fun w hw τ' hτ' => ?_, fun φ lam h => ?_, fun w A hA hu => a2 w fun g hg hK => ?_,
    fun w hw τ hτ => ⟨τ.twist _ (CuspSub.isOpen_ker_locDet (ν * ν) w), (a4 w hw _ _).1 hτ, fun A hA hu U hU hf => ?_⟩⟩
  · let τ := τ'.twist (CuspSub.locDet n (ν * ν) w)⁻¹ (by simpa using CuspSub.isOpen_ker_locDet (a := n) (ν * ν) w)
    have e : twRep τ.ρ (CuspSub.locDet n (ν * ν) w) = τ'.ρ := twRep_inv _ _
    exact b2 w τ τ' (hL w hw τ ((a4 w hw _ _).2 (e ▸ hτ'))) ⟨e ▸ .refl _⟩
  · have := (a3 (embU n φ) _ _ _ _ 1 fun x => g3 x x.2.1).1 h
    rwa [twRep_one] at this
  · by_cases hw : IsSplitAt w
    · exact ((g4 w g hg).1 hw).trans (locDet_KGL ((hκ.unr_iff ha (Or.inr rfl) hA).1 hu) hK)
    · refine ((g4 w g hg).2 hw).trans (locDet_KGL ((hνβ.unr_iff ha (Or.inr rfl) hA).1 fun s hs => ?_) hK)
      rw [MonoidHom.pow_apply, hu s hs, one_pow]
  · obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hf
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun u hu' => ?_, h0⟩
    change ((CuspSub.locDet n (ν * ν) w u : ℂˣ) : ℂ) • τ.ρ u v = v
    rw [locDet_KGL ((hκ.unr_iff ha (Or.inr rfl) hA).1 hu) (hU hu'), hv u hu', Units.val_one, one_smul]

section Lev

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω}

private theorem place_under {A : ValuationSubring Ω} {w : Plc L} (h : IsPlaceOver A w) :
    IsPlaceOver A (w.under (𝓞 (Lp L))) := fun x => by
  rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
  exact h (algebraMap (𝓞 (Lp L)) (𝓞 L) x)

private theorem split_l (v : Vl l L) : IsSplitAt (s.w v.1) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
    (HeightOneSpectrum.ext (Ideal.ext fun x => (place_under (s.hw v.1) x).symm.trans (s.hA v.1 x)))

private theorem split_at_base_place : IsSplitAt (s.w s.v0) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (s.split _ (Or.inr (Or.inr rfl))) _
    (HeightOneSpectrum.ext (Ideal.ext fun x => (place_under (s.hw _) x).symm.trans (s.hA _ x)))

private theorem pr_ine (V : s.Lev) {A : ValuationSubring Ω} {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S')
    (hA : IsPlaceOver A w) {g : G L Ω} (hg : g ∈ Ine (F := L) A) : V.pr g = 1 := by
  refine Subtype.ext ((QuotientGroup.eq_one_iff (W.resP L Ω g)).2
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)))
  simp only [Set.mem_iUnion]
  exact ⟨_, hw, A, place_under hA, hg⟩

private theorem pr_surj (V : s.Lev) : Function.Surjective V.pr := by
  rintro ⟨g, hg⟩
  obtain ⟨g, rfl⟩ : ∃ t, toGS Ω V.S' t = g := QuotientGroup.mk'_surjective _ g
  obtain ⟨t, rfl⟩ := (V.hη g).1 hg
  exact ⟨t, rfl⟩

private theorem pr_conj (V : s.Lev) {g g' : G L Ω}
    (h : g'.restrictScalars (Lp L) = s.c * g.restrictScalars (Lp L) * s.c⁻¹) : V.pr g' = V.frame.conj (V.pr g) := by
  refine Subtype.ext ?_
  change toGS Ω V.S' (g'.restrictScalars (Lp L)) =
    toGS Ω V.S' s.c * toGS Ω V.S' (g.restrictScalars (Lp L)) * (toGS Ω V.S' s.c)⁻¹
  rw [h, map_mul, map_mul, map_inv]

end Lev

private theorem ss_comp {Γ H k : Type} [Group Γ] [Group H] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : H →* Γ}
    (hφ : Function.Surjective φ) (h : Formalism.MainNotions.N.IsSSRep r) : Formalism.MainNotions.N.IsSSRep (r.comp φ) := fun U hU => by
  obtain ⟨U', h1, h2⟩ := h U fun g v hv => by
    obtain ⟨g, rfl⟩ := hφ g
    exact hU g v hv
  exact ⟨U', fun g v hv => h1 (φ g) v hv, h2⟩

private theorem part_tw {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {κ : Dec (F := F) A →* (Qbar l)ˣ} {wt : W.Emb l w → ℤ}
    {ph : Ine (F := F) A →* (Qbar l)ˣ} (H : W.IsWtPart h κ wt ph) {β : G F Ω →* (Qbar l)ˣ} (hβ : IsOpen (β.ker : Set (G F Ω))) :
    W.IsWtPart h (κ * β.comp (Dec (F := F) A).subtype) wt (ph * (β.comp (Ine (F := F) A).subtype)⁻¹) := by
  refine ⟨Subgroup.isOpen_mono (H₁ := ph.ker ⊓ β.ker.comap (Ine (F := F) A).subtype) (fun g hg => ?_)
    (H.1.inter (hβ.preimage continuous_subtype_val)), fun a ha g => ?_⟩
  · have h1 : ph g = 1 := hg.1
    have h2 : β g = 1 := hg.2
    change ph g * (β g)⁻¹ = 1
    rw [h1, h2, inv_one, mul_one]
  · rw [← H.2 a ha g]
    congr 1
    change κ _ * β g * (ph g * (β g)⁻¹) = _
    rw [mul_mul_mul_comm, mul_inv_cancel, mul_one]
