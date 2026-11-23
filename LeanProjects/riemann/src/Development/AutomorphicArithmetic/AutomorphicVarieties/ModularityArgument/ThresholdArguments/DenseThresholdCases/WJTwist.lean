import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.JTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SphUntw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UpUW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicTensorInductionOfLocalPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdCoreOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PartU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.LgAway

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.V.Z.Desc.W UpperTheory.Zero.LLC
open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
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
private theorem tw_aut (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} {β : G L Ω →* (Qbar l)ˣ} (hβ : Continuous β)
    {N : ℕ} (hN : β ^ (2 * N + 1) = 1) {c : G (Lp L) Ω} (hc : Af.IsConjEl c)
    (hcβ : ∀ s s' : G L Ω, s'.restrictScalars (Lp L) = c * s.restrictScalars (Lp L) * c⁻¹ → β s' = (β s)⁻¹)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) :
    ∃ (σ' : Submodule ℂ (UA L n → ℂ)) (art : (AdeleRing (𝓞 L) L)ˣ →* GlobalTheory.HeckeGal.Gab L Ω) (κ : Formalism.L2.Host.HChar L), IsAutRepU σ' ∧ GlobalTheory.HeckeGal.IsGlobalArtin art ∧
      GlobalTheory.HeckeGal.IsLAdicOf art ι κ 0 β ∧
      (∀ φ lam, HasWeightAt σ φ lam → HasWeightAt σ' φ lam) ∧
      (∀ (w : Plc L) (A : ValuationSubring Ω), IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
        IsUnramU σ w → IsUnramU σ' w) ∧
      (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
        ∃ τ' : SmIrr (GLw n w), IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ'.ρ ∧
          Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) ∧
          ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Ine (F := L) A, β g = 1) →
            ∀ U ≤ GlobalTheory.LFun.KGL w n, fixd τ.ρ U ≠ ⊥ → fixd τ'.ρ U ≠ ⊥) ∧
      ∀ w, IsSplitAt w → ∀ τ' : SmIrr (GLw n w), IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) τ'.ρ →
        ∃ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧
          Nonempty (τ'.ρ.Equiv (twRep τ.ρ (CuspSub.locDet n κ w))) := by
  obtain ⟨art, ha⟩ := P.aut.art L Ω
  have hm : 0 < 2 * N + 1 := Nat.succ_pos _
  have h0 : Continuous (β ^ (N + 1) :) := hβ.pow (N + 1)
  have h1 : (β ^ (N + 1)) ^ (2 * N + 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hN, one_pow]
  have h2 : β ^ (N + 1) * β ^ (N + 1) = β := by
    rw [← pow_add, show N + 1 + (N + 1) = 2 * N + 1 + 1 by ring, pow_succ, hN, one_mul]
  obtain ⟨ν, ⟨hν, hνβ⟩, -⟩ := GlobalTheory.HeckeGal.exists_unique_hchar_of_finite_order ha ι _ h0 hm h1
  have hκ : GlobalTheory.HeckeGal.IsLAdicOf art ι (ν * ν) 0 β := by simpa only [h2, add_zero] using hνβ.mul hνβ
  have hθ := UpperTheory.thetaChar_eq_self_of_conjugate_dual L Ω l ι art ha ν _ hm hν _ h0 hνβ c hc fun s s' e => by
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, hcβ s s' e, inv_pow]
  obtain ⟨g1, g2, g3⟩ := UpperTheory.detCharacter_ker_open_trivial_rational_archimedean L n ν _ hm hν
  have g4 := UpperTheory.detCharacter_eq_localDet_split_nonsplit L n ν hθ
  obtain ⟨σ', a1, a2, a3⟩ := UpperTheory.exists_automorphicRep_twist_by_character L n _ g1 g2 σ hσ
  have a4 : ∀ w, IsSplitAt w → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Representation ℂ (GLw n w) M),
      IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ ↔
        IsCompAlong σ' (locU n w) ((cLoc w).comp (locU n w).subtype) (twRep τ (CuspSub.locDet n (ν * ν) w)) :=
    fun w hw M _ _ τ => a3 _ _ _ _ τ _ fun x => (g4 w x x.2).1 hw
  refine ⟨σ', art, ν * ν, a1, ha, hκ, fun φ lam h => ?_, fun w A hA hu => a2 w fun g hg hK => ?_,
    fun w hw τ hτ => ⟨τ.twist _ (CuspSub.isOpen_ker_locDet (ν * ν) w), (a4 w hw _ _).1 hτ, ⟨.refl _⟩, fun A hA hu U hU hf => ?_⟩,
    fun w hw τ' hτ' => ?_⟩
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
  · let τ := τ'.twist (CuspSub.locDet n (ν * ν) w)⁻¹ (by simpa using CuspSub.isOpen_ker_locDet (a := n) (ν * ν) w)
    have e : twRep τ.ρ (CuspSub.locDet n (ν * ν) w) = τ'.ρ := twRep_inv _ _
    exact ⟨τ, (a4 w hw _ _).2 (e ▸ hτ'), ⟨e ▸ .refl _⟩⟩
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
private theorem ord_congr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {ι : Qbar l ≃+* ℂ} {a : Weil h →* (w.adicCompletion F)ˣ}
    {ω : (w.adicCompletion F)ˣ →* ℂˣ} {hh : (F →+* Qbar l) → ℤ} {ψ ψ' : Dec (F := F) A →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ)
    (e : ∀ g, (ψ g : Qbar l) = ψ' g) : OrdChar ι a ω hh ψ' :=
  (MonoidHom.ext fun g => Units.ext (e g) : ψ = ψ') ▸ H
section Pt
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ι : Qbar l ≃+* ℂ)
def UpperTheory.V.Z.Desc.W.PartOfAlt (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q τ₀).PartAltAlt ι lam ξ) : Prop :=
  ∃ (σ : Submodule ℂ (UA L n → ℂ)) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)),
    IsAutRepU σ ∧ IsBasis ι e ξ ∧ YOf Q ι τ₀ e ξ σ ≠ ⊥ ∧
    (∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ) ∧
    ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      _root_.UpperTheory.V.Z.Win.LocGlobT ι (Y.r.comp V.pr) w τ
private theorem autP (hP : _root_.UpperTheory.V.Af.HypothesesH') (hn : 1 ≤ n) (r : Resid V.frame c.O n) (hτ : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) :
    _root_.UpperTheory.V.Z.Ord.AutYAlt (hset Q τ₀) ι (_root_.UpperTheory.V.Z.Desc.W.PartOfAlt Q τ₀ ι) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, -, hcomp, hLG⟩ := _root_.UpperTheory.V.Z.Desc.P.partU_alt hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // _root_.UpperTheory.V.Z.Desc.W.PartOfAlt Q τ₀ ι lam d ξ Y} => Y.1.Y) ⟨Y, σ.1, e, σ.2, he, h0, hcomp, hLG⟩
end Pt
set_option maxHeartbeats 1600000 in
private theorem pt_part (PH : _root_.UpperTheory.V.Af.HypothesesH') {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) {x : B.Pt} (hx : J ≤ RingHom.ker x) {lam : Wt L l n}
    (hg : (hset Q R.τ₀).Good R.θ (x.comp (Λ.toPair B.u)).toRingHom lam) :
    ∃ (d : ℕ) (ξ : GV n (hset Q R.τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q R.τ₀).PartAltAlt ι lam ξ), _root_.UpperTheory.V.Z.Desc.W.PartOfAlt Q R.τ₀ ι lam d ξ Y ∧
      x.D = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v : V.frame.Vl, ∃ ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ,
        IsSubquotient (Y.σl v).ρ (PS ω) ∧ ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i) := by
  have P := PH.litN
  rcases hJ with ⟨-, rfl⟩ | ⟨_, _, f, -, hf, hs, hl, rfl⟩
  · exact absurd ((map_one x).symm.trans (hx Submodule.mem_top)) one_ne_zero
  obtain ⟨y, hy⟩ : ∃ y : (hset Q R.τ₀).TK R.θ R.a K →ₐ[c.O] Qbar l, ∀ b, y (f b) = x b :=
    ⟨_, AlgHom.liftOfSurjective_apply f hs x hx⟩
  have e1 : y.toRingHom.comp (algebraMap Λ.Λ _) = (x.comp (Λ.toPair B.u)).toRingHom :=
    RingHom.ext fun b => (congrArg y (hl b).symm).trans (hy _)
  have e2 : y.toRingHom.comp f.toRingHom = (x : B.B →+* Qbar l) := RingHom.ext hy
  rw [← e1] at hg
  obtain ⟨d, ξ, Y, h1, h4, h5⟩ := _root_.UpperTheory.V.Z.Ord.core_ordinary_of_literal_automorphy_n P L Ω l n c _ (_root_.UpperTheory.V.Hi.axU_s P l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι _
    (autP Q R.τ₀ ι PH hn r R.type) R.a K _ _ hf lam trivial y hg.2.1
  refine ⟨d, ξ, Y, h1, ((congrArg B.u.D.map e2.symm).trans ((CA.d_gmap B.u.D).2.1 _ _).symm).trans h4, fun v => ?_⟩
  obtain ⟨ω, w1, w2⟩ := h5 v
  refine ⟨ω, w1, fun i => ?_⟩
  exact ord_congr (w2 i) fun g => hy _
set_option maxHeartbeats 1000000 in
theorem UpperTheory.V.Z.Desc.W.jTwist_of_alt : TypeGd → _root_.UpperTheory.V.Z.Desc.W.TwAwayAlt → _root_.UpperTheory.V.Z.Desc.W.SphUntwAlt → OrdTw → _root_.UpperTheory.V.Z.Desc.W.PsFullAlt →
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.TwistOk J := by
  intro hTy hTw hSp hOr hPs PH l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x x' h β hx hg hβ ⟨k, hk⟩ hc _ h0 hD hψ
  have P := PH.litN
  have hAx := _root_.UpperTheory.V.Hi.axU_s P l L Ω s n hn V Q c R.m R.τ₀
  obtain ⟨⟨lam, hlam⟩, hW⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight P l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h hg.1
  obtain ⟨d, ξ, Y, ⟨σ, e, hσ, hb, hY, hcomp, s1⟩, hDx, hord⟩ := pt_part PH hn hJ hx ((hW lam hlam x).2.1 hg)
  have hpr := V.pr_cont W.continuous_resP
  have hρ : Continuous (Y.r.comp V.pr) := Y.cont.comp hpr
  have hβ' : IsOpen ((β.comp V.pr).ker : Set (G L Ω)) := hβ.preimage hpr
  have hβc := GlobalTheory.HeckeGal.continuous_of_isOpen_ker' _ hβ'
  obtain ⟨N, hN⟩ : Odd (l ^ k) := ((Fact.out : l.Prime).odd_of_ne_two s.odd).pow
  have s2 := partUR2Wt l L Ω s n hn V Q c ι R.m R.τ₀ lam d e ξ hb σ hσ hY
  have s3 := partUR2Unr l L Ω s n hn V Q c ι R.m R.τ₀ lam d e ξ hb σ hσ hY
  obtain ⟨σ', art, κ, t0, ha, hκ, t2, t3, t4, t5⟩ := tw_aut P ι hβc (N := N)
    (MonoidHom.ext fun g => by rw [← hN]; exact DFunLike.congr_fun hk (V.pr g)) s.hc
    (fun g g' e => (congrArg β (pr_conj V e)).trans (DFunLike.congr_fun hc (V.pr g))) hσ
  have hcont := UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n (Y.r.comp V.pr) _ hρ hβc
  choose ph hph hinj using hg.2
  have hph' : ∀ (v : Vl l L) j, W.IsWtPart (s.hw v) (x'.psi v j) (h v j)
      (ph v j * ((β.comp V.pr).comp (Ine (F := L) (s.A v)).subtype)⁻¹) := fun v j => by
    rw [hψ]
    exact part_tw (hph v j) hβ'
  refine _root_.UpperTheory.V.Z.Desc.W.upU_w_alt PH l L Ω s n hn V Q c r ι B Λ R K hS J hJ x' h lam ⟨hg.1, fun v j => ⟨_, hph' v j⟩⟩ hlam σ' _ t0 hcont
    ((UpperTheory.galoisRep_irreducibility_criterion.1 _ (G L Ω) _ n _).2.2 _ (ss_comp (pr_surj V) Y.ss)) (det_tw V.pr hDx hD) (fun w hs hw τ' b hτ' hb' => ?_)
    (fun y => t2 _ _ (s2 y)) (fun w hw => ?_) ?_ (fun v => ?_) fun u τ' hu hτ' rc hrc => ?_
  · obtain ⟨τ, h1, h2⟩ := t5 w hs τ' hτ'
    obtain ⟨g1, g2⟩ := hSp P L Ω n κ w τ τ' b hb' h2
    exact _root_.UpperTheory.V.Z.Desc.W.satFrobT_alt PH.toClassicalTheorems L Ω l ι n _ hcont w hw τ' b hb' fun A hA rc hrc =>
      _root_.UpperTheory.V.Z.Win.WDT.of_isWDOf (hTw P L Ω l ι n _ hρ art κ 0 _ ha hβc hκ w hw τ τ' g1 h2 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc)
        (_root_.UpperTheory.V.Z.Desc.W.woGd' (_root_.UpperTheory.V.Z.Desc.W.lgAway' (s1 w hs τ h1) hw A hA rc hrc) (g2 A hA rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc))))
  · obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω w : ∃ A : ValuationSubring Ω, IsPlaceOver A w)
    exact t3 w A hA (fun g hg => (congrArg β (pr_ine V hw hA hg)).trans β.map_one) (s3 w hw)
  · obtain ⟨τ₀, s5⟩ := Up.comp_ex hσ (split_at_base_place (s := s))
    obtain ⟨τ', u1, -, u2⟩ := t4 _ (split_at_base_place (s := s)) τ₀ s5
    refine ⟨τ', u1, u2 _ (s.hw _) (fun g hg => h0 ⟨g, hg, rfl⟩) _ ?_
      (partUR2V0 l L Ω s n hn V Q c ι R.m R.τ₀ lam d e ξ hb σ hσ hY _ s5)⟩
    refine le_trans ?_ (SphCompletion.KO_completion _ n).le
    rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · have hv : IsSplitAt (s.w v.1) := split_l (s := s) ⟨v.1, v.2⟩
    obtain ⟨τ', u1, u2, -⟩ := t4 _ hv _ (hcomp v)
    obtain ⟨ω, w1, w2⟩ := hord v
    obtain ⟨ω', w3, w4⟩ := hOr L Ω l ι n art κ _ ha hβc hκ _ _ (s.hw v.1) _ (hAx.art_spec v) _ τ' ω (htW lam) (x.psi v)
      (hPs P L Ω l ι n _ _ (s.hw v.1) _ (hAx.art_spec v) _ ω (htW lam) (x.psi v) (ph v) w1 w2
        (fun j => (funext (hlam v j)).symm ▸ hph v j) (hinj v)) w2 u2
    exact ⟨τ', ω', u1, w3, fun i => ord_congr (w4 i) fun g => congrArg Units.val (DFunLike.congr_fun (hψ v i) g).symm⟩
  · have hsp : ∀ u : s.St, IsSplitAt (s.w u) := fun u =>
      UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA u) (s.split _ (Or.inr (Or.inl u.2))) _ (Up.under_w _)
    obtain ⟨τ, h1, h2⟩ := t5 _ (hsp u) τ' hτ'
    obtain ⟨t, ht⟩ := au_isTeich c r
    choose loc hloc using fun u : s.St => Up.comp_ex hσ (hsp u)
    classical
    have hT := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι R.m R.τ₀ lam d e ξ hb σ hσ hY _ (R.type t ht) (Function.update loc u τ) (fun u' => by
      by_cases e : u' = u
      · subst e
        rwa [Function.update_self]
      · rw [Function.update_of_ne e]
        exact hloc _) u rc hrc
    rw [Function.update_self] at hT
    obtain ⟨g1, g2⟩ := hTy L Ω n _ _ (s.hw u) τ rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc)
      (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) hT
    exact hTw P L Ω l ι n _ hρ art κ 0 _ ha hβc hκ _ hu τ τ' g1 h2 _ (s.hw u) rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc)
      (_root_.UpperTheory.V.Z.Desc.W.woGd' (_root_.UpperTheory.V.Z.Desc.W.lgAway' (s1 _ (hsp u) τ h1) hu _ (s.hw u) rc hrc) g2)
end
