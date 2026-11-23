import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SpehInfLenOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord

open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx

private theorem finite_over_l (L : Type) [Field L] [NumberField L] (l : ℕ) [hl : Fact l.Prime] :
    {w : Plc L | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 L)} ≠ 0 := by
    simp [hl.out.ne_zero]
  exact (Ideal.finite_factors h0).subset fun w hw =>
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hw)

private theorem split_l {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Vl l L) : IsSplitAt (s.w v.1) :=
  UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA v.1) (s.split _ (Or.inl v.2)) _
    (HeightOneSpectrum.ext (Ideal.ext fun x =>
      (show _ ↔ _ from (s.hw v.1) (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v.1 x)))

section

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (Q : QData V) {c : Coef l} {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ι : Qbar l ≃+* ℂ)

private def PO (lam : Wt L l n) (d : ℕ) (ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ) (Y : (hset Q τ₀).Part ι lam ξ) : Prop :=
  Af.IsIrr (Y.r.comp V.pr) → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧
    Af.AttC ι (Y.r.comp V.pr) π ∧ ∀ v, π.IsLocComp ((hset Q τ₀).Sl v) (Y.σl v)

private theorem po_of (hP : Af.HypothesesH) (hn : 1 ≤ n) {lam : Wt L l n} {d : ℕ} {ξ : GV n (hset Q τ₀).Sl →* GL (Fin d) ℂ}
    (Y : (hset Q τ₀).Part ι lam ξ) (σ : Submodule ℂ (UA L n → ℂ)) (hσ : IsAutRepU σ)
    (hcomp : ∀ v : V.frame.Vl, IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) (Y.σl v).ρ)
    (hLG : ∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
      Af.LocGlob ι (Y.r.comp V.pr) w τ) : PO Q τ₀ ι lam d ξ Y := fun hi => by
  have hc : Continuous (Y.r.comp V.pr) := Y.cont.comp (V.pr_cont W.continuous_resP)
  obtain ⟨π, p1, p2, p3, p4⟩ := linkU hP L Ω (UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range L Ω s.unr) l s.odd ι n hn σ hσ (Y.r.comp V.pr) hc hi
    ((Filter.eventually_cofinite.2 (by simpa using finite_over_l L l)).mono fun w hw hsp τ hτc B hB =>
      Af.satFrob hP.toClassicalTheorems L Ω l ι n _ hc w hw τ B hB fun A h rc hrc => (hLG w hsp τ hτc A h rc hrc).1 hw)
  exact ⟨π, p1, p2, p3, fun v => p4 _ (split_l s v) _ (hcomp v)⟩

end

private theorem autPO (hP : Af.HypothesesH) (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n) (V : s.Lev) (Q : QData V) (c : Coef l)
    (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (hτ : TypeFor r ι τ₀) :
    AutY (hset Q τ₀) ι (PO Q τ₀ ι) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  · obtain ⟨Y, hY, -, hcomp, hLG⟩ := partU hP l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
    rw [← hY]
    exact le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // PO Q τ₀ ι lam d ξ Y} => Y.1.Y)
      ⟨Y, po_of Q τ₀ ι hP hn Y σ.1 σ.2 hcomp hLG⟩

theorem UpperTheory.V.Z.Ord.autUO :
    Af.HypothesesH → AutUO := fun hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι m τ₀ hτ =>
  autPO hP l L Ω s n hn V Q c r ι m τ₀ hτ
