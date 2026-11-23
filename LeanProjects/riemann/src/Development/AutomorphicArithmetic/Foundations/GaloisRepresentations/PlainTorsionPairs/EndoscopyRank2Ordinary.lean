import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.PlainTorOfMono0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JrTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AutomorphicTensorInductionOfLocalPlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Unr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PlainIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo1
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinInd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SuppSmo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.AdWit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ConjTor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.SatOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.EndOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.GalAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ArithmeticPointDecomposition

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
open private au_isTeich au_open from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
open private absPt ss_comp iso_of_det ss_of_irr irr_of_comp irr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp

theorem UpperTheory.Gal.projectedFormsSystemPart.autAway (PH : Af.HypothesesH) (hL : PartLink) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L]
    [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) (V : s.Lev)
    (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hτ : TypeFor r ι τ₀) (hS : V.S' = s.S) :
    (hset Q τ₀).Aut ι fun _ ρ => Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  obtain ⟨t, ht⟩ := au_isTeich c r
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) :=
    au_open _ (ι.injective.comp Subtype.val_injective) τ₀ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine SetLike.le_def.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, hP⟩ := hL l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → AwayOk s ι (Y.r.comp V.pr)} => Y.1.Y)
    ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := hP hi
  refine ⟨π, p1, p2, p3, fun w hw hw0 => ?_⟩
  by_cases hwS : w.under (𝓞 (Lp L)) ∈ V.S'
  swap
  · obtain ⟨B, hB⟩ := p4 w (partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 w hwS)
    exact ImaginaryQuadraticEtaCharacter.sphUnl L n hn π w B hB
  obtain ⟨hwv, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  rw [hS] at hwS
  have hu : w.under (𝓞 (Lp L)) ∈ s.St := by
    rcases hwS with h | h | h
    · refine absurd ?_ hw
      rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
      exact h
    · exact h
    · exact absurd h hw0
  refine hC L n hn π p2 (s.w (w.under (𝓞 (Lp L)))) w (hwv _).symm ?_
  refine (ImaginaryQuadraticEtaCharacter.plainIff L n hn π _).1 fun τ hτ' => ?_
  classical
  have hs : ∀ u : s.St, IsSplitAt (s.w u) := fun u => hsp _ (by
    rw [hwv]
    exact s.split _ (Or.inr (Or.inl u.2)))
  choose loc hloc using fun u : s.St => (Af.locCompC PH.toClassicalTheorems L n π (s.w u)).1
  obtain ⟨rc, hrc⟩ := PH.toClassicalTheorems.exists_rec (s.hw (w.under (𝓞 (Lp L))))
  have k := partUR2Type l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 _ (hτ t ht)
    (Function.update loc ⟨_, hu⟩ τ) (fun u' => p5 _ (hs u') _ (by
      by_cases e : u' = ⟨_, hu⟩
      · subst e
        rwa [Function.update_self]
      · rw [Function.update_of_ne e]
        exact hloc _)) ⟨_, hu⟩ rc hrc
  rw [Function.update_self] at k
  exact typePlain L Ω n hn π _ _ (s.hw _) τ hτ' rc (Z.Desc.W.toT PH.toClassicalTheorems hrc)
    (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) k

private theorem coreA (H : Af.HypothesesH) (hL : PartLink) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L]
    [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V}
    {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : HD Q ι Λ} {K : (hset Q R.τ₀).Lev}
    (hS : V.S' = s.S) {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧
      (Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr)) ∧ x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := wtBridge H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := coreH H.litN L Ω l n c (hset Q R.τ₀) (axU H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι _
    (autAway H hL hC s hn V Q c r ι R.m R.τ₀ R.type hS) lam (Set.mem_univ _)
    ((denseU H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  obtain ⟨ρ, hc, hs, hP, e3⟩ := absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har
  refine ⟨ρ, hc, hs, hP, ?_⟩
  replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr

theorem UpperTheory.Gal.projectedFormsSystemPart.tu_same {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hn : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {π π' : CuspSub F n}
    (h : Af.AttC ι ρ π) (h' : Af.AttC ι ρ π') {w : Plc F} (k : TU π w) : TU π' w := by
  obtain ⟨t, ht⟩ := ImaginaryQuadraticEtaCharacter.winOf F n hn π
  have ev : ∀ᶠ v : Plc F in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B := by
    filter_upwards [h.2, h'.2] with v ⟨B, hB, hE⟩ ⟨B', hB', hE'⟩
    exact ⟨B, hB, (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι v).2.2 n ρ B B' hE hE' ▸ hB'⟩
  have k' : ImaginaryQuadraticEtaCharacter.WinAt π' t w := by
    rcases hn.eq_or_lt with rfl | h2
    · exact ImaginaryQuadraticEtaCharacter.suppSmo1 F π π' ev t w (ht w k.1 k.2)
    · exact ImaginaryQuadraticEtaCharacter.suppSmo F n h2 π π' ev t w (ht w k.1 k.2)
  exact ⟨k'.1, ImaginaryQuadraticEtaCharacter.winUnl F n π' t w k'⟩
