import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.PatchOneAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitAtOfDegOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCodimOneStalkDvr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicWeightDefiniteUnitaryAutRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadLift
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RealGal
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.V.Af.Bc (res)
open UpperTheory.Gal.Int.Core
open UpperTheory.Gal.TP

namespace UpperTheory.Gal.Int.Core

theorem joinU_of (h1 : OneUs) (h2 : IsoOne) (h3 : PhiPol) (h4 : AutT) (hA : Sub.SatAE) (hC : Sub.ClConj) (hS : Sub.SatPol)
    (hW : Sub.ClAway) : JoinU := by
  intro hL m hm E Ω _ _ _ _ _ _ l _ ι hF d hd hsq U hU lam hl
  obtain ⟨T, hT, hAT⟩ := h4 E m U hU
  have hsp := hF.2.2.2.1
  have hFO : FieldOK E l d := ⟨hd, hsq, hF.2.1, fun w hw => ⟨fun h => hw (hsp w h), hF.2.2.1 w⟩⟩
  have key : ∀ u v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal → ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → Apart v u →
      ∃ r : G E Ω →* GL (Fin m) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∀ w, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, SatU U w B → FrobEig ι r w (algSat m (normV w) B)) ∧
        ∀ w, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w u → Apart w v → ∀ B, SatU U w B →
          Sub.Cl ι r w (algSat m (normV w) B) (GlobalTheory.GalDef.jumpsOf ι lam) := by
    intro u v hu hv huv
    obtain ⟨r, hc, hs, f1, f2, f3⟩ := hL E Ω l ι m hm d hFO T hT U hAT u v hu (hsp u hu) hv (hsp v hv) huv
    refine ⟨r, hc, hs, f1, fun w hw a1 a2 B hB => (sphG_iff_cl hS ι r w B lam).1 fun c => ?_⟩
    have hD := f2 w hw a1 a2 ⟨B, hB⟩
    cases c with
    | unr => exact fun h => absurd hw h
    | dR =>
      intro P AI ht A hA O _ _ _ Bw hj
      exact ⟨(hD P AI ht A hA O Bw hj).2.1, fun τ LL' τ' hi J hJ =>
        (hD P AI ht A hA O Bw hj).2.2 τ LL' τ' hi (lam _) J (hl _) hJ⟩
    | crys => exact fun P AI ht A hA O _ _ _ Bw hj => (hD P AI ht A hA O Bw hj).1
    | phi =>
      intro P AI ht A hA O _ _ _ Bw hj g
      exact h3 E Ω A w hA _ _ g (f3 w hw a1 a2 B hB P AI ht A hA O Bw hj g)
  obtain ⟨w₁, w₂, w₃, l1, l2, l3, a12, a13, a23⟩ := hF.2.2.2.2
  obtain ⟨r, hc, hs, f1, -⟩ := key w₂ w₁ l2 l1 a12
  refine ⟨r, hc, hs, fun w B hw hB => (sphG_iff_cl hS ι r w B lam).2 ?_⟩
  by_cases hwl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal
  · have pick : ∃ u v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal ∧ ((l : ℕ) : 𝓞 E) ∈ v.asIdeal ∧ Apart v u ∧
        Apart w u ∧ Apart w v := by
      unfold Apart at a12 a13 a23 ⊢
      by_cases e1 : w.under (𝓞 (maximalRealSubfield E)) = w₁.under (𝓞 (maximalRealSubfield E))
      · exact ⟨w₃, w₂, l3, l2, a23, e1 ▸ a13, e1 ▸ a12⟩
      · by_cases e2 : w.under (𝓞 (maximalRealSubfield E)) = w₂.under (𝓞 (maximalRealSubfield E))
        · exact ⟨w₃, w₁, l3, l1, a13, e2 ▸ a23, e1⟩
        · exact ⟨w₂, w₁, l2, l1, a12, e2, e1⟩
    obtain ⟨u, v, hu, hv, huv, hwu, hwv⟩ := pick
    obtain ⟨s, sc, ss, g1, g2⟩ := key u v hu hv huv
    refine hC E Ω l ι m s r sc (h2 E Ω l ι m s r sc hc ss hs ?_) w _ _ (g2 w hwl hwu hwv B hB.2)
    filter_upwards [h1 E d hd, hA E m U hU, GlobalTheory.CongEx.eventually_not_mem_l E l] with x x1 x2 x3 hp
    obtain ⟨B', hB'⟩ := x2 (x1 hp).1
    exact ⟨_, g1 x (x1 hp) x3 B' hB', f1 x (x1 hp) x3 B' hB'⟩
  · exact (hW E Ω l ι m r w hwl _ _).2 (f1 w hw hwl B hB.2)

theorem joinGL_holds : JoinGL := by
  intro hD hU E Ω _ _ _ _ _ _ l _ ι hF hI d hd hsq a ha π hπ
  obtain ⟨T, hT, -, U, hM⟩ := hD E l a (Fact.out) ha π hπ ∅
  obtain ⟨lam, hlam⟩ := GlobalTheory.Cong.exists_weight_of_isAutRepU E a U hM.aut
  obtain ⟨r, hc, hs, hr⟩ := hU E Ω l ι hF hI d hd hsq a ha U hM.aut lam hlam
  refine ⟨r, hc, hs, fun w B hw hB c => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL E a π w
  have h := hr w B hw ⟨hw.1, σ, hM.split w hw.1 σ hσ, ((GlobalTheory.Cong.satake_locComp E a π w σ hσ).1 B).1 hB⟩ c
  cases c with
  | unr => exact h
  | dR =>
    intro P AI ht A hA O _ _ _ Bw hj
    refine ⟨(h P AI ht A hA O Bw hj).1, fun τ LL' τ' hi J hJ => (h P AI ht A hA O Bw hj).2 τ LL' τ' hi J ?_⟩
    rw [hM.inf _ _ (hlam _)] at hJ
    exact hJ
  | crys => exact fun P AI ht A hA O _ _ _ Bw hj _ _ _ => h P AI ht A hA O Bw hj
  | phi => exact h

theorem joinEnd_holds : JoinEnd := by
  intro h E Ω _ _ _ _ _ _ l _ ι a ha π hπ
  obtain ⟨r, hc, hs, hr⟩ := h E Ω l ι a ha π hπ.all
  refine ⟨r, ⟨hc, hs, ?_⟩, fun w B hB =>
    ⟨hr w B trivial hB .unr, hr w B trivial hB .dR, hr w B trivial hB .crys, hr w B trivial hB .phi⟩⟩
  filter_upwards [GlobalTheory.CongEx.eventually_not_mem_l E l,
    GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π] with w hl hB
  obtain ⟨B, hB⟩ := hB
  exact ⟨B, hB, hr w B trivial hB .unr hl⟩

theorem stepDown_of (h2 : IsoOne) (hP : PatchOne) (hD : ∀ c, SphDown c) : StepDown := by
  intro hQL E Ω _ _ _ _ _ _ l _ ι a ha π fam
  have hsat := GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep GlobalTheory.automorphicFormsFiniteGL E a π
  let S : Set (QCM E Ω) := {Q | ∃ r : G ↥Q.K Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧ AttOne (CG.mk π).HasSat ι ↥Q.K r}
  have serve : ∀ w₀ (Q : QCM E Ω), Serves π ι w₀ Q → ∃ (P : CuspSub ↥Q.K a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)), IsLift π P ∧
      Continuous r ∧ IsSSRep r ∧ AttOne (CG.mk π).HasSat ι ↥Q.K r ∧
      ∀ w B, w.under (𝓞 E) = w₀ → (CG.mk P).HasSat w B → ∀ c, GlobalTheory.RoadU.SphAt c P ι r w B := by
    intro w₀ Q hQ
    obtain ⟨P, hPl⟩ := hQL E ↥Q.K Q.two a ha π hQ.2.1
    obtain ⟨p, ⟨r, hc, hs, hr⟩, hp1, hp2⟩ := hQ.2.2 P hPl
    refine ⟨P, r, hPl, hc, hs, ?_, fun w B hw => hr w B (hp2 w hw)⟩
    unfold AttOne
    filter_upwards [hp1, GlobalTheory.CongEx.eventually_not_mem_l (↥Q.K) l,
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under (K := E) (L := ↥Q.K)).eventually hsat] with w x1 x2 x3 hp
    obtain ⟨B, hB⟩ := x3
    have hq := GlobalTheory.RealGal.AttRes.normV_eq_pow (F := E) w
    have hf : w.asIdeal.inertiaDeg (𝓞 E) = 1 := Nat.Prime.eq_one_of_pow (hq ▸ hp)
    have hB' : (CG.mk P).HasSat w B := by simpa [hf] using hPl.sat w _ B hq hB
    exact ⟨B, hB, hr w B (x1 hp) hB' .unr x2⟩
  have famS : ∀ w₀ Q, Serves π ι w₀ Q → Q ∈ S := fun w₀ Q hQ => by
    obtain ⟨_, r, -, a1, a2, a3, -⟩ := serve w₀ Q hQ
    exact ⟨r, a1, a2, a3⟩
  obtain ⟨v0, -⟩ := GlobalTheory.CongEx.exists_place_over E l
  have hS : S.Infinite := (fam v0).mono fun Q hQ => famS v0 Q hQ
  choose r hr using fun Q : ↥S => Q.2
  obtain ⟨ρ, hρc, hρs, hev⟩ := hP E Ω l ι a (CG.mk π).HasSat (fun v B B' h h' => h.unique h') S hS r hr
  refine ⟨ρ, hρc, hρs, fun w B _ hB c => ?_⟩
  have hfin := (Filter.eventually_cofinite.1 hev).image Subtype.val
  obtain ⟨Q, hQ, hQn⟩ := ((fam w).diff hfin).nonempty
  have hiso : RepIso (r ⟨Q, famS w Q hQ⟩) (ρ.comp (res E Ω ↥Q.K)) := by
    by_contra hc
    exact hQn ⟨⟨Q, famS w Q hQ⟩, hc, rfl⟩
  obtain ⟨P, s, hPl, sc, ss, sa, hs⟩ := serve w Q hQ
  obtain ⟨rc, rs, ra⟩ := hr ⟨Q, famS w Q hQ⟩
  have e : RepIso s (r ⟨Q, famS w Q hQ⟩) := by
    refine h2 (↥Q.K) Ω l ι a s _ sc rc ss rs ?_
    filter_upwards [sa, ra] with x x1 x2 hp
    obtain ⟨B1, b1, c1⟩ := x1 hp
    obtain ⟨B2, b2, c2⟩ := x2 hp
    obtain rfl := b1.unique b2
    exact ⟨_, c1, c2⟩
  refine hD c E Ω l ι a π Q P hPl ρ w B hB hQ.1 fun w' hw' hB' => ?_
  exact GlobalTheory.RoadW.sphAt_of_repIso ι P rc hiso c w' B (GlobalTheory.RoadW.sphAt_of_repIso ι P sc e c w' B (hs w' B hw' hB' c))

end UpperTheory.Gal.Int.Core
