import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.OptUCoverPre

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem cx_cls_eq_zero {R : Type} [CommRing R] (Kc : Cx.{1} R) {n : ℕ} (x : Kc.X n) (hx : Kc.d n x = 0) :
    Kc.cls x hx = 0 ↔ x ∈ Kc.B n := by
  unfold Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

section Gen

universe u v u' v'

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem rc_d_val (F : C ⥤ ModuleCat.{0} R) (U : ObjectProperty C) {Q : ObjectProperty C} (hQ : Cosieve Q) (n : ℕ)
    (y : (RC F U hQ).X n) : ((RC F U hQ).d n y).1 = CH.d (U.ι ⋙ F) n y.1 := rfl

theorem morU_resU {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
    {U V : ObjectProperty C} {U' V' : ObjectProperty C'} (hV : V ≤ U) (hV' : V' ≤ U') (hU : ∀ T, U' T → U (m.G.obj T))
    (hVV : ∀ T, V' T → V (m.G.obj T)) (n : ℕ) (x : CH.Cn (U.ι ⋙ F) n) :
    (morU m hVV).pullC n ((resU F hV).pullC n x) = (resU F' hV').pullC n ((morU m hU).pullC n x) := rfl

theorem morU_restrict {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R))
    {U : ObjectProperty C} {U' : ObjectProperty C'} (hU : ∀ T, U' T → U (m.G.obj T)) (n : ℕ) (z : CH.Cn F n) :
    (morU m hU).pullC n ((CH.Mor.restrict F U.ι).pullC n z) = (CH.Mor.restrict F' U'.ι).pullC n (m.pullC n z) := rfl

theorem resU_restrict (F : C ⥤ ModuleCat.{0} R) {U V : ObjectProperty C} (h : V ≤ U) (n : ℕ) (z : CH.Cn F n) :
    (resU F h).pullC n ((CH.Mor.restrict F U.ι).pullC n z) = (CH.Mor.restrict F V.ι).pullC n z := rfl

theorem restrict_relS (F : C ⥤ ModuleCat.{0} R) (U Q : ObjectProperty C) (n : ℕ) (z : CH.Cn F n) (hz : z ∈ relS F Q n) :
    (CH.Mor.restrict F U.ι).pullC n z ∈ relS (U.ι ⋙ F) (fun T => Q T.obj) n := fun s hs => hz _ hs

end Gen

theorem ri_glob (hSL : SiteLaws) (hMV : MVBij) (hCD : CovDesc) (hZR : ZarRel) (hTop : TopRes)
    {K : Type} [Field K] {W Z Y : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) [Mono i] (π : Y ⟶ Z)
    (ι : Type) [DecidableEq ι] (f : ι → Z.Opens) (hf : (⨆ o, f o) = ⊤)
    (hQ : Cosieve (On q i)) (hQ' : Cosieve (On (π ≫ q) (pullback.snd i π)))
    (hloc : ∀ (S : Finset ι), S.Nonempty → ∀ (a : ℕ) h h' (n : ℕ),
      Function.Bijective ((pullRC π rfl a (U := capU (fun o => inU q (f o)) S)
        (U' := capU (fun o => inU (π ≫ q) (π ⁻¹ᵁ f o)) S) hQ hQ' h h').mapH n))
    (a n : ℕ) (z : CH.Cn (G q a) n) (hz : CH.d (G q a) n z = 0) (hrel : z ∈ relS (G q a) (On q i) n)
    (hnull : RelNull (G (π ≫ q) a) (On (π ≫ q) (pullback.snd i π)) n (pullC π rfl a n z)) :
    RelNull (G q a) (On q i) n z := by
  obtain ⟨hcosZ, -, htopZ, -, hpre, hon⟩ := hSL K W Z Y q i π
  have hcosY := (hSL K Y Y Y (π ≫ q) (𝟙 Y) (𝟙 Y)).1
  let UA : ι → ObjectProperty (Thick (smFun Z q)) := fun o => inU q (f o)
  let UB : ι → ObjectProperty (Thick (smFun Y (π ≫ q))) := fun o => inU (π ≫ q) (π ⁻¹ᵁ f o)
  let A := covSy (G q a) UA hQ
  let B := covSy (G (π ≫ q) a) UB hQ'
  have hcap : ∀ S : Finset ι, ∀ T, capU UB S T → capU UA S ((smS π rfl).G.obj T) := fun S T hT =>
    ⟨let ⟨α, h⟩ := hT.1; ⟨α, ((hpre (f α) T).1 h)⟩, fun α hα => (hpre (f α) T).1 (hT.2 α hα)⟩
  have hOn : ∀ T, On (π ≫ q) (pullback.snd i π) T → On q i ((smS π rfl).G.obj T) := fun T h => (hon T).1 h
  let m : A.Hom B :=
    { φ := fun S => pullRC π rfl a (U := capU UA S) (U' := capU UB S) hQ hQ' (hcap S) hOn
      nat := fun h n x => Subtype.ext (morU_resU (morG π rfl a) _ _ (hcap _) (hcap _) n x.1) }
  have hA : A.Desc := hCD K ι _ (G q a) UA (On q i) hQ fun o => hcosZ _
  have hB : B.Desc := hCD K ι _ (G (π ≫ q) a) UB (On (π ≫ q) (pullback.snd i π)) hQ' fun o => hcosY _
  have hinj : Function.Injective ((m.φ ∅).mapH n) :=
    (hMV K ι A B m hA hB (fun S hS k => hloc S hS a (hcap S) hOn k) n).1

  have hmemE := restrict_relS (G q a) (capU UA ∅) (On q i) n z hrel
  let xE : (A.K ∅).X n := ⟨_, hmemE⟩
  have hxE : (A.K ∅).d n xE = 0 := Subtype.ext ((rc_d_val (G q a) (capU UA ∅) hQ n xE).trans (by
    rw [CH.Mor.d_pullC, hz, map_zero]; rfl))
  have hφE : ((m.φ ∅).f n xE).1 = (CH.Mor.restrict (G (π ≫ q) a) (capU UB ∅).ι).pullC n (pullC π rfl a n z) :=
    morU_restrict (morG π rfl a) (hcap ∅) n z
  have hclsE : (A.K ∅).cls xE hxE = 0 := by
    apply hinj
    rw [map_zero]
    change (B.K ∅).cls ((m.φ ∅).f n xE) _ = 0
    rw [cx_cls_eq_zero]
    cases n with
    | zero =>
      have h0 : pullC π rfl a 0 z = 0 := hnull
      apply Subtype.ext
      rw [hφE, h0, map_zero]
      rfl
    | succ n =>
      obtain ⟨b, hb, hdb⟩ := hnull
      refine ⟨⟨(CH.Mor.restrict (G (π ≫ q) a) (capU UB ∅).ι).pullC n b, fun s hs => hb _ hs⟩, Subtype.ext ?_⟩
      rw [hφE, ← hdb]
      exact (rc_d_val (G (π ≫ q) a) (capU UB ∅) hQ' n _).trans (CH.Mor.d_pullC _ n b)

  have hZar : ∀ (P : ObjectProperty (Thick (smFun Z q))) (hP : P = fun T => ∃ α, inU q (f α) T) (h : P ≤ inU q ⊤) k,
      Function.Bijective ((RC.res (G q a) hQ h).mapH k) := by
    rintro P rfl h k
    exact hZR K W Z q i hQ ι ⊤ f hf h a k
  have hPE : capU UA ∅ = fun T => ∃ α, inU q (f α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun α hα => by simp at hα⟩⟩
  have hle : capU UA ∅ ≤ inU q ⊤ := fun T _ => htopZ T
  have hmemT := restrict_relS (G q a) (inU q ⊤) (On q i) n z hrel
  let xT : (RC (G q a) (inU q ⊤) hQ).X n := ⟨_, hmemT⟩
  have hxT : (RC (G q a) (inU q ⊤) hQ).d n xT = 0 := Subtype.ext ((rc_d_val (G q a) (inU q ⊤) hQ n xT).trans (by
    rw [CH.Mor.d_pullC, hz, map_zero]; rfl))
  have hclsT : (RC (G q a) (inU q ⊤) hQ).cls xT hxT = 0 := by
    apply (hZar _ hPE hle n).1
    rw [map_zero]
    have e : (RC.res (G q a) hQ hle).f n xT = xE := Subtype.ext (resU_restrict (G q a) hle n z)
    change (A.K ∅).cls ((RC.res (G q a) hQ hle).f n xT) _ = 0
    simp only [e]
    exact hclsE
  rw [cx_cls_eq_zero] at hclsT
  have hT := hTop K _ (G q a) (inU q ⊤) (On q i) htopZ
  cases n with
  | zero =>
    have h0 : xT = 0 := hclsT
    apply (hT 0).1.1
    rw [map_zero]
    exact congrArg Subtype.val h0
  | succ n =>
    obtain ⟨y, hy⟩ := hclsT
    obtain ⟨y₀, hy₀⟩ := (hT n).1.2 y.1
    refine ⟨y₀, ((hT n).2 y₀).1 (hy₀ ▸ y.2), ?_⟩
    apply (hT (n + 1)).1.1
    rw [← CH.Mor.d_pullC, hy₀, ← rc_d_val]
    exact congrArg Subtype.val hy

theorem relInjOf_pf (hTop : TopRes) : RelInjOf := by
  intro hSL hMV hCD hZR hCL hCB hIso K _ _ W Z Y q _ _ i π _ D d hd hB a n z hz hrel hnull
  obtain ⟨B⟩ := hB
  classical
  haveI := B.closed
  have hQ : Cosieve (On q i) := (hSL K W Z Z q i (𝟙 Z)).2.1
  have hQ' : Cosieve (On (π ≫ q) (pullback.snd i π)) :=
    (hSL K (pullback i π) Y Y (π ≫ q) (pullback.snd i π) (𝟙 Y)).2.1
  exact ri_glob hSL hMV hCD hZR hTop q i π (Option B.ι) (optU B) (optU_cover B) hQ hQ'
    (fun S hS a h h' k => relInj_loc hSL hIso hCL hCB K W Z Y q i π D d hd B hQ hQ' S hS a h h' k) a n z hz hrel hnull

end CrystallineSemistableComparison.Onto

end
