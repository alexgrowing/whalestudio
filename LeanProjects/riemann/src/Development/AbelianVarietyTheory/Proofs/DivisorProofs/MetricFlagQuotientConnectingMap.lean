import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagModelOfIsIsometry

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open Limits

namespace GlobalTheory.StepLine

theorem isVB_cokernel_of_succ {X : Scheme.{0}} {A₀ A₁ : X.Modules} {u : A₀ ⟶ A₁} {a : ℕ}
    (hu : IsSubbundle u) (h₀ : IsVB A₀ a) (h₁ : IsVB A₁ (a + 1)) : IsVB (cokernel u) 1 := fun x => by
  have : Nonempty X := ⟨x⟩
  have := hu.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨h, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } h₀ hs
  obtain rfl : s = 1 := by have := h.rank_unique h₁; omega
  exact hs x

abbrev seq {X : Scheme.{0}} {A₀ A₁ : X.Modules} (u : A₀ ⟶ A₁) : ShortComplex X.Modules :=
  .mk u (cokernel.π u) (cokernel.condition u)

theorem seq_shortExact {X : Scheme.{0}} {A₀ A₁ : X.Modules} {u : A₀ ⟶ A₁} (hu : IsSubbundle u) :
    (seq u).ShortExact :=
  have := hu.mono
  { exact := ShortComplex.exact_cokernel _ }

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Line

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  (ρ : Y ⟶ Y₁) (wρ : ρ ≫ q₁ = p) {G : Y₁.Modules} {E : Y.Modules}
  (ψ : (Scheme.Modules.pullback ρ).obj G ≅ E) {n : ℕ} (fl : Vert.Flag E n) (l : Fin n)
  {A₀ A₁ : Y₁.Modules} (u : A₀ ⟶ A₁) (v : A₁ ⟶ G)
  (e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc)
  (e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ)

theorem map_comp_e₁ (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom)
    (he₀ : e₀.hom ≫ fl.ι l.castSucc = (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ ψ.hom) :
    (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l := by
  rw [← cancel_mono (fl.ι l.succ), Category.assoc, Category.assoc, he₁, fl.step_ι, he₀,
    Functor.map_comp, Category.assoc]

variable {ρ ψ fl l u v e₀ e₁} in

def grIso (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l) :
    (Scheme.Modules.pullback ρ).obj (cokernel u) ≅ fl.gr l :=
  PreservesCokernel.iso (Scheme.Modules.pullback ρ) u ≪≫ cokernel.mapIso _ _ e₀ e₁ sq

variable {ρ ψ fl l u v e₀ e₁} in
theorem map_π_grIso (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l) :
    (Scheme.Modules.pullback ρ).map (cokernel.π u) ≫ (grIso sq).hom = e₁.hom ≫ fl.π l := by
  have e := Limits.π_comp_cokernelComparison u (Scheme.Modules.pullback ρ)
  rw [← Limits.PreservesCokernel.iso_inv] at e
  have e' := congrArg (· ≫ (Limits.PreservesCokernel.iso (Scheme.Modules.pullback ρ) u).hom) e
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at e'
  change _ ≫ (PreservesCokernel.iso (Scheme.Modules.pullback ρ) u).hom ≫
    (cokernel.mapIso _ _ e₀ e₁ sq).hom = e₁.hom ≫ cokernel.π (fl.step l)
  rw [← Category.assoc, ← e']
  simp [cokernel.mapIso]

end Line

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Chart

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}

def pullChart (hA₀ : IsVB A₀ l) (hQ : IsVB (cokernel u) 1)
    (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
    (a : AdaptedChart (seq u) l 1) : AdaptedChart (VMetric.stepSeq fl l) l 1 :=
  have := hA₀.isQuasicoherent
  have := hQ.isQuasicoherent
  { U := ρ ⁻¹ᵁ a.U
    e := fun j => e₀.hom.app _ (pullbackSections ρ _ le_rfl (a.e j))
    t := fun j => e₁.hom.app _ (pullbackSections ρ _ le_rfl (a.t j))
    he := (a.he.pullback ρ).map_iso e₀.hom
    ht := by
      have h := (a.ht.pullback ρ).map_iso (grIso sq).hom
      convert h using 2 with j
      rw [← QCoh.pullback_map_app_pullbackSections]
      exact (congr(($(map_π_grIso sq)).app _ _)).symm }

end Chart

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Gram

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  (a : AdaptedChart (seq u) l 1)

theorem pullChart_frame (j : Fin l ⊕ Fin 1) :
    (pullChart hA₀ hQ sq a).frame j =
      have := hA₁.isQuasicoherent
      e₁.hom.app _ (pullbackSections ρ _ le_rfl (a.frame j)) := by
  have := hA₁.isQuasicoherent
  have := hA₀.isQuasicoherent
  rcases j with j | j
  · change (fl.step l).app _ (e₀.hom.app _ _) = e₁.hom.app _ (pullbackSections ρ _ le_rfl (u.app a.U (a.e j)))
    rw [← QCoh.pullback_map_app_pullbackSections]
    exact (congr(($(sq)).app _ _)).symm
  · rfl

theorem pullChart_quot :
    (pullChart hA₀ hQ sq a).quot = (a.quot.pull hQ ρ).map (grIso sq) := by
  have := hQ.isQuasicoherent
  have e : (pullChart hA₀ hQ sq a).quot.e = ((a.quot.pull hQ ρ).map (grIso sq)).e := by
    funext j
    refine Eq.trans ?_ (congrArg ((grIso sq).hom.app _)
      (QCoh.pullback_map_app_pullbackSections ρ (cokernel.π u) le_rfl (a.t j)))
    exact (congr(($(map_π_grIso sq)).app _ _)).symm
  have key : ∀ {F : Y.Modules} {U : Y.Opens} {e e' : Fin 1 → Γ(F, U)} (he : IsFrame e)
      (he' : IsFrame e'), e = e' → (⟨U, e, he⟩ : Chart F 1) = ⟨U, e', he'⟩ := by
    rintro F U e e' he he' rfl
    rfl
  exact key _ _ e

end Gram

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Met

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁} {v : A₁ ⟶ G}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  (a : AdaptedChart (seq u) l 1)
  {ψ : (Scheme.Modules.pullback ρ).obj G ≅ E} (g : VMetric q₁ G n) (h' : VMetric p E n)
  (wρ : ρ ≫ q₁ = p)

theorem gram_pullChart (hψ : (g.pull ρ wρ).IsIsometry h' ψ) (hv : IsSubbundle v)
    (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom) {τ : k →+* ℂ}
    {z : CxPts p τ} (hz : z ∈ ptsIn p τ (ρ ⁻¹ᵁ a.U)) :
    ((h'.stepMet fl l).met τ).gram (pullChart hA₀ hQ sq a).frame z =
      ((g.restrict hv hA₁).met τ).gram a.frame (PtsOver.map ρ wρ _ z) := by
  have := g.isVB.isQuasicoherent
  have := hA₁.isQuasicoherent
  have hz' : PtsOver.map ρ wρ _ z ∈ ptsIn q₁ τ a.U := hz
  ext j m
  change ((h'.met τ).restrict (fl.isSubbundle l.succ) (fl.isVB l.succ)).form _ _ z =
    ((g.met τ).restrict hv hA₁).form _ _ _
  refine (Met.form_restrict _ _ _ _ _ hz).trans (Eq.trans ?_ (Met.form_restrict _ _ _ _ _ hz').symm)
  have e (j) : (fl.ι l.succ).app (ρ ⁻¹ᵁ a.U) ((pullChart hA₀ hQ sq a).frame j) =
      ψ.hom.app _ (pullbackSections ρ G le_rfl (v.app a.U (a.frame j))) := by
    rw [pullChart_frame hA₀ hA₁ hQ sq a j, ← QCoh.pullback_map_app_pullbackSections]
    exact congr(($(he₁)).app _ _)
  rw [e j, e m, hψ τ _ _ _ z hz]
  exact (g.met τ).form_pull ρ wρ _ _ le_rfl hz

end Met

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

section Eq

variable {k : Type} [CommRing k] {Y Y₁ : Scheme.{0}} {p : Y ⟶ Sp k} {q₁ : Y₁ ⟶ Sp k}
  {ρ : Y ⟶ Y₁} {G : Y₁.Modules} {E : Y.Modules} {n : ℕ} {fl : Vert.Flag E n} {l : Fin n}
  {A₀ A₁ : Y₁.Modules} {u : A₀ ⟶ A₁} {v : A₁ ⟶ G}
  {e₀ : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc}
  {e₁ : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ}
  (hA₀ : IsVB A₀ l) (hA₁ : IsVB A₁ (l + 1)) (hQ : IsVB (cokernel u) 1)
  (sq : (Scheme.Modules.pullback ρ).map u ≫ e₁.hom = e₀.hom ≫ fl.step l)
  {ψ : (Scheme.Modules.pullback ρ).obj G ≅ E} (g : VMetric q₁ G n) (h' : VMetric p E n)
  (wρ : ρ ≫ q₁ = p)

theorem grMet_eq (hψ : (g.pull ρ wρ).IsIsometry h' ψ) (hu : IsSubbundle u) (hv : IsSubbundle v)
    (he₁ : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom) :
    h'.grMet fl l = ((((g.restrict hv hA₁).quot (seq_shortExact hu) hA₀ hQ).pull ρ wρ).map
      (grIso sq)) := by
  refine VMetric.ext (funext fun τ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted (seq_shortExact hu) hA₀ hQ (PtsOver.map ρ wρ _ z)
  have ha' : z ∈ ptsIn p τ (ρ ⁻¹ᵁ a.U) := ha
  refine ⟨(pullChart hA₀ hQ sq a).quot, ha', ?_⟩
  refine (((h'.stepMet fl l).met τ).quot_G (VMetric.stepSeq_shortExact fl l) (fl.isVB l.castSucc)
    (fl.isVB_gr l) (pullChart hA₀ hQ sq a) ha').trans ?_
  rw [gram_pullChart hA₀ hA₁ hQ sq a g h' wρ hψ hv he₁ ha', pullChart_quot hA₀ hQ sq a]
  set M := ((g.restrict hv hA₁).quot (seq_shortExact hu) hA₀ hQ).met τ with hM
  change _ = ((M.pull ρ wρ).map (grIso sq)).G ((a.quot.pull M.isVB ρ).map (grIso sq)) z
  have h₁ := (M.pull ρ wρ).map_G (grIso sq) (a.quot.pull M.isVB ρ) ha'
  have h₂ := M.pull_G ρ wρ a.quot ha
  have h₃ := ((g.restrict hv hA₁).met τ).quot_G (seq_shortExact hu) hA₀ hQ a ha
  rw [h₁, h₂]
  exact h₃.symm

end Eq

end GlobalTheory.StepLine

namespace GlobalTheory.StepLine

variable {k : Type} [CommRing k]

theorem isIsometry_pull_congr {X Y : Scheme.{0}} {q : Y ⟶ Sp k} {t : X ⟶ Sp k} {E : Y.Modules}
    {r : ℕ} (h : VMetric q E r) {f f' : X ⟶ Y} (e : f = f') (hf : f ≫ q = t) (hf' : f' ≫ q = t) :
    (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
  subst e
  intro σ V s s' y hy
  rfl

theorem det_congr {X : Scheme.{0}} {p : X ⟶ Sp k} {F : X.Modules} {r : ℕ} {h₁ h₂ : VMetric p F r}
    (H₁ : h₁.IsCInf) (H₂ : h₂.IsCInf) (e : h₁ = h₂) : VMetric.det H₁ = VMetric.det H₂ := by
  subst e
  rfl

end GlobalTheory.StepLine

theorem GlobalTheory.StepLine.isometric_grLB_of_steps_pull : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (l : Fin n) (A₀ A₁ : Y₁.Modules) (u : A₀ ⟶ A₁) (v : A₁ ⟶ (Scheme.Modules.pullback σ).obj E),
    GlobalTheory.VB.IsSubbundle u → GlobalTheory.VB.IsSubbundle v → GlobalTheory.VB.IsVB A₀ l → GlobalTheory.VB.IsVB A₁ (l + 1) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₁ ≅ fl.F l.succ, e.hom ≫ fl.ι l.succ =
      (Scheme.Modules.pullback ρ).map v ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj A₀ ≅ fl.F l.castSucc, e.hom ≫ fl.ι l.castSucc =
      (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    ∃ M : HermLB q₁, (M.pull ρ wρ).Isometric (VMetric.grLB fl l (H.pull π w)) := by
  intro k _ B Y Y₁ q p q₁ π σ ρ w wσ wρ wq E n h H fl l A₀ A₁ u v hu hv hA₀ hA₁ ⟨e₁, he₁⟩ ⟨e₀, he₀⟩
  let ψ := (Scheme.Modules.pullbackComp ρ σ).app E ≪≫ (Scheme.Modules.pullbackCongr wσ).app E
  have he₁' : e₁.hom ≫ fl.ι l.succ = (Scheme.Modules.pullback ρ).map v ≫ ψ.hom := he₁
  have he₀' : e₀.hom ≫ fl.ι l.castSucc = (Scheme.Modules.pullback ρ).map (u ≫ v) ≫ ψ.hom := he₀
  have e : (ρ ≫ σ) ≫ q = p := by rw [Category.assoc, wq, wρ]
  have hψ : ((h.pull σ wq).pull ρ wρ).IsIsometry (h.pull π w) ψ :=
    IsometryPullback.isIsometry_trans ((VMetric.isIsometry_pull_id_comp k B q E n h).2 Y₁ Y q₁ p σ ρ wq wρ e)
      (StepLine.isIsometry_pull_congr h wσ e w)
  have sq := StepLine.map_comp_e₁ ρ ψ fl l u v e₀ e₁ he₁' he₀'
  have hQ := StepLine.isVB_cokernel_of_succ hu hA₀ hA₁
  have HQ := (((H.pull σ wq).restrict hv hA₁).quot (StepLine.seq_shortExact hu) hA₀ hQ)
  refine ⟨VMetric.det HQ, ?_⟩
  have eq := StepLine.grMet_eq hA₀ hA₁ hQ sq (h.pull σ wq) (h.pull π w) wρ hψ hu hv he₁'
  refine (VMetric.isometric_det_pull HQ ρ wρ).symm.trans
    ((VMetric.isometric_det_map (HQ.pull ρ wρ) (StepLine.grIso sq)).trans ?_)
  rw [VMetric.grLB, StepLine.det_congr _ ((H.pull π w).grMet fl l) eq.symm]
  exact HermLB.Isometric.refl _
