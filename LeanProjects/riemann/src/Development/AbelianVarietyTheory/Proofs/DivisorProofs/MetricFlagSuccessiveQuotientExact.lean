import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortExactOfComposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SubqPair

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.VMetric
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem chart_eq {F : X.Modules} {r : ℕ} {U : X.Opens} {e e' : Fin r → Γ(F, U)} (he : IsFrame e)
    (he' : IsFrame e') (h : e = e') : (⟨U, e, he⟩ : Chart F r) = ⟨U, e', he'⟩ := by
  subst h
  rfl

theorem isometric_det_of_eq {F : X.Modules} {r : ℕ} {h₁ h₂ : VMetric p F r} (H₁ : h₁.IsCInf)
    (H₂ : h₂.IsCInf) (e : h₁ = h₂) : (det H₁).Isometric (det H₂) := by
  subst e
  exact CurveDens.det_isometric_of_isIsometry k X p _ _ r _ _ H₁ H₂ (Iso.refl _)
    fun _ _ _ _ _ _ => rfl

theorem pull_restrict {E F : X.Modules} {r s : ℕ} (h : VMetric p E r) {j : F ⟶ E}
    (hj : IsSubbundle j) (hF : IsVB F s) (π : Y ⟶ X) (w : π ≫ p = q)
    (hj' : IsSubbundle ((Scheme.Modules.pullback π).map j)) :
    (h.restrict hj hF).pull π w = (h.pull π w).restrict hj' (hF.pullback π) := by
  have := hF.isQuasicoherent
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  have hc := hF.mem_pick (PtsOver.map π w _ z)
  refine ⟨(hF.pick (PtsOver.map π w _ z)).pull hF π, hc, ?_⟩
  refine (((h.met σ).restrict hj hF).pull_G π w _ hc).trans ?_
  ext a b
  have e (a) := QCoh.pullback_map_app_pullbackSections π j
    (le_refl (π ⁻¹ᵁ (hF.pick (PtsOver.map π w _ z)).U)) ((hF.pick (PtsOver.map π w _ z)).e a)
  exact (((h.met σ).form_pull π w _ _ le_rfl hc).symm).trans
    (congrArg₂ (fun s t => ((h.met σ).pull π w).form s t z) (e a).symm (e b).symm)

theorem pull_quot {S : ShortComplex X.Modules} {r s : ℕ} (h : VMetric p S.X₂ (r + s))
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (π : Y ⟶ X) (w : π ≫ p = q)
    (w' : (Scheme.Modules.pullback π).map S.f ≫ (Scheme.Modules.pullback π).map S.g = 0)
    (hS' : (ShortComplex.mk _ _ w').ShortExact) :
    (h.quot hS h₁ h₃).pull π w =
      VMetric.quot (S := .mk _ _ w') (h.pull π w) hS' (h₁.pullback π) (h₃.pullback π) := by
  have := h₁.isQuasicoherent
  have := h.isVB.isQuasicoherent
  have := h₃.isQuasicoherent
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun z => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ (PtsOver.map π w _ z)
  have eg : (fun j => ((Scheme.Modules.pullback π).map S.g).app (π ⁻¹ᵁ a.U)
      (pullbackSections π _ le_rfl (a.t j))) =
      fun j => pullbackSections π _ le_rfl (S.g.app a.U (a.t j)) :=
    funext fun j => QCoh.pullback_map_app_pullbackSections π S.g _ _
  let a' : AdaptedChart (.mk _ _ w') r s :=
    { U := π ⁻¹ᵁ a.U
      e := fun j => pullbackSections π _ le_rfl (a.e j)
      t := fun j => pullbackSections π _ le_rfl (a.t j)
      he := a.he.pullback π
      ht := eg ▸ a.ht.pullback π }
  have ha' : z ∈ ptsIn q σ a'.U := ha
  have hq : a'.quot = a.quot.pull h₃ π := chart_eq _ _ eg
  have hf (j) : a'.frame j = pullbackSections π _ le_rfl (a.frame j) := by
    rcases j with j | j
    · exact QCoh.pullback_map_app_pullbackSections π S.f _ _
    · rfl
  refine ⟨a'.quot, ha', Eq.trans ?_ (Met.quot_G (S := .mk _ _ w') ((h.met σ).pull π w) hS'
    (h₁.pullback π) (h₃.pullback π) a' ha').symm⟩
  rw [hq]
  refine (((h.met σ).quot hS h₁ h₃).pull_G π w a.quot ha).trans ?_
  rw [(h.met σ).quot_G hS h₁ h₃ a ha]
  congr 1
  ext i j
  exact ((h.met σ).form_pull π w _ _ le_rfl ha').symm.trans
    (congrArg₂ (fun s t => ((h.met σ).pull π w).form s t z) (hf i).symm (hf j).symm)

theorem isIsometry_quot_zero {S : ShortComplex X.Modules} (h : VMetric p S.X₂ (0 + 1))
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    VMetric.IsIsometry (r := 1) h (h.quot hS h₁ h₃) (asIso S.g) := by
  rw [VMetric.isIsometry_iff]
  refine VMetric.ext (funext fun σ => Met.ext_of_exists fun y => ?_)
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  have ht : IsFrame a.t := by
    convert a.ht.map_iso (inv S.g) using 2 with j
    exact (congr(($(IsIso.hom_inv_id S.g)).app a.U (a.t j))).symm
  let c : Chart S.X₂ 1 := ⟨a.U, a.t, ht⟩
  refine ⟨a.quot, ha, ((h.met σ).quot_G hS h₁ h₃ a ha).trans ?_⟩
  refine Eq.trans ?_ (Met.map_G (r := 1) (h.met σ) (asIso S.g) c ha).symm
  ext i j
  rw [← Met.form_frame (r := 1) (h.met σ) c ha]
  simp [quotGram, Matrix.mul_apply, Matrix.toBlocks₂₂, Met.gram, AdaptedChart.frame, c]

theorem isometric_pair {E A B V : X.Modules} {r n : ℕ} {h : VMetric p E r} (H : h.IsCInf)
    (fl : Vert.Flag E r) (hn₀ : n < r) (hn : n + 1 < r) {u : A ⟶ B} {t : B ⟶ V} {w : u ≫ t = 0}
    (hS : (ShortComplex.mk u t w).ShortExact) (hA : IsVB A n) (hB : IsVB B (n + (1 + 1)))
    (hV : IsVB V (1 + 1)) {j : B ⟶ E} (hj : IsSubbundle j)
    (eB : B ≅ fl.F (Fin.succ ⟨n + 1, hn⟩)) (heB : eB.hom ≫ fl.ι _ = j)
    (eA : A ≅ fl.F (Fin.castSucc ⟨n, hn₀⟩)) (heA : eA.hom ≫ fl.ι _ = u ≫ j)
    (fl₁ : Vert.Flag V 2) (x : fl.F (Fin.succ ⟨n, hn₀⟩) ⟶ B) (g : fl.F (Fin.succ ⟨n, hn₀⟩) ⟶ fl₁.F 1)
    (hx : x ≫ j = fl.ι _) (hg : g ≫ fl₁.ι 1 = x ≫ t) [Epi g] {h₁ : VMetric p V 2} (H₁ : h₁.IsCInf)
    (e₁ : h₁ = VMetric.quot (S := .mk u t w) (r := n) (s := 1 + 1) (h.restrict hj hB) hS hA hV) :
    (grLB fl₁ 0 H₁).Isometric (grLB fl ⟨n, hn₀⟩ H) ∧
      (grLB fl₁ 1 H₁).Isometric (grLB fl ⟨n + 1, hn⟩ H) := by
  subst e₁
  let i₀ : Fin r := ⟨n, hn₀⟩
  let i₁ : Fin r := ⟨n + 1, hn⟩
  change eB.hom ≫ fl.ι i₁.succ = j at heB
  change eA.hom ≫ fl.ι i₀.castSucc = u ≫ j at heA
  change x ≫ j = fl.ι i₀.succ at hx
  have := hj.mono
  have res {F F' : X.Modules} {s : ℕ} {a : F ⟶ E} {b : F' ⟶ E} (ha : IsSubbundle a)
      (hb : IsSubbundle b) (hF : IsVB F s) (hF' : IsVB F' s) (e : F ≅ F') (he : e.hom ≫ b = a) :
      (h.restrict ha hF).IsIsometry (h.restrict hb hF') e := fun σ U s t y hy => by
    refine ((h.met σ).form_restrict hb hF' _ _ hy).trans
      (Eq.trans ?_ ((h.met σ).form_restrict ha hF s t hy).symm)
    rw [← he]
    rfl
  let f : A ⟶ fl.F i₀.succ := eA.hom ≫ fl.step i₀
  let q₁ : B ⟶ fl.gr i₁ := eB.hom ≫ fl.π i₁
  have hxB : x ≫ eB.hom = fl.step i₁ := by
    rw [← cancel_mono (fl.ι i₁.succ), Category.assoc, heB, hx]
    exact (fl.step_ι i₁).symm
  have w₀ : f ≫ fl.π i₀ = 0 := by
    simp only [f, Category.assoc]
    rw [show fl.step i₀ ≫ fl.π i₀ = 0 from cokernel.condition _, comp_zero]
  have w₁ : x ≫ q₁ = 0 := by
    rw [← Category.assoc, hxB]
    exact cokernel.condition _
  have hS₀ : (ShortComplex.mk f _ w₀).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl i₀) eA.symm (Iso.refl _)
      (Iso.refl _) (by simp [f]) (by simp)) (stepSeq_shortExact fl i₀)
  have hS₁ : (ShortComplex.mk x q₁ w₁).ShortExact :=
    ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl i₁) (Iso.refl _) eB.symm
      (Iso.refl _) ((Category.id_comp _).trans ((Iso.eq_comp_inv _).2 hxB)) (by simp [q₁]))
      (stepSeq_shortExact fl i₁)
  have hu : f ≫ x = u := by
    rw [← cancel_mono j, Category.assoc, hx, Category.assoc, fl.step_ι, heA]
  have hxs : IsSubbundle x := isSubbundle_of_shortExact hS₁ (fl.isVB_gr i₁)
  obtain ⟨l, m, w₃, hS₃, el, em⟩ := ThirdIso.abelian f x u (fl.π i₀) q₁ t w₀ w₁ w hS₀ hS₁ hS hu
  have hl : IsSubbundle l := isSubbundle_of_shortExact hS₃ (fl.isVB_gr i₁)
  have key (σ : k →+* ℂ) := MetStage.metStages k X p σ _ _ _ _ _ _ f x u (fl.π i₀) q₁ t w₀ w₁ w
    hS₀ hS₁ hS l m w₃ hS₃ n hA (fl.isVB i₀.succ) (fl.isVB_gr i₀) (fl.isVB_gr i₁) hV hxs
    ((h.restrict hj hB).met σ) hu el em hl

  have hfg : fl.step i₀ ≫ g = 0 := by
    rw [← cancel_mono (fl₁.ι 1), ← cancel_epi eA.hom, zero_comp, comp_zero, Category.assoc, hg,
      ← Category.assoc, ← Category.assoc]
    exact (congrArg (· ≫ t) hu).trans w
  let e : fl.gr i₀ ⟶ fl₁.F 1 := cokernel.desc _ g hfg
  have he : fl.π i₀ ≫ e = g := cokernel.π_desc _ _ _
  have hel : e ≫ fl₁.ι 1 = l := by
    rw [← cancel_epi (fl.π i₀), ← Category.assoc, he, hg, el]
  have : Mono l := hl.mono
  have : Mono e := mono_of_mono_fac hel
  have : Epi e := epi_of_epi_fac he
  have : IsIso e := isIso_of_mono_of_epi e
  have HB : (h.restrict hj hB).IsCInf := H.restrict hj hB
  constructor
  · have : IsIso (stepSeq fl₁ 0).g := (stepSeq_shortExact fl₁ 0).isIso_g_iff.2
      (isVB_zero_iff.1 (fl₁.isVB 0))
    have a₁ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ _
      (H₁.restrict (fl₁.isSubbundle 1) (fl₁.isVB 1)) (H₁.grMet fl₁ 0) _
      (isIsometry_quot_zero (S := stepSeq fl₁ 0) (stepMet _ fl₁ 0) (stepSeq_shortExact fl₁ 0)
        (fl₁.isVB 0) (fl₁.isVB_gr 0))
    have a₂ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ _
      (H₁.restrict hl (fl.isVB_gr i₀)) (H₁.restrict (fl₁.isSubbundle 1) (fl₁.isVB 1)) (asIso e)
      fun σ U s t y hy => by
        refine (Met.form_restrict _ (fl₁.isSubbundle 1) (fl₁.isVB 1) _ _ hy).trans
          (Eq.trans ?_ (Met.form_restrict _ hl (fl.isVB_gr i₀) s t hy).symm)
        rw [← hel]
        rfl
    have a₃ := isometric_det_of_eq (H₁.restrict hl (fl.isVB_gr i₀))
      (IsCInf.quot (S := .mk f _ w₀) hS₀ hA (fl.isVB_gr i₀) (HB.restrict hxs (fl.isVB i₀.succ)))
      (VMetric.ext (funext fun σ => (key σ).1))
    have a₄ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk f _ w₀) (stepSeq fl i₀) n 1 _
      (h.stepMet fl i₀) (HB.restrict hxs (fl.isVB i₀.succ)) (H.restrict _ _) hS₀
      (stepSeq_shortExact fl i₀) hA (fl.isVB_gr i₀) (fl.isVB i₀.castSucc) (fl.isVB_gr i₀) eA
      (Iso.refl _) (Category.comp_id _).symm fun σ U s t y hy => by
        refine ((h.met σ).form_restrict (fl.isSubbundle i₀.succ) (fl.isVB i₀.succ) _ _ hy).trans
          (Eq.trans ?_ ((Met.form_restrict _ hxs (fl.isVB i₀.succ) s t hy).trans
            ((h.met σ).form_restrict hj hB _ _ hy)).symm)
        rw [← hx]
        rfl).1
    exact a₁.symm.trans (a₂.symm.trans (a₃.trans a₄))
  · have : IsIso (fl₁.ι 2) := fl₁.isIso_last
    have a₁ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk l m w₃) (stepSeq fl₁ 1) 1 1 _
      (stepMet _ fl₁ 1) H₁ (H₁.restrict _ _) hS₃ (stepSeq_shortExact fl₁ 1) (fl.isVB_gr i₀)
      (fl.isVB_gr i₁) (fl₁.isVB 1) (fl₁.isVB_gr 1) (asIso e) (asIso (fl₁.ι 2)).symm
      ((Iso.eq_comp_inv (asIso (fl₁.ι 2))).2 ((Category.assoc _ _ _).trans
        ((congrArg (e ≫ ·) (fl₁.step_ι 1)).trans hel))) fun σ U s t y hy => by
        refine (Met.form_restrict _ (fl₁.isSubbundle 2) (fl₁.isVB 2) _ _ hy).trans ?_
        have e (v : Γ(V, U)) : (fl₁.ι 2).app U ((inv (fl₁.ι 2)).app U v) = v :=
          congr(($(IsIso.inv_hom_id (fl₁.ι 2))).app U v)
        exact congrArg₂ (fun s t => Met.form _ s t y) (e s) (e t)).1
    have a₂ := isometric_det_of_eq (IsCInf.quot (S := .mk l m w₃) hS₃ (fl.isVB_gr i₀)
      (fl.isVB_gr i₁) H₁) (IsCInf.quot (S := .mk x q₁ w₁) (r := n + 1) (s := 1) hS₁
        (fl.isVB i₀.succ) (fl.isVB_gr i₁) HB) (VMetric.ext (funext fun σ => (key σ).2))
    have a₃ := (isometric_detQuot_and_bcInt_eq_of_iso k X p (.mk x q₁ w₁) (stepSeq fl i₁) (n + 1) 1
      _ (h.stepMet fl i₁) HB (H.restrict _ _) hS₁ (stepSeq_shortExact fl i₁) (fl.isVB i₀.succ)
      (fl.isVB_gr i₁) (fl.isVB i₁.castSucc) (fl.isVB_gr i₁) (Iso.refl _) eB
      ((Category.id_comp _).trans hxB.symm) (res hj _ hB _ eB heB)).1
    exact a₁.symm.trans (a₂.trans a₃)

end GlobalTheory.SubqPair

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

theorem GlobalTheory.SubqPair.exists_isometric_pair : ∀ (k : Type) [CommRing k] (B Y Y₁ : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (q₁ : Y₁ ⟶ Sp k)
    (π : Y ⟶ B) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (w : π ≫ q = p) (wσ : ρ ≫ σ = π) (wρ : ρ ≫ q₁ = p) (wq : σ ≫ q = q₁)
    (E : B.Modules) (n : ℕ) (h : VMetric q E n) (H : h.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (i i' : Fin n), (i' : ℕ) = i + 1 → ∀ (S P E₁ : Y₁.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback σ).obj E)
    (t : P ⟶ E₁) (wst : s ≫ t = 0) (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    (ShortComplex.mk s t wst).ShortExact → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j → GlobalTheory.VB.IsVB S i →
    GlobalTheory.VB.IsVB P ((i : ℕ) + 2) → GlobalTheory.VB.IsVB E₁ 2 →
    (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ fl.F i'.succ, e.hom ≫ fl.ι i'.succ =
      (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ fl.F i.castSucc, e.hom ≫ fl.ι i.castSucc =
      (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E) →
    (∃ (x : fl.F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : fl.F i.succ ⟶ fl₁.F 1),
      x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app E ≫
        (Scheme.Modules.pullbackCongr wσ).hom.app E = fl.ι i.succ ∧
      g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) →
    ∃ (h₁ : VMetric q₁ E₁ 2) (H₁ : h₁.IsCInf),
      (VMetric.grLB fl₁ 0 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i (H.pull π w)) ∧
      (VMetric.grLB fl₁ 1 (H₁.pull ρ wρ)).Isometric (VMetric.grLB fl i' (H.pull π w)) := by
  intro k _ B Y Y₁ q p q₁ π σ ρ w wσ wρ wq E n h H fl i i' hi S P E₁ s j t wst fl₁ hS hs hj hSv hP hE₁
    ⟨eP, heP⟩ ⟨eS, heS⟩ ⟨x, g, hx, hg, _⟩
  obtain ⟨i, hi₀⟩ := i
  obtain ⟨i', hi₁⟩ := i'
  obtain rfl : i' = i + 1 := hi
  subst wσ
  have H₁ := VMetric.IsCInf.quot (S := .mk s t wst) (r := i) (s := 1 + 1) hS hSv hE₁
    ((H.pull σ wq).restrict hj hP)
  refine ⟨_, H₁, ?_⟩
  have := hS.epi_g
  have := hSv.isQuasicoherent
  have := hP.isQuasicoherent
  have w' : (Scheme.Modules.pullback ρ).map s ≫ (Scheme.Modules.pullback ρ).map t = 0 := by
    rw [← Functor.map_comp, wst, Functor.map_zero]
  have hS' : (ShortComplex.mk _ _ w').ShortExact :=
    ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback ρ hS.exact).1
      (SubPull.isSubbundle_pullback _ _ ρ _ _ s i hSv hs).mono (QCoh.exact_map_pullback ρ hS.exact).2
  have hj₁ := SubPull.isSubbundle_pullback _ _ ρ _ _ j _ hP hj
  let φ := (Scheme.Modules.pullbackComp ρ σ).app E
  have hj₂ : VB.IsSubbundle ((Scheme.Modules.pullback ρ).map j ≫ φ.hom) := by
    obtain ⟨_, a, ha⟩ := hj₁
    exact ⟨inferInstance, a, ha.of_iso (Limits.cokernelCompIsIso _ _).symm⟩
  refine GlobalTheory.SubqPair.isometric_pair (H.pull _ w) fl hi₀ hi₁ hS' (hSv.pullback ρ) (hP.pullback ρ)
    (hE₁.pullback ρ) hj₂ eP heP eS (heS.trans ?_) fl₁ x g hx hg (H₁.pull ρ wρ) ?_
  · rw [Functor.map_comp, Category.assoc]
    rfl
  · refine (GlobalTheory.SubqPair.pull_quot (S := .mk s t wst) (r := i) (s := 1 + 1) _ hS hSv hE₁ ρ wρ w' hS').trans ?_
    congr 1
    refine (GlobalTheory.SubqPair.pull_restrict _ hj hP ρ wρ hj₁).trans ?_
    refine VMetric.ext (funext fun τ => Met.ext_form fun U a b y hy => ?_)
    refine (Met.form_restrict _ hj₁ (hP.pullback ρ) a b hy).trans
      (Eq.trans ?_ (Met.form_restrict _ hj₂ (hP.pullback ρ) a b hy).symm)
    exact ((VMetric.isIsometry_pull_id_comp k B q E n h).2 Y₁ Y q₁ p σ ρ wq wρ w τ U _ _ y hy).symm

end
