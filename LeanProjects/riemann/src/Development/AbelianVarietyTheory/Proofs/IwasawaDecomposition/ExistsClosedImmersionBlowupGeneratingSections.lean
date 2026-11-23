import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.AnForm.R

namespace GlobalTheory.ProjBlowup

theorem exists_blowup_graph {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsProjOver s) (J : X.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (hσ : Generates J σ) :
    ∃ (G : Scheme.{0}) (b : G ⟶ X) (c : G ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      FinalTheorems.Blowup b J ∧ Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  have : IsProper (PSpace.str R m) := isProper_str R m
  have : LocallyOfFiniteType s := by
    obtain ⟨n, i, hi, rfl⟩ := hs
    have := isProper_str R n
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  let U : X.Opens := J.support.compl
  have hU : ∀ x : U.toScheme, U.ι x ∉ J.support := fun x => x.2
  have htop : ∀ {W : Scheme.{0}} (g : W ⟶ X), (∀ w, g w ∉ J.support) → J.comap g = ⊤ := fun g hg =>
    eq_top_of_forall_notMem _ fun w hw => hg w ((mem_support_comap J g w).1 hw)
  obtain ⟨φ, hφ, hφσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X U _ L m σ U.ι (U.ι ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ U.ι hσ)
    (by rw [htop _ hU]; exact effCartier_top _)
  let b := graphClosure.fst s (PSpace.str R m) U.ι φ hφ.symm
  let c := graphClosure.snd s (PSpace.str R m) U.ι φ hφ.symm
  let j := graphClosure.incl s (PSpace.str R m) U.ι φ hφ.symm
  have hjb : j ≫ b = U.ι := graphClosure.incl_fst ..
  have hjc : j ≫ c = φ := graphClosure.incl_snd ..
  have hbc : Proportional σ b c := .of_comp j (by rwa [hjb, hjc])
  have hc : b ≫ s = c ≫ PSpace.str R m := graphClosure.condition ..
  have hι : pullback.lift b c hc = graphClosure.ι s (PSpace.str R m) U.ι φ hφ.symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]; rfl
    · rw [pullback.lift_snd]; rfl
  refine ⟨_, b, c, hc, ⟨GlobalTheory.T.effCartier_of_proportional_sections R X _ U _ L m σ b c j (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ b hσ) hbc inferInstance
    inferInstance fun t => ?_, fun W g hg => ?_⟩, hbc, ?_⟩
  · rw [mem_support_comap, ← Scheme.Hom.comp_apply, hjb]; exact hU t
  · obtain ⟨ψ, hψ, hψσ⟩ := GlobalTheory.T.exists_proj_map_proportional_sections R X W _ L m σ g (g ≫ s) (GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ g hσ) hg
    have hd := GlobalTheory.T.isSchemeTheoreticallyDominant_compl_effCartier W _ hg
    let d := Scheme.Opens.ι (X := W) (J.comap g).support.compl
    have hdU : ∀ t, (d ≫ g) t ∉ J.support := fun t ht => t.2 ((mem_support_comap J g _).2 ht)
    let w := IsOpenImmersion.lift U.ι (d ≫ g) (by
      rintro _ ⟨t, rfl⟩
      exact ⟨⟨_, hdU t⟩, rfl⟩)
    have hw : w ≫ U.ι = d ≫ g := IsOpenImmersion.lift_fac ..
    have hw' : d ≫ ψ = w ≫ φ := GlobalTheory.T.eq_of_proportional_to_generating_sections R X _ L m σ (d ≫ g) _ _ (htop _ hdU ▸ GlobalTheory.T.sectionsGenerateIdealAlong_comap_of_twisted X _ J L m σ (d ≫ g) hσ)
      (by rw [Category.assoc, hψ, Category.assoc, hφ, reassoc_of% hw]) (hψσ.comp d) (hw ▸ hφσ.comp w)
    have key : ∀ h : W ⟶ _, h ≫ b = g → d ≫ h = w ≫ j := fun h hh => by
      have H := graphClosure.isPullback_incl s (PSpace.str R m) U.ι φ hφ.symm
      have e : w ≫ U.ι = (d ≫ h) ≫ b := by rw [hw, Category.assoc, hh]
      have h1 := H.lift_fst w (d ≫ h) e
      rw [Category.comp_id] at h1
      rw [← H.lift_snd w (d ≫ h) e, h1]
    have hl := graphClosure.lift_fst s (PSpace.str R m) U.ι φ hφ.symm g ψ hψ.symm d w hw.symm hw'
    exact ⟨_, hl, fun h hh => hom_ext_of_isSchemeTheoreticallyDominant d b ((key h hh).trans (key _ hl).symm)
      (hh.trans hl.symm)⟩
  · rw [hι]; infer_instance

theorem exists_iso_of_blowup {X X' G : Scheme.{0}} (J : X.IdealSheafData) (b : X' ⟶ X) (b₀ : G ⟶ X)
    (hb : FinalTheorems.Blowup b J) (hb₀ : FinalTheorems.Blowup b₀ J) : ∃ e : X' ⟶ G, IsIso e ∧ e ≫ b₀ = b := by
  obtain ⟨e, he, -⟩ := hb₀.2 X' b hb.1
  obtain ⟨e', he', -⟩ := hb.2 G b₀ hb₀.1
  have h1 : e ≫ e' = 𝟙 X' := by
    obtain ⟨_, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (e ≫ e') (by show (e ≫ e') ≫ b = b; rw [Category.assoc, he', he]), hu (𝟙 X') (Category.id_comp _)]
  have h2 : e' ≫ e = 𝟙 G := by
    obtain ⟨_, -, hu⟩ := hb₀.2 G b₀ hb₀.1
    rw [hu (e' ≫ e) (by show (e' ≫ e) ≫ b₀ = b₀; rw [Category.assoc, he, he']), hu (𝟙 G) (Category.id_comp _)]
  exact ⟨e, ⟨e', h1, h2⟩, he⟩

theorem exists_closedImmersion_of_generates : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (J : X.IdealSheafData)
    (b : X' ⟶ X) (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), IsProjOver s → FinalTheorems.Blowup b J →
    GlobalTheory.ProjBlowup.Generates J σ → ∃ (c : X' ⟶ PSpace R m) (hc : b ≫ s = c ≫ PSpace.str R m),
      GlobalTheory.ProjBlowup.Proportional σ b c ∧ IsClosedImmersion (pullback.lift b c hc) := by
  intro R _ _ X X' s J b L₀ m σ hs hb hσ
  obtain ⟨G, b₀, c₀, hc₀, hb₀, hp₀, hi₀⟩ := exists_blowup_graph s hs J L₀ m σ hσ
  obtain ⟨e, he, heb⟩ := exists_iso_of_blowup J b b₀ hb hb₀
  have hc : b ≫ s = (e ≫ c₀) ≫ PSpace.str R m := by rw [← heb, Category.assoc, Category.assoc, hc₀]
  have hp : Proportional σ b (e ≫ c₀) := heb ▸ hp₀.comp e
  have hl : pullback.lift b (e ≫ c₀) hc = e ≫ pullback.lift b₀ c₀ hc₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, heb]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  refine ⟨e ≫ c₀, hc, hp, ?_⟩
  rw [hl]
  infer_instance

end GlobalTheory.ProjBlowup
