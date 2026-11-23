import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyFlagPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsToPSpaceOfIsSubbundle
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB

namespace GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.LineQuot

section Sub

variable {X : Scheme.{0}} {A B E : X.Modules} {a b r : ℕ}

private theorem rank_cokernel {u : A ⟶ E} (hu : IsSubbundle u) (hA : IsVB A a) (hE : IsVB E r) :
    IsVB (cokernel u) (r - a) := fun x => by
  have : Nonempty X := ⟨x⟩
  obtain ⟨_, s, hs⟩ := hu
  obtain rfl : r = a + s := hE.rank_unique (VBExt.isVB_and_cls_det_of_shortExact X (.mk u (cokernel.π _)
    (cokernel.condition _)) a s { exact := ShortComplex.exact_cokernel _ } hA hs).1
  rw [Nat.add_sub_cancel_left]
  exact hs x

private theorem sub_comp {u : A ⟶ B} {g : B ⟶ E} (hu : IsSubbundle u) (hg : IsSubbundle g) :
    IsSubbundle (u ≫ g) := by
  have := hu.mono
  have := hg.mono
  obtain ⟨s, hs⟩ := hu.isVB_cokernel
  obtain ⟨t, ht⟩ := hg.isVB_cokernel
  exact ⟨inferInstance, _, (VBExt.isVB_and_cls_det_of_shortExact X _ _ _
    (Vert.shortExact_cokernel_comp u g) hs ht).1⟩

private theorem sub_of_comp {u : A ⟶ B} {g : B ⟶ E} {f : A ⟶ E} (w : u ≫ g = f) (hf : IsSubbundle f)
    (hg : IsSubbundle g) (hA : IsVB A a) (hB : IsVB B b) (hE : IsVB E r) (h₁ : a ≤ b) (h₂ : b ≤ r) :
    IsSubbundle u := by
  subst w
  have := hg.mono
  have := hf.mono
  refine ⟨mono_of_mono u g, b - a, VB.isVB_X₁_of_shortExact X _ _ _ (Vert.shortExact_cokernel_comp u g) ?_
    (rank_cokernel hg hB hE)⟩
  have h := rank_cokernel hf hA hE
  rwa [show r - a = b - a + (r - b) by omega] at h

private theorem sub_comp_iso {u : A ⟶ B} (hu : IsSubbundle u) (e : B ⟶ E) [IsIso e] : IsSubbundle (u ≫ e) :=
  have ⟨_, s, hs⟩ := hu
  ⟨inferInstance, s, hs.of_iso (cokernelCompIsIso u e).symm⟩

private theorem exists_le (fl : Vert.Flag E r) (i : Fin (r + 1)) :
    ∀ l : Fin (r + 1), i ≤ l → ∃ t : fl.F i ⟶ fl.F l, t ≫ fl.ι l = fl.ι i := by
  intro l
  induction l using Fin.induction with
  | zero =>
    intro h
    obtain rfl : i = 0 := le_antisymm h (Fin.zero_le _)
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ l ih =>
    intro h
    rcases h.eq_or_lt with rfl | h
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨t, ht⟩ := ih (Fin.le_castSucc_iff.2 h)
      exact ⟨t ≫ fl.step l, by rw [Category.assoc, fl.step_ι, ht]⟩

end Sub

variable {B G T Y : Scheme.{0}} {γ : G ⟶ B} {E : B.Modules} {n m₁ m₂ : ℕ} {S P : G.Modules} {s : S ⟶ P}
  {j : P ⟶ (Scheme.Modules.pullback γ).obj E}

private theorem pair_ext (hS : IsVB S m₁) (hP : IsVB P m₂) (hs : IsSubbundle s) (hj : IsSubbundle j)
    (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (g₁ g₂ : T ⟶ G) {g : T ⟶ B} (w₁ : g₁ ≫ γ = g) (w₂ : g₂ ≫ γ = g)
    (h₁ : ∃ e : (Scheme.Modules.pullback g₁).obj S ≅ (Scheme.Modules.pullback g₂).obj S,
      e.hom ≫ (Scheme.Modules.pullback g₂).map (s ≫ j) ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map (s ≫ j) ≫ (cmp g₁ γ w₁).hom.app E)
    (h₂ : ∃ e : (Scheme.Modules.pullback g₁).obj P ≅ (Scheme.Modules.pullback g₂).obj P,
      e.hom ≫ (Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E =
        (Scheme.Modules.pullback g₁).map j ≫ (cmp g₁ γ w₁).hom.app E) : g₁ = g₂ := by
  obtain ⟨eS, heS⟩ := h₁
  obtain ⟨eP, heP⟩ := h₂
  have hj' := sub_comp_iso (SubPull.isSubbundle_pullback _ _ g₂ _ _ j m₂ hP hj) ((cmp g₂ γ w₂).hom.app E)
  have := hj'.mono
  refine (hG T g _ _ ((Scheme.Modules.pullback g₂).map s) _ (SubPull.isSubbundle_pullback _ _ g₂ _ _ s m₁ hS hs) hj'
    (hS.pullback g₂) (hP.pullback g₂)).unique ⟨w₁, eS, eP, heP, ?_⟩
    ⟨w₂, Iso.refl _, Iso.refl _, Category.id_comp _, by simp⟩
  rw [← cancel_mono ((Scheme.Modules.pullback g₂).map j ≫ (cmp g₂ γ w₂).hom.app E), Category.assoc, Category.assoc,
    heP]
  simpa only [Functor.map_comp, Category.assoc] using heS

private theorem exists_iso_comp {π : Y ⟶ B} (ρ : Y ⟶ G) (wρ : ρ ≫ γ = π) (σ : T ⟶ Y) (υ : T ⟶ G) {g : T ⟶ B}
    (wσ : σ ≫ π = g) (wυ : υ ≫ γ = g) (w : (σ ≫ ρ) ≫ γ = g) {A : G.Modules}
    (u : A ⟶ (Scheme.Modules.pullback γ).obj E) {F : Y.Modules} (ι : F ⟶ (Scheme.Modules.pullback π).obj E)
    {F' : T.Modules} (ι' : F' ⟶ (Scheme.Modules.pullback υ).obj ((Scheme.Modules.pullback γ).obj E))
    (a : (Scheme.Modules.pullback ρ).obj A ≅ F)
    (ha : a.hom ≫ ι = (Scheme.Modules.pullback ρ).map u ≫ (cmp ρ γ wρ).hom.app E)
    (b : (Scheme.Modules.pullback σ).obj F ≅ F')
    (hb : b.hom ≫ ι' ≫ (cmp υ γ wυ).hom.app E = (Scheme.Modules.pullback σ).map ι ≫ (cmp σ π wσ).hom.app E)
    (c : (Scheme.Modules.pullback υ).obj A ≅ F') (hc : c.hom ≫ ι' = (Scheme.Modules.pullback υ).map u) :
    ∃ e : (Scheme.Modules.pullback (σ ≫ ρ)).obj A ≅ (Scheme.Modules.pullback υ).obj A,
      e.hom ≫ (Scheme.Modules.pullback υ).map u ≫ (cmp υ γ wυ).hom.app E =
        (Scheme.Modules.pullback (σ ≫ ρ)).map u ≫ (cmp (σ ≫ ρ) γ w).hom.app E := by
  refine ⟨((cmp σ ρ rfl).app A).symm ≪≫ (Scheme.Modules.pullback σ).mapIso a ≪≫ b ≪≫ c.symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← hc, Category.assoc, Iso.inv_hom_id_assoc, hb, ← Functor.map_comp_assoc, ha, Functor.map_comp_assoc,
    cmp_assoc σ ρ γ wρ wσ rfl w, Iso.inv_comp_eq, Iso.app_hom, cmp_naturality_assoc]

private theorem exists_sections (hE : IsVB E n) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (hS : IsVB S m₁) (hP : IsVB P m₂)
    (hs : IsSubbundle s) (hj : IsSubbundle j) (hG : OmitFlag.IsPairBundle γ E m₁ m₂ s j) (π : Y ⟶ B)
    (fl : ∀ _ : Unit, Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hY : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) fl) :
    ∃ ρ : Y ⟶ G, ρ ≫ γ = π ∧ ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι := by
  let i₁ : Fin (n + 1) := ⟨m₁, by omega⟩
  let i₂ : Fin (n + 1) := ⟨m₂, by omega⟩
  obtain ⟨t, ht⟩ := exists_le (fl ()) i₁ i₂ h₁₂
  obtain ⟨ρ, ⟨wρ, aS, aP, haP, haS⟩, -⟩ := hG Y π _ _ t ((fl ()).ι i₂)
    (sub_of_comp ht ((fl ()).isSubbundle _) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
      (hE.pullback π) h₁₂ h₂) ((fl ()).isSubbundle _) ((fl ()).isVB i₁) ((fl ()).isVB i₂)
  rw [← cmp_hom_app] at haP
  have haS' : aS.hom ≫ (fl ()).ι i₁ = (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (cmp ρ γ wρ).hom.app E := by
    rw [← ht, reassoc_of% haS, haP, Functor.map_comp_assoc]
  refine ⟨ρ, wρ, fun x => ?_⟩
  obtain ⟨U, hx, flU, cS, cP, hcS, hcP⟩ :=
    FlagTwoSteps.exists_flag_two_steps G _ S P n m₁ m₂ h₁₂ h₂ s j (hE.pullback γ) hS hP hs hj x
  obtain ⟨σ, ⟨wσ, hσ⟩, -⟩ := hY U.toScheme (U.ι ≫ γ) fun _ => flU.ofIso ((cmp U.ι γ rfl).app E)
  obtain ⟨b₁, hb₁⟩ := hσ () i₁
  obtain ⟨b₂, hb₂⟩ := hσ () i₂
  have w : (σ ≫ ρ) ≫ γ = U.ι ≫ γ := by rw [Category.assoc, wρ, wσ]
  exact ⟨U, σ, hx, pair_ext hS hP hs hj hG _ _ w rfl
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₁) aS haS' b₁ hb₁ cS hcS)
    (exists_iso_comp ρ wρ σ U.ι wσ rfl w _ _ (flU.ι i₂) aP haP b₂ hb₂ cP hcP)⟩

private theorem closed_of_sections {Z : Scheme.{0}} (ρ : Y ⟶ G) (f : G ⟶ Z) [IsProper (ρ ≫ f)]
    (h : ∀ x : G, ∃ (U : G.Opens) (σ : U.toScheme ⟶ Y), x ∈ U ∧ σ ≫ ρ = U.ι) :
    UniversallyClosed f ∧ LocallyOfFiniteType f := by
  choose U σ hx hσ using h
  have : Surjective ρ := ⟨fun x => ⟨σ x ⟨x, hx x⟩,
    (Scheme.Hom.comp_apply (σ x) ρ _).symm.trans (by rw [hσ]; rfl)⟩⟩
  refine ⟨UniversallyClosed.of_comp_surjective ρ f, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType) U
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hx x⟩)).2 fun x => ?_
  have : LocallyOfFiniteType (σ x ≫ ρ) := by rw [hσ]; infer_instance
  have := locallyOfFiniteType_of_comp (σ x) ρ
  rw [← hσ, Category.assoc]
  infer_instance

end GlobalTheory.PairProj

open CategoryTheory.Limits GlobalTheory.PairProj in
theorem _root_.GlobalTheory.T.pair_bundle_flag_compat : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k), IsProjOver q →
    ∀ (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
    ∀ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
      GlobalTheory.VB.IsVB S m₁ → GlobalTheory.VB.IsVB P m₂ → GlobalTheory.VB.IsSubbundle s → GlobalTheory.VB.IsSubbundle j →
      GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j → IsProjOver (γ ≫ q) := by
  intro k _ _ B q hq E n m₁ m₂ hE h₁₂ h₂ G γ S P s j hS hP hs hj hG
  obtain ⟨Y, π, fl, hY, hYp⟩ := GlobalTheory.T.exists_flag_bundle_proj_vector_bundle k B q E n hq hE
  obtain ⟨ρ, wρ, hρ⟩ := exists_sections hE h₁₂ h₂ hS hP hs hj hG π fl hY
  have : IsProper (ρ ≫ γ ≫ q) := by
    rw [← Category.assoc, wρ]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver hYp).1
  obtain ⟨_, _⟩ := closed_of_sections ρ (γ ≫ q) hρ
  obtain ⟨N₁, φ₁, hφ₁, H₁⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₁ hE (h₁₂.trans h₂) G γ S (s ≫ j)
    hS (sub_comp hs hj)
  obtain ⟨N₂, φ₂, hφ₂, H₂⟩ := PluckerMap.exists_toPSpace_of_isSubbundle k B q hq E n m₂ hE h₂ G γ P j hP hj
  have hPN (N : ℕ) : IsProjOver (PSpace.str k N) := ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hZ := ProjSpace.isProjOver_pullback (ProjSpace.isProjOver_pullback hq (hPN N₁)) (hPN N₂)
  let ψ₁ : G ⟶ pullback q (PSpace.str k N₁) := pullback.lift γ φ₁ hφ₁.symm
  let ψ : G ⟶ pullback (pullback.fst q (PSpace.str k N₁) ≫ q) (PSpace.str k N₂) :=
    pullback.lift ψ₁ φ₂ (by rw [hφ₂, pullback.lift_fst_assoc])
  have hψ : ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q = γ ≫ q := by
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]
  have : Mono ψ := ⟨fun {T} g₁ g₂ h => by
    have e₀ : g₁ ≫ ψ₁ = g₂ ≫ ψ₁ := by
      simpa only [ψ, Category.assoc, pullback.lift_fst] using h =≫ pullback.fst _ _
    have e₂ : g₁ ≫ φ₂ = g₂ ≫ φ₂ := by
      simpa only [ψ, Category.assoc, pullback.lift_snd] using h =≫ pullback.snd _ _
    have e₁ : g₁ ≫ φ₁ = g₂ ≫ φ₁ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_snd] using e₀ =≫ pullback.snd _ _
    have w : g₁ ≫ γ = g₂ ≫ γ := by
      simpa only [ψ₁, Category.assoc, pullback.lift_fst] using e₀ =≫ pullback.fst _ _
    exact pair_ext hS hP hs hj hG g₁ g₂ w rfl (H₁ T g₁ g₂ _ w rfl e₁) (H₂ T g₁ g₂ _ w rfl e₂)⟩
  have := (isProper_and_exists_isAmpleLB_of_isProjOver hZ).1
  have : IsSeparated (γ ≫ q) := by rw [← hψ]; infer_instance
  have : IsProper (ψ ≫ pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q) := by rw [hψ]; exact {}
  have : IsClosedImmersion ψ := (IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨IsProper.of_comp ψ
    (pullback.fst _ _ ≫ pullback.fst q (PSpace.str k N₁) ≫ q), inferInstance⟩
  rw [← hψ]
  exact ProjSpace.isProjOver_comp_of_isClosedImmersion ψ hZ
