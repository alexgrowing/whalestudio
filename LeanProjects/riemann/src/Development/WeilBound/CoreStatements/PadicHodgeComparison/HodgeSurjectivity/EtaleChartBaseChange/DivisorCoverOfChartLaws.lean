import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

theorem etale_of_subsingleton2 {A S : Type} [CommRing A] [CommRing S] [Subsingleton S] (f : A →+* S) : f.Etale := by
  letI := f.toAlgebra
  haveI : IsLocalization.Away (0 : A) S := (isLocalization_iff _ _).mpr
    ⟨fun _ => isUnit_of_subsingleton _, fun z => ⟨(0, 1), Subsingleton.elim _ _⟩,
      fun {x y} _ => ⟨⟨0, 1, pow_one 0⟩, by simp⟩⟩
  exact Algebra.Etale.of_isLocalizationAway (0 : A)

theorem coord_empty_open {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) :
    Nonempty (Coord q ⊥ 0) :=
  ⟨⟨isAffineOpen_bot X, Fin.elim0, etale_of_subsingleton2 _⟩⟩

theorem coord_transfer2 {O : Type} [CommRing O] {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {q' : X' ⟶ Spec (CommRingCat.of O)} {V : X.Opens} {V' : X'.Opens} {d : ℕ} (c : Coord q V d)
    (hV' : IsAffineOpen V') (φ : Γ(X, V) →+* Γ(X', V')) (hφ : Function.Bijective φ)
    (hs : φ.comp (strV q V) = strV q' V') : Nonempty (Coord q' V' d) := by
  refine ⟨⟨hV', fun j => φ (c.t j), ?_⟩⟩
  have e : (MvPolynomial.eval₂Hom (strV q' V') fun j => φ (c.t j)) =
      φ.comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [← hs]
    ext <;> simp
  rw [e]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (RingHom.Etale.of_bijective hφ)

theorem appLE_bij_of_image2 {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) (V : X.Opens)
    (hU : f ''ᵁ V = U) (e : V ≤ f ⁻¹ᵁ U) : Function.Bijective (f.appLE U V e).hom := by
  subst hU
  rw [← Scheme.Hom.appIso_hom']
  exact (f.appIso V).commRingCatIsoToRingEquiv.bijective

theorem isSeparated_of_over_field {K : Type} [Field K] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of K)) [IsSeparated p] :
    Y.IsSeparated :=
  ⟨by rw [← terminal.comp_from p]; infer_instance⟩

section

variable {K : Type} [Field K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

def DGood2 (B : Blow q i π D d) (U : Y.Opens) (σ : (U : Scheme.{0}) ⟶ D.Y) : Prop :=
  σ ≫ D.f = U.ι ∧ IsAffineOpen U ∧ ∀ (V : Y.Opens) (h : V ≤ U), IsAffineOpen V →
      (∃ n, Nonempty (Coord (π ≫ q) V n)) ∧ (∃ n, Nonempty (Coord (pullback.snd i π ≫ π ≫ q) (pullback.snd i π ⁻¹ᵁ V) n)) ∧
      RingHom.ker ((pullback.snd i π).app V).hom = Ideal.span {V.topIso.hom.hom (B.f (Y.homOfLE h ≫ σ))} ∧
      ∀ (a : ℕ) (ω : Om K (Sec (π ≫ q) V) a), (show Sec (π ≫ q) V from V.topIso.hom.hom (B.f (Y.homOfLE h ≫ σ))) • ω = 0 → ω = 0

theorem appLE_congr2 {X X' : Scheme.{0}} {f g : X ⟶ X'} (hfg : f = g) (U : X'.Opens) (V : X.Opens) (e e') :
    f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

theorem off_centre2 (B : Blow q i π D d) (A : Z.Opens) (hA : A ≤ B.U) (hAa : IsAffineOpen A) :
    IsAffineOpen (π ⁻¹ᵁ A) ∧ Function.Bijective (π.app A).hom := by
  haveI := B.iso
  have hh : (π ∣_ B.U) ≫ B.U.ι = (π ⁻¹ᵁ B.U).ι ≫ π := morphismRestrict_ι π B.U
  have hr : ((π ∣_ B.U) ≫ B.U.ι).opensRange = B.U := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  have hpre : ((π ∣_ B.U) ≫ B.U.ι) ⁻¹ᵁ A = (π ⁻¹ᵁ B.U).ι ⁻¹ᵁ (π ⁻¹ᵁ A) := congrArg (fun g => g ⁻¹ᵁ A) hh
  have h1 : ((π ∣_ B.U) ≫ B.U.ι) ''ᵁ ((π ⁻¹ᵁ B.U).ι ⁻¹ᵁ (π ⁻¹ᵁ A)) = A := by
    rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hr, inf_eq_right.mpr hA]
  have h2 : (π ⁻¹ᵁ B.U).ι ''ᵁ ((π ⁻¹ᵁ B.U).ι ⁻¹ᵁ (π ⁻¹ᵁ A)) = π ⁻¹ᵁ A := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (fun x hx => hA hx)]
  constructor
  · rw [← h2]
    refine (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (π ⁻¹ᵁ B.U).ι).mpr ?_
    refine (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion ((π ∣_ B.U) ≫ B.U.ι)).mp ?_
    rw [h1]
    exact hAa
  · have c1 := appLE_bij_of_image2 ((π ∣_ B.U) ≫ B.U.ι) A _ h1 hpre.ge
    have c2 := appLE_bij_of_image2 (π ⁻¹ᵁ B.U).ι (π ⁻¹ᵁ A) _ h2 le_rfl
    rw [appLE_congr2 hh A ((π ⁻¹ᵁ B.U).ι ⁻¹ᵁ (π ⁻¹ᵁ A)) _ le_rfl,
      ← Scheme.Hom.appLE_comp_appLE (π ⁻¹ᵁ B.U).ι π A (π ⁻¹ᵁ A) _ le_rfl le_rfl,
      CommRingCat.hom_comp, RingHom.coe_comp] at c1
    rw [Scheme.Hom.app_eq_appLE]
    exact (Function.Bijective.of_comp_iff' c2 _).mp c1

theorem divisor_good_off_centre (B : Blow q i π D d) (V' : Y.Opens) (σ' : (V' : Scheme.{0}) ⟶ D.Y) (hσ : σ' ≫ D.f = V'.ι)
    (hV' : V' ≤ π ⁻¹ᵁ B.U) (ha : IsAffineOpen V') (n : ℕ) (c : Coord (π ≫ q) V' n) : DGood2 B V' σ' := by
  refine ⟨hσ, ha, fun V h hV => ?_⟩
  have hVU : V ≤ π ⁻¹ᵁ B.U := h.trans hV'
  have hbot : pullback.snd i π ⁻¹ᵁ V = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h3 : π (pullback.snd i π x) ∈ (B.U : Set Z) := hVU hx
    rw [B.U_eq] at h3
    exact (h3 ⟨pullback.fst i π x, by simpa using congrArg (fun g : pullback i π ⟶ Z => g x) (pullback.condition (f := i) (g := π))⟩).elim
  have hu : IsUnit (B.f (Y.homOfLE h ≫ σ')) := B.unit _ (by
    intro x _
    have e : (Y.homOfLE h ≫ σ') ≫ D.f ≫ π = V.ι ≫ π := by
      rw [← Category.assoc, Category.assoc (Y.homOfLE h), hσ, Scheme.homOfLE_ι]
    rw [e]
    exact hVU x.2)
  have hu' : IsUnit (V.topIso.hom.hom (B.f (Y.homOfLE h ≫ σ'))) := hu.map _
  haveI : Subsingleton Γ(pullback i π, pullback.snd i π ⁻¹ᵁ V) := by rw [hbot]; infer_instance
  refine ⟨?_, ⟨0, by rw [hbot]; exact coord_empty_open _⟩, ?_, fun a ω hω => (hu'.smul_eq_zero).mp hω⟩
  · obtain ⟨c', -⟩ := coord_res c h hV
    exact ⟨n, ⟨c'⟩⟩
  · rw [Ideal.span_singleton_eq_top.mpr hu']
    exact eq_top_iff.mpr fun x _ => (RingHom.mem_ker).mpr (Subsingleton.elim _ _)

theorem good_open_off_centre [IsProper q] [Smooth q] (B : Blow q i π D d) (y : Y) (hy : π y ∈ B.U) :
    ∃ (V' : Y.Opens) (σ' : (V' : Scheme.{0}) ⟶ D.Y), y ∈ V' ∧ DGood2 B V' σ' := by
  obtain ⟨Cv⟩ := (cov_ex q).1 inferInstance
  have hz : π y ∈ (⨆ β, Cv.U β) := by rw [Cv.cover]; trivial
  obtain ⟨β, hβ⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  obtain ⟨_, ⟨A, hAa, rfl⟩, hzA, hAle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (show π y ∈ ((Cv.U β ⊓ B.U : Z.Opens) : Set Z) from ⟨hβ, hy⟩) (Cv.U β ⊓ B.U).2
  have hA1 : A ≤ Cv.U β := fun x hx => (hAle hx).1
  have hA2 : A ≤ B.U := fun x hx => (hAle hx).2
  obtain ⟨cA, -⟩ := coord_res (Cv.c β) hA1 hAa
  obtain ⟨hpa, hbij⟩ := off_centre2 B A hA2 hAa
  have hs : (π.app A).hom.comp (strV q A) = strV (π ≫ q) (π ⁻¹ᵁ A) := by
    rw [strV, strV, ← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  obtain ⟨cP⟩ := coord_transfer2 cA hpa (π.app A).hom hbij hs
  have hy0 : y ∈ sSup (𝒱D D) := by rw [B.loc]; trivial
  obtain ⟨V0, hV0, hyV0⟩ := TopologicalSpace.Opens.mem_sSup.mp hy0
  obtain ⟨σ0, hσ0⟩ := hV0
  obtain ⟨_, ⟨V', hV'a, rfl⟩, hyV', hV'le⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ ((π ⁻¹ᵁ A ⊓ V0 : Y.Opens) : Set Y) from ⟨hzA, hyV0⟩) (π ⁻¹ᵁ A ⊓ V0).2
  have hV'1 : V' ≤ π ⁻¹ᵁ A := fun x hx => (hV'le hx).1
  have hV'2 : V' ≤ V0 := fun x hx => (hV'le hx).2
  obtain ⟨cV, -⟩ := coord_res cP hV'1 hV'a
  refine ⟨V', Y.homOfLE hV'2 ≫ σ0, hyV', divisor_good_off_centre B V' _ ?_ (fun x hx => hA2 (hV'1 hx)) hV'a _ cV⟩
  rw [Category.assoc, hσ0, Scheme.homOfLE_ι]

theorem f_chart2 (B : Blow q i π D d) (α : B.ι) (k : Fin d) (V : Y.Opens) (h : V ≤ (B.c α).C k) :
    V.topIso.hom.hom (B.f (Y.homOfLE h ≫ B.σ α k)) =
      (π.appLE (B.V α) V (h.trans ((B.c α).C_le k))).hom ((B.c α).t k) := by
  have key : π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k) ≫ ((B.c α).C k).topIso.inv ≫ (Y.homOfLE h).appTop ≫
      V.topIso.hom = π.appLE (B.V α) V (h.trans ((B.c α).C_le k)) := by
    simp only [Scheme.Opens.topIso_inv, Scheme.Opens.topIso_hom, Scheme.homOfLE_appTop]
    rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.appLE_map]
  rw [B.f_nat, B.f_σ, ← key]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]

theorem good_chart2 (hCL : ChartLaws) (B : Blow q i π D d) (α : B.ι) (k : Fin d) :
    DGood2 B ((B.c α).C k) (B.σ α k) := by
  haveI := B.closed
  refine ⟨B.σ_f α k, (B.c α).C_aff k, fun V h hV => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := (hCL K W Z Y q i π d (B.V α) (B.c α)).2.2.2 k V h hV
  refine ⟨⟨_, h1⟩, ⟨_, h2⟩, ?_, ?_⟩
  · rw [f_chart2 B α k V h]; exact h3
  · intro a ω
    rw [f_chart2 B α k V h]
    exact h4 a ω

end

theorem divisor_cover_of_chart_laws (hCL : ChartLaws) : DivCover := by
  intro K _ W Z Y q _ _ i π _ D d B
  haveI := B.closed
  haveI hsep : Y.IsSeparated := isSeparated_of_over_field (π ≫ q)
  have hpt : ∀ y : Y, ∃ (V' : Y.Opens) (σ' : (V' : Scheme.{0}) ⟶ D.Y), y ∈ V' ∧ DGood2 B V' σ' := by
    intro y
    by_cases hy : π y ∈ B.U
    · exact good_open_off_centre B y hy
    · have hz : π y ∈ Set.range i := by
        have h0 : π y ∉ (B.U : Set Z) := hy
        rw [B.U_eq] at h0
        simpa using h0
      obtain ⟨w, hw⟩ := hz
      have hw' : w ∈ i ⁻¹ᵁ (⨆ α, B.V α) := B.cover trivial
      have h5 : π y ∈ ⨆ α, B.V α := by rw [← hw]; exact hw'
      obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp h5
      have h6 : y ∈ ⨆ k, (B.c α).C k := (B.c α).C_cover hα
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp h6
      exact ⟨_, _, hk, good_chart2 hCL B α k⟩
  choose V' σ' hyV hG using hpt
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (π ≫ q)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V' y : Set Y)) (fun y => (V' y).2)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hyV y⟩)
  refine ⟨t.card, fun α => V' (t.equivFin.symm α), fun α => σ' (t.equivFin.symm α), fun α => (hG _).1, ?_,
    fun α α' => ((hG _).2.1).inf (hG _).2.1, fun α V h hV => (hG _).2.2 V h hV⟩
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

end CrystallineSemistableComparison.Onto

end
