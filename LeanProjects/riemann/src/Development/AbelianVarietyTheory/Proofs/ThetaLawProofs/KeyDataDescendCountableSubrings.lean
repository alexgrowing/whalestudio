import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianProjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProjByBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MorphismDescendsToSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCountableLocalPidSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.VeryAmpleByDescendsCountableSubringStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GrpObjDescendsFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyCountableDescent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa

theorem exists_keyPB_on {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (Q : Out.PolAV (Sp R'))
    (φ : Q.A.left ⟶ x.P.A.left) (h : IsGrpPullback Q.A x.P.A (spMap f) φ) (hL : LBIso Q.L (x.P.L.pull φ))
    (hgg : Q.g = x.P.g) (hg : 1 ≤ Q.g) :
    ∃ rig hr th hth v hv, KeyPB ⟨Q, hg, rig, hr, th, hth, v, hv⟩ x f := by
  obtain ⟨w, hw⟩ := hL
  have hw' := (isGen_iff _).1 hw
  have he : eSec Q.A ≫ φ = spMap f ≫ eSec x.P.A := PolBaseChange.eSec_comm h
  obtain ⟨rig, hr, hm⟩ := H1.exists_gen_move x.P.isLB Q.isLB w hw' (K := PUnit) (fun _ => eSec x.P.A) (fun _ => eSec Q.A)
    (fun _ => 1) (spMap f) (fun _ => he) x.rig x.rig_gen
  obtain ⟨th, e'⟩ := sec_pull_down hw' x.P.isLB Q.isLB x.th
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  have c₂ : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange R R' f x.P.A Q.A φ h x.P.isAb.smooth x.P.g x.v x.basis
  have hb : ∀ {n : ℕ} (e : n = x.P.g), IsLieBasis fun i : Fin n => u (i.cast e) := fun e => by
    subst e
    exact hu
  refine ⟨rig, hr, th, fun s => ?_, _, hb hgg, φ, he, w, hgg, Chart.dualMapR f, h, hw,
    (maps_iff w _ (fun _ => eSec x.P.A) _ rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L) (fun _ => rfl)).2 hm,
    appLE_eq_of_stalk _ x.th th (e' _ (𝟙 _)), fun a => ?_, ?_, fun i => huv _⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    obtain ⟨l, hl⟩ := exists_chart Q.isLB y
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨l, hl, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (x.th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := e' _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_keyPB_rescale {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (x : KeyIn R) (Q : Out.PolAV (Sp R'))
    (hg rig hr th hth v hv th' hth' v' hv') (H : KeyPB ⟨Q, hg, rig, hr, th, hth, v, hv⟩ x f) (a : R) (ha : IsUnit a)
    (M : Matrix (Fin Q.g) (Fin Q.g) R) (hM : IsUnit M.det)
    (hth'' : ∀ i, LB.Sec.f th' i = constFn Q.A.hom _ (f a) * LB.Sec.f th i)
    (hv'' : ∀ i, IsLieComb (fun k => f (M i k)) v (v' i)) :
    ∃ y : KeyIn R, KeyPB ⟨Q, hg, rig, hr, th', hth', v', hv'⟩ y f := by
  obtain ⟨φ, he, w, hgg, F, h, hw, hrr, hs, hF, hFe, hvv⟩ := H
  dsimp only at φ he w hgg h hw hrr hs hvv
  have hF' : F = Chart.dualMapR f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by rw [hF]; ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hFe]; ext <;> simp [Chart.dualMapR])
  subst hF'
  have c₁ : IsCommMonObj x.P.A := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hb⟩ := LieComb.lieComb_algebra R x.P.A x.P.g x.v x.basis.1
  have hc : ∀ {n : ℕ} (e : n = x.P.g) (t t' : Fin n → (epsR R' ⟶ Q.A)) (N : Matrix (Fin n) (Fin n) R), IsUnit N.det →
      (∀ i, (t i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (x.v (i.cast e)).left) →
      (∀ i, IsLieComb (fun k => f (N i k)) t (t' i)) →
      ∃ u : Fin x.P.g → (epsR R ⟶ x.P.A), IsLieBasis u ∧
        ∀ i, (t' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (u (i.cast e)).left := fun e t t' N hN ht ht' => by
    subst e
    choose u hu using fun i => (hex (N i)).exists
    exact ⟨u, (hb N u x.basis hu).2 hN,
      fun i => (lieComb_baseChange R R' f x.P.A Q.A φ h _ x.v (u i) (N i) t (t' i) ht (hu i)).2 (ht' i)⟩
  obtain ⟨u, hu, huv⟩ := hc hgg v v' M hM hvv hv''
  have e := (KeyCancel.appLE_eq_iff_stalk w x.th th).1 hs
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom a x.th, fun s => ?_, u, hu⟩,
    φ, he, w, hgg, _, h, hw, hrr, appLE_eq_of_stalk _ _ th' fun y j k hj hk => ?_, hF, hFe, huv⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ ha _ hz'⟩
  · have a₁ := e _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at a₁ ⊢
    have a₃ := gs_of_id φ y hj ((sec_eq_iff x.P.A.hom (KeyNormalExists.constMul x.P.A.hom a x.th) x.th a).1
      (fun _ => rfl) j _ hj)
    rw [a₃, a₁, h.1.w, cst_comp, (sec_eq_iff _ _ _ _).1 hth'' k y hk, mul_left_comm]

theorem exists_isPullback_prod {S S₀ : Scheme.{0}} {g : S ⟶ S₀} {A : Over S} {A₀ : Over S₀} {π : A.left ⟶ A₀.left}
    (h : IsPullback π A.hom A₀.hom g) : ∃ π₂ : (A ⊗ A).left ⟶ (A₀ ⊗ A₀).left,
      IsPullback π₂ (A ⊗ A).hom (A₀ ⊗ A₀).hom g ∧ π₂ ≫ (fst A₀ A₀).left = (fst A A).left ≫ π ∧
        π₂ ≫ (snd A₀ A₀).left = (snd A A).left ≫ π := by
  have h₀ : IsPullback (snd A₀ A₀).left (fst A₀ A₀).left A₀.hom A₀.hom := (IsPullback.of_hasPullback A₀.hom A₀.hom).flip
  have h₁ : IsPullback (snd A A).left (fst A A).left A.hom A.hom := (IsPullback.of_hasPullback A.hom A.hom).flip
  have h₂ := h₁.paste_horiz h
  rw [← h.w] at h₂
  have w : ((snd A A).left ≫ π) ≫ A₀.hom = ((fst A A).left ≫ π) ≫ A₀.hom := by
    rw [h₂.w, Category.assoc]
  have e₁ := h₀.lift_fst _ _ w
  have e₂ := h₀.lift_snd _ _ w
  refine ⟨h₀.lift _ _ w, ?_, e₂, e₁⟩
  rw [← e₁] at h₂
  have h₃ := (IsPullback.of_right h₂ e₂ h₀).paste_vert h
  rwa [Over.w, Over.w] at h₃

theorem exists_polAV_descent (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
    (P : Out.PolAV (Sp R)) : ∃ (R₁ : Subring R) (_ : IsLocalRing R₁) (_ : IsPrincipalIdealRing R₁) (P₁ : Out.PolAV (Sp R₁))
      (j : P.A.left ⟶ P₁.A.left), Countable R₁ ∧ IsGrpPullback P.A P₁.A (spMap R₁.subtype) j ∧
        LBIso P.L (P₁.L.pull j) ∧ P.g = P₁.g := by
  have := P.isAb.smooth
  obtain ⟨Hb, hH, m, s, hs⟩ := AbProj.isProjBy_of_isPullback P (IsPullback.id_horiz P.A.hom)
  obtain ⟨R₀, _, _, X₀, f₀, π, H₀, s₀, hc₀, -, -, -, hπ, hfl, hH₀, hs₀, -⟩ :=
    GlobalTheory.T.veryAmpleBy_descends_to_countable_subring R P.A.left P.A.hom Hb m s ∅ hH hs Set.countable_empty
  have hp₀ : AbLaw.IsProjBy f₀ := ⟨H₀, hH₀, m, s₀, hs₀⟩
  have hpr : IsProper f₀ := AbLaw.isProper_of_isProjBy R₀ X₀ f₀ hp₀
  have hfp : LocallyOfFinitePresentation f₀ := inferInstance
  let A₀ : Over (Sp R₀) := Over.mk f₀
  obtain ⟨π₂, hπ₂, a₁, a₂⟩ := exists_isPullback_prod (A := P.A) (A₀ := A₀) hπ
  have hpr₂ : IsProper (A₀ ⊗ A₀).hom := inferInstanceAs (IsProper (pullback.fst f₀ f₀ ≫ f₀))
  obtain ⟨Se, hSe⟩ := morphism_descends_to_subring R R₀ (Sp R) (Sp R₀) X₀ (𝟙 _) (𝟙 _) f₀ (spMap R₀.subtype)
    (η[P.A].left ≫ π) (IsPullback.id_vert _) (by
      have a : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
      rw [Category.assoc, hπ.w, ← Category.assoc, a]; simp)
  obtain ⟨Si, hSi⟩ := morphism_descends_to_subring R R₀ P.A.left X₀ X₀ P.A.hom f₀ f₀ π
    ((GrpObj.inv : P.A ⟶ P.A).left ≫ π) hπ (by rw [Category.assoc, hπ.w, ← Category.assoc, Over.w])
  obtain ⟨Sm, hSm⟩ := morphism_descends_to_subring R R₀ (P.A ⊗ P.A).left (A₀ ⊗ A₀).left X₀ (P.A ⊗ P.A).hom
    (A₀ ⊗ A₀).hom f₀ π₂ (μ[P.A].left ≫ π) hπ₂ (by rw [Category.assoc, hπ.w, ← Category.assoc, Over.w, hπ₂.w])
  obtain ⟨Sl, hSl⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R R₀ P.A.left X₀ P.A.hom f₀ π P.L hπ P.isLB
  obtain ⟨R₁, _, _, hc₁, hsub, -, hff⟩ := GlobalTheory.exists_countable_local_pid_subring R ((R₀ : Set R) ∪ ((Se : Set R) ∪ (Si ∪ (Sm ∪ Sl))))
    ((Set.countable_coe_iff.1 hc₀).union (Se.countable_toSet.union (Si.countable_toSet.union
      (Sm.countable_toSet.union Sl.countable_toSet))))
  simp only [Set.union_subset_iff] at hsub
  obtain ⟨h₀₁, be, bi, bm, bl⟩ := hsub
  have h01 : R₀ ≤ R₁ := h₀₁
  have hsp : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h01) := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  obtain ⟨A₁, π₁, h₁⟩ : ∃ (A₁ : Over (Sp R₁)) (π₁ : A₁.left ⟶ X₀), IsPullback π₁ A₁.hom f₀ (spMap (Subring.inclusion h01)) :=
    ⟨Over.mk (pullback.snd _ _), pullback.fst _ _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨j, j₁, j₂⟩ : ∃ j : P.A.left ⟶ A₁.left, j ≫ π₁ = π ∧ j ≫ A₁.hom = P.A.hom ≫ spMap R₁.subtype :=
    ⟨h₁.lift π (P.A.hom ≫ spMap R₁.subtype) (by rw [hπ.w, Category.assoc, hsp]), h₁.lift_fst _ _ _, h₁.lift_snd _ _ _⟩
  have hj : IsPullback j P.A.hom A₁.hom (spMap R₁.subtype) := IsPullback.of_right (by rw [j₁, ← hsp]; exact hπ) j₂ h₁
  obtain ⟨ρ₂, hρ₂, b₁, b₂⟩ := exists_isPullback_prod (A := A₁) (A₀ := A₀) h₁
  obtain ⟨j', hj', c₁, c₂⟩ := exists_isPullback_prod hj
  have lft : ∀ (T : Over (Sp R)) (T₁ : Over (Sp R₁)) (k : T.left ⟶ T₁.left) (φ : T ⟶ P.A) (ψ : T₁.left ⟶ X₀),
      k ≫ T₁.hom = T.hom ≫ spMap R₁.subtype → k ≫ ψ = φ.left ≫ π →
      ψ ≫ f₀ = T₁.hom ≫ spMap (Subring.inclusion h01) → ∃ φ₁ : T₁ ⟶ A₁, φ.left ≫ j = k ≫ φ₁.left := by
    intro T T₁ k φ ψ hk e₁ e₂
    refine ⟨Over.homMk (h₁.lift ψ T₁.hom e₂) (h₁.lift_snd _ _ _), ?_⟩
    change _ = k ≫ h₁.lift ψ T₁.hom e₂
    apply h₁.hom_ext
    · rw [Category.assoc, j₁, Category.assoc, h₁.lift_fst, e₁]
    · rw [Category.assoc, j₂, Category.assoc, h₁.lift_snd, hk, ← Category.assoc, Over.w]
  obtain ⟨ψe, e₁, e₂⟩ := hSe R₁ h01 be (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h01)) (spMap R₁.subtype)
    (IsPullback.id_vert _) hsp.symm (by simp)
  obtain ⟨e, he⟩ := lft (𝟙_ _) (𝟙_ _) (spMap R₁.subtype) η[P.A] ψe (by simp) e₁ (by simpa using e₂)
  obtain ⟨ψi, i₁, i₂⟩ := hSi R₁ h01 bi A₁.left A₁.hom π₁ j h₁ j₁ j₂
  obtain ⟨i, hi⟩ := lft P.A A₁ j GrpObj.inv ψi j₂ i₁ (i₂.trans h₁.w)
  obtain ⟨ψm, m₁, m₂⟩ := hSm R₁ h01 bm (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom ρ₂ j' hρ₂ (by
    apply pullback.hom_ext
    · change (j' ≫ ρ₂) ≫ (fst A₀ A₀).left = π₂ ≫ (fst A₀ A₀).left
      rw [Category.assoc, b₁, ← Category.assoc, c₁, Category.assoc, j₁, a₁]
    · change (j' ≫ ρ₂) ≫ (snd A₀ A₀).left = π₂ ≫ (snd A₀ A₀).left
      rw [Category.assoc, b₂, ← Category.assoc, c₂, Category.assoc, j₁, a₂]) hj'.w
  obtain ⟨mu, hmu⟩ := lft (P.A ⊗ P.A) (A₁ ⊗ A₁) j' μ[P.A] ψm hj'.w m₁ (m₂.trans hρ₂.w)
  obtain ⟨L₁, hL₁, hiso⟩ := hSl R₁ h01 bl A₁.left A₁.hom π₁ j h₁ j₁ j₂
  have : Flat A₁.hom := MorphismProperty.of_isPullback (P := @Flat) h₁ hfl
  have : IsProper A₁.hom := MorphismProperty.of_isPullback (P := @IsProper) h₁ hpr
  obtain ⟨_, hG⟩ := GlobalTheory.GrpDescent.grpObj_descends_faithfullyFlat R₁ R P.A A₁ j e mu i j' hj c₁ c₂ he hmu hi
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆⟩ := GlobalTheory.PolFlatDescent.polarisation_of_faithfullyFlat hL R₁ R P A₁ L₁ j
    (AbLaw.isProjBy_baseChange R₀ R₁ _ X₀ A₁.left f₀ π₁ A₁.hom h₁ hp₀) hL₁ hG hiso
  exact ⟨R₁, inferInstance, inferInstance, { A := A₁, isAb := p₁, g := P.g, smoothDim := p₂, L := L₁, isLB := hL₁, rigid := p₃, sym := p₄, ample := p₅, ktriv := p₆ }, j, hc₁, hG, hiso, rfl⟩

theorem exists_keyIn_descent (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R]
    (x : KeyIn R) (s : Set R) (hs : s.Countable) : ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀)
      (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨R₁, _, _, P₁, j, hc₁, hG, hiso, hgg⟩ := exists_polAV_descent hL R P
  obtain ⟨x₁, rfl⟩ := (GlobalTheory.KeyOnPol.main hL R₁).1 P₁ (hgg ▸ hg)
  obtain ⟨rig₁, hr₁, th₁, hth₁, v₁, hv₁, H₁⟩ := exists_keyPB_on R₁.subtype x₁ P j hG hiso hgg hg
  obtain ⟨a, t, ht, hat, H₂⟩ := (GlobalTheory.KeyOnPol.main hL R).2 ⟨P, hg, rig₁, hr₁, th₁, hth₁, v₁, hv₁⟩ rig hr th hth v hv
  have := P.isAb.comm
  choose M hM using fun i => (hv₁.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of M).det := ((LieComb.lieComb_algebra R P.A P.g v₁ hv₁.1).2.2.2.2 M v hv₁ hM).1 hv
  obtain ⟨R₂, _, _, hc₂, hsub, hloc, -⟩ := GlobalTheory.exists_countable_local_pid_subring R
    ((R₁ : Set R) ∪ (s ∪ ({(a : R)} ∪ Set.range fun p : Fin P.g × Fin P.g => M p.1 p.2)))
    ((Set.countable_coe_iff.1 hc₁).union (hs.union ((Set.countable_singleton _).union (Set.countable_range _))))
  simp only [Set.union_subset_iff, Set.singleton_subset_iff, Set.range_subset_iff] at hsub
  obtain ⟨h₁₂, bs, ba, bM⟩ := hsub
  have h12 : R₁ ≤ R₂ := h₁₂
  obtain ⟨x₂, H₃⟩ := exists_keyPB_ring x₁ (Subring.inclusion h12)
  have e₁₂ : R₂.subtype.comp (Subring.inclusion h12) = R₁.subtype := RingHom.ext fun _ => rfl
  have H₄ := KeyCancel.keyPB_cancel _ _ _ x₁ x₂ _ (Subring.inclusion h12) R₂.subtype H₃ (by rw [e₁₂]; exact H₁)
  let N : Matrix (Fin P.g) (Fin P.g) R₂ := fun i k => ⟨M i k, bM (i, k)⟩
  have hN : IsUnit N.det := isUnit_of_map_unit R₂.subtype _ (by rw [RingHom.map_det]; exact hdet)
  obtain ⟨y, H₅⟩ := exists_keyPB_rescale R₂.subtype x₂ P hg rig₁ hr₁ th₁ hth₁ v₁ hv₁ t ht v hv H₄ ⟨a, ba⟩
    (isUnit_of_map_unit R₂.subtype _ a.isUnit) N hN hat hM
  have H₆ := keyPB_trans _ _ _ y _ _ _ _ H₅ H₂
  rw [RingHom.id_comp] at H₆
  exact ⟨R₂, inferInstance, inferInstance, y, hc₂, bs, hloc, H₆⟩

theorem keyIn_descends_countable : Out.Laws → (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsPrincipalIdealRing R] [CharZero R] (x : KeyIn R) (s : Set R), s.Countable → ∃ (R₀ : Subring R) (_ : IsLocalRing R₀) (_ : IsPrincipalIdealRing R₀) (x₀ : KeyIn R₀), Countable R₀ ∧ s ⊆ R₀ ∧ IsLocalHom R₀.subtype ∧ KeyPB x x₀ R₀.subtype) ∧ KeyDesc := by
  refine fun hL => ⟨fun R _ _ _ _ _ x s hs => exists_keyIn_descent hL R x s hs, fun K _ _ x => ?_⟩
  obtain ⟨R₀, _, _, x₀, hc, -, hloc, H⟩ := exists_keyIn_descent hL K x ∅ Set.countable_empty
  let K₀ : Subfield K :=
    { R₀ with
      inv_mem' := fun z hz => by
        by_cases h0 : z = 0
        · rw [h0, inv_zero]; exact R₀.zero_mem
        · obtain ⟨b, hb⟩ := (isUnit_of_map_unit R₀.subtype ⟨z, hz⟩ (IsUnit.mk0 z h0)).exists_right_inv
          have e : z * (b : K) = 1 := congrArg Subtype.val hb
          rw [← eq_inv_of_mul_eq_one_right e]; exact b.2 }
  exact ⟨K₀, x₀, hc, H⟩

end GlobalTheory.KeyCountableDescent
