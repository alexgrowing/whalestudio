import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapLocallyQuasiFiniteStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowerMapFlatSemiabelianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThickeningGroupHomExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitTorusExtensionTorsionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SurjectiveLeftOfFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupOpenImmersionLiftStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformizationThickeningCompatStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfTorsionKernelStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsOfClosedSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEqStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Stight.D1

section Unit
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal]

theorem kernel_map [PreservesLimitsOfShape WalkingCospan F] {A B : C} [GrpObj B] {N : ℕ} {j : A ⟶ B}
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback (F.map j) (toUnit (F.obj A)) ((𝟙 (F.obj B)) ^ N) η[F.obj B] := by
  have h := hp.map F
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso F).symm (Iso.refl _)
    (by simp) (toUnit_unique _ _) ?_ ?_
  · simp [Tors.map_pow_id]
  · simp [Functor.obj.η_def]

theorem isPullback_map_unit {A E B : C} {a : A ⟶ E} {b : E ⟶ B} {e : 𝟙_ C ⟶ B}
    (h : IsPullback (F.map a) (toUnit (F.obj A)) (F.map b) (Functor.LaxMonoidal.ε F ≫ F.map e)) :
    IsPullback (F.map a) (F.map (toUnit A)) (F.map b) (F.map e) := by
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _) (Functor.Monoidal.εIso F) (Iso.refl _)
    (by simp) (by rw [← cancel_mono (Functor.Monoidal.εIso F).inv]; exact toUnit_unique _ _) (by simp) (by simp)

end Unit

section Iso
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

theorem kernel_iso {A B B' : C} [GrpObj B] [GrpObj B'] {N : ℕ} {j : A ⟶ B} (β : B ≅ B') [IsMonHom β.hom]
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback (j ≫ β.hom) (toUnit A) ((𝟙 B') ^ N) η[B'] := by
  refine IsPullback.of_iso hp (Iso.refl _) β (Iso.refl _) β (by simp) (by simp) ?_ (by simp)
  rw [MonObj.pow_comp, MonObj.comp_pow]
  simp

theorem factor_of_kernel [BraidedCategory C] {P P' Q Q' : C} [GrpObj P'] [IsCommMonObj P'] [GrpObj Q'] [IsCommMonObj Q']
    {N : ℕ} {jP : P ⟶ P'} {jQ : Q ⟶ Q'}
    (hP : IsPullback jP (toUnit P) ((𝟙 P') ^ N) η[P']) (hQ : IsPullback jQ (toUnit Q) ((𝟙 Q') ^ N) η[Q'])
    (φ : P' ⟶ Q') [IsMonHom φ] : ∃ w : P ⟶ Q, w ≫ jQ = jP ≫ φ := by
  refine Tors.lift_of_torsion hQ _ ?_
  have h := Tors.torsion_of_comp hP (𝟙 _)
  rw [Category.id_comp] at h
  rw [← MonObj.pow_comp, h]
  simp

end Iso

theorem kernel_pull {S' S : Scheme.{0}} (x : S' ⟶ S) {A B : Over S} [GrpObj B] {N : ℕ} {j : A ⟶ B}
    (hp : IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B]) :
    IsPullback ((Over.pullback x).map j) (toUnit ((Over.pullback x).obj A))
      ((𝟙 ((Over.pullback x).obj B)) ^ N) η[(Over.pullback x).obj B] :=
  kernel_map (Over.pullback x) hp

theorem comp_left_of_map {S' S : Scheme.{0}} (x : S' ⟶ S) {P G B : Over S} (v : P ⟶ G) (c : P ⟶ B)
    (qq : (Over.pullback x).obj G ⟶ (Over.pullback x).obj B)
    (h : (Over.pullback x).map c = (Over.pullback x).map v ≫ qq) {Y : Scheme.{0}} (y : Y ⟶ P.left)
    (y' : Y ⟶ ((Over.pullback x).obj G).left) (hy : y' ≫ pullback.fst G.hom x = y ≫ v.left) :
    y ≫ c.left = y' ≫ qq.left ≫ pullback.fst B.hom x := by
  have hc : y ≫ P.hom = y' ≫ pullback.snd G.hom x ≫ x := by
    rw [← pullback.condition, ← Category.assoc, hy, Category.assoc, Over.w]
  let w : Y ⟶ ((Over.pullback x).obj P).left := pullback.lift y (y' ≫ pullback.snd G.hom x) (by simpa using hc)
  have hw1 : w ≫ pullback.fst P.hom x = y := pullback.lift_fst _ _ _
  have hw2 : w ≫ ((Over.pullback x).map v).left = y' := by
    refine pullback.hom_ext ?_ ?_
    · have h1 : ((Over.pullback x).map v).left ≫ pullback.fst G.hom x = pullback.fst P.hom x ≫ v.left :=
        pullback.lift_fst _ _ _
      rw [Category.assoc, h1, ← Category.assoc, hw1, hy]
    · have h2 : ((Over.pullback x).map v).left ≫ pullback.snd G.hom x = pullback.snd P.hom x :=
        pullback.lift_snd _ _ _
      rw [Category.assoc, h2]
      exact pullback.lift_snd _ _ _
  have h3 : ((Over.pullback x).map c).left ≫ pullback.fst B.hom x = pullback.fst P.hom x ≫ c.left :=
    pullback.lift_fst _ _ _
  calc y ≫ c.left = w ≫ pullback.fst P.hom x ≫ c.left := by rw [← Category.assoc, hw1]
    _ = w ≫ ((Over.pullback x).map c).left ≫ pullback.fst B.hom x := by rw [h3]
    _ = y' ≫ qq.left ≫ pullback.fst B.hom x := by
      rw [h, Over.comp_left, Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc, hw2,
        Category.assoc]

theorem mulN_eq_pow {S : Scheme.{0}} (P : Over S) [GrpObj P] (n : ℕ) : mulN P n = (𝟙 P) ^ n := by
  induction n with
  | zero => simp [mulN, Hom.one_def]
  | succ n ih => rw [pow_succ, ← ih, mulN, Hom.mul_def]

theorem finiteMulTorus : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ), 1 ≤ N → IsFinite ((𝟙 (splitTorus S X)) ^ N).left := by
  intro S X _ _ _ N hN
  rw [← mulN_eq_pow]
  exact GlobalTheory.Diag.isFinite_mulN S X (by omega)

theorem kernelOf : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Over S) [GrpObj P], IsSemiAbelian P → ∀ N : ℕ, 1 ≤ N → IsFinite ((𝟙 P) ^ N).left → ∃ (A : Over S) (_ : GrpObj A) (_ : IsCommMonObj A) (j : A ⟶ P), IsMonHom j ∧ IsPullback j (toUnit A) ((𝟙 P) ^ N) η[P] ∧ IsFinite A.hom ∧ Flat A.hom := by
  intro S _ P _ hP N hN hfin
  have := hP.comm
  have := hP.smooth
  have := hP.separated
  have := hP.quasiCompact
  have := GlobalTheory.T.power_map_flat_semiabelian S P hP N hN
  have := GlobalTheory.T.power_map_locally_quasi_finite S P hP N hN
  have hp : IsPullback (pullback.fst ((𝟙 P) ^ N) η[P]) (toUnit (pullback ((𝟙 P) ^ N) η[P])) ((𝟙 P) ^ N) η[P] := by
    have h := IsPullback.of_hasPullback ((𝟙 P) ^ N) η[P]
    rwa [toUnit_unique (pullback.snd _ _) (toUnit _)] at h
  obtain ⟨g1, g2, g3⟩ := Tors.exists_kernel_grp hp
  obtain ⟨h1, -⟩ := Tors.kernel_props hp
  refine ⟨_, g1, g2, _, g3, hp, ?_, h1⟩
  have hl := hp.map (Over.forget S)
  have hA : (toUnit (pullback ((𝟙 P) ^ N) η[P])).left = (pullback ((𝟙 P) ^ N) η[P]).hom := by
    simpa using Over.w (toUnit (pullback ((𝟙 P) ^ N) η[P]))
  have hl' : IsPullback (pullback.fst ((𝟙 P) ^ N) η[P]).left (pullback ((𝟙 P) ^ N) η[P]).hom ((𝟙 P) ^ N).left (η[P]).left := by
    rw [← hA]; exact hl
  exact MorphismProperty.of_isPullback hl' hfin

theorem gt_q_compat : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ), thickMap R I e G ≫ (U.gt (e + 1)).q.left = (U.gt e).q.left ≫ thickMap R I e D.toPre.P.A := by
  intro R _ _ I D A G _ _ U e
  refine pullback.hom_ext ?_ ?_
  · have h := U.gt_q e
    have h1 : thickMap R I e D.toPre.P.A ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _ |>.trans (Category.comp_id _)
    simp only [Category.assoc]
    rw [h1]
    exact h
  · have w1 := Over.w (U.gt (e + 1)).q
    have w2 := Over.w (U.gt e).q
    have s1 : thickMap R I e D.toPre.P.A ≫ pullback.snd _ _ = pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    have s2 : thickMap R I e G ≫ pullback.snd _ _ = pullback.snd _ _ ≫ thickTrans R I e := pullback.lift_snd _ _ _
    simp only [Over.pullback_obj_hom] at w1 w2
    simp only [Category.assoc]
    rw [w1, s1, s2, ← Category.assoc, w2]

theorem finiteMulAbelian : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (B : Over S) [GrpObj B], IsAbelianScheme B → ∀ N : ℕ, 1 ≤ N → IsFinite ((𝟙 B) ^ N).left := by
  intro S _ B _ hB N hN
  have := hB.proper
  have := GlobalTheory.T.power_map_locally_quasi_finite S B (GlobalTheory.isSemiAbelian_of_isAbelianScheme B hB) N hN
  have hw : ((𝟙 B) ^ N).left ≫ B.hom = B.hom := Over.w _
  have : IsProper ((𝟙 B) ^ N).left := by
    have h : IsProper (((𝟙 B) ^ N).left ≫ B.hom) := by rw [hw]; infer_instance
    exact IsProper.of_comp _ B.hom
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem finitePart_extension_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (G B : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj B] [IsCommMonObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : ∀ e, thickObj R (IsLocalRing.maximalIdeal R) e G ⟶ thickObj R (IsLocalRing.maximalIdeal R) e B) (ii : ∀ e, splitTorus (Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)))) X ⟶ thickObj R (IsLocalRing.maximalIdeal R) e G), IsAbelianScheme B → (∀ e, IsMonHom (q e)) → (∀ e, IsMonHom (ii e)) → (∀ e, thickMap R (IsLocalRing.maximalIdeal R) e G ≫ (q (e + 1)).left = (q e).left ≫ thickMap R (IsLocalRing.maximalIdeal R) e B) → (∀ e, thickMap R (IsLocalRing.maximalIdeal R) e (splitTorus (Spec (CommRingCat.of R)) X) ≫ (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) (e + 1)) X).hom.left ≫ (ii (e + 1)).left = (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom.left ≫ (ii e).left ≫ thickMap R (IsLocalRing.maximalIdeal R) e G) → (∀ e, ii e ≫ q e = toUnit _ ≫ η[thickObj R (IsLocalRing.maximalIdeal R) e B]) → Flat (q 0).left → Surjective (q 0).left → QuasiCompact (q 0).left → IsPullback (ii 0) (toUnit _) (q 0) η[thickObj R (IsLocalRing.maximalIdeal R) 0 B] → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Type) [CommGroup T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → IsFinite Γf.G.hom → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ (M C : Type) (_ : CommGroup M) (_ : CommGroup C) (ΓM : QFGroup R M) (ΓB : QFGroup R C) (iM : ΓM.G.left ⟶ (splitTorus (Spec (CommRingCat.of R)) X).left) (iB : ΓB.G.left ⟶ B.left) (a : ΓM.G ⟶ Γf.G) (b : Γf.G ⟶ ΓB.G), ΓM.IsTorsionAlong _ (𝟙 _) N iM ∧ ΓB.IsTorsionAlong B (𝟙 _) N iB ∧ IsMonHom a ∧ IsMonHom b ∧ IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit _) b η[ΓB.G] ∧ ∀ (e : ℕ) (Y : Scheme.{0}) (y : Y ⟶ Γf.G.left) (y' : Y ⟶ (thickObj R (IsLocalRing.maximalIdeal R) e G).left), y' ≫ (fstG (IsLocalRing.maximalIdeal R) e G).left = y ≫ u.left ≫ i → y ≫ b.left ≫ iB = y' ≫ (q e).left ≫ pullback.fst B.hom (thick R (IsLocalRing.maximalIdeal R) e) := by
  intro R _ _ _ _ _ _ G B _ _ _ _ X _ _ _ q ii hBab qhom ihom hcq hci hiq hfl hsu hqc hk0 N hN T _ Γ i hi H _ Γf u _ hop hfin hcl
  have hBs : IsSemiAbelian B := GlobalTheory.isSemiAbelian_of_isAbelianScheme B hBab
  obtain ⟨AB, _, _, jB, _, hpB, finB, flatB⟩ := kernelOf (Spec (CommRingCat.of R)) B hBs N hN
    (finiteMulAbelian _ B hBab N hN)
  obtain ⟨AT, _, _, jT, _, hpT, finT, flatT⟩ := kernelOf (Spec (CommRingCat.of R)) (splitTorus (Spec (CommRingCat.of R)) X) inferInstance N hN
    (finiteMulTorus _ X N hN)
  obtain ⟨v, hvl, _, _, hker⟩ := GlobalTheory.T.torsion_group_open_immersion_lift R G N T Γ i hi H Γf u hop hcl
  have monoB : Mono jB := Tors.mono_of_pullback hpB
  have hfb : ∀ e, ∃ w : thickObj R (IsLocalRing.maximalIdeal R) e Γf.G ⟶ thickObj R (IsLocalRing.maximalIdeal R) e AB,
      w ≫ (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB = (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v ≫ q e := fun e => by
    have := qhom e
    have h1 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpB
    have h2 := hker e
    exact factor_of_kernel h2 h1 (q e)
  haveI := hfin
  obtain ⟨b, _, hb⟩ := GlobalTheory.T.thickening_group_hom_extends R (IsLocalRing.maximalIdeal R) Γf.G AB G B v jB q qhom hcq hfb
  have hfa : ∀ e, ∃ w : thickObj R (IsLocalRing.maximalIdeal R) e AT ⟶ thickObj R (IsLocalRing.maximalIdeal R) e Γf.G,
      w ≫ (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map v = (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jT ≫
        ((GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom ≫ ii e) := fun e => by
    have := ihom e
    have h1 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpT
    have h2 := hker e
    exact factor_of_kernel h1 h2 _
  obtain ⟨a, _, ha⟩ := GlobalTheory.T.thickening_group_hom_extends R (IsLocalRing.maximalIdeal R) AT Γf.G (splitTorus (Spec (CommRingCat.of R)) X) G jT v
    (fun e => (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) e) X).hom ≫ ii e)
    (fun e => by have := ihom e; infer_instance)
    (fun e => by simpa [Over.comp_left] using hci e) hfa
  have hb0 := hb 0
  have ha0 := ha 0
  rw [Functor.map_comp] at hb0 ha0
  have hk1 := kernel_iso (GlobalTheory.Diag.baseChangeIso (thick R (IsLocalRing.maximalIdeal R) 0) X) (kernel_pull (thick R (IsLocalRing.maximalIdeal R) 0) hpT)
  have hk2 := kernel_pull (thick R (IsLocalRing.maximalIdeal R) 0) hpB
  have hk3 := hker 0
  have := qhom 0
  have := ihom 0
  obtain ⟨hf, hs, hpk⟩ := GlobalTheory.T.split_torus_extension_torsion _ X (thickObj R (IsLocalRing.maximalIdeal R) 0 G) (thickObj R (IsLocalRing.maximalIdeal R) 0 B) (ii 0) (q 0) hfl hsu hqc hk0 N hN _ _ _ _ _ _ η[(Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj AB] hk1 hk3 hk2 (IsMonHom.one_hom _) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map a) ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map b) (by rw [ha0, Category.assoc]) hb0
  rw [Functor.obj.η_def AB] at hpk
  have flatG : Flat Γf.G.hom := Γf.flat
  have hab : a ≫ b = toUnit AT ≫ η[AB] := by
    refine GlobalTheory.T.finite_map_eq_of_thickenings_eq R (IsLocalRing.maximalIdeal R) AT AB _ _ (fun e => ?_)
    have hm : Mono ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB) :=
      Tors.mono_of_pullback (kernel_pull (thick R (IsLocalRing.maximalIdeal R) e) hpB)
    rw [← cancel_mono ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map jB)]
    have e1 := ha e
    have e2 := hb e
    rw [Functor.map_comp] at e1 e2
    have e3 : η[thickObj R (IsLocalRing.maximalIdeal R) e B] =
        Functor.LaxMonoidal.ε (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)) ≫
          (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e)).map η[B] := Functor.obj.η_def B
    rw [Functor.map_comp, Category.assoc, e2, ← Category.assoc, e1, Category.assoc, Category.assoc, hiq e, e3,
      ← Functor.map_comp, Category.assoc, IsMonHom.one_hom, Functor.map_comp]
    simp only [← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.Monoidal.εIso (Over.pullback (thick R (IsLocalRing.maximalIdeal R) e))).inv]
    exact toUnit_unique _ _
  obtain ⟨hcl', hfb', hsb', hpb'⟩ := GlobalTheory.CompanionTheory.Ar.BT.FinFlat.exact_of_closedFibre R AT Γf.G AB a b η[AB] hab (isPullback_map_unit _ hpk) hf hs
  obtain ⟨C, _, ΓB, φB, _, htB⟩ := GlobalTheory.T.generic_points_of_torsion_kernel R B hBs N hN AB jB hpB (fun g hg => by
    obtain ⟨w, rfl⟩ := hsb'.surj g
    have hw : (Γf.G.hom w).asIdeal = ⊥ := by
      rw [← Scheme.Hom.comp_apply, Over.w b] at hg
      exact hg
    obtain ⟨t, x, hx⟩ := Γf.pt_onto w hw
    exact ⟨Γf.pt t ≫ b, x, by simp [hx]⟩)
  obtain ⟨M, _, ΓM, φM, _, htM⟩ := GlobalTheory.T.generic_points_of_torsion_kernel R _ inferInstance N hN AT jT hpT (GlobalTheory.T.generic_points_of_closed_subgroup R H Γf AT AB a b η[AB] hcl' hpb')
  have hinv : IsMonHom φB.inv := inferInstance
  have isoL : IsIso φB.inv.left := inferInstanceAs (IsIso ((Over.forget _).map φB.inv))
  have isoM : IsIso φM.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φM.hom))
  refine ⟨M, C, _, _, ΓM, ΓB, φM.hom.left ≫ jT.left, φB.hom.left ≫ jB.left, φM.hom ≫ a, b ≫ φB.inv, htM, htB,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · rw [Over.comp_left]; infer_instance
  · refine IsPullback.of_iso hpb' φM.symm (Iso.refl _) (Iso.refl _) φB.symm (by simp) (toUnit_unique _ _) (by simp) ?_
    simp
  · intro e Y y y' h
    have hv : y' ≫ pullback.fst G.hom (thick R (IsLocalRing.maximalIdeal R) e) = y ≫ v.left := by
      rw [hvl]; exact h
    have key := comp_left_of_map (thick R (IsLocalRing.maximalIdeal R) e) v (b ≫ jB) (q e) (hb e) y y' hv
    rw [← key]
    simp [Over.comp_left]

theorem finitePart_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (D : DegData R (IsLocalRing.maximalIdeal R)) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre (IsLocalRing.maximalIdeal R) D A G) (N : ℕ), 1 ≤ N → ∀ (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G (𝟙 _) N i → ∀ (H : Type) [CommGroup H] [Finite H] (Γf : QFGroup R H) (u : Γf.G ⟶ Γ.G) [IsMonHom u], IsOpenImmersion u.left → IsFinite Γf.G.hom → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ Set.range u.left) → ∃ (M C : Type) (_ : CommGroup M) (_ : CommGroup C) (ΓM : QFGroup R M) (ΓB : QFGroup R C) (iM : ΓM.G.left ⟶ (splitTorus (Spec (CommRingCat.of R)) D.toPre.X).left) (iB : ΓB.G.left ⟶ D.toPre.P.A.left) (a : ΓM.G ⟶ Γf.G) (b : Γf.G ⟶ ΓB.G), ΓM.IsTorsionAlong _ (𝟙 _) N iM ∧ ΓB.IsTorsionAlong D.toPre.P.A (𝟙 _) N iB ∧ IsMonHom a ∧ IsMonHom b ∧ IsClosedImmersion a.left ∧ Flat b.left ∧ Surjective b.left ∧ IsPullback a (toUnit _) b η[ΓB.G] ∧ ∀ (e : ℕ) (Y : Scheme.{0}) (y : Y ⟶ Γf.G.left) (y' : Y ⟶ (thickObj R (IsLocalRing.maximalIdeal R) e G).left), y' ≫ (fstG (IsLocalRing.maximalIdeal R) e G).left = y ≫ u.left ≫ i → y ≫ b.left ≫ iB = y' ≫ (U.gt e).pG.left := by
  intro R _ _ _ _ _ _ D A G _ _ U N hN T _ _ Γ i hi H _ _ Γf u _ hop hfin hcl
  have hq0 : QuasiCompact (U.gt 0).q.left := by
    have := (U.gt 0).q_affine
    infer_instance
  exact finitePart_extension_core R G D.toPre.P.A D.toPre.X (fun e => (U.gt e).q) (fun e => (U.gt e).i) D.toPre.P.isAb
    (fun e => (U.gt e).q_hom) (fun e => (U.gt e).i_hom) (gt_q_compat R _ D A G U)
    (GlobalTheory.T.uniformization_thickening_compat R _ D A G U) (fun e => (U.gt e).isKernel.w) (U.gt 0).q_flat (U.gt 0).q_surj hq0 (U.gt 0).isKernel N hN T Γ i hi H Γf u hop hfin hcl

end PositivityTheory.HtPt.Stight.D1
