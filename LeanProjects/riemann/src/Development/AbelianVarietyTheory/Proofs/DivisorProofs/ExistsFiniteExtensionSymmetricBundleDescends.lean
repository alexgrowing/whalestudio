import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundlePullbackGrpPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionRigidTranslateSameMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionPointAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangePolarisationTranslateTwoTorsionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem pull_pol : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (f : Sp R ⟶ Sp R₀) (A : PolAV (Sp R₀)) (G : Over (Sp R)) [GrpObj G] (α : G.left ⟶ A.A.left), IsGrpPullback G A.A f α → (A.L.pull α).IsLB ∧ Rigidified G (A.L.pull α) ∧ Sym G (A.L.pull α) ∧ RelAmple G (A.L.pull α) ∧ KTriv G (A.L.pull α) := by
  intro R R₀ _ _ f A G _ α hα
  have hw := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen A.isLB α)
  exact ⟨pull_isLB A.isLB α, GlobalTheory.PolBaseChange.rigidified_pull hα A.rigid, GlobalTheory.PolBaseChange.sym_pull hα A.sym,
    relAmple_pull hα.1 A.isLB (pull_isLB A.isLB α) hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample,
    kTriv_pull hα A.isLB (pull_isLB A.isLB α) hw A.ktriv⟩

theorem isSquare_unique : ∀ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} (φ : G'.left ⟶ G.left) (φ₂ φ₂' : (G' ⊗ G').left ⟶ (G ⊗ G).left), IsSquare φ φ₂ → IsSquare φ φ₂' → φ₂ = φ₂' := by
  intro S S' G' G φ φ₂ φ₂' h h'
  have e : φ₂ ≫ (G ⊗ G).hom = φ₂' ≫ (G ⊗ G).hom := by
    rw [← Over.w (fst G G), ← Category.assoc, ← Category.assoc, h.1, h'.1]
  let u : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂ rfl
  let v : Over.mk (φ₂ ≫ (G ⊗ G).hom) ⟶ G ⊗ G := Over.homMk φ₂' e.symm
  have : u = v := CartesianMonoidalCategory.hom_ext _ _
    (Over.OverMorphism.ext (by simpa [u, v] using h.1.trans h'.1.symm))
    (Over.OverMorphism.ext (by simpa [u, v] using h.2.trans h'.2.symm))
  exact congrArg (fun z => z.left) this
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate GlobalTheory.GtCoordCompare

theorem lbIso_diff_pull_pull : ∀ (X Y₁ Y₂ Z : Scheme.{0}) (M : LB X) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) (u₁ v₁ : Y₁ ⟶ Y₁) (u₂ v₂ : Y₂ ⟶ Y₂) (q₁ : Z ⟶ Y₁) (q₂ : Z ⟶ Y₂), M.IsLB → q₁ ≫ u₁ ≫ g₁ = q₂ ≫ u₂ ≫ g₂ → q₁ ≫ v₁ ≫ g₁ = q₂ ≫ v₂ ≫ g₂ → LBIso ((LB.LinComb (M.pull g₁) (K := Fin 2) ![u₁, v₁] ![1, -1]).pull q₁) ((LB.LinComb (M.pull g₂) (K := Fin 2) ![u₂, v₂] ![1, -1]).pull q₂) := by
  intro X Y₁ Y₂ Z M g₁ g₂ u₁ v₁ u₂ v₂ q₁ q₂ hM hu hv
  refine lbIso_of_refines hM
    ((((refines_self (L := M) (fun _ : PUnit => g₁) (fun _ => 1)).linComb _ _)).linComb _ _)
    ((((refines_self (L := M) (fun _ : PUnit => g₂) (fun _ => 1)).linComb _ _)).linComb _ _) _ isGen_one
    fun U _ f => ?_
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, hu, hv]
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem transl_comp_eq : ∀ {S S₁ S₀ : Scheme.{0}} (G : Over S) (G₁ : Over S₁) (A : Over S₀) [GrpObj G] [GrpObj G₁] [GrpObj A] (f : S ⟶ S₀) (f₁ : S₁ ⟶ S₀) (φ : G.left ⟶ A.left) (φ₁ : G₁.left ⟶ A.left), IsGrpPullback G A f φ → IsGrpPullback G₁ A f₁ φ₁ → ∀ (x : 𝟙_ (Over S) ⟶ G) (t : 𝟙_ (Over S₁) ⟶ G₁) (Z : Scheme.{0}) (q : Z ⟶ G.left) (q₁ : Z ⟶ G₁.left), q ≫ φ = q₁ ≫ φ₁ → q ≫ (toUnit G ≫ x).left ≫ φ = q₁ ≫ (toUnit G₁ ≫ t).left ≫ φ₁ → q ≫ (GlobalTheory.PolTranslate.transl x).left ≫ φ = q₁ ≫ (GlobalTheory.PolTranslate.transl t).left ≫ φ₁ := by
  intro S S₁ S₀ G G₁ A _ _ _ f f₁ φ φ₁ h h₁ x t Z q q₁ e ec
  let T : Over S := Over.mk (q ≫ G.hom)
  let T₁ : Over S₁ := Over.mk (q₁ ≫ G₁.hom)
  let a : T ⟶ G := Over.homMk q rfl
  let a₁ : T₁ ⟶ G₁ := Over.homMk q₁ rfl
  have k : q ≫ (GlobalTheory.PolTranslate.transl x).left = (a * (toUnit T ≫ x)).left := comp_transl_left a x
  have k₁ : q₁ ≫ (GlobalTheory.PolTranslate.transl t).left = (a₁ * (toUnit T₁ ≫ t)).left := comp_transl_left a₁ t
  have hw : (q ≫ G.hom) ≫ f = (q₁ ≫ G₁.hom) ≫ f₁ := by
    rw [Category.assoc, Category.assoc, ← h.1.w, ← h₁.1.w, ← Category.assoc, ← Category.assoc, e]
  let x₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk (a.left ≫ φ) (by
    show (q ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, Category.assoc])
  let y₀ : Over.mk (T.hom ≫ f) ⟶ A := Over.homMk ((toUnit T ≫ x).left ≫ φ) (by
    show ((toUnit T ≫ x).left ≫ φ) ≫ A.hom = (q ≫ G.hom) ≫ f
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w (toUnit T ≫ x)]
    rfl)
  let x₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk (a₁.left ≫ φ₁) (by
    show (q₁ ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, Category.assoc])
  let y₁ : Over.mk (T₁.hom ≫ f₁) ⟶ A := Over.homMk ((toUnit T₁ ≫ t).left ≫ φ₁) (by
    show ((toUnit T₁ ≫ t).left ≫ φ₁) ≫ A.hom = (q₁ ≫ G₁.hom) ≫ f₁
    rw [Category.assoc, h₁.1.w, ← Category.assoc, Over.w (toUnit T₁ ≫ t)]
    rfl)
  have E := h.2 T a (toUnit T ≫ x) x₀ y₀ rfl rfl
  have E₁ := h₁.2 T₁ a₁ (toUnit T₁ ≫ t) x₁ y₁ rfl rfl
  let j : Over.mk (T.hom ≫ f) ⟶ Over.mk (T₁.hom ≫ f₁) := Over.homMk (𝟙 Z) (by
    show 𝟙 Z ≫ (q₁ ≫ G₁.hom) ≫ f₁ = (q ≫ G.hom) ≫ f
    rw [Category.id_comp, hw])
  have hx : j ≫ x₁ = x₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ q₁ ≫ φ₁ = q ≫ φ
    rw [Category.id_comp, e])
  have hy : j ≫ y₁ = y₀ := Over.OverMorphism.ext (by
    show 𝟙 Z ≫ (toUnit T₁ ≫ t).left ≫ φ₁ = (toUnit T ≫ x).left ≫ φ
    have k2 : (toUnit T ≫ x).left = q ≫ (toUnit G ≫ x).left := by
      simp only [Over.comp_left]
      show (q ≫ G.hom) ≫ x.left = q ≫ (G.hom ≫ x.left)
      rw [Category.assoc]
    have k3 : (toUnit T₁ ≫ t).left = q₁ ≫ (toUnit G₁ ≫ t).left := by
      simp only [Over.comp_left]
      show (q₁ ≫ G₁.hom) ≫ t.left = q₁ ≫ (G₁.hom ≫ t.left)
      rw [Category.assoc]
    rw [Category.id_comp, k2, k3, Category.assoc, Category.assoc]
    exact ec.symm)
  have H := congrArg (fun z => z.left) (MonObj.comp_mul j x₁ y₁)
  rw [hx, hy] at H
  rw [← Category.assoc, ← Category.assoc, k, k₁, ← E, ← E₁, ← H]
  exact Category.id_comp _
end GlobalTheory.SymFinExt

namespace GlobalTheory.SymFinExt
open GlobalTheory.RigidTranslate

theorem lam_pull_id {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) : LBIso L (L.pull (𝟙 X)) :=
  LBIso.chartPull (chartPullId L) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L (𝟙 X) (𝟙 X) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)

theorem exists_finite_ext : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A : PolAV (Sp K)) (A' : PolAV (Sp Ω)) (α : A'.A.left ⟶ A.A.left) (α₂ : (G2 A'.A).left ⟶ (G2 A.A).left), IsGrpPullback A'.A A.A (spMap ga) α → Geo.Tor.IsSquare α α₂ → LBIso (abelian₂ A'.A A'.L) ((abelian₂ A.A A.L).pull α₂) → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left) (p : pullback A'.A.hom (spMap j) ⟶ A₁.A.left), io.Finite ∧ l.comp io = j.comp ga ∧ IsGrpPullback A₁.A A.A (spMap io) α₁ ∧ Geo.Tor.IsSquare α₁ α₁₂ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) ∧ p ≫ α₁ = pullback.fst _ _ ≫ α ∧ p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l ∧ LBIso (A'.L.pull (pullback.fst A'.A.hom (spMap j))) (A₁.L.pull p) := by
  intro K Ω _ _ _ ga A A' α α₂ hα hsq hΛ
  have := A.isAb.comm
  have := A'.isAb.comm
  obtain ⟨hLB, hrig, hsym, hamp, hK⟩ := pull_pol Ω K (spMap ga) A A'.A α hα
  let P : PolAV (Sp Ω) := ⟨A'.A, A'.isAb, A'.g, A'.smoothDim, A.L.pull α, hLB, hrig, hsym, hamp, hK⟩
  have hΛA : (abelian₂ A.A A.L).IsLB := DVR.linComb_isLB _ A.isLB _ _
  obtain ⟨β₂, hβ, hT⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (spMap ga) A.A A'.A α hα
  have e₁ := hT A.L (A.L.pull α) _ (abelian₂ A.A A.L) (𝟙 _) A.isLB hLB hΛA (GlobalTheory.PolBaseChange.lbIso_refl hLB)
    (lam_pull_id hΛA)
  rw [Category.comp_id, isSquare_unique α β₂ α₂ hβ hsq] at e₁
  have hΛ' : LBIso (abelian₂ P.A A'.L) (abelian₂ P.A P.L) :=
    LBIso.trans (DVR.linComb_isLB _ A'.isLB _ _) (pull_isLB hΛA _) (DVR.linComb_isLB _ hLB _ _) hΛ e₁.symm
  obtain ⟨x, hx2, hxL⟩ := GlobalTheory.T.exists_twoTorsion_rigidTranslate_same_mumfordBundle Ω P A'.L A'.isLB A'.rigid A'.sym hΛ'
  obtain ⟨K', _, io, l, y, hfin, hcomp, hy2, hy⟩ := GlobalTheory.T.exists_finite_ext_twoTorsion_point_abelianVariety K Ω ga A A'.A α hα x hx2
  obtain ⟨A₁, α₁, α₁₂, t, hα₁, hsq₁, hΛ₁, ht, hL₁⟩ := GlobalTheory.T.exists_baseChange_polarisation_translate_two_torsion K K' io A y hy2
  have hid : spMap (RingHom.id Ω) = 𝟙 _ := Spec.map_id _
  have w : (pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ α) ≫ A.A.hom =
      (pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap l) ≫ spMap io := by
    rw [Category.assoc, hα.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc]
    congr 1
    rw [← hcomp, hid, Category.id_comp]
    show Spec.map (CommRingCat.ofHom (l.comp io)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  let p := hα₁.1.lift _ _ w
  have hp1 : p ≫ α₁ = pullback.fst _ _ ≫ α := hα₁.1.lift_fst _ _ _
  have hp2 : p ≫ A₁.A.hom = pullback.snd _ _ ≫ spMap l := hα₁.1.lift_snd _ _ _
  refine ⟨K', inferInstance, io, Ω, inferInstance, RingHom.id Ω, l, A₁, α₁, α₁₂, p, hfin, by rw [hcomp]; rfl,
    hα₁, hsq₁, hΛ₁, hp1, hp2, ?_⟩
  have hc : pullback.fst A'.A.hom (spMap (RingHom.id Ω)) ≫ (toUnit A'.A ≫ x).left ≫ α =
      p ≫ (toUnit A₁.A ≫ t).left ≫ α₁ := by
    have hsnd : pullback.snd A'.A.hom (spMap (RingHom.id Ω)) ≫ spMap (RingHom.id Ω) = pullback.snd _ _ := by
      rw [hid, Category.comp_id]
    show pullback.fst _ _ ≫ (A'.A.hom ≫ x.left) ≫ α = p ≫ (A₁.A.hom ≫ t.left) ≫ α₁
    rw [Category.assoc, ← Category.assoc (pullback.fst _ _), pullback.condition, hsnd, Category.assoc,
      ← Category.assoc p, hp2, Category.assoc, ht, hy]
  have htr := transl_comp_eq A'.A A₁.A A.A (spMap ga) (spMap io) α α₁ hα hα₁ x t _ _ p hp1.symm hc
  have hE := lbIso_diff_pull_pull _ _ _ _ A.L α α₁ _ _ _ _ (pullback.fst A'.A.hom (spMap (RingHom.id Ω))) p A.isLB
    htr hc
  have hR₁ : (rigTransl (A.L.pull α₁) t).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  have hR : (rigTransl (A.L.pull α) x).IsLB := DVR.linComb_isLB _ (pull_isLB A.isLB _) _ _
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB hR _) (pull_isLB A₁.isLB _) (GlobalTheory.RigidBundleGlue.LBIso.pull hxL _)
    (LBIso.trans (pull_isLB hR _) (pull_isLB hR₁ _) (pull_isLB A₁.isLB _) hE (GlobalTheory.RigidBundleGlue.LBIso.pull hL₁.symm _))

end GlobalTheory.SymFinExt

end
