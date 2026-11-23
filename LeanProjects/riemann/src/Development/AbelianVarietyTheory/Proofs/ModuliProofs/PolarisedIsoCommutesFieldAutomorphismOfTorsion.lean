import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsFib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.SerreTwist

theorem iso_eq_of_torsion (hL : Laws) {C : Type} [Field C] [IsAlgClosed C] (Q Q' : PolAV (Sp C))
    (a b : Q.A ≅ Q'.A) (ha : η[Q.A] ≫ a.hom = η[Q'.A]) (hb : η[Q.A] ≫ b.hom = η[Q'.A])
    (la : LBIso Q.L (Q'.L.pull a.hom.left)) (lb : LBIso Q.L (Q'.L.pull b.hom.left))
    {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0)
    (h : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ a.hom = x ≫ b.hom) : a.hom = b.hom := by
  have hη : η[Q.A] ≫ (a ≪≫ b.symm).hom = η[Q.A] := by
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ha, ← hb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hmon : IsMonHom (a ≪≫ b.symm).hom := hL.rigidity _ Q.A Q.A Q.isAb Q.isAb _ hη
  have hpb : LBIso (Q.L.pull (a ≪≫ b.symm).hom.left) (Q'.L.pull a.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso lb _
      (by rw [← Over.comp_left, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  obtain ⟨w, hw⟩ : LBIso Q.L (Q.L.pull (a ≪≫ b.symm).hom.left) :=
    LBIso.trans Q.isLB (pull_isLB Q'.isLB _) (pull_isLB Q.isLB _) la (LBIso.symm hpb)
  have hfix : ∀ x : Over.mk (𝟙 (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a ≪≫ b.symm).hom = x := by
    intro x hx
    rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h x hx, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key := GlobalTheory.MatchRigid.aut_eq_id hL Q (𝟙 (Sp C)) hk hkC (a ≪≫ b.symm) w hw hfix
  have := congrArg (· ≫ b.hom) key
  simpa using this

theorem exists_fibre (hB : PolBaseChangeSt) {S S' : Scheme.{0}} (P : PolAV S) (t : S' ⟶ S) :
    ∃ (Q : PolAV S') (e : Q.A.left ≅ (Over.mk t ⊗ P.A).left),
      e.hom ≫ (fst (Over.mk t) P.A).left = Q.A.hom ∧
      LBIso Q.L (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left)) ∧
      ∃ F : (𝟙_ (Over S') ⟶ Q.A) →* (Over.mk t ⟶ P.A),
        ∀ x, x.left ≫ e.hom = (lift (𝟙 (Over.mk t)) (F x)).left := by
  obtain ⟨Q, g, hg, -, hmul, w, hw⟩ := hB S S' t P
  have hpb : IsPullback Q.A.hom g t P.A.hom := hg.flip
  let c : Over.mk t ⟶ Over.mk ((𝟙_ (Over S')).hom ≫ t) := Over.homMk (𝟙 S') (by simp)
  have hsnd : hpb.isoPullback.hom ≫ (snd (Over.mk t) P.A).left = g := by
    rw [Over.snd_left]; exact hpb.isoPullback_hom_snd
  refine ⟨Q, hpb.isoPullback, ?_, ?_,
    MonoidHom.mk' (fun x => c ≫ toBase hg.w x) (fun x y => by simp only [hmul, MonObj.comp_mul]), fun x => ?_⟩
  · rw [Over.fst_left]; exact hpb.isoPullback_hom_fst
  · rw [hsnd]; exact LBIso.symm ⟨w, hw⟩
  · apply pullback.hom_ext
    · simp [c]
      exact (pullback.lift_fst _ _ _).symm
    · have hs : hpb.isoPullback.hom ≫ pullback.snd (Over.mk t).hom P.A.hom = g := hpb.isoPullback_hom_snd
      rw [Category.assoc, hs, Over.lift_left]
      erw [pullback.lift_snd]
      simp [c, toBase]

theorem prod_iso_eq (hL : Laws) {S : Scheme.{0}} (P P' : PolAV S) {C : Type} [Field C] [IsAlgClosed C]
    (t : Sp C ⟶ S) {k : ℕ} (hk : 3 ≤ k) (hkC : (k : C) ≠ 0) (φ : Fin 2 → (Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A))
    (h1 : ∀ i, (φ i).hom ≫ fst _ _ = fst _ _)
    (h2 : ∀ i, lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ (φ i).hom ≫ snd _ _ = 1)
    (h3 : ∀ i, LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull ((φ i).hom ≫ snd (Over.mk t) P'.A).left))
    (h4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ (φ 0).hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ (φ 1).hom ≫ snd _ _) :
    (φ 0).hom = (φ 1).hom := by
  obtain ⟨Q, e, he1, he2, F, hF⟩ := exists_fibre hL.polBaseChange P t
  obtain ⟨Q', e', he1', he2', F', hF'⟩ := exists_fibre hL.polBaseChange P' t

  have hlift : ∀ i (z : Over.mk t ⟶ P.A), lift (𝟙 (Over.mk t)) z ≫ (φ i).hom =
      lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) z ≫ (φ i).hom ≫ snd _ _) := by
    intro i z
    apply CartesianMonoidalCategory.hom_ext
    · simp [h1 i]
    · simp
  have h1' : ∀ i, (φ i).hom.left ≫ (fst (Over.mk t) P'.A).left = (fst (Over.mk t) P.A).left := by
    intro i
    rw [← Over.comp_left, h1 i]

  let θ : Fin 2 → (Q.A.left ≅ Q'.A.left) := fun i => e ≪≫ (Over.forget S).mapIso (φ i) ≪≫ e'.symm
  have hθ : ∀ i, (θ i).hom = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hw : ∀ i, (θ i).hom ≫ Q'.A.hom = Q.A.hom := by
    intro i
    rw [hθ, ← he1', ← he1, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h1']
  let a : Fin 2 → (Q.A ≅ Q'.A) := fun i => Over.isoMk (θ i) (hw i)
  have ha_left : ∀ i, (a i).hom.left = e.hom ≫ (φ i).hom.left ≫ e'.inv := fun i => rfl
  have hcomp : ∀ i (x : 𝟙_ (Over (Sp C)) ⟶ Q.A), x.left ≫ (a i).hom.left =
      (lift (𝟙 (Over.mk t)) (lift (𝟙 (Over.mk t)) (F x) ≫ (φ i).hom ≫ snd _ _)).left ≫ e'.inv := by
    intro i x
    rw [ha_left, ← Category.assoc, hF, ← Category.assoc, ← Over.comp_left, hlift]

  have hone : ∀ (R : PolAV (Sp C)), (1 : 𝟙_ (Over (Sp C)) ⟶ R.A) = η[R.A] := by
    intro R
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have ha : ∀ i, η[Q.A] ≫ (a i).hom = η[Q'.A] := by
    intro i
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← hone Q, hcomp, map_one, h2 i, ← map_one F', ← hF', hone Q', Category.assoc,
      Iso.hom_inv_id, Category.comp_id]

  have la : ∀ i, LBIso Q.L (Q'.L.pull (a i).hom.left) := by
    intro i
    have h3e : LBIso (P.L.pull (e.hom ≫ (snd (Over.mk t) P.A).left))
        (P'.L.pull ((a i).hom.left ≫ e'.hom ≫ (snd (Over.mk t) P'.A).left)) :=
      GlobalTheory.GenSpread.lbIso_pull_comp e.hom rfl
        (by rw [ha_left, Over.comp_left]; simp only [Category.assoc, Iso.inv_hom_id_assoc]) (h3 i)
    have hQ' := GlobalTheory.GenSpread.lbIso_pull_of_lbIso he2' (a i).hom.left rfl
    exact LBIso.trans Q.isLB (pull_isLB P'.isLB _) (pull_isLB Q'.isLB _)
      (LBIso.trans Q.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) he2 h3e) (LBIso.symm hQ')

  have htor : ∀ x : 𝟙_ (Over (Sp C)) ⟶ Q.A, x ^ k = 1 → x ≫ (a 0).hom = x ≫ (a 1).hom := by
    intro x hx
    have hFx : F x ^ k = 1 := by rw [← map_pow, hx, map_one]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, hcomp, hcomp, h4 (F x) hFx]
  have key := congrArg Over.Hom.left (iso_eq_of_torsion hL Q Q' (a 0) (a 1) (ha 0) (ha 1) (la 0) (la 1) hk hkC htor)
  rw [ha_left, ha_left] at key
  apply Over.OverMorphism.ext
  simpa using key

end GlobalTheory.SerreTwist

theorem GlobalTheory.SerreTwist.whisker_comp_eq : Laws → ∀ (S : Scheme.{0}) (P P' : PolAV S) (C : Type) [Field C] [IsAlgClosed C] (t : Sp C ⟶ S) (φ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (φ.hom ≫ snd (Over.mk t) P'.A).left) → ∀ k : ℕ, 3 ≤ k → (k : C) ≠ 0 → ∀ s : Over.mk t ≅ Over.mk t, (∀ x : Over.mk t ⟶ P.A, x ^ k = 1 → lift (𝟙 (Over.mk t)) (s.hom ≫ x) ≫ φ.hom ≫ snd _ _ = s.hom ≫ lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _) → s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ = φ.hom ≫ snd _ _ := by
  intro hL S P P' C inst1 inst2 t φ h1 h2 h3 k hk hkC s hs
  let ψ : Over.mk t ⊗ P.A ≅ Over.mk t ⊗ P'.A := whiskerRightIso s P.A ≪≫ φ ≪≫ whiskerRightIso s.symm P'.A
  have hψ : ψ.hom = s.hom ▷ P.A ≫ φ.hom ≫ s.inv ▷ P'.A := rfl
  have hψs : ψ.hom ≫ snd _ _ = s.hom ▷ P.A ≫ φ.hom ≫ snd _ _ := by
    rw [hψ]; simp

  have hsw : ∀ z : Over.mk t ⟶ P.A,
      lift (𝟙 (Over.mk t)) z ≫ s.hom ▷ P.A = s.hom ≫ lift (𝟙 (Over.mk t)) (s.inv ≫ z) := by
    intro z
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have ψ1 : ψ.hom ≫ fst _ _ = fst _ _ := by
    rw [hψ]; simp [reassoc_of% h1]
  have ψ2 : lift (𝟙 (Over.mk t)) (1 : Over.mk t ⟶ P.A) ≫ ψ.hom ≫ snd _ _ = 1 := by
    rw [hψs, ← Category.assoc, hsw, MonObj.comp_one, Category.assoc, h2, MonObj.comp_one]
  have ψ3 : LBIso (P.L.pull (snd (Over.mk t) P.A).left) (P'.L.pull (ψ.hom ≫ snd (Over.mk t) P'.A).left) := by
    rw [hψs]
    exact GlobalTheory.GenSpread.lbIso_pull_comp (s.hom ▷ P.A).left (by rw [← Over.comp_left, whiskerRight_snd])
      (by rw [Over.comp_left]) h3
  have ψ4 : ∀ x : Over.mk t ⟶ P.A, x ^ k = 1 →
      lift (𝟙 (Over.mk t)) x ≫ φ.hom ≫ snd _ _ = lift (𝟙 (Over.mk t)) x ≫ ψ.hom ≫ snd _ _ := by
    intro x hx
    have hx' : (s.inv ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    conv_rhs => rw [hψs, ← Category.assoc, hsw, Category.assoc]
    rw [← hs _ hx', Iso.hom_inv_id_assoc]
  have key : φ.hom = ψ.hom :=
    GlobalTheory.SerreTwist.prod_iso_eq hL P P' t hk hkC ![φ, ψ] (Fin.forall_fin_two.2 ⟨h1, ψ1⟩)
      (Fin.forall_fin_two.2 ⟨h2, ψ2⟩) (Fin.forall_fin_two.2 ⟨h3, ψ3⟩) ψ4
  rw [← hψs, ← key]

end
