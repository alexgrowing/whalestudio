import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelPullIso

open ReciprocityTheory.ChartRestriction.G.Out

theorem isThetaPt_of_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P' k (fun i => x i ≫ φ.hom) v) :
    IsThetaPt P k x v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  exact GlobalTheory.ThetaPtUp.isThetaPtOver_down (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q

section Basis

variable {S : Scheme.{0}} {P : PolAV S} {M : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P M ze) {g : ℕ} (hg : P.g = g)

theorem basis_pow (i : Fin (2 * g)) : levelBasis lev hg i ^ M = 1 := lev.torsion _

theorem basis_indep (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * g) → Fin M)
    (h : linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c' i : ℕ))) : c = c' := by
  subst hg; exact lev.indep K s c c' h

theorem basis_span (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A) (hy : y ^ M = 1) : ∃ c : Fin (2 * g) → Fin M,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ levelBasis lev hg i)
        (fun i => (c i : ℕ)) = y := by
  subst hg; exact lev.span K s y hy

theorem basis_pairing (i j : Fin (2 * g)) :
    WeilIs P.A P.L M (levelBasis lev hg i) (levelBasis lev hg j) (ze ^ stdSymp g i j) := by
  subst hg; exact lev.pairing i j

end Basis

theorem comp_pow_eq_one_iff {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ≅ B) [IsMonHom φ.hom]
    (x : T ⟶ A) (M : ℕ) : (x ≫ φ.hom) ^ M = 1 ↔ x ^ M = 1 := by
  let F : (T ⟶ A) →* (T ⟶ B) := IsMonHom.monoidHom φ.hom T
  have hF : Function.Injective F := fun a b h => (cancel_mono φ.hom).1 h
  have e : F (x ^ M) = (x ≫ φ.hom) ^ M := map_pow F x M
  rw [← e]
  exact map_eq_one_iff F hF

theorem exists_level (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] {P P' : PolAV S} (hg' : P'.g = P.g)
    (φ : P.A ≅ P'.A) [IsMonHom φ.hom] (hw : LBIso P.L (P'.L.pull φ.hom.left)) {M : ℕ} {ze : Γ(S, ⊤)ˣ}
    (lev' : Level P' M ze) : ∃ lev : Level P M ze, ∀ i, lev.pt i ≫ φ.hom = levelBasis lev' hg' i := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨x, hx⟩ : ∃ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), ∀ i, x i ≫ φ.hom = levelBasis lev' hg' i :=
    ⟨fun i => levelBasis lev' hg' i ≫ φ.inv, fun i => by simp⟩
  have ht : ∀ i, x i ^ M = 1 := fun i => by
    rw [← comp_pow_eq_one_iff φ, hx]; exact basis_pow lev' hg' i
  have hc : ∀ {T : Over S} (h : T ⟶ baseOver S) (a : Fin (2 * P.g) → ℕ),
      linComb (fun i => h ≫ x i) a ≫ φ.hom = linComb (fun i => h ≫ levelBasis lev' hg' i) a := fun h a => by
    rw [ThetaPtDet.linComb_comp]
    exact congrArg (linComb · a) (funext fun i => by rw [Category.assoc, hx])
  refine ⟨⟨x, lev'.prim, ht, fun K _ _ s c c' e => ?_, fun K _ _ s y hy => ?_, fun i j => ?_⟩, hx⟩
  · exact basis_indep lev' hg' K s c c' ((hc _ _).symm.trans ((congrArg (· ≫ φ.hom) e).trans (hc _ _)))
  · obtain ⟨c, e⟩ := basis_span lev' hg' K s (y ≫ φ.hom) ((comp_pow_eq_one_iff φ y M).2 hy)
    exact ⟨c, (cancel_mono φ.hom).1 ((hc _ _).trans e)⟩
  · rw [← weilIs_iso_iff hL.globalFns hL.cube P P' φ w hw M _ _ (ht i) (ht j), hx, hx]
    exact basis_pairing lev' hg' i j

end GlobalTheory.LevelPullIso

open GlobalTheory.LevelPullIso in

theorem GlobalTheory.exists_level_thetaPt_of_polIso : Out.Laws → ∀ (g N' : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P P' : Out.PolAV (Sp K)) (hg : P.g = g) (hg' : P'.g = g) (φ : P.A ≅ P'.A), IsPolIso P P' φ → ∀ (ze : Γ(Sp K, ⊤)ˣ) (lev' : Out.Level P' (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P' N' (levelPoint lev' hg') v → ∃ lev : Out.Level P (N' ^ 2) ze, (∀ i, levelBasis lev hg i ≫ φ.hom = levelBasis lev' hg' i) ∧ Out.IsThetaPt P N' (levelPoint lev hg) v := by
  intro hL g N' K _ _ P P' hg hg' φ ⟨hφ, t⟩ ze lev' v hv
  subst hg
  have hw : LBIso P.L (P'.L.pull φ.hom.left) := LBIso.symm t
  obtain ⟨lev, hl⟩ := exists_level hL hg' φ hw lev'
  have hp : ∀ a, levelPoint lev rfl a ≫ φ.hom = levelPoint lev' hg' a := fun a => by
    rw [ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (Out.linComb · _) (funext hl)
  refine ⟨lev, hl, isThetaPt_of_iso φ hw (fun a => ThetaPtDet.levelPoint_pow lev rfl a) ?_⟩
  rw [funext hp]
  exact hv

end
