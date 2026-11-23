import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LieEigenbasis

theorem existsUnique_sum_single {k : Type} [Field k] {n N : ℕ} (s : Fin N → Fin n)
    (hs : Function.Injective s) (c : Fin n → k) (hc : ∀ i, i ∉ Set.range s → c i = 0) :
    ∃! d : Fin N → k, c = ∑ j, d j • (Pi.single (s j) 1 : Fin n → k) := by
  have h : ∀ (d : Fin N → k) (j : Fin N),
      (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) (s j) = d j := fun d j => by
    simp [Finset.sum_apply, Pi.single_apply, hs.eq_iff]
  refine ⟨fun j => c (s j), funext fun i => ?_, fun d hd => funext fun j => by rw [hd, h]⟩
  by_cases hi : i ∈ Set.range s
  · obtain ⟨j, rfl⟩ := hi
    rw [h]
  · rw [hc i hi, Finset.sum_apply]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have : i ≠ s j := fun e => hi ⟨j, e.symm⟩
    simp [this]

end GlobalTheory.LieEigenbasis

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap) in

theorem GlobalTheory.lieMult_of_eigenbasis : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}) := by
  intro k _ O _ G _ act n v τs _ hv hτ τ
  have := act.hom
  obtain ⟨x, hx, hxv⟩ := Chart.chart_of_basis hv
  have hxv' : ∀ j, v j = tvec (x := x) (Pi.single j 1) := hxv
  have hdiag : ∀ a i, tmap hx (act.act a) (Pi.single i 1) = τs i a • (Pi.single i 1 : Fin n → k) :=
    fun a i => (Chart.tvec_eig_iff hx _ _ _).1 (by
      rw [← hxv']; exact Over.OverMorphism.ext (hτ i a))
  have hmap : ∀ a c i, tmap hx (act.act a) c i = τs i a * c i := fun a c i => by
    conv_lhs => rw [← Finset.univ_sum_single c]
    have : ∀ j, (Pi.single j (c j) : Fin n → k) = c j • (Pi.single j 1 : Fin n → k) := fun j => by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    simp only [this, map_sum, map_smul, hdiag]
    simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  let N := Nat.card {i // τs i = τ}
  let q : Fin N ≃ {i // τs i = τ} := (Finite.equivFin _).symm
  let s : Fin N → Fin n := fun j => (q j).1
  have hs : Function.Injective s := Subtype.val_injective.comp q.injective
  have hpr : ∀ d : Fin N → k, prodPts d (fun j => v (s j)) =
      tvec (x := x) (∑ j, d j • (Pi.single (s j) 1 : Fin n → k)) := fun d => by
    have ht : ∀ j, Chart.IsTan (v (s j)) := fun j => (Chart.isTan_iff _).2 (hv.1 _)
    obtain ⟨h, e⟩ := Chart.prodPts_tan hx d (fun j => v (s j)) ht
    refine (Chart.tcoord_spec hx _ h).trans ?_
    change tvec (x := x) _ = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [Chart.tcoord_eq hx _ (ht j) _ (hxv _)]
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ G) ≃* (epsR k ⟶ G) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl G)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ G).left = η[G].left := Category.id_comp _
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, w ≫ act.act a = Chart.spMap (scaleD (τ a)) ≫ w)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.OverMorphism.ext_iff, Over.comp_left, Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) N ⟨fun j => v (s j), fun j => ⟨hv.1 _, fun a => ?_⟩, ?_⟩
  · have := hτ (s j) a
    rw [(q j).2] at this
    exact Over.OverMorphism.ext this
  · rintro w ⟨hw, hw'⟩
    have ht := (Chart.isTan_iff _).2 hw
    obtain ⟨c, rfl⟩ : ∃ c, w = tvec (x := x) c := ⟨_, Chart.tcoord_spec hx w ht⟩
    refine (existsUnique_congr fun d => ?_).1
      (LieEigenbasis.existsUnique_sum_single s hs c fun i hi => ?_)
    · refine Iff.trans ?_ (Chart.isLieComb_iff d _ _).symm
      rw [hpr]
      exact ⟨fun h => by rw [← h], Chart.tvec_inj hx⟩
    · by_contra hc
      refine hi ⟨q.symm ⟨i, RingHom.ext fun a => ?_⟩, by simp [s]⟩
      have := congrFun ((Chart.tvec_eig_iff hx _ _ _).1 (hw' a)) i
      rw [hmap] at this
      exact mul_right_cancel₀ hc this
