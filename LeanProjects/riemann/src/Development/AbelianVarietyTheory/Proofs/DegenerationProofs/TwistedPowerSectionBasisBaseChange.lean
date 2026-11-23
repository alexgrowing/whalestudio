import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasWtZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.BasisBaseChange

open GlobalTheory.FieldBaseChange

section Algebra

variable {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem basis_map_of_basis {φ : R →+* R'} (f : M →ₛₗ[φ] M') {I J : Type} [Fintype I] [Fintype J]
    (b : J → M) (β : I → M) (hb : ∀ s, ∃! a : J → R, s = ∑ j, a j • b j)
    (hβ : ∀ s, ∃! a : I → R, s = ∑ i, a i • β i)
    (hf : ∀ s, ∃! a : J → R', s = ∑ j, a j • f (b j)) (s : M') : ∃! a : I → R', s = ∑ i, a i • f (β i) := by
  classical
  choose u hu _ using fun i => hb (β i)
  choose w hw _ using fun j => hβ (b j)
  have huw : ∀ i i', ∑ j, u i j * w j i' = if i = i' then 1 else 0 := fun i => by
    have h1 : β i = ∑ i', (∑ j, u i j * w j i') • β i' := by
      conv_lhs => rw [hu i]
      simp only [Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.smul_sum, ← hw j]
    have h2 : β i = ∑ i', (if i = i' then (1 : R) else 0) • β i' := by simp
    exact congrFun ((hβ (β i)).unique h1 h2)
  have fβ : ∀ a : I → R', ∑ i, a i • f (β i) = ∑ j, (∑ i, a i * φ (u i j)) • f (b j) := fun a => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.smul_sum, hu i, map_sum]
    simp only [map_smulₛₗ, ← hu i]
  have fb : ∀ c : J → R', ∑ j, c j • f (b j) = ∑ i, (∑ j, c j * φ (w j i)) • f (β i) := fun c => by
    simp only [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.smul_sum, hw j, map_sum]
    simp only [map_smulₛₗ, ← hw j]
  have back : ∀ (a : I → R') i', ∑ j, (∑ i, a i * φ (u i j)) * φ (w j i') = a i' := fun a i' => by
    simp only [Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← map_sum, huw]
    simp [apply_ite φ]
  obtain ⟨c, hc, hcu⟩ := hf s
  refine ⟨_, hc.trans (fb c), fun a ha => funext fun i => ?_⟩
  rw [← hcu _ (ha.trans (fβ a)), back]

end Algebra

theorem isLin_iff {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp R) {H : LB Y} {I : Type} [Fintype I]
    (s : I → SecOver p H) (a : I → R) (t : SecOver p H) : IsLin p s a t ↔ t = ∑ i, a i • s i := by
  have e : ∀ l, chartFun p H l (∑ i, a i • s i) = ∑ i, a i • chartFun p H l (s i) := fun l =>
    (map_sum (chartLin p H l) _ _).trans rfl
  exact ⟨fun h => SecOver.ext _ _ fun l => (h l).trans (e l).symm, fun h l => (congrArg (chartFun p H l) h).trans (e l)⟩

theorem basis_of_isPullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {A : Over (Sp R)}
    {L : LB A.left} (hL : L.IsLB) {K : Type} [Fintype K] (ψ : K → (A.left ⟶ A.left)) (ε : K → ℤ) {m : ℕ}
    (b : Fin m → SecOver A.hom (LB.LinComb L ψ ε))
    (hb : IsSecBasis (T := Over.mk (spMap φ)) (A := A) _
      (fun i => DVR.pullSec L ψ ε (b i) (snd (Over.mk (spMap φ)) A).left))
    {B : Scheme.{0}} {pB : B ⟶ Sp R'} {π : B ⟶ A.left} (H : IsPullback π pB A.hom (spMap φ))
    {ψ' : K → (B ⟶ A.left)} (hψ : ∀ k, ψ' k = π ≫ ψ k) (s : SecOver pB (LB.LinComb L ψ' ε)) :
    ∃! a : Fin m → R', s = ∑ i, a i • pullOver L ε H.w hψ (b i) := by
  let T : Over (Sp R) := Over.mk (spMap φ)
  let p : (T ⊗ A).left ⟶ Sp R' := (fst T A).left
  let q : (T ⊗ A).left ⟶ A.left := (snd T A).left
  have H' : IsPullback q p A.hom (spMap φ) := (IsPullback.of_hasPullback (spMap φ) A.hom).flip
  let e := H.isoIsPullback _ _ H'
  have e1 : e.hom ≫ q = π := H.isoIsPullback_hom_fst _ _ H'
  have e2 : e.hom ≫ p = pB ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_hom_snd _ _ H'
  have e3 : e.inv ≫ π = q := H.isoIsPullback_inv_fst _ _ H'
  have e4 : e.inv ≫ pB = p ≫ Spec.map (CommRingCat.ofHom (RingHom.id R')) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]; exact H.isoIsPullback_inv_snd _ _ H'
  have f1 : ∀ k, ψ' k = e.hom ≫ (q ≫ ψ k) := fun k => by rw [hψ, ← e1, Category.assoc]
  have f2 : ∀ k, q ≫ ψ k = e.inv ≫ ψ' k := fun k => by rw [hψ, ← e3, Category.assoc]
  let F := pullOver L ε e2 (φ := fun k => q ≫ ψ k) f1
  let G := pullOver L ε e4 (φ' := fun k => q ≫ ψ k) f2
  let b' : Fin m → SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε) := fun i => DVR.pullSec L ψ ε (b i) q
  have FG : ∀ t, F (G t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver e4 f2 _ _ hJ, Category.assoc, e.hom_inv_id, Category.comp_id]
  have GF : ∀ t, G (F t) = t := fun t => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e4 f2 _ _ hJ, sval_pullOver e2 f1 _ _ hJ, Category.assoc, e.inv_hom_id, Category.comp_id]
  have Fb : ∀ i, F (b' i) = pullOver L ε H.w hψ (b i) := fun i => sec_ext' hL fun y J hJ => by
    rw [sval_pullOver e2 f1 _ _ hJ, sval_pullOver H.w hψ _ _ hJ]
    exact (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.assoc, e1])
  have hb' : ∀ t : SecOver p (LB.LinComb L (fun k => q ≫ ψ k) ε), ∃! a : Fin m → R', t = ∑ i, a i • b' i := by
    intro t
    obtain ⟨r, hr, hu⟩ := hb t
    have e : ∀ i, (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i)) = r i := fun i => Iso.hom_inv_id_apply _ _
    refine ⟨fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (r i), (isLin_iff p _ _ _).1 fun j => ?_,
      fun a ha => ?_⟩
    · refine (hr j).trans (Finset.sum_congr rfl fun i _ => ?_)
      simp only [constFn, e]
      rfl
    · have := hu (fun i => (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (a i)) ((isLin_iff p _ _ _).2 ha)
      funext i
      rw [← this]
      exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R')) (a i)).symm
  have Fs : ∀ a : Fin m → R', F (∑ i, a i • b' i) = ∑ i, a i • pullOver L ε H.w hψ (b i) := fun a => by
    simp only [map_sum, map_smulₛₗ, Fb, RingHom.id_apply]
  obtain ⟨a, ha, hu⟩ := hb' (G s)
  refine ⟨a, ?_, fun a' ha' => hu a' ?_⟩
  · show s = _
    rw [← Fs, ← ha, FG]
  · show G s = _
    rw [ha', ← Fs, GF]

theorem basis_pullback : DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (N : ℕ), 1 ≤ N → ∀ (α : D.X) (R' : Type) [CommRing R'] (φ : R →+* R') (B : Scheme.{0}) (pB : B ⟶ Sp R') (π : B ⟶ D.P.A.left), IsPullback π pB D.P.A.hom (spMap φ) → ∀ (I : Type) [Fintype I] (β : I → D.SecB N α), IsBasisB D β → ∀ b : LB.Sec (LB.LinComb D.P.L (fun i => π ≫ D.famφB α i) (DegPre.famε N)), ∃! a : I → R', IsLin pB (fun i => DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π) a b := by
  intro hT R _ _ _ _ D N hN α R' _ φ B pB π H I _ β hβ s
  have hL := D.P.isLB
  obtain ⟨m, b, -, hb⟩ := hT R D N hN α
  have H₀ : IsPullback (𝟙 D.P.A.left) D.P.A.hom D.P.A.hom (spMap (RingHom.id R)) := by
    have : spMap (RingHom.id R) = 𝟙 _ := by simp [spMap]
    rw [this]
    exact IsPullback.id_horiz _
  have hψ₀ : ∀ k, D.famφB α k = 𝟙 _ ≫ D.famφB α k := fun k => (Category.id_comp _).symm
  have h0 := basis_of_isPullback (RingHom.id R) hL (D.famφB α) (DegPre.famε N) b
    (hb R (RingHom.id R) _ fun _ _ => rfl) H₀ hψ₀
  have e0 : ∀ i, pullOver D.P.L (DegPre.famε N) H₀.w hψ₀ (b i) = b i := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H₀.w hψ₀ _ _ hJ).trans (by rw [Category.comp_id])
  simp only [e0] at h0
  have hψ : ∀ k, (fun i => π ≫ D.famφB α i) k = π ≫ D.famφB α k := fun _ => rfl
  have h1 := basis_of_isPullback φ hL (D.famφB α) (DegPre.famε N) b (hb R' φ _ fun _ _ => rfl) H hψ
  have h2 := basis_map_of_basis (pullOver D.P.L (DegPre.famε N) H.w hψ) b β h0
    (fun t => (existsUnique_congr fun a => isLin_iff D.P.A.hom β a t).1 (hβ t)) h1 s
  have e1 : ∀ i, pullOver D.P.L (DegPre.famε N) H.w hψ (β i) =
      DVR.pullSec D.P.L (D.famφB α) (DegPre.famε N) (β i) π := fun i => sec_ext' hL fun y J hJ =>
    (sval_pullOver H.w hψ _ _ hJ).trans (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ y hJ).symm
  simp only [e1] at h2
  exact (existsUnique_congr fun a => isLin_iff pB _ a s).2 h2

end GlobalTheory.ZH.BasisBaseChange
end
