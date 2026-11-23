import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentLinearCombinationIsTangent
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SecJet.ModelLat

theorem eq_tanComb {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m : ℕ} {c : Fin m → R}
    {v : Fin m → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) : w = tanComb c v := by
  obtain ⟨u, hu, rfl⟩ := h
  unfold tanComb
  congr 2
  exact funext fun i => Over.OverMorphism.ext (hu i)

theorem dualMapR_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  refine (spMap_comp_spMap _ _).trans ?_
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [Chart.dualMapR]

theorem lift_sum {R K : Type} [CommRing R] [CommRing K] {g : R →+* K} {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj G]
    [GrpObj A] [IsCommMonObj A] {φ : A.left ⟶ G.left} (hφ : IsGrpPullback A G (spMap g) φ) {n m : ℕ}
    {v : Fin n → (epsR K ⟶ A)} (hv : ∀ i, IsTangent (v i)) (a : Fin m → R) (x : Fin m → Fin n → K)
    (hx : ∀ i, ∃ Y : epsR R ⟶ G, IsTangent Y ∧ IsVecOver g φ Y (tanComb (x i) v)) :
    ∃ Y : epsR R ⟶ G, IsTangent Y ∧ IsVecOver g φ Y (tanComb (∑ i, g (a i) • x i) v) := by
  choose Y hY hY' using hx
  refine ⟨tanComb a Y, isTangent_tanComb R G m Y a hY, ?_⟩
  obtain ⟨-, -, hcomp, -⟩ := LieComb.lieComb_algebra K A n v hv
  have h := hcomp m x (fun i => tanComb (x i) v) (fun i => g (a i)) _ (fun i => isLieComb_tanComb _ _)
    (isLieComb_tanComb _ _)
  rw [← eq_tanComb h]
  exact (lieComb_baseChange R K g G A φ hφ m Y _ a _ _ hY' (isLieComb_tanComb a Y)).2 (isLieComb_tanComb _ _)

def liftable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj G]
    [GrpObj A] [IsCommMonObj A] {φ : A.left ⟶ G.left} (hφ : IsGrpPullback A G (spMap (algebraMap R K)) φ) {n : ℕ}
    {v : Fin n → (epsR K ⟶ A)} (hv : ∀ i, IsTangent (v i)) : Submodule R (Fin n → K) where
  carrier := {z | ∃ Y : epsR R ⟶ G, IsTangent Y ∧ IsVecOver (algebraMap R K) φ Y (tanComb z v)}
  zero_mem' := by simpa using lift_sum hφ hv (m := 0) ![] ![] (fun i => i.elim0)
  add_mem' := fun {x y} hx hy => by
    simpa using lift_sum hφ hv ![1, 1] ![x, y] (fun i => by fin_cases i; exacts [hx, hy])
  smul_mem' := fun a x hx => by
    simpa using lift_sum hφ hv ![a] ![x] (fun i => by fin_cases i; exact hx)

end GlobalTheory.SecJet.ModelLat

namespace GlobalTheory.SecJet

open ModelLat

theorem exists_tangent_of_mem_latBC : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (K'' : Type) [Field K''] [NumberField K''] [Algebra K K''] (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (v' : Fin F.P₀.g → (epsR K'' ⟶ P.A)), Hypotheses2 → GlobalTheory.IsPolFibre (algebraMap K K'') F.P₀ P ψ → IsModel w → (∀ k, GlobalTheory.IsVecOver (algebraMap K K'') ψ (F.v k) (v' k)) → ∀ z ∈ latBC K'' F.lieLat, ∃ Y : epsR (𝓞 K'') ⟶ AA, IsTangent Y ∧ GlobalTheory.IsVecOver (algebraMap (𝓞 K'') K'') φ Y (tanComb z v') := by
  intro K _ _ F K'' _ _ _ P ψ AA _ _ φ MM N w v' hP hψ hM hv
  obtain ⟨-, -, -, hφ, ⟨G, _, j, φ₀, hG, hj, -, rfl, hφ₀⟩, -⟩ := hM
  have : IsCommMonObj P.A := P.isAb.comm
  have hvt : ∀ i, IsTangent (v' i) := fun i => (hv i).isTangent hψ.2.1 (F.basis.1 i)
  let b := algebraMap (𝓞 K) (𝓞 K'')
  have hb : (algebraMap (𝓞 K'') K'').comp b = (algebraMap K K'').comp (algebraMap (𝓞 K) K) := by
    ext; rfl
  have h' := isGrpPullback_pullback F.G (spMap b)
  have n' : IsGrpPullback P.A F.G (spMap (algebraMap (𝓞 K'') K'') ≫ spMap b) (ψ ≫ F.φ) :=
    (hψ.2.1.comp F.fib).congr (by rw [spMap_comp_spMap, spMap_comp_spMap, hb]) rfl
  have hw : (ψ ≫ F.φ) ≫ F.G.hom = (P.A.hom ≫ spMap (algebraMap (𝓞 K'') K'')) ≫ spMap b :=
    n'.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := h'.1.lift_fst _ _ hw
  have hφ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ hw)
  have : IsMonHom (𝟙 P.A) := inferInstance
  obtain ⟨E, ⟨hE, hE'⟩, -⟩ := hP.p22.fractionField_of_isGrpPullback (IsSemiAbelian.pullback _ F.G F.semi) hG hφ' hφ₀
    (𝟙 P.A)
  rw [Over.id_left, Category.id_comp] at hE'
  suffices h : latBC K'' F.lieLat ≤ liftable hφ hvt from h
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, hc, rfl⟩
  change (fun i => algebraMap K K'' (c i)) ∈ liftable hφ hvt
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨u, hu, x, hx, hc⟩ := hc
    obtain ⟨u', hu', -⟩ := existsUnique_isVecOver (A' := (Over.pullback (spMap b)).obj F.G) (f := b) h'.1 u
    refine ⟨(u' ≫ E) ≫ j, GrpTangent.isTangent_comp (GrpTangent.isTangent_comp (hu'.isTangent h' hu) E) j, ?_⟩
    have h₁ := (lieComb_baseChange K K'' _ _ _ ψ hψ.2.1 _ F.v x c v' _ hv hc).2 (isLieComb_tanComb _ _)
    obtain ⟨y, hy, -⟩ := existsUnique_isVecOver hφ'.1 u'
    have h₂ : y = tanComb (fun i => algebraMap K K'' (c i)) v' := by
      refine Over.OverMorphism.ext (n'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
      unfold IsVecOver at hx hu' hy
      have a₁ : y.left ≫ ψ ≫ F.φ = spMap (Chart.dualMapR ((algebraMap (𝓞 K'') K'').comp b)) ≫ u.left := by
        rw [← e₁, ← Category.assoc, hy, Category.assoc, hu', ← dualMapR_comp, Category.assoc]
      rw [a₁, hb, ← dualMapR_comp, Category.assoc, ← hx, ← Category.assoc, ← h₁, Category.assoc]
    rw [← h₂]
    unfold IsVecOver at hy ⊢
    rw [hE', ← Category.assoc, ← Category.assoc, hy]
    simp only [Over.comp_left, Category.assoc]
  | zero =>
    convert (liftable hφ hvt).zero_mem using 1
    ext i
    simp
  | add x y _ _ hx hy =>
    convert (liftable hφ hvt).add_mem hx hy using 1
    ext i
    simp
  | smul t x _ hx =>
    have := (liftable hφ hvt).smul_mem (b t) hx
    convert this using 1
    ext i
    rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl

end GlobalTheory.SecJet
