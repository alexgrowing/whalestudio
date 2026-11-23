import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.CechPic GlobalTheory.AmpleRigid
open scoped TensorProduct CategoryTheory.Obj
universe u

private theorem diag_fst {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_fst]
  rfl

private theorem diag_snd {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_snd]
  rfl

section

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}}
  {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'} {f : S' ⟶ S}

private theorem tensor_left_hom_ext_of_fst_snd {S : Scheme.{0}} {X Y : Over S} {W : Scheme.{0}} {u v : W ⟶ (X ⊗ Y).left}
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  have hw : u ≫ (X ⊗ Y).hom = v ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, h₁, Category.assoc]
  let U : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk u
  let V : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk v hw.symm
  have hUV : U = V := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₁)
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₂)
  exact congrArg CommaMorphism.left hUV

private theorem map_diag (m : GObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply tensor_left_hom_ext_of_fst_snd
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_fst, Category.id_comp]
    rw [Category.assoc, m.sq.1, key, Category.assoc, diag_fst, Category.comp_id]
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_snd, Category.id_comp]
    rw [Category.assoc, m.sq.2, key, Category.assoc, diag_snd, Category.comp_id]

private theorem pull_diag_cls (m : GObjMap o' o f) :
    pull m.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← map_diag m, pull_comp,
    ← cls_pull o.isLB _ (pull_isLB o.isLB m.φ₂),
    (cls_eq_iff (pull_isLB o.isLB m.φ₂) o'.isLB).2 (LBIso.symm m.pol)]

private theorem eq_at_point (hN : 3 ≤ N) (m m' : GObjMap o' o f) {K : Type} [Field K] [IsAlgClosed K] (j : Sp K ⟶ S') :
    pullback.fst o'.A.hom j ≫ m.φ = pullback.fst o'.A.hom j ≫ m'.φ := by
  have hA' : IsAbelianScheme ((Over.pullback j).obj o'.A) := by
    haveI := o'.ab.comm
    haveI := o'.ab.smooth
    haveI := o'.ab.proper
    haveI := o'.ab.geomConnected
    constructor
    · infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  have c := (isGrpPullback_pullback o'.A j).comp m.cart
  have c' := (isGrpPullback_pullback o'.A j).comp m'.cart
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample hA' c c' ?_ hN ?_ ?_
  · rw [pull_comp, pull_comp, pull_diag_cls m, pull_diag_cls m']
  · intro h0
    let ψ : ℚ →+* K := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) (j ≫ s')).hom.comp
      (algebraMap ℚ R)
    have e0 : ψ (N : ℚ) = ψ 0 := by rw [map_natCast, map_zero]; exact h0
    have e1 : (N : ℚ) = 0 := ψ.injective e0
    norm_cast at e1
    omega
  · intro Ω _ _ t x hx
    let β : R →+* Ω := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of Ω) ((t ≫ j) ≫ s')).hom
    have hβ : (t ≫ j) ≫ s' = spMap β := by
      simp only [spMap, β, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o'.geom Ω (t ≫ j) β hβ
    let x₁ := pushHom (isGrpPullback_pullback o'.A j) (Over.mk t) x
    have hx₁ : x₁ ^ N = 1 := by
      simp only [x₁]
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := (I.onto N (by omega) x₁).1 hx₁
    have hl : x.left ≫ pullback.fst o'.A.hom j = x₁.left := rfl
    have key : ∀ mm : GObjMap o' o f, x.left ≫ pullback.fst o'.A.hom j ≫ mm.φ =
        (toUnit (Over.mk (t ≫ j))).left ≫ f ≫ (o.eta y).left := by
      intro mm
      rw [← Category.assoc, hl, ← hy, ← hI y, Over.comp_left, Category.assoc, mm.eta y]
    rw [key m, key m']

end

theorem UpperTheory.Gal.G3.pRigid :
    Rigid := by
  intro p _ D R _ _ gb S S' s s' f hf N o o' m m'
  have hN : 3 ≤ (N : ℕ) := N.2.1
  obtain ⟨σ, hσmon, hσ⟩ := GlobalTheory.SiegRigid.exists_aut m.cart m'.cart
  have hid : σ.hom = 𝟙 o'.A := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre GlobalTheory.laws_without_cohomology.1 o'.A o'.ab σ.hom
      (IsMonHom.one_hom σ.hom) ?_
    intro t
    let K := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫
      S'.fromSpecResidueField t
    refine ⟨Sp K, pullback o'.A.hom j, j, pullback.fst o'.A.hom j, pullback.snd o'.A.hom j,
      IsLocalRing.closedPoint K, ?_, IsPullback.of_hasPullback _ _, ?_⟩
    · exact Scheme.fromSpecResidueField_apply t _
    · apply m'.cart.1.hom_ext
      · rw [Category.assoc, hσ, eq_at_point hN m m' j]
      · rw [Category.assoc, Over.w]
  rw [← hσ, hid, Over.id_left, Category.id_comp]
