import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumProjSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectOddLevelRigid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBCTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HTUniv.Nat

open GlobalTheory.CechPic GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem pull_cls_diag {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'}
    {f : S' ⟶ S} (mp : ObjMap o' o f) :
    pull mp.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  have hs := mp.sq
  have e : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ mp.φ₂ = mp.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
    have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o.A) (𝟙 o.A))
    have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o.A) (𝟙 o.A))
    have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 o'.A) (𝟙 o'.A))
    have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 o'.A) (𝟙 o'.A))
    simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst o.A o.A).left = (_ ≫ _) ≫ (fst o.A o.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
    · show (_ ≫ _) ≫ (snd o.A o.A).left = (_ ≫ _) ≫ (snd o.A o.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp
  have h1 : pull mp.φ₂ (cls o.P o.isLB) = cls o'.P o'.isLB :=
    ((cls_eq_iff o'.isLB (pull_isLB o.isLB mp.φ₂)).2 mp.pol).symm
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← e, pull_comp, h1]

theorem phi_eq (hN : 3 ≤ N) (hNp : N.Coprime p) {k : Type} [Field k] [IsAlgClosed k] {t : Sp k ⟶ Sp R}
    (o₀ : Obj b N t) {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {z : Sp k ⟶ S}
    {φ φ' : o₀.A.left ⟶ o.A.left} (h : IsGrpPullback o₀.A o.A z φ) (h' : IsGrpPullback o₀.A o.A z φ')
    (hc : pull φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      pull φ' (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)))
    (he : ∀ y, (o₀.eta y).left ≫ φ = z ≫ (o.eta y).left) (he' : ∀ y, (o₀.eta y).left ≫ φ' = z ≫ (o.eta y).left) :
    φ = φ' := by
  have hN0 : 0 < N := by omega
  have hNK : (N : k) ≠ 0 := by
    have hu := (b.unit N hNp).map (Spec.preimage t).hom
    rw [map_natCast] at hu
    exact hu.ne_zero
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample o₀.ab h h' hc hN hNK fun Ω _ _ x y hy => ?_
  obtain ⟨I, hI⟩ := o₀.geom Ω x (Spec.preimage (x ≫ t)).hom (Spec.map_preimage _).symm
  obtain ⟨a, ha⟩ := (I.onto N hN0 hNp y).1 hy
  rw [← ha, ← hI a]
  simp only [Over.comp_left, Category.assoc, he, he']

theorem corr_of_isBC {R₀ R₁ R₂ : Type} [CommRing R₀] [CommRing R₁] [CommRing R₂] [Algebra R₀ R₁]
    {I₀ : Ideal R₀} {I₁ : Ideal R₁} {I₂ : Ideal R₂} {κ₀ : DividedPowers I₀} {κ₁ : DividedPowers I₁}
    {κ₂ : DividedPowers I₂} {S₀ S₁ S₂ : Scheme.{0}} {t₀ : S₀ ⟶ Sp R₀} {t₁ : S₁ ⟶ Sp R₁} {t₂ : S₂ ⟶ Sp R₂}
    {A₀ : Over S₀} {A₁ : Over S₁} {A₂ : Over S₂} [GrpObj A₀] [GrpObj A₁] [GrpObj A₂] {b₁ : S₁ ⟶ S₀}
    {b₂ : S₂ ⟶ S₁} {φ₁ : A₁.left ⟶ A₀.left} {φ₂ : A₂.left ⟶ A₁.left} {σ : R₁ →+* R₂}
    {m : GrpMor κ₀ t₀ A₀ κ₁ t₁ A₁ (algebraMap R₀ R₁) b₁ φ₁} (hm : m.IsBC)
    (M : GrpMor κ₁ t₁ A₁ κ₂ t₂ A₂ σ b₂ φ₂) {h : Crys κ₁ t₁ A₁} {h' : Crys κ₂ t₂ A₂}
    (e : ∀ q, h' (M.pull (m.pull q)) = σ (h (m.pull q))) : M.Corr h h' := by
  intro q
  obtain ⟨w, rfl⟩ := hm.2 q
  induction w with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul r q =>
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, map_smul, map_smul, e, smul_eq_mul, smul_eq_mul, map_mul]

set_option maxHeartbeats 1000000 in

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t), ∀ (d : ℕ) (s : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)) (c : (Fin d → k) →ₗ[k] k) (s' : Sp (DualNumber k) ⟶ Sp R) (o' : GlobalTheory.UPel.HT.Obj b N s') (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (n : GlobalTheory.UPel.HT.ObjMap o' o (spMap (TrivSqZeroExt.map c).toRingHom)) (x : HdR o₀.A) (y : primDR o₀.A →ₗ[k] (Fin d → k)), GlobalTheory.FODef.IsFilLiftV m.cart x y → IsFilLift m'.cart x (c ∘ₗ y) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ d s o m c s' o' m' n x y hxy
  obtain ⟨dd, hdd, edd⟩ := hxy
  let σ : TrivSqZeroExt k (Fin d → k) →+* DualNumber k := (TrivSqZeroExt.map c).toRingHom
  have hz : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap σ =
      spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom := by
    rw [← Cris.spMap_comp]
    congr 1
    ext a <;> simp [σ]

  have hrig : m'.φ ≫ n.φ = m.φ := by
    refine (phi_eq hN hNp o₀ o ((m'.cart.comp n.cart).congr hz rfl) m.cart ?_ ?_ m.eta).symm.symm
    · rw [pull_comp, pull_cls_diag n, pull_cls_diag m', pull_cls_diag m]
    · intro y
      rw [← Category.assoc, m'.eta y, Category.assoc, n.eta y, ← Category.assoc, hz]

  have hdp : (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))).IsDPMorphism (epsDP k) σ := by
    unfold epsDP
    refine isDPMorphism_sqDP _ _ σ fun a ha => ?_
    have ha' : a.fst = 0 := ha
    change (σ a).fst = 0
    simp [σ, ha']
  have M : GrpMor (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) (spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom)
      o₀.A (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A σ (𝟙 _) (Over.Hom.left (𝟙 o₀.A)) :=
    GrpMor.of_hom hdp hz.symm (𝟙 o₀.A)
  have hBC : (constMor o₀.A).IsBC := GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k k o₀.A o₀.ab _ (constMor o₀.A)
  have hBCV : (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A).IsBC :=
    GlobalTheory.SqZeroCrys.isBC_trivSqZeroExt k (Fin d → k) o₀.A o₀.ab _ _
  let d' : Crys (epsDP k) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A :=
    hBC.bcMap x + (TrivSqZeroExt.inr (1 : k) : DualNumber k) • hBC.bcMap (c ∘ₗ y)
  have ed' : ∀ q, d' ((constMor o₀.A).pull q) = TrivSqZeroExt.inl (x q) + TrivSqZeroExt.inr (c (y q)) := by
    intro q
    have e1 := (hBC.corr_iff (h := x)).2 rfl q
    have e2 := (hBC.corr_iff (h := c ∘ₗ y)).2 rfl q
    simp only [d', LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hMc : M.Corr dd d' := corr_of_isBC hBCV M fun q => by
    rw [GrpMor.pull_pull (GlobalTheory.FODef.constMorV k (Fin d → k) o₀.A) M (constMor o₀.A) (fun _ => by
      ext <;> simp [σ, TrivSqZeroExt.algebraMap_eq_inl]) (by simp) q, ed', edd q]
    ext <;> simp [σ]
  have Nm : GrpMor (dp0 _) (𝟙 _) o.A (dp0 _) (𝟙 _) o'.A σ (spMap σ) n.φ :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) n.cart
  have hNc := crysToDR_corr (divided₂ (GlobalTheory.FODef.sqZero k (Fin d → k))) m.cart m'.cart M Nm
    (by rw [hrig]; simp) hMc
  refine ⟨d', ?_, fun q => ?_⟩
  · letI : Algebra (TrivSqZeroExt k (Fin d → k)) (DualNumber k) := σ.toAlgebra
    obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (TrivSqZeroExt k (Fin d → k)) o.A o.ab
    have hF := (GlobalTheory.abelianDeRham.2.2.1 _ o.A g o.ab hg (DualNumber k) o'.A n.φ n.cart).2
    exact mem_Fil_of_corr (hφ := n.cart) hF hNc hdd
  · rw [ed']
    rfl

end GlobalTheory.HTUniv.Nat
