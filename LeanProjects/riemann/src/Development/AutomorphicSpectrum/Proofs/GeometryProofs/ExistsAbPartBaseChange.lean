import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC

open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

variable {L L' : Type} [Field L] [Field L']

def torusExtBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := qB_flat f T.q T.q_flat
    q_surjective := qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (qB_sq f T.q) T.q_quasiCompact
    i := iB f T.X T.i
    i_hom := iB_hom f T.X T.i
    isKernel := iB_isKernel f T.X T.q T.i T.isKernel }

theorem torusRing_hom_ext {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (g h : torusRing ZU X ⟶ CommRingCat.of A)
    (w : ∀ χ : X, g.hom (AddMonoidAlgebra.single χ 1) = h.hom (AddMonoidAlgebra.single χ 1)) : g = h := by
  apply CommRingCat.hom_ext
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) w
  have hb : b = ((b.down : ℤ) : ULift ℤ) := by ext; simp
  have e : ∀ (n : ℤ) (r : torusRing ZU X ⟶ CommRingCat.of A),
      r.hom (AddMonoidAlgebra.single 0 ((n : ℤ) : ULift ℤ)) = (n : A) := fun n r => by
    have : (AddMonoidAlgebra.single (0 : X) ((n : ℤ) : ULift ℤ) : AddMonoidAlgebra (ULift ℤ) X) = (n : AddMonoidAlgebra (ULift ℤ) X) := by
      rw [AddMonoidAlgebra.intCast_def]
    exact (congrArg r.hom this).trans (map_intCast r.hom n)
  rw [hb, e, e]

def toZTorus (S : Scheme.{0}) (X : Type) [AddCommGroup X] : (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

theorem hT_toZTorus {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    hT f X ≫ toZTorus S X = toZTorus S' X :=
  pullback.lift_fst _ _ _

theorem splitTorus_left_ext {S T : Scheme.{0}} {X : Type} [AddCommGroup X] {a b : T ⟶ (splitTorus S X).left}
    (h₁ : a ≫ toZTorus S X = b ≫ toZTorus S X) (h₂ : a ≫ (splitTorus S X).hom = b ≫ (splitTorus S X).hom) : a = b :=
  pullback.hom_ext h₁ h₂

theorem point_hT {X : Type} [AddCommGroup X] (e : L →+* L') {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) : t'.left ≫ hT (spMap e) X = t.left := by
  have key : (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) = (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) := by
    have p : Spec.preimage (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) =
        Spec.preimage (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) :=
      torusRing_hom_ext _ _ fun χ => (h χ).symm
    have := congrArg Spec.map p
    rwa [Spec.map_preimage, Spec.map_preimage] at this
  refine splitTorus_left_ext ?_ ?_
  · rw [Category.assoc, hT_toZTorus]; exact key
  · rw [Category.assoc, hT_snd, ← Category.assoc, Over.w t', Over.w t]; rfl

def eBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : (torusExtBC f T).B ≅ (Over.pullback f).obj B' :=
  (Over.pullback f).mapIso e

theorem eBC_hom (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    [GrpObj B'] (e : T.B ≅ B') (h : letI := T.grpB; IsMonHom e.hom) :
    letI := (torusExtBC f T).grpB; IsMonHom (eBC f T e).hom := by
  letI := T.grpB
  haveI := h
  exact (inferInstance : IsMonHom ((Over.pullback f).map e.hom))

theorem map_left_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem quot_bc (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : ((torusExtBC f T).q ≫ (eBC f T e).hom).left ≫ pullback.fst B'.hom f =
      pullback.fst G.hom f ≫ (T.q ≫ e.hom).left := by
  change ((Over.pullback f).map T.q ≫ (Over.pullback f).map e.hom).left ≫ _ = _
  rw [← Functor.map_comp]
  exact map_left_fst f _

theorem iB_point (e : L →+* L') {G : Over (Sp L)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp L) X ⟶ G) {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) :
    (t' ≫ iB (spMap e) X i).left ≫ pullback.fst G.hom (spMap e) = (t ≫ i).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, iB_h, ← Category.assoc, point_hT e a t' t h]

theorem torusOver_torusExtBC (e : L →+* L') {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusOver e T (torusExtBC (spMap e) T) (pullback.fst G.hom (spMap e)) := by
  letI := T.addCommGroup
  exact ⟨AddEquiv.refl _, fun A _ a t' t h => iB_point e T.i a t' t h⟩

theorem lbIso_square {X X' Y Y' : Scheme.{0}} {φ : X' ⟶ X} {β : Y' ⟶ Y} {ψ : X ⟶ Y} {ψ' : X' ⟶ Y'}
    (hc : ψ' ≫ β = φ ≫ ψ) {A : LB X} {A' : LB X'} {B : LB Y} {B' : LB Y'} (hB : B.IsLB) (hA' : A'.IsLB)
    (hB' : B'.IsLB) (hA : A.IsLB) (a : LBIso A' (A.pull φ)) (b : LBIso B' (B.pull β)) (h : LBIso A (B.pull ψ)) :
    LBIso A' (B'.pull ψ') := by
  have a1 : LBIso (A.pull φ) ((B.pull β).pull ψ') :=
    LBIso.chartPull (chartPullPull A φ φ rfl)
      (chartPullLinComb B β (fun _ : PUnit => ψ') (fun _ => ψ) (fun _ => 1) φ (fun _ => hc)) h
  have a2 : LBIso (B'.pull ψ') ((B.pull β).pull ψ') :=
    LBIso.chartPull (chartPullPull _ ψ' ψ' rfl) (chartPullPull _ ψ' ψ' rfl) b
  have l1 := pull_isLB hA φ
  have l2 := pull_isLB (pull_isLB hB β) ψ'
  have l3 := pull_isLB hB' ψ'
  exact LBIso.trans hA' l1 l3 a (LBIso.trans l1 l2 l3 a1 a2.symm)

theorem exists_abPart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ∧ GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e P.τ P'.τ mK.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨PK, cK, sK, aK, rK, mK, hK⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tK
  obtain ⟨PB, cB, sB, aB, rB, mB, hB⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tB
  obtain ⟨mZ, hZ⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ P.m mK
  let tK' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tK.G, IsSemiAbelian.pullback (spMap e) P.tK.G P.tK.semi,
    OAct.pullback (spMap e) P.tK.G P.tK.act, PK, cK, sK, aK, rK⟩
  let tB' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tB.G, IsSemiAbelian.pullback (spMap e) P.tB.G P.tB.semi,
    OAct.pullback (spMap e) P.tB.G P.tB.act, PB, cB, sB, aB, rB⟩
  let τ' : TorusExtension tK'.G := torusExtBC (spMap e) P.τ
  let e' : τ'.B ≅ tB'.G := eBC (spMap e) P.τ P.e
  have hψ : (τ'.q ≫ e'.hom).left ≫ mB.φ = mK.φ ≫ (P.τ.q ≫ P.e.hom).left := by
    rw [hK, hB]
    exact quot_bc (spMap e) P.τ P.e
  have act' : ∀ a, tK'.act.act a ≫ τ'.q ≫ e'.hom = τ'.q ≫ e'.hom ≫ tB'.act.act a := fun a => by
    change (Over.pullback (spMap e)).map (P.tK.act.act a) ≫ (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom = (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom ≫ (Over.pullback (spMap e)).map (P.tB.act.act a)
    simp only [← Functor.map_comp]
    rw [P.act a]
  have pp' : LBIso tK'.PP.L (tB'.PP.L.pull (τ'.q ≫ e'.hom).left) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    obtain ⟨wB, gB, -⟩ := mB.lin
    exact lbIso_square hψ P.tB.PP.isLB tK'.PP.isLB tB'.PP.isLB P.tK.PP.isLB ⟨wK, gK⟩ ⟨wB, gB⟩ P.pp
  have hT : TorusOver e P.τ τ' mK.φ := by
    rw [hK]
    exact torusOver_torusExtBC e P.τ
  exact ⟨⟨tK', mZ, τ', tB', e', eBC_hom (spMap e) P.τ P.e P.e_hom, act', pp'⟩, mK, mB, hZ.symm, hψ.symm, hT⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC
