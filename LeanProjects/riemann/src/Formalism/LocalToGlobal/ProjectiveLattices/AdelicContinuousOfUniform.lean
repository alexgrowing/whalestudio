import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section BC

theorem bcSp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def bcPm {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) : Gx (spMap ψ ≫ x) ⟶ Gx x :=
  pullback.lift (pullback.fst (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom ≫ spMap ψ)
    (pullback.snd (Over.mk (spMap ψ ≫ x)).hom Xo.univ.t.G.hom)
    (by rw [Category.assoc]; exact pullback.condition)

theorem bcPm_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left := by
  rw [Over.snd_left, Over.snd_left]
  exact pullback.lift_snd _ _ _

theorem bcPm_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) :
    bcPm ψ x ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk (spMap ψ ≫ x)) Xo.univ.t.G).left ≫ spMap ψ := by
  rw [Over.fst_left, Over.fst_left]
  exact pullback.lift_fst _ _ _

theorem appLE_comp_pullback {A B C : Scheme.{0}} (P : A ⟶ B) (q : B ⟶ C) (q' : A ⟶ C) (hq : P ≫ q = q') (W : C.Opens)
    (V1 : B.Opens) (V2 : A.Opens) (h1 : V1 ≤ q ⁻¹ᵁ W) (h2 : V2 ≤ P ⁻¹ᵁ V1) (h3 : V2 ≤ q' ⁻¹ᵁ W) (u : Γ(C, W)) :
    (P.appLE V1 V2 h2).hom ((q.appLE W V1 h1).hom u) = (q'.appLE W V2 h3).hom u := by
  subst hq
  rw [← CommRingCat.comp_apply]
  first
    | rw [Scheme.Hom.appLE_comp_appLE]
    | rw [Scheme.appLE_comp_appLE]

theorem ppxG {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i j : Fin 1 → Xo.univ.t.PP.L.ι) :
    (((PPx x).g i j : Γ(Gx x, (PPx x).U i ⊓ (PPx x).U j))) =
      ((snd (Over.mk x) Xo.univ.t.G).left.appLE (Xo.univ.t.PP.L.U (i 0) ⊓ Xo.univ.t.PP.L.U (j 0))
        ((PPx x).U i ⊓ (PPx x).U j)
        (fun p hp => ⟨Set.mem_iInter.1 hp.1 0, Set.mem_iInter.1 hp.2 0⟩)).hom
        (Xo.univ.t.PP.L.g (i 0) (j 0) : Γ(Xo.univ.t.G.left, _)) := by
  simp only [PPx, ReciprocityTheory.ChartRestriction.G.Out.LPow, LB.LinComb, Fin.prod_univ_one, zpow_one]
  rfl

def bcS {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) :
    LB.Sec (PPx (spMap ψ ≫ x)) where
  f i := ((bcPm ψ x).appLE _ _ (ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) i)).hom (s.f i)
  compat i j := by
    have hi := ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) i
    have hj := ppx_le_cov (bcPm ψ x) (bcPm_snd ψ x) j
    have hij : (PPx (spMap ψ ≫ x)).U i ⊓ (PPx (spMap ψ ≫ x)).U j ≤
        bcPm ψ x ⁻¹ᵁ ((PPx x).U i ⊓ (PPx x).U j) := fun p hp => ⟨hi hp.1, hj hp.2⟩
    have e := congrArg ((bcPm ψ x).appLE _ _ hij).hom (s.compat i j)
    rw [map_mul] at e
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      Scheme.Hom.map_appLE] at e
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_map]
    rw [e]
    congr 1
    refine (congrArg (fun w => ((bcPm ψ x).appLE _ _ hij).hom w) (ppxG x i j)).trans
      (Eq.trans ?_ (ppxG (spMap ψ ≫ x) i j).symm)
    exact appLE_comp_pullback _ _ _ (bcPm_snd ψ x) _ _ _ _ _ _ _

theorem bcTan {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, bcSp, bcSp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [← Category.assoc, bcSp]
    have e : (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
        ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom :=
      RingHom.ext fun a => by simp [dualMap]
    rw [e, ← bcSp, Category.assoc, h2]
    first
      | exact congrArg CommaMorphism.left (comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (Hom.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (MonObj.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | exact congrArg CommaMorphism.left (Mon_Class.comp_one (Over.homMk (U := Over.mk (spMap ψ ≫ x)) (V := Over.mk x) (spMap ψ) rfl) : _)
      | simp [Hom.one_def]

theorem bcEig {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, h a, ← Category.assoc, ← Category.assoc, bcSp, bcSp]
  congr 2
  refine RingHom.ext fun d => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, smul_eq_mul, map_mul, AlgHom.commutes]

theorem bcOver {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    {x : Sp S ⟶ Xo.X} (h : x ≫ Xo.s = sOf c S) : (spMap ψ.toRingHom ≫ x) ≫ Xo.s = sOf c T := by
  rw [Category.assoc, h]
  unfold sOf
  rw [bcSp]
  congr 1
  ext a
  simp

variable (Xo c) in

def BasBC (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) (τ : E →+* ℂ)
    (w : Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left),
    IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w →
      ∃! a : Fin (Dw.mult τ) → CAt σ,
        IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w

variable (Xo c) in

def GenBC (σ : c.F →+* ℂ) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) (s' : LB.Sec (PPx (spMap ψ.toRingHom ≫ y.x))),
    ∃! a : CAt σ, ∀ i, s'.f i = scal (spMap ψ.toRingHom ≫ y.x) a i * (bcS ψ.toRingHom y.x y.s).f i

def bcPt {σ : c.F →+* ℂ} (hB : BasBC Xo c σ) (hG : GenBC Xo c σ) (p : TRing c.F) (y : FrPt Xo c p.R)
    (ψ : p.R →ₐ[c.F] CAt σ) : FrPt Xo c (CAt σ) where
  x := spMap ψ.toRingHom ≫ y.x
  x_over := bcOver ψ y.x_over
  u τ i := spMap (dualMap ψ.toRingHom) ≫ y.u τ i
  tan τ i := bcTan ψ.toRingHom (y.tan τ i)
  eig τ i := bcEig ψ τ (y.eig τ i)
  basis τ w hw he := hB p y ψ τ w hw he
  s := bcS ψ.toRingHom y.x y.s
  gen s' := hG p y ψ s'

end BC

section Loc

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

def LocSplit (V : HSp D) (Kf : Subgroup (GA D V)) : Prop :=
  ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ a : GA D V → GA D V, ContinuousOn a N ∧ a g₀ = 1 ∧
    ∀ g ∈ N, a g ∈ GinfC V ∧ ∃ k ∈ Kf, g = g₀ * a g * k

def ArchCont (V : HSp D) {X : Comp → Data E r}
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) : Prop :=
  ∀ k τ, Continuous (archM V (th k τ))

def locFr (V : HSp D) {X : Comp → Data E r} (dict : GA D V → Σ k, Frame (X k).Ψ r)
    (th : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hr : V.rank = r)
    (x0 : ∀ k, Frame (X k).Ψ r) (a : GA D V → GA D V) (g₀ g : GA D V) : Frame (X (dict g₀).1).Ψ r :=
  rmul (dict g₀).2 (archMat V th hr x0 (a g) (dict g₀).1)

end Loc

end Formalism.L2.Pj
