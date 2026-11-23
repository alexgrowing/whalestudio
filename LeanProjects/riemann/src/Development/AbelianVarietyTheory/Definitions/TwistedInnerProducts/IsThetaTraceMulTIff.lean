import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EmbeddingSectionsSpanGeometricFibre

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaTraceTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem fn_ext_of_surjective {W Y : Scheme.{0}} (Ψ : W ⟶ Y) [Surjective Ψ] [IsReduced Y] {U : Y.Opens}
    {a b : Γ(Y, U)} (h : ∀ w, Ψ w ∈ U → gs Ψ w U a = gs Ψ w U b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨w, rfl⟩ := Ψ.surjective y
  have hU : Ψ w ∈ U := Y.basicOpen_le _ hy
  have hw : w ∈ W.basicOpen ((Ψ.app U).hom (a - b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hy
  rw [W.mem_basicOpen _ w hU] at hw
  have e := h w hU
  rw [gs_eq _ _ _ hU, gs_eq _ _ _ hU, ← sub_eq_zero, ← map_sub, ← map_sub] at e
  exact absurd (e ▸ hw) not_isUnit_zero

theorem sec_eq_of_surjective {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {T : Over S} {W : Scheme.{0}}
    (Ψ : W ⟶ (T ⊗ A).left) [Surjective Ψ] [IsReduced (T ⊗ A).left] {k : ℤ} {u v : LB.Sec (LPow A L.L k T)}
    (h : ∀ w J, Good L.L w J → sv A L u Ψ w J = sv A L v Ψ w J) : u = v := by
  refine sec_ext fun j => fn_ext_of_surjective Ψ fun w hw => ?_
  obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB w (fun _ : Fin 1 => Ψ ≫ (snd T A).left) j
    (fun a b _ => by rw [Subsingleton.elim a b]) (fun k => Set.mem_iInter.1 hw k)
  exact (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) u Ψ w J j e).symm.trans
    ((h w J hJ).trans (sval_of (L := L.L) (φ := fun _ : Fin 1 => (snd T A).left) v Ψ w J j e))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem isThetaTrace_mulT_iff {p : ℕ} (hp : 1 ≤ p) {Ω : Type} [Field Ω] (x : Sp Ω ⟶ Xo.X)
    (s u : LB.Sec (PPx x)) :
    IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (x := x) (x' := x) (mulT Xo.univ.t.G (Over.mk x) p).left p s u ↔ u = s := by
  have hL := abelianSchemeLaws_all.1
  constructor
  · intro h
    have := Xo.univ.t.semi.smooth
    have : Smooth (fst (Over.mk x) Xo.univ.t.G).left := by
      show Smooth (pullback.fst x Xo.univ.t.G.hom)
      infer_instance
    have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Sp Ω))
    have : IsReduced (Over.mk x ⊗ Xo.univ.t.G).left :=
      GlobalTheory.isReduced_of_smooth_of_isReduced (fst (Over.mk x) Xo.univ.t.G).left
    have : Surjective (mulT Xo.univ.t.G (Over.mk x) p).left :=
      (GlobalTheory.EmbSpan.pt_pow_and_surjective hL (UnivPol.pol Xo) x p hp).2
    refine sec_eq_of_surjective (L := Xo.univ.t.PP) (mulT Xo.univ.t.G (Over.mk x) p).left fun w J hJ => ?_
    have e := h.sv_eq_of_mulT hL.globalFns (UnivPol.pol Xo).isAb (𝟙 _) w hJ
    rwa [Category.id_comp] at e
  · rintro rfl
    obtain ⟨s₁, h⟩ := exists_isMulPull p u
    exact isThetaTrace_mulT h

def scale {Ω : Type} [Field Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (u : LB.Sec (PPx y.x))
    (hu : ∀ s' : LB.Sec (PPx y.x), ∃! a : Ω, ∀ i, s'.f i = scal y.x a i * u.f i) : FrPt Xo c Ω :=
  { y with s := u, gen := hu }

theorem hkTr_scale_iff {p : ℕ} (hp : 1 ≤ p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω)
    (u : LB.Sec (PPx y.x)) (hu : ∀ s' : LB.Sec (PPx y.x), ∃! a : Ω, ∀ i, s'.f i = scal y.x a i * u.f i)
    (a : Ω) (ha : ∀ i, u.f i = scal y.x a i * y.s.f i) :
    hkTr Xo c p Ω y (scale y u hu) ((conj y.x y.x).symm (mulT Xo.univ.t.G (Over.mk y.x) p).left) ↔ a = 1 := by
  have e : hkTr Xo c p Ω y (scale y u hu) ((conj y.x y.x).symm (mulT Xo.univ.t.G (Over.mk y.x) p).left) ↔
      u = y.s := by
    rw [← isThetaTrace_mulT_iff hp y.x y.s u]
    show IsThetaTrace _ _ (conj y.x y.x ((conj y.x y.x).symm _)) p y.s u ↔ _
    rw [Equiv.apply_symm_apply]
  have h1 : ∀ i, y.s.f i = scal y.x 1 i * y.s.f i := fun i => by
    simp [Formalism.L2.Pj.scal, liftFun]
  rw [e]
  constructor
  · rintro rfl
    exact (y.gen y.s).unique ha h1
  · rintro rfl
    exact sec_ext fun i => (ha i).trans (h1 i).symm

end GlobalTheory.ThetaTraceTest
