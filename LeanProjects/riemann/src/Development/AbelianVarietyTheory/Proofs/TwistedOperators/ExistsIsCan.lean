import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

section Family

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def IsCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (pm : Gx x₁ ⟶ Gx x) : Prop :=
  x₁ = spMap χ ≫ x ∧ pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left ≫ spMap χ

def IsFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X}
    (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') : Prop :=
  ∃ (pm : Gx x₁ ⟶ Gx x) (pm' : Gx x₁' ⟶ Gx x'), IsCan χ pm ∧ IsCan χ pm' ∧ Ψ₁ ≫ pm' = pm ≫ Ψ ∧
    Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left

def IsHeckeFam (P : Ideal (𝓞 E)) (p i : ℕ) {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') : Prop :=
  IsLinHom Ψ ∧ Etale Ψ ∧ Surjective Ψ ∧ (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2) β) ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
        IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁

def IsListed {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') {n : ℕ}
    (σ : Fin n → (Over.mk x ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
    IsFib χ Ψ Ψ₁ → ∃ e : Fin n ≃ transKer Xo.univ.t.G Ψ₁, ∀ j, (e j).1.left = spMap χ ≫ (σ j).left

theorem exists_isCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (hx : x₁ = spMap χ ≫ x) : ∃ pm : Gx x₁ ⟶ Gx x, IsCan χ pm :=
  ⟨pullback.lift (pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ)
      (pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ ≫ x =
          pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), hx, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem exists_isFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X}
    {x₁ x₁' : Sp Ω ⟶ Xo.X} (hx : x₁ = spMap χ ≫ x) (hx' : x₁' = spMap χ ≫ x') (Ψ : Gx x ⟶ Gx x')
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left) :
    ∃ Ψ₁ : Gx x₁ ⟶ Gx x₁', IsFib χ Ψ Ψ₁ := by
  obtain ⟨pm, hp⟩ := exists_isCan χ hx
  obtain ⟨pm', hp'⟩ := exists_isCan χ hx'
  let Ψ₁ : Gx x₁ ⟶ Gx x₁' := pullback.lift (f := (Over.mk x₁').hom) (g := Xo.univ.t.G.hom)
    (fst (Over.mk x₁) Xo.univ.t.G).left (pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left) (by
      simp only [Category.assoc]
      rw [GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hΨ, reassoc_of% hp.2.2, ← hx']
      rfl)
  have a : Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left := pullback.lift_fst _ _ _
  have b : Ψ₁ ≫ (snd (Over.mk x₁') Xo.univ.t.G).left = pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left :=
    pullback.lift_snd _ _ _
  refine ⟨Ψ₁, pm, pm', hp, hp', GlobalTheory.HeckeFrCompare.gx_ext ?_ ?_, a⟩
  · rw [Category.assoc, Category.assoc, hp'.2.2, hΨ, hp.2.2, reassoc_of% a]
  · rw [Category.assoc, Category.assoc, hp'.2.1, b]

@[reducible] def fieldCAt {K : Type} [Field K] (σ : K →+* ℂ) : Field (CAt σ) :=
  { (inferInstance : CommRing (CAt σ)), (inferInstanceAs (Field ℂ) : Field (CAt σ)) with }

theorem algClosedCAt {K : Type} [Field K] (σ : K →+* ℂ) : @IsAlgClosed (CAt σ) (fieldCAt σ) :=
  inferInstanceAs (IsAlgClosed ℂ)

def HkPtC {c : Coeff l} {σ : c.F →+* ℂ} (p : ℕ) (y : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G))
    (z : FrPt Xo c (CAt σ)) : Prop :=
  @HkPt E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _
    (@hkTr E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _) y C z

end Family

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict GlobalTheory.LevelCusp
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure QMatch (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v ∈ X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ
  lat' : ∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ

variable {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E}

theorem QMatch.mem (h : QMatch X X' N a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem QMatch.hermC_eq (h : QMatch X X' N a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem QMatch.dmin_eq (h : QMatch X X' N a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem QMatch.mem_dom (h : QMatch X X' N a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

end GlobalTheory.HeckeEx
