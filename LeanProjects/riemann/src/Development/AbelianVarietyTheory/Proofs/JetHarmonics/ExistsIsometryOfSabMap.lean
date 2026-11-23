import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelAutomorphismPeriodFamily
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
import Formalism.LocalToGlobal.ProjectiveLattices.IsLevMove

noncomputable section

namespace GlobalTheory.LevelCusp

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure IsMatch (X X' : Data E r) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ

theorem isMatch_of_isUStab (X : Data E r) {a : GL (Fin r) E} (h : IsUStab X.Gm X.Λ a) : IsMatch X X a :=
  ⟨rfl, rfl, rfl, h.1, h.2⟩

theorem hermC_of_herm {G G' a : Matrix (Fin r) (Fin r) E} {ε : E}
    (h : ∀ u v, herm G' (a *ᵥ u) (a *ᵥ v) = ε * herm G u v) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) = τ ε * hermC τ G u v := by
  classical
  have key : ∀ i j, ∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j)) = τ ε * τ (G i j) := fun i j => by
    have := congrArg τ (h (Pi.single i 1) (Pi.single j 1))
    simp only [herm, cc, Matrix.mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at this
    rw [this]
    simp [Pi.single_apply, apply_ite, ite_mul]
  have e : hermC τ G' (a.map τ *ᵥ u) (a.map τ *ᵥ v) =
      ∑ j, ∑ i, u i * (∑ p, ∑ q, τ (a p i) * τ (G' p q) * conj (τ (a q j))) * conj (v j) := by
    simp only [hermC, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [e, Finset.sum_comm]
  simp only [key, hermC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {X X' : Data E r} {a : GL (Fin r) E}

theorem IsMatch.mem (h : IsMatch X X' a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem IsMatch.hermC_eq (h : IsMatch X X' a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem IsMatch.dmin_eq (h : IsMatch X X' a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem IsMatch.mem_dom (h : IsMatch X X' a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UnifPoint GlobalTheory.LevStab
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
  {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}

theorem exists_isometry_of_sabMap (F : FamilyUnif Xo σ ty) {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    {i j : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di j).La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') (hu : F.u i P ≫ ρ = F.u j P') :
    ∃ (gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di j).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (F.Di j).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ (∀ a, P' (gam a) = h (P a)) ∧
      ∀ z, (F.ex j P' (h z)).left = (F.ex i P z).left ≫ ν.φ := by
  obtain ⟨β, hβ⟩ := GlobalTheory.CMSpreadCompare.exists_pointEquiv ν.cart (Over.mk (F.u i P)) (s := F.u j P') hu.symm
  have hr : ReadsPeriods Xo.univ.t unitOn (F.Di i) ty P (fun z => β (F.ex i P z)) := by
    refine ⟨fun z => by rw [β.map_eq_one_iff, F.ex_ker i P hP], fun a z => ?_, fun k a b c hk hc => ?_⟩
    · apply Over.OverMorphism.ext
      rw [hβ, F.ex_lin i P hP, Over.comp_left, Over.comp_left, hβ, Category.assoc, Category.assoc]
      exact congrArg _ (ν.act a)
    · obtain ⟨w, hw, -⟩ := ν.lin
      have h₁ := (weilIs_grpPullback_of_comm _ _ Xo.univ.t.G Xo.univ.t.G ρ ν.φ _ _ Xo.univ.t.PP.isLB
        Xo.univ.t.PP.isLB ν.cart ⟨w, hw⟩ _ k _ _ (pushPt ν.cart.1.w _) (pushPt ν.cart.1.w _) _ rfl rfl).1
        (F.ex_weil i P hP k a b c hk hc)
      exact weilIs_congr hu (hβ _).symm (hβ _).symm h₁
  obtain ⟨gam, h, hEF, hh, hx⟩ := exists_isometry_of_hol hP hP' (e := fun z => β (F.ex i P z)) (e' := F.ex j P')
    (fun z w => by rw [F.ex_add i P hP, map_mul]) (β.surjective.comp (F.ex_onto i P hP))
    (by
      simp only [hβ]
      exact GlobalTheory.CMSpreadCompare.isHolTo_postcomp (GlobalTheory.ClassUniq.isHolTo_ex F i P hP) _)
    ⟨F.ex_add j P' hP', F.ex_onto j P' hP', GlobalTheory.ClassUniq.isHolTo_ex F j P' hP', (F.ex_diff j P' hP').1,
      (F.ex_diff j P' hP').2⟩ hr ⟨F.ex_ker j P' hP', F.ex_lin j P' hP', F.ex_weil j P' hP'⟩
  exact ⟨gam, h, hEF, hh, fun z => by rw [hx, hβ]⟩

end Exp

end GlobalTheory.LevelCusp
