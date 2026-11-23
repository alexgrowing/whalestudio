import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.EllConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_mem (H : Host E) (a : OK H) : H.bar (a : 𝓞 E) ∈ OK H := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = H.w0 := hx
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator]
    exact sub_mem (one_mem _) (wK H).2
  | algebraMap r =>
    have : H.bar (algebraMap ℤ (𝓞 E) r) = algebraMap ℤ (𝓞 E) r := by simp
    show H.bar (algebraMap ℤ (𝓞 E) r) ∈ OK H
    rw [this]
    exact Subalgebra.algebraMap_mem _ r
  | add x y hx hy h₁ h₂ => exact (map_add H.bar x y) ▸ add_mem h₁ h₂
  | mul x y hx hy h₁ h₂ => exact (map_mul H.bar x y) ▸ mul_mem h₁ h₂

def barK (H : Host E) : OK H →+* OK H where
  toFun a := ⟨H.bar (a : 𝓞 E), bar_mem H a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

theorem barK_wK_add (H : Host E) : barK H (wK H) + wK H = 1 :=
  Subtype.ext (by
    show H.bar H.w0 + H.w0 = 1
    rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_add_cancel])

theorem isLieComb_one_sub {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (v : epsR R ⟶ G)
    (hv : IsTangent v) (ω : R) (f g : G ⟶ G) (hfg : g * f = 𝟙 G) (h : IsLieComb ![ω] ![v] (v ≫ f)) :
    IsLieComb ![1 - ω] ![v] (v ≫ g) := by
  have hv' : ∀ i, IsTangent (![v] i) := fun i => by fin_cases i; exact hv
  rw [GlobalTheory.LieComb.isLieComb_iff_tanExp] at h ⊢
  have e₁ : (v ≫ g) * (v ≫ f) = v := by rw [← MonObj.comp_mul, hfg, Category.comp_id]
  have e₂ := map_add (GlobalTheory.LieComb.combHom hv') ![1 - ω] ![ω]
  have e₃ : (![1 - ω] + ![ω] : Fin 1 → R) = Pi.single 0 1 := by
    funext i
    fin_cases i
    simp
  rw [e₃] at e₂
  have e₄ : v = GlobalTheory.SqZero.tanExp ![v] ![1 - ω] * GlobalTheory.SqZero.tanExp ![v] ![ω] :=
    (GlobalTheory.LieComb.tanExp_single hv' 0).symm.trans (congrArg Additive.toMul e₂)
  rw [← h] at e₄
  exact mul_right_cancel (e₁.trans e₄)

open GlobalTheory.PrimNorm in

theorem lbIso_of_adj {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {f g : B ⟶ B} (h : LamEq M f (𝟙 B) M (𝟙 B) g) : LBIso (cubeLB B ![𝟙 B, g] M) (cubeLB B ![𝟙 B, f] M) := by
  have h' : LBIso (cubeLB B ![fst B B ≫ f, snd B B] M) (cubeLB B ![fst B B, snd B B ≫ g] M) := by
    simpa only [LamEq, Category.comp_id] using h
  have e := diff₂_ptCls_adj hM h' (𝟙 B) (𝟙 B)
  rw [Category.id_comp, Category.id_comp, diff₂_comm] at e
  exact (lbIso_iff hM _ _ _ _).2 ((prod_square_id _ _ (cls M)).trans (e.symm.trans (prod_square_id _ _ (cls M)).symm))

theorem exists_conj_action (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R]
    (ω : R) (C : Ell H R ω) :
    ∃ a : OAct (OK H) C.P.A, (∀ x y : OK H, (y : 𝓞 E) = H.bar x → a.act x = C.act.act y) ∧
      IsLieComb ![1 - ω] ![C.v] (C.v ≫ a.act (wK H)) ∧
      (∀ x y : OK H, (y : 𝓞 E) = H.bar x → LamEq C.P.L (a.act x) (𝟙 C.P.A) C.P.L (𝟙 C.P.A) (a.act y)) ∧
      LBIso C.P.L (cubeLB C.P.A ![𝟙 C.P.A, a.act (wK H)] C.P.L) := by
  refine ⟨Serre.comapAct C.act (barK H), fun x y h => ?_, ?_, fun x y h => ?_, ?_⟩
  · exact congrArg C.act.act (Subtype.ext h.symm)
  · exact isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
      (by rw [Serre.comapAct_act, ← C.act.add, barK_wK_add, C.act.one]) C.eig
  · exact C.adj _ _ (congrArg H.bar h)
  · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
      (lbIso_of_adj C.P.isLB (C.adj (barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))

end GlobalTheory.CM.EllConj
end
