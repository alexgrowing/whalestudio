import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceBound

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.ColumnMultSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def permUnit (κ : Type) [CommRing κ] {r : ℕ} (π : Equiv.Perm (Fin r)) : GL (Fin r) κ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem reord_eq_conj {D : D7} {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) :
    ∃ w : G0 Pg r, ∀ g : G0 Pg r, reord π g = w * g * w⁻¹ := by
  refine ⟨fun PP => permUnit (kP PP.1) π, fun g => ?_⟩
  funext PP
  apply Units.ext
  show Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) π.symm (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) =
    π.toPEquiv.toMatrix * (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) * π.symm.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem columnMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.Pg.card = 2 * D.R.f → (∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP)) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (∀ χ ∈ A.X, IsAbsIrrChar χ) → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P1], ∀ χ ∈ A.X, ∃ n : ℕ, (Nat.card F.P1 : D.what₂.LL)⁻¹ * ∑ h : F.P1, χ (h : G) * (((F.ψ1 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (n : D.what₂.LL) ∧ |(n : ℝ) - (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ)| ≤ 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hcard hq hadm hirr hprod _ χ hχ
  classical
  obtain ⟨ψ, hψ, -, π, -, hmem, hchi⟩ := hlev
  obtain ⟨w, hw⟩ := reord_eq_conj (D := D) (Pg := R.Pg) π
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hg : 0 < min (D.host.g 0) (D.host.g 1) := lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar (RingHom.id ℂ) R.Pg D.R.r fun g => D.what₂.embLL (χ (R.eG.symm g)) :=
    hprod χ hχ
  obtain ⟨⟨n, hn, hb⟩, -⟩ := GlobalTheory.FinGL.MultSharpObj.multSharp D.host.E ℂ (RingHom.id ℂ) R.Pg D.R.f
    (min (D.host.g 0) (D.host.g 1)) D.R.r D.R.rS D.R.k ψ hcard hk hr hg hadm hq hψ _ hp
  refine ⟨n, ?_, hb⟩
  have hm : ∀ g : G, R.eG g ∈ (R.levR F true).H ↔ g ∈ F.P1 := fun g => by
    show R.eG.symm (R.eG g) ∈ F.P1 ↔ _
    rw [MulEquiv.symm_apply_apply]
  have hc : ∀ (g : G) (h : R.eG g ∈ (R.levR F true).H), (((R.levR F true).chi ⟨R.eG g, h⟩ : ℂˣ) : ℂ) =
      D.what₂.embLL ((F.ψ1 ⟨g, (hm g).1 h⟩ : D.what₂.LLˣ) : D.what₂.LL) := fun g h => by
    show D.what₂.embLL ((F.ψ1 ⟨R.eG.symm (R.eG g), h⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply g
  let e : F.P1 ≃ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H :=
    (R.eG.trans (MulAut.conj w)).toEquiv.subtypeEquiv fun g => by
      rw [← hm, hmem, hw]; rfl
  apply D.what₂.embLL.injective
  rw [map_natCast, ← hn, map_mul, map_inv₀, map_natCast, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.levelMult
  rw [Nat.card_congr e]
  congr 1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily R.Pg D.R.r
  letI : Fintype (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H := Fintype.ofFinite _
  refine Fintype.sum_equiv e _ _ fun x => ?_
  have h1 : R.eG x ∈ (R.levR F true).H := (hm x).2 x.2
  have h2 := (hmem _).1 h1
  have he : e x = ⟨reord π (R.eG x), h2⟩ := Subtype.ext (hw _).symm
  rw [he, ← hchi _ h1 h2, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, hc]
  congr 2
  show χ x = χ (R.eG.symm (reord π (R.eG x)))
  rw [hw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, (hirr χ hχ).conj]

end GlobalTheory.ColumnMultSum

end
