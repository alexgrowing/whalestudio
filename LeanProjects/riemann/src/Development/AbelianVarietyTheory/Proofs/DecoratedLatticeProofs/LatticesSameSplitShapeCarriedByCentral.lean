import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 1000000 in

theorem sMoves_of_wShape : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  intro D k _ _ _ _ p S S₀ A Ln ρ d o ζ L L' N N' α α' β β' γ δ c₀ a₀ hζ hL hL' hW hW' hN hc₀ hb hb' hd
  obtain ⟨c, hc, hpc⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀ hc₀
  obtain ⟨c', hc', hpc'⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀⁻¹ (inv_ne_zero hc₀)
  obtain ⟨a, haC, ha⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, haC, hc, ?_⟩
  apply GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S L L' c _ hL hL' hc
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hatW : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = X.map f := fun _ => rfl
  have hrat : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = (rat X).map p.pr := fun _ => rfl
  have hkey : ∀ {n m l : ℕ} (M : Matrix (Fin n) (Fin l) (AE D)) (R : Matrix (Fin l) (Fin m) (AE D))
      (u : Fin m → k), M.map p.pr *ᵥ (R.map p.pr *ᵥ u) = (M * R).map p.pr *ᵥ u := by
    intro n m l M R u; rw [Matrix.mulVec_mulVec, Matrix.map_mul]

  have hsum : atW p d.e * atW p d.qX + atW p d.i₀ * atW p d.q0 + atW p d.e' * atW p d.qY = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), ← Matrix.map_add _ (map_add f), d.sum_eq_one_rat,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hsumA : atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), o.iA_qA_add, Matrix.map_one _ (map_zero f) (map_one f)]
  have hrk : Ln.rank = 1 := hζ.1
  have j0 : Fin Ln.rank := ⟨0, by omega⟩
  have huniq : ∀ j : Fin Ln.rank, j = j0 := fun j => Fin.ext (by have := j.2; have := j0.2; omega)
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [huniq j, h0]; rfl
    simp [this]
  have hfζ : f (ζ j0) ≠ 0 := fun h => hζ0 (f.injective (by rw [h, map_zero]))
  set ζk : Fin Ln.rank → k := fun j => f (ζ j) with hζk
  set zv : Fin S.rank → k := fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r')) with hzv
  have hz : zv = atW p (d.i₀ * o.iB) *ᵥ ζk := by
    funext r
    simp only [hzv, vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec f (d.i₀ * o.iB) ζ r
  have hdec : ∀ x : Fin S.rank → k, ∃ (x1 x2 : Fin ρ → k) (t : k) (y : Fin A.rank → k),
      x = atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
   intro x
   set x0 := atW p d.q0 *ᵥ x
   set w := atW p o.qB *ᵥ x0
   set y := atW p o.qA *ᵥ x0
   set t := w j0 / f (ζ j0)
   have hw : w = t • ζk := by
     funext j; rw [huniq j]; simp only [Pi.smul_apply, smul_eq_mul, hζk, t]; field_simp
   have hx : x = atW p d.e *ᵥ (atW p d.qX *ᵥ x) + atW p d.e' *ᵥ (atW p d.qY *ᵥ x) + t • zv +
       atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
     rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, hz, ← Matrix.mulVec_smul, ← hw]
     have hm : atW p d.i₀ * (atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB) * atW p d.q0 =
         atW p d.i₀ * atW p d.q0 := by rw [hsumA, Matrix.mul_one]
     have h0 : atW p (d.i₀ * o.iA) *ᵥ y + atW p (d.i₀ * o.iB) *ᵥ w = atW p d.i₀ *ᵥ x0 := by
       simp only [y, w, x0, hatW, Matrix.map_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
       simp only [← hatW]
       rw [← hm]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
     calc x = (1 : Matrix (Fin S.rank) (Fin S.rank) k) *ᵥ x := (Matrix.one_mulVec x).symm
       _ = _ := by
         rw [← hsum, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
           ← Matrix.mulVec_mulVec, ← h0]
         abel
   exact ⟨_, _, _, _, hx⟩
  intro x
  obtain ⟨x1, x2, t, y, rfl⟩ := hdec x
  rw [hW x1 x2 t y]
  have jX : rat d.e = d.jX := rfl
  have jY : rat d.e' = d.jY := rfl
  have jA : rat (d.i₀ * o.iA) = d.j0 * o.jA := rat_mul _ _
  have jB : rat (d.i₀ * o.iB) = d.j0 * o.jB := rat_mul _ _
  have hGX : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX _
  have hGY : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jY = d.jY := d.wittDecomp_anisotropicEmbedding_inclY _
  have hG0' : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.j0 = d.j0 ⬝ Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) :=
    d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
  have hG0 : ∀ {m : ℕ} (R : Matrix (Fin S₀.rank) (Fin m) (AE D)), Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ (d.j0 ⬝ R) =
      d.j0 ⬝ (Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ R) := by
    intro m R; rw [← Matrix.mul_assoc, hG0', Matrix.mul_assoc]
  have hBB : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jB = o.jB := by rw [o.emb_jB, mt_one, Matrix.mul_one]
  have hAA : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jA = o.jA ⬝ (Formalism.L2.Theta.mt A a₀ ⬝ Formalism.L2.Theta.mt A a) := by
    rw [o.emb_jA, mt_mul]
  set G := Formalism.L2.Theta.mt S (embA d o (a₀ * a)) with hG
  have T1 : G.map p.pr *ᵥ (atW p d.e *ᵥ x1) = atW p d.e *ᵥ x1 := by rw [hrat, hkey, jX, hGX]
  have T2 : G.map p.pr *ᵥ (atW p d.e' *ᵥ x2) = atW p d.e' *ᵥ x2 := by rw [hrat, hkey, jY, hGY]
  have hz' : zv = (d.j0 ⬝ o.jB).map p.pr *ᵥ ζk := by
    rw [← jB]; exact hz
  have T3 : G.map p.pr *ᵥ zv = zv := by
    rw [hz', hkey, hG0, hBB]
  have hms : ∀ {m n : ℕ} (r : AE D) (X : Matrix (Fin m) (Fin n) (AE D)), (r • X).map p.pr = p.pr r • X.map p.pr := by
    intro m n r X; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have T4 : G.map p.pr *ᵥ (atW p (d.i₀ * o.iA) *ᵥ y) =
      c₀⁻¹ • (atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y)) := by
    rw [hrat, hkey, hkey, jA, hG0, hAA, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul,
      hms, Matrix.smul_mulVec, hpc', Matrix.mul_assoc]
  have himg : p.pr c • (G.map p.pr *ᵥ (atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
      atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y))) =
      atW p d.e *ᵥ (c₀ • x1) + atW p d.e' *ᵥ (c₀ • x2) + (c₀ * t) • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y) := by
    rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, T1, T2, T3, T4, hpc]
    simp only [smul_add, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  rw [himg, hW' (c₀ • x1) (c₀ • x2) (c₀ * t) y, hN]
  have hval : ∀ u u' z : k, valuation k (u * c₀) = valuation k u' → (u * (c₀ * z) ∈ 𝒪[k] ↔ u' * z ∈ 𝒪[k]) := by
    intro u u' z h
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← mul_assoc, map_mul, h, ← map_mul]
  refine and_congr (forall_congr' fun i => (hval _ _ _ (hb i)).symm)
    (and_congr (forall_congr' fun i => (hval _ _ _ (hb' i)).symm) (and_congr (hval _ _ _ hd).symm Iff.rfl))

end GlobalTheory.Core.Mi.LatMatch

end
