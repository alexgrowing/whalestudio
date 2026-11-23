import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPreDataDyadicFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DownMoveLocalDualLatticeEqLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelFunctionalEqStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DnMove

set_option maxHeartbeats 4000000

theorem gl_inv_map_mul_map {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (A : GL (Fin n) E) (y : Matrix (Fin n) (Fin n) ℂ) :
    ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map φ * ((A : Matrix (Fin n) (Fin n) E).map φ * y) = y := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem tr_eq_of_isTr {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (hY : I.IdY l Z u a i hi eY) (b : (I.stp u a i).β) (g0 : (I.stp u a i).G b)
    (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi))
    (hγ : (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam b g0) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i)
    (hT : IsTr (atInf (embT (I.rec7 l Z)) γ.1.1) (eY s') (eY s)) :
    (I.stp u a i).tr B.fields.emb B.embLL b g0 h s = B.embLL (((I.stp u a i).chr b g0 : B.LLˣ) : B.LL) * h s' := by
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g0)⁻¹ s) = _
  congr 2
  apply Subtype.ext
  funext τ
  have h1 := hT τ
  rw [hY, hY] at h1
  show (((I.stp u a i).gam b g0)⁻¹ : GL (Fin (B.R.N i)) B.fields.E).1.map _ * s.1 τ = s'.1 τ
  have h2 : atInf (embT (I.rec7 l Z)) (γ.1.1) τ = (((I.stp u a i).gam b g0 : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E).map (embAt B.embLL B.fields.emb τ) := by
    rw [← hγ]
    show (γ.1.1).map (embT (I.rec7 l Z) τ) = (γ.1.1).map (embAt B.embLL B.fields.emb τ)
    congr 1
    ext x
    show B.host.emb τ x = B.embLL (B.tauLL τ x)
    rw [← GlobalTheory.Mem.PreXModel.embLL_tauLL]
    rfl
  rw [h1, h2]
  exact gl_inv_map_mul_map _ _ _

theorem dnNatTieG_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → DnNatTieG L eY eV K := by
  intro B X I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL
  intro v β c g hg
  have hβ := GlobalTheory.T.move_down_level_prime_keeps_chart I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg
  obtain ⟨γ, η, κ, hγ, hη, hrel, hchi⟩ := GlobalTheory.T.moveDown_levelPrime_adelic_factorisation I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg hβ
  refine ⟨hβ, γ, η, κ, hη, hrel, GlobalTheory.T.downMove_localDualLattice_eq_levelPrime I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ,
    GlobalTheory.T.move_down_level_functional_eq I hOk hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL v β c g hg γ hγ, ?_⟩
  intro h s s' hT
  show (I.stp u a i).trTo B.fields.emb B.embLL c.1.1 (((I.atIn u a).A i).dnPt v c.1 g) h s = _
  rw [hchi]
  exact tr_eq_of_isTr I l Z u a i hi eY hY _ _ γ hγ h s s' hT

end GlobalTheory.DnMove

end
