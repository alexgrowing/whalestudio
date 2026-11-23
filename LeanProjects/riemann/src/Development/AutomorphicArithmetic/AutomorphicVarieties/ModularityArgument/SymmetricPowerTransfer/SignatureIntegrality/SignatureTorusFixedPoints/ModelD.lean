import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.NormalD

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

private theorem eD_coe {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (g : DX Δ) :
    (eD hs g : Matrix (Fin 2) (Fin 2) K) = (mt g).map (proj hs) := by
  rfl

private theorem ev_coe {K : Type} [Field K] {τ a : K} (h : a * a = τ * a - 1) (z : (Etau K τ)ˣ) :
    (evU h z : K) = (z : Etau K τ).re + a * (z : Etau K τ).im := rfl

private theorem proj_smul {K : Type} [Field K] {Δ s : K} (hs : s * s = Δ) (c : K) (x : Lsq K Δ) :
    proj hs (c • x) = c * proj hs x := by
  simp [proj]
  ring

theorem _root_.UpperTheory.V.Z.Sym.Sig.modelD : UpperTheory.V.Z.Sym.Sig.ModelD := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 a ha γ j ⟨hdet, htr⟩ hemb
  obtain ⟨-, -, -, -, hdt, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  have inj := (algebraMap k (Lsq k Δ)).injective
  have hdet1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 :=
    inj (by rw [← (hdt γ).1, hdet, map_one])
  have htr1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = (a : k) + ((a⁻¹ : kˣ) : k) :=
    inj (by rw [← (hdt γ).2, htr])
  have hprod : valuation k ((a⁻¹ : kˣ) : k) * valuation k (a : k) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : a ≠ a⁻¹ := by
    intro h
    have h' : valuation k ((a⁻¹ : kˣ) : k) < 1 := by
      rw [← h]
      exact ha
    exact (mul_lt_of_le_one_of_lt h'.le ha).ne hprod
  have hcp : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).charpoly =
      (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) := by
    rw [Matrix.charpoly_fin_two, htr1, hdet1]
    have hab : (a : k) * ((a⁻¹ : kˣ) : k) = 1 := Units.mul_inv a
    rw [← hab, C_add, C_mul]
    ring
  obtain ⟨g₀, hg₀⟩ := normalD k (eD hs γ) a a⁻¹ hne hcp
  refine ⟨g₀, hg₀, fun t => ?_⟩
  apply Units.ext
  have hM : ((eD hs (j t) : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).re • (1 : Matrix (Fin 2) (Fin 2) k) +
        (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).im • ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    rw [eD_coe, eD_coe, hemb t]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, proj_smul, Matrix.one_apply]
    split_ifs <;> simp
  have hg : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (g₀ : Matrix (Fin 2) (Fin 2) k) * ((dg ![a, a⁻¹] : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) := by
    rw [hg₀, Units.val_mul, Units.val_mul]
  have hPP : (g₀ : Matrix (Fin 2) (Fin 2) k) * ((g₀⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hM, hg, Units.val_mul, Units.val_mul]
  unfold dg
  rw [val_diagT, val_diagT]
  have hdiag : (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).re • (1 : Matrix (Fin 2) (Fin 2) k) +
      (t : Etau k ((a : k) + ((a⁻¹ : kˣ) : k))).im • diagonal (fun i => ((![a, a⁻¹] i : kˣ) : k)) =
      diagonal fun i => ((![evU (root_left a) t, evU (root_right a) t] i : kˣ) : k) := by
    ext i l
    fin_cases i <;> fin_cases l <;> simp [Matrix.one_apply, Matrix.diagonal_apply, ev_coe] <;> ring
  rw [← hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hPP,
    Matrix.mul_smul, Matrix.smul_mul]

end UpperTheory.V.Z.Sym.Sig

end
