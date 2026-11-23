import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Gauge Gauge.VLem

noncomputable section

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq} {e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)}
  {Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)}

theorem drtr_actA_cb (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cbA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vcb l) * f ρ := by
  rw [MA.cbA, actA_sc]
  rfl

theorem drtr_actA_c (l : Fin P.r) (f : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (MA.cA P (MA.DQ P) l) f = fun ρ => MA.coordQ (TT := P.TT) (M.vc l) * f ρ := by
  rw [MA.cA, actA_sc]
  rfl

theorem drtr_dMul_one (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) : dMul (fun _ => (1 : ℂ)) Φ = Φ := by
  funext c g
  simp [dMul]

theorem drtr_listb (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cbA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => star (c a)).prod) Φ =
        Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ) := by
      funext c g
      show _ = star (c a) • ((ls.map fun a => star (c a)).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hcb : FamR P Bs Dc (Q.crd (cbOp a) (dMul (fun c => (ls.map fun a => star (c a)).prod) Φ)) :=
      famR_opL hF a 4
    refine ⟨eq ▸ hcb, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hcb (fun c => star (c a)) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vcb a))
      (fun q => coordE_vcb _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_cb, hT]

theorem drtr_listc (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (he : IsFrameB P Bs e)
    (ls : List (Fin P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : FamR P Bs Dc Φ) :
    FamR P Bs Dc (dMul (fun c => (ls.map fun a => c a).prod) Φ) ∧
      trR P Bs.μsec e (dMul (fun c => (ls.map fun a => c a).prod) Φ) =
        MA.actA P (ls.map fun a => MA.cA P (MA.DQ P) a).prod (trR P Bs.μsec e Φ) := by
  induction ls with
  | nil =>
    simp only [List.map_nil, List.prod_nil]
    rw [drtr_dMul_one, actA_one]
    exact ⟨hΦ, rfl⟩
  | cons a ls ih =>
    obtain ⟨hF, hT⟩ := ih
    have eq : dMul (fun c => ((a :: ls).map fun a => c a).prod) Φ =
        Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ) := by
      funext c g
      show _ = c a • ((ls.map fun a => c a).prod • Φ c g)
      simp only [dMul, List.map_cons, List.prod_cons, mul_smul]
    have hc : FamR P Bs Dc (Q.crd (cOp a) (dMul (fun c => (ls.map fun a => c a).prod) Φ)) :=
      famR_opL hF a 1
    refine ⟨eq ▸ hc, ?_⟩
    rw [eq, trR_mul hpl hk he hF _ hc (fun c => c a) (fun _ _ => rfl) (MA.coordQ (TT := P.TT) (M.vc a))
      (fun q => coordE_vc _ _), List.map_cons, List.prod_cons, actA_mul, drtr_actA_c, hT]

end

theorem residue_derivative_transition : JDRDrTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk e he L hL Dc Φ hΦ
  obtain ⟨-, -, hc, -, hcb, -⟩ := hL
  have eb : drbF P.r = fun c => ((List.finRange P.r).map fun a => star (c a)).prod := by
    funext c
    rw [drbF, map_prod, ← List.prod_ofFn, List.ofFn_eq_map]
    rfl
  have ec : drF P.r = fun c => ((List.finRange P.r).map fun a => c a).prod := by
    funext c
    rw [drF, ← List.prod_ofFn, List.ofFn_eq_map]
  have hDrb : L.Drb = ((List.finRange P.r).map fun a => MA.cbA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Drb, hcb, List.ofFn_eq_map]
  have hDr : L.Dr = ((List.finRange P.r).map fun a => MA.cA P (MA.DQ P) a).prod := by
    rw [R.LevelData.Dr, hc, List.ofFn_eq_map]
  refine ⟨fun ρ => ?_, fun ρ => ?_⟩
  · have h := (drtr_listb hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← eb, ← hDrb] at h
    exact congrFun h ρ
  · have h := (drtr_listc hpl hk he (List.finRange P.r) Φ hΦ).2
    rw [← ec, ← hDr] at h
    exact congrFun h ρ

end

end Formalism.FourierDecayAlt.P.CutMP
