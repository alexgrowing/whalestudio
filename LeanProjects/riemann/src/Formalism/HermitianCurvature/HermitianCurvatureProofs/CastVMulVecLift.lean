import Formalism.HermitianCurvature.HermitianCurvatureProofs.DwPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GenCapRepIntertwine
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

open Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.DiagonalScalarMatrices

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

section lift

variable {k : ℕ}

theorem frame_lift_list {i r' m : ℕ} (vs : List (Fin (2 * r' + k + 1) → ℂ)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ)
    (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k (i + r') (vs.map (liftVec k i r')) (fun c => liftVec k i r' (Bs c)) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun a => (PI.QnLevBasicsW.level_group_isotropic_vector k i r' (Bs a) (h1 a)).1, fun a b => ?_, fun a x hx => ?_⟩
  · rw [PIQnLT.herm_liftVec]; exact h2 a b
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    rw [PIQnLT.herm_liftVec]
    exact h3 a v hv

theorem frame_lift_cast {i r' n m : ℕ} (hn : i + r' = n) (vs : List (Fin (2 * r' + k + 1) → ℂ))
    (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (h : IsFrameOf k r' vs Bs) :
    IsFrameOf k n (vs.map fun v => D.castV hn (liftVec k i r' v)) (fun c => D.castV hn (liftVec k i r' (Bs c))) := by
  subst hn
  simp only [JCTx5.castV_rfl]
  exact frame_lift_list vs Bs h

theorem capRep_lift_cast {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {i r' n m : ℕ} (hn : i + r' = n)
    (π0 : Mx k n → (Wp →L[ℂ] Wp)) (Bs : Fin m → Fin (2 * r' + k + 1) → ℂ) (w : ℂ) (v : Wp) :
    capRep k n π0 (fun c => D.castV hn (liftVec k i r' (Bs c))) w v =
      capRep k r' (fun y => π0 (D.castM hn (ιLev k i r' y))) Bs w v := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact JCTx5.capRep_lift π0 Bs w v

theorem castV_mulVec_lift {i r' n : ℕ} (hn : i + r' = n) (M : B.Mat k r') (v : Fin (2 * r' + k + 1) → ℂ) :
    D.castM hn (ιLev k i r' M) *ᵥ D.castV hn (liftVec k i r' v) = D.castV hn (liftVec k i r' (M *ᵥ v)) := by
  subst hn
  simp only [JCTx5.castV_rfl, JCTx5.castM_rfl]
  exact PIQnLT.mulVec_liftVec M v

end lift

section types

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tp_eigen_lev {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (ρ : M.Ty P) (w : ℂ) (u : Wp) :
    capRep P.k (P.r - P.r) (p.T.bs P.r).π (fun a => m₀r *ᵥ Bs' a) w (p.TP.E ρ u) =
      M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • p.TP.E ρ u := by
  have hn : P.r + (P.r - P.r) = P.r := by omega
  obtain ⟨hν, hm, hbase⟩ := hLF
  have hB1 := Topx1.vecw_frame_fwd (p.T.bs P.r) hbase hB
  have hB2 := frame_lift_cast hn _ _ hB1
  have ez : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have ee : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← castV_mulVec_lift hn, hm, hν]
  simp only [List.map_cons, List.map_nil, ez, ee] at hB2
  have h := p.TP.eigen _ hB2 ρ w u
  rw [capRep_lift_cast hn] at h
  have hπ : (fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y))) = (p.T.bs P.r).π :=
    funext fun y => (p.T.π_lev P.r le_rfl y).symm
  rw [hπ] at h
  exact h

theorem aeval_intertwine (V : Wq →L[ℂ] Wp) (R : Module.End ℂ Wq) (Lf : Module.End ℂ Wp)
    (h : ∀ v, V (R v) = Lf (V v)) (p : Polynomial ℂ) : ∀ v, V (Polynomial.aeval R p v) = Polynomial.aeval Lf p (V v) := by
  induction p using Polynomial.induction_on with
  | C a => intro v; simp
  | add p q hp hq => intro v; simp [hp, hq]
  | monomial n a ih =>
    intro v
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eR : Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval R (Polynomial.C a * Polynomial.X ^ n) * R := by rw [map_mul, Polynomial.aeval_X]
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    rw [e1, eR, eL, Module.End.mul_apply, Module.End.mul_apply, ih, h]

theorem aeval_eigen (Lf : Module.End ℂ Wp) (x : Wp) (c : ℂ) (h : Lf x = c • x) (p : Polynomial ℂ) :
    Polynomial.aeval Lf p x = p.eval c • x := by
  induction p using Polynomial.induction_on with
  | C a => simp [Algebra.algebraMap_eq_smul_one]
  | add p q hp hq => simp [hp, hq, add_smul]
  | monomial n a ih =>
    have e1 : Polynomial.C a * Polynomial.X ^ (n + 1) = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
    have eL : Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n * Polynomial.X) =
        Polynomial.aeval Lf (Polynomial.C a * Polynomial.X ^ n) * Lf := by rw [map_mul, Polynomial.aeval_X]
    have ev : (Polynomial.C a * Polynomial.X ^ n * Polynomial.X).eval c =
        (Polynomial.C a * Polynomial.X ^ n).eval c * c := by rw [Polynomial.eval_mul, Polynomial.eval_X]
    rw [e1, eL, Module.End.mul_apply, h, map_smul, ih, smul_smul, ev, mul_comm]

theorem poly_types {P : M.Par} (p : KB.Pl P Wp Wq) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)) (hLF : PBI.LevFrame p ν'r m₀r)
    {Bs' : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    (hB : IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z', ν'r] Bs') (V : Wq →L[ℂ] Wp)
    (hV : PBI.GrpInt (p.T.bs P.r) ν'r m₀r V) (hex : ∑ ρ : M.Ty P, (p.TP.E ρ).comp V = V)
    (Y₀ : ℂ) (q : Polynomial ℂ) (v : Wq) :
    V (Polynomial.aeval (qdet (Qr.EB (p.T.bs P.r).π' Bs') (Y₀ + ((P.k : ℂ) - 2) / 2)) q v) =
      ∑ ρ : M.Ty P, q.eval (M.xC P ρ Y₀) • p.TP.E ρ (V v) := by
  set S := p.T.bs P.r
  have hbase := hLF.2.2
  have hBz' : IsFrameOf P.k (P.r - P.r) [S.z'] Bs' :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) hB
  have hBz : IsFrameOf P.k (P.r - P.r) [S.z] (fun a => m₀r *ᵥ Bs' a) :=
    Topx1.vecw_frame_sub (fun v hv => by simp at hv; simp [hv]) (Topx1.vecw_frame_fwd S hbase hB)
  have hglR := Formalism.FourierDecayAlt.P.frame_general_linear Wq P.k (P.r - P.r) (P.k - 1) S.z' S.π' Bs' ⟨S.π'_rep, S.π'_cont⟩ hBz'
  have hglL := Formalism.FourierDecayAlt.P.frame_general_linear Wp P.k (P.r - P.r) (P.k - 1) S.z S.π (fun a => m₀r *ᵥ Bs' a)
    ⟨S.π_rep, S.π_cont⟩ hBz
  set w0 : ℂ := Y₀ + ((P.k : ℂ) - 2) / 2
  have hint : ∀ v, V (qdet (Qr.EB S.π' Bs') w0 v) = qdet (Qr.EB S.π (fun a => m₀r *ᵥ Bs' a)) w0 (V v) := by
    intro v
    rw [← hglR.2, ← hglL.2]
    exact (PBI.gen_capRep_intertwine S hbase V hV hB w0 v).symm
  rw [aeval_intertwine V _ _ hint q v]
  conv_lhs => rw [← hex]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  refine aeval_eigen _ _ _ ?_ q
  rw [← hglL.2, tp_eigen_lev p ν'r m₀r hLF hB ρ w0 (V v)]
  congr 2
  ring

end types

end Formalism.FourierDecayAlt.P.DiagonalScalarMatrices
