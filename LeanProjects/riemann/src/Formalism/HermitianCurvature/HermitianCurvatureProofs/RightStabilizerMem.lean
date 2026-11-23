import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCharacterOneOfProduct

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

abbrev RR (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) : Type :=
  (Mt k r × ((C2.LPidx w → ℂ) × Mt k r)) × (Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r))

section defs

variable (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))

def Xi (x : C2.Lstidx w → ℂ) (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (G.upper (e (x, q.1.2.1))) * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def Xi0 (q : RR k r w) : B.SS k r :=
  ((q.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ * Matrix.of q.1.2.2)),
   (q.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2)))

def rhoX (x : C2.Lstidx w → ℂ) : B.Mat k r := Dx2.Rad.rhoF S γ w x

def rhoP (x : C2.Lstidx w → ℂ) : B.Mat k r := γ⁻¹ * (rhoX S γ w x)⁻¹ * γ

def m0L (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ * (rhoX S γ w x)⁻¹ * C2.tauM k r S.z (G.upper (e (x, y)))

def m0R (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : B.Mat k r :=
  (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper u))⁻¹ * rhoP S γ w x * C2.tauM k r S.z' (G.upper u)

def Tx (x : C2.Lstidx w → ℂ) (q : RR k r w) : RR k r w :=
  ((q.1.1, (q.1.2.1, Matrix.of.symm (m0L S γ w e x q.1.2.1 * Matrix.of q.1.2.2))),
   (q.2.1, (utc (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1),
     Matrix.of.symm (m0R S γ w x q.2.2.1 * Matrix.of q.2.2.2))))

def nuR (μ0 μ0' : Measure (Mt k r)) : Measure (RR k r w) :=
  (S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)).prod
    (S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'))

def Tt (p : (C2.Lstidx w → ℂ) × RR k r w) : (C2.Lstidx w → ℂ) × RR k r w := (p.1, Tx S γ w e p.1 p.2)

end defs

section alg

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

include hγ hd hZw hpos in
theorem good : Dx2.Rad.Good S γ w d :=
  ⟨fun x => Dx2.Rad.exists_rho S hγ hpos hd hZw x, Dx2.Rad.u_inj S hγ hpos hd hZw,
    fun _ hρ => Dx2.Rad.u_lstg S hγ hpos hd hZw hρ⟩

include hγ hd hZw hpos in
theorem rhoX_spec (x : C2.Lstidx w → ℂ) :
    rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := by
  have h := Dx2.Rad.exists_rho S hγ hpos hd hZw x
  have e1 : rhoX S γ w x = h.choose := by
    show Formalism.FourierDecayAlt.D.rhoOfU S γ (Dx2.Rad.low w x)ᴴ = _
    unfold Formalism.FourierDecayAlt.D.rhoOfU
    rw [dif_pos h]
  rw [e1, UC.lowS_eq_low]
  exact h.choose_spec

include hγ hd hZw hpos in
theorem rhoP_N (x : C2.Lstidx w → ℂ) : rhoP S γ w x ∈ Nset k r := by
  have h1 := (rhoX_spec S hγ hd hZw hpos x).1
  have hu := PI.StabSplit.GV_unit k r hγ
  have e : rhoP S γ w x = (γ⁻¹ * rhoX S γ w x * γ)⁻¹ := by
    unfold rhoP
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, mul_assoc]
  rw [e]
  exact Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv h1.2

theorem lowPH_UT (y : C2.LPidx w → ℂ) : (lowP w y)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowerUnipotent_mem w y).1

theorem lowSH_UT (x : C2.Lstidx w → ℂ) : (lowS w x)ᴴ ∈ C2.UTset (r + 1) :=
  UC.LT_ct (UC.lowS_mem w x).1

include he in
theorem upper_e_UT (p : (C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) : G.upper (e p) ∈ C2.UTset (r + 1) := by
  rw [he p]
  exact UC.prod_UT w p

include hγ hd hZw hpos he in
theorem left_stabilizer_mem (x : C2.Lstidx w → ℂ) (y : C2.LPidx w → ℂ) : m0L S γ w e x y ∈ C2.N0set k r S.z := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z hz
  obtain ⟨hρR, hρu⟩ := rhoX_spec S hγ hd hZw hpos x
  have hτv := A.tau_N hz (lowPH_UT y)
  have hτe := A.tau_N hz (upper_e_UT e he (x, y))
  have h1 : (C2.tauM k r S.z (lowP w y)ᴴ)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hτv
  have h2 : (rhoX S γ w x)⁻¹ ∈ Nset k r := WeylGroupFacts.mem_n_inv hρR.1
  have hN : m0L S γ w e x y ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 h2) hτe
  refine ⟨hN, ?_⟩
  unfold m0L
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 h2))).2.2 _ (A.n_in_S hτe),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S h2), A.uMap_inv hz hτv, A.uMap_inv hz hρR.1, hρu,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (lowPH_UT y)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z hz _ (upper_e_UT e he (x, y))).2.2, he]
  calc ((lowP w y)ᴴ).adjugate * ((lowS w x)ᴴ).adjugate * ((lowS w x)ᴴ * (lowP w y)ᴴ)
      = ((lowP w y)ᴴ).adjugate * (((lowS w x)ᴴ).adjugate * (lowS w x)ᴴ) * (lowP w y)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [Matrix.adjugate_mul, A.det_UT (lowSH_UT x), one_smul, Matrix.mul_one, Matrix.adjugate_mul,
          A.det_UT (lowPH_UT y), one_smul]

include hγ hd hZw hpos in
theorem uP_UT (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) :
    C2.uMap k r S.z' (rhoP S γ w x) * G.upper u ∈ C2.UTset (r + 1) := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτ := A.tau_N hz' (UC.upper_mem u)
  rw [← (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2,
    ← (hUF.1 _ (A.n_in_S hρ)).2.2 _ (A.n_in_S hτ)]
  exact (hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul hρ hτ))).2.1

include hγ hd hZw hpos in
theorem right_stabilizer_mem (x : C2.Lstidx w → ℂ) (u : G.UT (r + 1) → ℂ) : m0R S γ w x u ∈ C2.N0set k r S.z' := by
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hUF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r S.z' hz'
  have hρ := rhoP_N S hγ hd hZw hpos x
  have hτa := A.tau_N hz' (uP_UT S hγ hd hZw hpos x u)
  have hτ := A.tau_N hz' (UC.upper_mem u)
  have h1 := WeylGroupFacts.mem_n_inv hτa
  have hN : m0R S γ w x u ∈ Nset k r := WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul h1 hρ) hτ
  refine ⟨hN, ?_⟩
  unfold m0R
  rw [(hUF.1 _ (A.n_in_S (WeylGroupFacts.mem_n_mul h1 hρ))).2.2 _ (A.n_in_S hτ),
    (hUF.1 _ (A.n_in_S h1)).2.2 _ (A.n_in_S hρ), A.uMap_inv hz' hτa,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (uP_UT S hγ hd hZw hpos x u)).2.2,
    (Formalism.FourierDecayAlt.P.c2_tau_mem k r S.z' hz' _ (UC.upper_mem u)).2.2, Matrix.mul_assoc,
    Matrix.adjugate_mul, A.det_UT (uP_UT S hγ hd hZw hpos x u), one_smul]

include hγ hd hZw hpos he in

theorem Xi_eq (x : C2.Lstidx w → ℂ) (q : RR k r w) :
    Xi S w e x q = C6.actR γ (rhoX S γ w x) (Xi0 S w (Tx S γ w e x q)) := by
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  have hρ := (rhoX_spec S hγ hd hZw hpos x).1
  have hρu : IsUnit (rhoX S γ w x).det := PI.StabSplit.GV_unit k r hρ.1.1
  have hγu : IsUnit γ.det := PI.StabSplit.GV_unit k r hγ
  have hA : IsUnit (C2.tauM k r S.z (lowP w q.1.2.1)ᴴ).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz (lowPH_UT q.1.2.1)).1
  have hM := uP_UT S hγ hd hZw hpos x q.2.2.1
  have hB : IsUnit (C2.tauM k r S.z' (C2.uMap k r S.z' (rhoP S γ w x) * G.upper q.2.2.1)).det :=
    PI.StabSplit.GV_unit k r (A.tau_N hz' hM).1
  simp only [Xi, Xi0, Tx, C6.actR, Equiv.apply_symm_apply, UC.upper_utc hM, m0L, m0R, ← mul_assoc,
    Matrix.mul_nonsing_inv_cancel_right _ _ hA, Matrix.mul_nonsing_inv_cancel_right _ _ hB,
    Matrix.mul_nonsing_inv _ hρu]
  simp only [rhoP, ← mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hρu,
    Matrix.mul_nonsing_inv_cancel_right _ _ hγu, Matrix.nonsing_inv_mul _ hγu, one_mul]

end alg

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
