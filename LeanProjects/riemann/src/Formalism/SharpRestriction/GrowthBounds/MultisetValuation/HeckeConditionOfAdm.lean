import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HkEsymmSmul
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem hk_point (Y : Pend X) (hC : CountLoc) (hT : RestTmFQ X)
    (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} {cK : Y.Kc} (ha : a ≠ 0) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ)
    (hTh : ThEq Y a a' v j) {Cl Yb : Type} [Fintype Cl] [Fintype Yb] {wt : Cl → ℕ} {La : Cl → Yb → X.Lt j}
    (hS : KSum Y j cK Cl Yb wt La) (hAd : KAdj Y j Cl Yb wt La)
    (i : ℕ) (F : X.Fm j) (hF : F ∈ X.FQ j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup)
    (hL' : (X.Pj (j + 1)).IsLatTup L') :
    X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ l ∈ range (i + 1), (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) •
        X.Kz j (X.Tm v (i - l) j F) c' L' := by
  obtain ⟨hlat, _, h4⟩ := hS
  apply MvPolynomial.map_injective (algebraMap X.G.Kf Y.Kc) (algebraMap X.G.Kf Y.Kc).injective
  have eT : X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1) :=
    Tminus_eq (X.Pj (j + 1)) (X.vJ (j + 1) v) i (X.Kz j F c') L'
  rw [eT, map_sum, map_sum]
  have eL : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1)) =
        ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
          Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) := by
    intro L1 hL1
    exact h4 F hF c' _ (hk_latTup_update _ hL' _ L1 ((mem_EE _).1 hL1).1)
  rw [Finset.sum_congr rfl eL, Finset.sum_comm]
  have eL2 : ∀ x ∈ (Finset.univ : Finset Cl), ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
        Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) =
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, (cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ •
            Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro x _
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ker_dn_sum hC hp ha ha' hTh (La x y) (hlat x y) c' L' hL' i _
  rw [Finset.sum_congr rfl eL2]
  have eR : ∀ l ∈ range (i + 1), MvPolynomial.map (algebraMap X.G.Kf Y.Kc)
      ((cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • X.Kz j (X.Tm v (i - l) j F) c' L') =
      (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • (cK • ∑ x : Cl,
        ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro l _
    rw [map_smulK Y, h4 _ (hT v (i - l) j F hF) c' L' hL', hAd v (i - l) F hF (c', L') hL',
      Finset.smul_sum (r := cK)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl eR]
  have hs : ∀ (r : X.G.Kf) (z : XspC (X.Pj (j + 1)) Y.Kc), r • z = algebraMap X.G.Kf Y.Kc r • z :=
    fun r z => (algebraMap_smul Y.Kc r z).symm
  simp only [hs, Finset.smul_sum, smul_smul]
  symm
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun A1 _ => ?_
  congr 1
  simp only [map_mul, map_inv₀, map_natCast]
  ring

theorem heckeCondition_of_adm (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hC : CountLoc) (hT : RestTmFQ X) :
    RestHecke X := by
  obtain ⟨_, _, _, _, _, h3b, h4, h5, h5b, h6, _, _, _⟩ := hA
  intro v
  have hfr := frac_of_place X v
  have he := eO_pos X v
  have hp : (p : X.G.Kf) ≠ 0 := pKf_ne Y
  have h5' : ∀ j, ∃ a a' : X.G.Kf, j < X.mm → (X.vEqK a 0 ∧ X.vEqK a' 0 ∧ ThEq Y a a' v j) := by
    intro j
    by_cases hj : j < X.mm
    · obtain ⟨u, u', h1, h2, h3⟩ := h5 v j hj
      exact ⟨u, u', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, 1, fun h => absurd h hj⟩
  choose a a' H using h5'
  refine ⟨fun l => (a (l - 1) * a' (l - 1))⁻¹, fun l => a (l - 1) * (p : X.G.Kf) ^ (X.vm v l), ?_, ?_, ?_⟩
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2, _⟩ := H (l - 1) (by omega)
    have := vEqK_inv X hfr (vEqK_mul X hfr h1 h2)
    simpa using this
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, _, _⟩ := H (l - 1) (by omega)
    have := vEqK_mul X hfr h1 (vEqK_ppow X hfr he (X.vm v l))
    simpa using this
  · intro j hj i F hF
    obtain ⟨h1, h2, hTh⟩ := H j hj
    obtain ⟨cK, Cl, Yb, iC, iY, wt, La, hS, hAd⟩ := ksa_of_adm D h4 h5b h6 hj
    have ha := vEqK.ne_zero X h1
    have ha' := vEqK.ne_zero X h2
    show X.ecal v i (j + 1) (X.Kz j F) = ((a j * a' j)⁻¹ ^ i) • X.Kz j (∑ l ∈ range (i + 1),
      (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
        (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)
    funext c' L'
    by_cases hL' : (X.Pj (j + 1)).IsLatTup L'
    · have eR : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) =
          ∑ l ∈ range (i + 1),
            ((MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
              (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
              (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ))))) •
              X.Kz j (X.Tm v (i - l) j F) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold Sys.ecal
        rw [map_smul, map_smul, smul_smul]
        rfl
      rw [eR]
      show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
        X.Tm v i (j + 1) (X.Kz j F) c' L' = _
      rw [hk_point Y hC hT hp ha ha' v j hTh hS hAd i F hF c' L' hL']
      simp only [Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      congr 1
      have := hk_coef X hp (a j) (a' j) ha v j i l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
      rw [mul_assoc ((a j * a' j)⁻¹ ^ i)] at this
      rw [← this]
      ring
    · have e1 : X.Tm v i (j + 1) (X.Kz j F) c' L' = 0 :=
        (restTmEquiv X (j + 1) v i _ (Eqv_of_FQ X (h3b j hj F hF))).1 c' L' hL'
      have e2 : X.ecal v i (j + 1) (X.Kz j F) c' L' = 0 := by
        show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
          X.Tm v i (j + 1) (X.Kz j F) c' L' = 0
        rw [e1, smul_zero]
      rw [e2]
      have hmem : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) ∈ X.FQ (j + 1) :=
        h3b j hj _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
          (Submodule.smul_mem _ _ (hT v (i - l) j F hF)))
      rw [Pi.smul_apply, Pi.smul_apply, FQ_zero_off X hmem c' L' hL', smul_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
