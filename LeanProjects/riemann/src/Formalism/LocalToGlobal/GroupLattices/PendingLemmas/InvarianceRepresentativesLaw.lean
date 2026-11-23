import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist

noncomputable section

namespace Formalism.L2.G.Pend

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

section Gen

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def KapLaw (Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) : Prop :=
  ∀ j (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ), (X.Pj j).IsLatTup L →
    Th j (c, (X.Lv.lev j c).smul γ L) La' =
      MvPowerSeries.C ((kapG X Kc j c γ)⁻¹) * SA X Kc j (gamAt X j c γ) (Th j (c, L) La')

variable (hfin : ∀ j c, (X.Lv.lev j c).FinClasses)
  (ThR : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc)

def StabLaw : Prop :=
  ∀ j (c : X.Lv.comp j) (L0 : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (ε : (X.Lv.lev j c).Γ), (c, L0) ∈ repOf X.Lv hfin j →
    (X.Lv.lev j c).smul ε L0 = L0 →
      MvPowerSeries.C ((kapG X Kc j c ε)⁻¹) * SA X Kc j (gamAt X j c ε) (ThR j (c, L0) La') = ThR j (c, L0) La'

theorem SA_C_mul (j : ℕ) (B : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) (a : Kc)
    (f : MvPowerSeries (X.ZA j) Kc) :
    SA X Kc j B (MvPowerSeries.C a * f) = MvPowerSeries.C a * SA X Kc j B f := by
  unfold SA
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_actS X Kc j B), map_mul,
    MvPowerSeries.coe_substAlgHom (hasSubst_actS X Kc j B), MvPowerSeries.subst_C]

theorem thN_eq (j : ℕ) (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) :
    thFN X Kc hfin (thGeo X Kc hfin ThR) j (c, L) La' =
      MvPowerSeries.C ((kapG X Kc j c (delt X hfin j c L))⁻¹) * SA X Kc j (gamAt X j c (delt X hfin j c L))
        (ThR j (c, (X.Lv.lev j c).smul (delt X hfin j c L)⁻¹ L) La') := rfl

theorem kapLaw_of_stabLaw (hp0 : (p : Kc) ≠ 0) (hS : StabLaw X Kc hfin ThR) :
    KapLaw X Kc (thFN X Kc hfin (thGeo X Kc hfin ThR)) := by
  intro j c L La' γ hL
  have hL' : (X.Pj j).IsLatTup ((X.Lv.lev j c).smul γ L) := (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ L).2 hL
  obtain ⟨L0, h0, e0⟩ := delt_spec X hfin j c L hL
  obtain ⟨L1, h1, e1⟩ := delt_spec X hfin j c _ hL'
  rw [thN_eq, thN_eq]
  generalize delt X hfin j c L = δ at e0 ⊢
  generalize delt X hfin j c ((X.Lv.lev j c).smul γ L) = δ' at e1 ⊢
  have e2 : (X.Lv.lev j c).smul γ L = (X.Lv.lev j c).smul (γ * δ) L0 := by
    rw [lsmul_mul, ← e0]
  have h10 : L1 = L0 := (repOf_ex X.Lv hfin j c _ hL').unique ⟨h1, δ', e1⟩ ⟨h0, γ * δ, e2⟩
  subst h10
  have r1 : (X.Lv.lev j c).smul δ'⁻¹ ((X.Lv.lev j c).smul γ L) = L1 := by
    conv_lhs => rw [e1]
    exact lsmul_inv_lsmul _ _ _
  have r0 : (X.Lv.lev j c).smul δ⁻¹ L = L1 := by
    conv_lhs => rw [e0]
    exact lsmul_inv_lsmul _ _ _
  have hst : (X.Lv.lev j c).smul ((γ * δ)⁻¹ * δ') L1 = L1 := by
    rw [lsmul_mul, ← e1, e2, lsmul_inv_lsmul]
  rw [r1, r0]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (γ * δ)⁻¹ * δ' := ⟨_, rfl⟩
  rw [← hε] at hst
  have hd : δ' = γ * δ * ε := by rw [hε]; group
  subst hd
  have hS' := hS j c L1 La' ε h0 hst
  rw [SA_C_mul, SA_mul, ← gamAt_mul, ← mul_assoc, ← map_mul]
  conv_rhs => rw [← hS']
  rw [SA_C_mul, SA_mul, ← gamAt_mul, ← mul_assoc, ← map_mul, kapG_mul X Kc hp0, kapG_mul X Kc hp0, mul_inv, mul_inv]

theorem ker_law (hp0 : (p : Kc) ≠ 0) {Gd : ∀ j, (X.Pj j).Xsp → Prop} (hD : DelEquivOn X Kc Gd)
    (Th : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (X.ZA j) Kc) (hK : KapLaw X Kc Th) (j : ℕ)
    (c : X.Lv.comp j) (L : (X.Pj j).Tup) (La' : X.Lt (j + 1)) (γ : (X.Lv.lev j c).Γ) (G : (X.Pj j).Xsp)
    (hL : (X.Pj j).IsLatTup L) (hGood : Gd j G) (t : X.G.Kf) :
    (eSX X j (c, (X.Lv.lev j c).smul γ L) * t) •
        delF X Kc j ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G)
          (Th j (c, (X.Lv.lev j c).smul γ L) La') =
      (eSX X j (c, L) * t) • delF X Kc j G (Th j (c, L) La') := by
  have hpK : (p : X.G.Kf) ≠ 0 := fun h => hp0 (by rw [← map_natCast (algebraMap X.G.Kf Kc), h, map_zero])
  have e1 : ((((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O) • (X.Lv.lev j c).actX γ G) =
      (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)) •
        (X.Pj j).natAct (fun v => (X.Lv.lev j c).act v γ) G := (algebraMap_smul X.G.Kf _ _).symm
  have e2 : delF X Kc j ((X.Pj j).natAct (fun v => (X.Lv.lev j c).act v γ) G)
      (SA X Kc j (gamAt X j c γ) (Th j (c, L) La')) =
        cA X Kc j (gamAt X j c γ) • delF X Kc j G (Th j (c, L) La') :=
    hD j (fun v => (X.Lv.lev j c).act v γ) G (Th j (c, L) La') hGood
  rw [hK j c L La' γ hL, delF_C_mul, e1, map_smul, LinearMap.smul_apply, e2, eSX_smul X hpK j c γ L hL]
  rw [← algebraMap_smul Kc (eSX X j (c, L) * pP X X.G.Kf j (gamAt X j c γ) * t),
    ← algebraMap_smul Kc (algebraMap X.G.O X.G.Kf (((X.Lv.lev j c).χ γ : X.G.Oˣ) : X.G.O)),
    ← algebraMap_smul Kc (eSX X j (c, L) * t), smul_smul, smul_smul, smul_smul]
  congr 1
  have hk := kapG_ne_zero X Kc hp0 j c γ
  have hk' := kapG_eq X Kc j c γ
  rw [map_mul, map_mul, map_mul, pPart_map]
  show _ * (kapG X Kc j c γ)⁻¹ * chiC X Kc j c γ * cA X Kc j (gamAt X j c γ) = _
  field_simp
  rw [hk']
  ring

end Gen

section Cp

variable [IsFractionRing X.G.O X.G.Kf] (E : CEmb X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    (be : MvPowerSeries (Fin 2) (K0 p))

end Cp

section Top

variable [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (hst : FinStab X.Lv)
    {g : Formalism.MainNotions.GL3Theta.G1 p} (hLT : LTIso g) {T : Type} (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ T)
    (F : ∀ j, X.Lt j → X.Lt (j + 1) → MvPowerSeries (T × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

end Top

end Formalism.L2.G.Pend
