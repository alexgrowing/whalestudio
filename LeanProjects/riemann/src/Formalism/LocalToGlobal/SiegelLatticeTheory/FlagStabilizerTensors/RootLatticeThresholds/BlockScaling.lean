import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVecFin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ModelMeasure
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.StandardCoordinates
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PiMeasureScaling
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.TriangularProducts
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotientSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealConjugatorData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.BlockScaling

theorem rdE_eq_rd' (D : D7) : D.host.rdE = Formalism.FourierDecayAlt.S6.rd D.host.E := by
  unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
  rw [Int.cast_abs, one_div]

theorem scal_of_bD : ∀ (l : List (ℕ × ℂ)) (a b : ℕ), Formalism.MainNotions.BigCellDensity.bD l a = Formalism.MainNotions.BigCellDensity.bD l b →
    Formalism.FourierDecayAlt.D.ptScal l a = Formalism.FourierDecayAlt.D.ptScal l b
  | [], _, _, _ => rfl
  | (s, t) :: l, a, b, h => by
    simp only [Formalism.MainNotions.BigCellDensity.bD] at h
    simp only [Formalism.FourierDecayAlt.D.ptScal]
    split_ifs at h ⊢ with ha hb hb <;> first | rfl | omega | exact scal_of_bD l _ _ (by omega)

theorem scal_partner : ∀ (l : List (ℕ × ℂ)) (a : ℕ), Formalism.FourierDecayAlt.D.ptScal l (Formalism.FourierDecayAlt.D.ptPartner l a) = Formalism.FourierDecayAlt.D.ptScal l a
  | [], _ => rfl
  | (s, t) :: l, a => by
    by_cases ha : a < s
    · have hp : Formalism.FourierDecayAlt.D.ptPartner ((s, t) :: l) a = s - 1 - a := by simp [Formalism.FourierDecayAlt.D.ptPartner, ha]
      rw [hp]
      simp [Formalism.FourierDecayAlt.D.ptScal, ha, show s - 1 - a < s by omega]
    · have hp : Formalism.FourierDecayAlt.D.ptPartner ((s, t) :: l) a = s + Formalism.FourierDecayAlt.D.ptPartner l (a - s) := by
        simp [Formalism.FourierDecayAlt.D.ptPartner, ha]
      rw [hp]
      simp only [Formalism.FourierDecayAlt.D.ptScal, if_neg ha, if_neg (show ¬ (s + Formalism.FourierDecayAlt.D.ptPartner l (a - s) < s) by omega),
        Nat.add_sub_cancel_left]
      exact scal_partner l _

theorem dPt_free {r : ℕ} (γ : Formalism.MainNotions.S.Point ℂ (r + 1)) (q : Formalism.FourierDecayAlt.C2.Lstidx (Formalism.MainNotions.BigCellDensity.wPt γ)) :
    Formalism.MainNotions.BigCellDensity.dPt γ (Formalism.MainNotions.BigCellDensity.wPt γ q.1.1) = Formalism.MainNotions.BigCellDensity.dPt γ (Formalism.MainNotions.BigCellDensity.wPt γ q.1.2) := by
  have hb := (Formalism.MainNotions.BigCellDensity.root_iff γ q.1.2 q.1.1 q.2.1).2 q.2.2
  rw [Formalism.MainNotions.BigCellDensity.blockIdx_bD, Formalism.MainNotions.BigCellDensity.blockIdx_bD] at hb
  unfold Formalism.MainNotions.BigCellDensity.dPt
  rw [Formalism.MainNotions.BigCellDensity.wPt_val, Formalism.MainNotions.BigCellDensity.wPt_val, scal_partner, scal_partner]
  exact scal_of_bD _ _ _ hb.symm

theorem ico_int (s : ℕ) (f : ℤ → ℝ) :
    ∏ m ∈ Finset.Ico (1 : ℤ) (s : ℤ), f m ^ ((s : ℤ) - m) = ∏ m ∈ Finset.Ico 1 s, f (m : ℤ) ^ (s - m) := by
  refine Finset.prod_nbij' (fun m : ℤ => m.toNat) (fun m : ℕ => (m : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Ico] at hm ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Ico] at hm ⊢
    omega
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    omega
  · intro m _
    simp
  · intro m hm
    simp only [Finset.mem_Ico] at hm
    have h1 : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    rw [h1, show (s : ℤ) - m = ((s - m.toNat : ℕ) : ℤ) by omega, zpow_natCast]

theorem toStd_fst (r : ℕ) (g : ℝ) : ∀ (o : ℕ) (L : Formalism.FourierDecayAlt.C.LPt),
    (Formalism.FourierDecayAlt.D.toStd r g o L).map Prod.fst = L.map Prod.fst
  | _, [] => rfl
  | o, (s, t) :: L => by
    simp only [Formalism.FourierDecayAlt.D.toStd, List.map_cons]
    rw [toStd_fst r g (o + s) L]

theorem blkOf_eq_bi {K : Type*} : ∀ (L : List (K × ℕ)) (i : ℕ),
    Formalism.L2.SG.RealObj.blkOf L i = Formalism.L2.SG.TriangularProducts.bi (L.map Prod.snd) i
  | [], _ => rfl
  | (t, s) :: L, i => by
    simp only [Formalism.L2.SG.RealObj.blkOf, Formalism.L2.SG.TriangularProducts.bi, List.map_cons]
    split_ifs
    · rfl
    · rw [blkOf_eq_bi L (i - s), add_comm]

theorem conj_trG {n N : ℕ} {ε : Fin n → Bool} {Q : Matrix (Fin n) (Fin N) ℂ} {Qi : Matrix (Fin N) (Fin n) ℂ}
    (hQiQ : Qi * Q = 1) (hQQi : Q * Qi = 1) (γ hh hh' y : Formalism.REAL.UJ ε) :
    (Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ * hh'))⁻¹ * Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * y * hh) *
              Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ * hh') = Qi * Formalism.MainNotions.S.uMat (hh'⁻¹ * (γ⁻¹ * y * γ) * hh') * Q := by
  have hinv : (Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ * hh'))⁻¹ = Formalism.L2.SG.RealObj.trG Q Qi ((hh⁻¹ * γ * hh')⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    unfold Formalism.L2.SG.RealObj.trG
    calc Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh') * Q * (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')⁻¹ * Q)
        = Qi * (Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh') * (Q * Qi) * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')⁻¹) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hQQi, Matrix.mul_one, show Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh') * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')⁻¹ =
          Formalism.MainNotions.S.uMat ((hh⁻¹ * γ * hh') * (hh⁻¹ * γ * hh')⁻¹) from rfl, mul_inv_cancel]
        show Qi * 1 * Q = 1
        rw [Matrix.mul_one, hQiQ]
  rw [hinv]
  unfold Formalism.L2.SG.RealObj.trG
  have e : hh'⁻¹ * (γ⁻¹ * y * γ) * hh' = (hh⁻¹ * γ * hh')⁻¹ * (hh⁻¹ * y * hh) * (hh⁻¹ * γ * hh') := by
    group
  rw [e]
  calc Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')⁻¹ * Q * (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * y * hh) * Q) *
        (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh') * Q)
      = Qi * (Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')⁻¹ * (Q * Qi) * Formalism.MainNotions.S.uMat (hh⁻¹ * y * hh) * (Q * Qi) *
          Formalism.MainNotions.S.uMat (hh⁻¹ * γ * hh')) * Q := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [hQQi, Matrix.mul_one, Matrix.mul_one]
      rfl

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf in

theorem rset_of_stV {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
    {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
    (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (hh hh' : Formalism.REAL.UJ (X.B.I.ε v))
    (he : ∀ a, Formalism.MainNotions.S.uMat hh *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : Formalism.MainNotions.S.uMat hh *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u))
    (he' : ∀ a, Formalism.MainNotions.S.uMat hh' *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz' : Formalism.MainNotions.S.uMat hh' *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u'))
    (hzW : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u)))
    (hzW' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')))
    (y : Formalism.REAL.UJ (X.B.I.ε v)) (hy : y ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) :
    Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * y * hh) ∈
      Formalism.FourierDecayAlt.C6.Rset (Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ v * hh')) := by
  have hQiQ := hT.1
  have hQQi := hT.2.1
  have hcoe : ∀ a b c : Formalism.REAL.UJ (X.B.I.ε v), Formalism.MainNotions.S.uMat (a⁻¹ * b * c) = (Formalism.MainNotions.S.uMat a)⁻¹ * Formalism.MainNotions.S.uMat b *
      Formalism.MainNotions.S.uMat c := fun a b c => by
    rw [show Formalism.MainNotions.S.uMat (a⁻¹ * b * c) = Formalism.MainNotions.S.uMat a⁻¹ * Formalism.MainNotions.S.uMat b * Formalism.MainNotions.S.uMat c from rfl,
      Formalism.L2.SG.RealConjugatorData.uMat_inv']
  have hu : ∀ a : Formalism.REAL.UJ (X.B.I.ε v), IsUnit (Formalism.MainNotions.S.uMat a).det := fun a => by
    have := Formalism.L2.SG.RealConjugatorData.uMat_mul_inv a
    exact Matrix.isUnit_det_of_right_inverse this
  refine ⟨?_, ?_⟩
  ·
    have h1 := Formalism.L2.SG.QuotientSpan.inN_conj (hh := Formalism.MainNotions.S.uMat hh) hh.2 (hu hh) he hz hy.1
    rw [← hcoe] at h1
    exact (Formalism.L2.SG.QuotientSpan.inN_iff v hl hT _ hzW _ (hh⁻¹ * y * hh).2).1 h1
  ·
    have hinv : (Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ v * hh'))⁻¹ = Formalism.L2.SG.RealObj.trG Q Qi ((hh⁻¹ * γ v * hh')⁻¹) := by
      refine Matrix.inv_eq_right_inv ?_
      unfold Formalism.L2.SG.RealObj.trG
      calc Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh') * Q * (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')⁻¹ * Q)
          = Qi * (Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh') * (Q * Qi) * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')⁻¹) * Q := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hQQi, Matrix.mul_one, show Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh') * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')⁻¹ =
            Formalism.MainNotions.S.uMat ((hh⁻¹ * γ v * hh') * (hh⁻¹ * γ v * hh')⁻¹) from rfl, mul_inv_cancel]
          show Qi * 1 * Q = 1
          rw [Matrix.mul_one, hQiQ]
    have hconj : (Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ v * hh'))⁻¹ * Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * y * hh) *
        Formalism.L2.SG.RealObj.trG Q Qi (hh⁻¹ * γ v * hh') = Qi * Formalism.MainNotions.S.uMat (hh'⁻¹ * ((γ v)⁻¹ * y * γ v) * hh') * Q := by
      rw [hinv]
      unfold Formalism.L2.SG.RealObj.trG
      have e : hh'⁻¹ * ((γ v)⁻¹ * y * γ v) * hh' = (hh⁻¹ * γ v * hh')⁻¹ * (hh⁻¹ * y * hh) * (hh⁻¹ * γ v * hh') := by
        group
      rw [e]
      calc Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')⁻¹ * Q * (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * y * hh) * Q) *
            (Qi * Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh') * Q)
          = Qi * (Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')⁻¹ * (Q * Qi) * Formalism.MainNotions.S.uMat (hh⁻¹ * y * hh) * (Q * Qi) *
              Formalism.MainNotions.S.uMat (hh⁻¹ * γ v * hh')) * Q := by simp only [Matrix.mul_assoc]
        _ = _ := by
          rw [hQQi, Matrix.mul_one, Matrix.mul_one]
          rfl
    rw [hconj]
    have h1 := Formalism.L2.SG.QuotientSpan.inN_conj (hh := Formalism.MainNotions.S.uMat hh') hh'.2 (hu hh') he' hz' hy.2
    rw [← hcoe] at h1
    exact (Formalism.L2.SG.QuotientSpan.inN_iff v hl hT _ hzW' _ (hh'⁻¹ * ((γ v)⁻¹ * y * γ v) * hh').2).1 h1

end Formalism.L2.SG.BlockScaling

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.Carrier.JointQuot

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

section ZsMq

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau)
  (he : PlaceTie X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)
  (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ) (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
  (T : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.D.LevTower D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
  (hT : ∀ j, Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (T j).base.z' = ((D.mem u').A.T : ℝ))
  (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
  (χ : ℝ → ℝ) (sg : Fin (nfE D) → ℂ) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
  (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
  (top : ∀ j : Fin (nfE D), (Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j))) →
    List Formalism.FourierDecayAlt.C.Letter → Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ) (A₀ : ℝ)
  (Mo : ModelsFor (sOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀)))

local notation "PP" => CarrierOf (carrierInOf X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀) Mo

theorem measPinAt_of (sc : ℝ) (hsc : 0 < sc) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (hFX : (PP).FromX) (hB : (PP).Base i0 i0')
    (hemb : ∀ j x, (PP).S.emb j (X.ιE x) = X.B.I.φ ((PP).τ j) x)
    (hbase : ∀ v, Formalism.FourierDecayAlt.D.IsBaseFrame ((PP).T ((PP).τ.symm v)).base ((PP).ν' ((PP).τ.symm v))
      ((PP).m₀ ((PP).τ.symm v))) :
    MeasPinAt X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc i0 i0' := by
  intro p w hp hw h h' hD v μRv hHaar hpin hloc
  obtain ⟨hZp, -, -, hδG⟩ := orbVec_data X u u' e he hv C CA de de' l grid grid1 T hT fc χ sg ν' m₀ top A₀ Mo sc hsc
    i0 i0' hFX hB hemb hbase p w hp hw h h' hD v
  obtain ⟨hQ, hz, hz', -⟩ := hFX v
  set p' := Formalism.FourierDecayAlt.D.toStd (PP).S.G.r (PP).S.g 1 (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p) with hp'

  obtain ⟨pN, hpN⟩ : ∃ pN : Formalism.MainNotions.S.Point ℂ (D.R.rS + 1), pN.1 = p'.map Prod.swap := ⟨⟨p'.map Prod.swap,
      fun x hx => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
        exact ⟨(hloc.1 b hb).2, (hloc.1 b hb).1⟩, by
      have h2 := hloc.2
      simp only [Formalism.FourierDecayAlt.D.ptSize] at h2
      rw [List.map_map]
      exact h2⟩, rfl⟩
  have hswap : pN.1.map Prod.swap = p' := by
    rw [hpN, List.map_map]
    exact List.map_id'' (fun x => Prod.swap_swap x) p'
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS ((PP).T ((PP).τ.symm v)).base.z ((PP).T ((PP).τ.symm v)).base.z'
      (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)) =
      Formalism.FourierDecayAlt.C2.monoP (Formalism.MainNotions.BigCellDensity.wPt pN) (Formalism.MainNotions.BigCellDensity.dPt pN) := by
    rw [hZp, ← Formalism.MainNotions.BigCellDensity.ptMatN_mono pN, hswap]
  have hw' : (hloc.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p' : Equiv.Perm (Fin (D.R.rS + 1))) = Formalism.MainNotions.BigCellDensity.wPt pN := by
    refine Equiv.ext fun x => Fin.ext ?_
    calc ((hloc.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p' : Equiv.Perm (Fin (D.R.rS + 1))) x).val
        = (Formalism.FourierDecayAlt.D.ptPerm p' ⟨x.val, by rw [hloc.2]; exact x.isLt⟩).val := Formalism.MainNotions.BigCellDensity.cast_perm_val _ _ _
      _ = Formalism.FourierDecayAlt.D.ptPartner p' x.val := (Formalism.FourierDecayAlt.P.ptPerm_spec p' (D.R.rS + 1) hloc).1 _
      _ = Formalism.FourierDecayAlt.D.ptPartner (pN.1.map Prod.swap) x.val := by rw [hswap]
      _ = (Formalism.MainNotions.BigCellDensity.wPt pN x).val := (Formalism.MainNotions.BigCellDensity.wPt_val pN x).symm
  have hdm : ∀ q : Formalism.FourierDecayAlt.C2.Lstidx (Formalism.MainNotions.BigCellDensity.wPt pN),
      ‖Formalism.MainNotions.BigCellDensity.dPt pN (Formalism.MainNotions.BigCellDensity.wPt pN q.1.1)‖ = ‖Formalism.MainNotions.BigCellDensity.dPt pN (Formalism.MainNotions.BigCellDensity.wPt pN q.1.2)‖ :=
    fun q => by rw [Formalism.L2.SG.BlockScaling.dPt_free pN q]

  have hT' : Formalism.L2.SG.LocWSOf.IsTranspC X v (-(Complex.I * (((PP).S.g : ℝ) : ℂ)) / (2 * (Real.pi : ℂ))) D.R.k D.R.rS
      ((PP).Q v) ((PP).Qi v) := hQ
  have hg0 : (0 : ℝ) < ((PP).S.g : ℝ) := by
    show (0 : ℝ) < ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
    push_cast
    exact mul_pos (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1) (by exact_mod_cast (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2)
  set lam : ℂ := -(Complex.I * (((PP).S.g : ℝ) : ℂ)) / (2 * (Real.pi : ℂ)) with hlam
  have hl : lam ≠ 0 := by
    refine div_ne_zero (neg_ne_zero.2 (mul_ne_zero Complex.I_ne_zero ?_)) ?_
    · exact_mod_cast hg0.ne'
    · exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hzW : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS ((PP).Qi v *ᵥ rv X.B.I v (X.zR u)) := by
    have h1 := ((PP).T ((PP).τ.symm v)).base.z_mem
    exact hz ▸ h1
  have hzW' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS ((PP).Qi v *ᵥ rv X.B.I v (X.zR u')) := by
    have h1 := ((PP).T ((PP).τ.symm v)).base.z'_mem
    exact hz' ▸ h1
  have hΦ1 : Measurable (fun s : Formalism.REAL.UJ (X.B.I.ε v) => (h v)⁻¹ * s * h v) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hΦ2 : Measurable (fun s : Formalism.REAL.UJ (X.B.I.ε v) => Matrix.of.symm (trG ((PP).Q v) ((PP).Qi v) s)) := by
    refine Continuous.measurable ?_
    unfold trG
    exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const
  have hconc : ((μRv.map (fun s => (h v)⁻¹ * s * h v)).map
      (fun s => Matrix.of.symm (trG ((PP).Q v) ((PP).Qi v) s))) {x | Matrix.of x ∉ Formalism.FourierDecayAlt.C6.Rset
        (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))} = 0 := by
    have hS : IsClosed {x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset
        (trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))} :=
      (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.Rad.isUnit_G hδG)).closed
    rw [Measure.map_map hΦ2 hΦ1]
    refine (Measure.map_apply (hΦ2.comp hΦ1) ?_).trans ?_
    · exact hS.measurableSet.compl
    refine measure_mono_null ?_ hHaar.2.2.1
    intro y hy hyS
    refine hy ?_
    exact Formalism.L2.SG.BlockScaling.rset_of_stV v hl hT' u u' (gamW X u u' w) (h v) (h' v)
      (fun a => hD.1 v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (hD.1 v _ (Or.inr rfl))
      (fun a => hD.2.1 v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (hD.2.1 v _ (Or.inr rfl)) hzW hzW' y hyS

  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    have hpt := hp
    unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
    split_ifs at hpt with hPtL
    rw [← Option.some_inj.mp hpt]; rfl
  have hsz : ∀ i : ℕ, Formalism.MainNotions.S.blockIdx pN.1 i = Formalism.L2.SG.RealObj.blkOf w.1 i := by
    intro i
    rw [Formalism.L2.SG.TriangularProducts.blockIdx_eq_bi, Formalism.L2.SG.BlockScaling.blkOf_eq_bi, hpN, hw1, List.map_map, List.map_map]
    congr 1
    have e1 : (Prod.snd ∘ Prod.swap : ℕ × ℂ → ℕ) = Prod.fst := rfl
    have e2 : (Prod.snd ∘ Prod.swap : ℕ × D.host.E → ℕ) = Prod.fst := rfl
    rw [e1, e2, show Formalism.L2.SG.DataInst.signPt D.R.rS p = Formalism.L2.SG.DataInst.signAux D.R.rS 1 p from rfl,
      Formalism.L2.SG.DataInst.sign_list_fst, hp', Formalism.L2.SG.BlockScaling.toStd_fst]
    simp [Formalism.FourierDecayAlt.C.loc]
  let idxE : ↥(Formalism.MainNotions.S.rootPat pN) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    { toFun := fun q => ⟨q.1, by
        have hq := q.2
        simp only [Formalism.MainNotions.S.rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        exact ⟨hq.1, by rw [← hsz, ← hsz]; exact hq.2⟩⟩
      invFun := fun q => ⟨q.1, by
        simp only [Formalism.MainNotions.S.rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨q.2.1, by rw [hsz, hsz]; exact q.2.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hmap : ((μRv.map (fun s => (h v)⁻¹ * s * h v)).map
      (fun s => Matrix.of.symm (trG ((PP).Q v) ((PP).Qi v) s))).map (fun x => Formalism.MainNotions.S.rootCoords D.R.k D.R.rS
        ((PP).T ((PP).τ.symm v)).base.z' pN (Matrix.of.symm
          ((trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v))⁻¹ * Matrix.of x *
            trG ((PP).Q v) ((PP).Qi v) ((h v)⁻¹ * (gamW X u u' w) v * h' v)))) =
      ENNReal.ofReal (Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
        (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p)) • volume := by
    have hrd : (D.host.rdE : ℂ) ≠ 0 := by
      have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
      intro h0; rw [h0, mul_zero] at this; exact zero_ne_one this
    set c : ℂ := (D.host.rdE : ℂ) * lam with hc
    have hc0 : c ≠ 0 := mul_ne_zero hrd hl
    set sP : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) → ℂ := fun q => c ^ (D.R.rS - q.2.val) / c ^ (D.R.rS - q.1.val) with hsP
    have hsP0 : ∀ q, sP q ≠ 0 := fun q => div_ne_zero (pow_ne_zero _ hc0) (pow_ne_zero _ hc0)
    have hstm : Measurable (stCoordV X u' w (gamW X u u' w) v) := by
      refine Continuous.measurable ?_
      unfold stCoordV Formalism.L2.SG.HidaSetting.hJ
      fun_prop
    have hGm : Measurable (fun (y' : Formalism.L2.SG.RealObj.FreeE w → ℂ) (q : ↥(Formalism.MainNotions.S.rootPat pN)) => sP q.1 * y' (idxE q)) :=
      measurable_pi_lambda _ fun q => measurable_const.mul (measurable_pi_apply _)
    rw [Measure.map_map hΦ2 hΦ1]
    refine (Measure.map_map ?_ (hΦ2.comp hΦ1)).trans ?_
    · refine Continuous.measurable ((Formalism.L2.SG.RootPatterns.rootCoords_cont _ _ _ _).comp ?_)
      exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    refine (congrArg (fun f => Measure.map f μRv) (?_ : _ = (fun (y' : Formalism.L2.SG.RealObj.FreeE w → ℂ)
      (q : ↥(Formalism.MainNotions.S.rootPat pN)) => sP q.1 * y' (idxE q)) ∘ stCoordV X u' w (gamW X u u' w) v)).trans ?_
    · funext y q
      have hq := q.2
      simp only [Formalism.MainNotions.S.rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have ha : q.1.1.val < D.R.rS := by have := Fin.lt_def.1 hq.1; have := q.1.2.isLt; omega
      simp only [Function.comp_apply, Formalism.MainNotions.S.rootCoords, Equiv.apply_symm_apply]
      unfold Formalism.MainNotions.S.flagMat
      rw [dif_pos ha]
      erw [Formalism.L2.SG.BlockScaling.conj_trG hT'.1 hT'.2.1]
      have hcoe : Formalism.MainNotions.S.uMat ((h' v)⁻¹ * ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) * h' v) =
          (Formalism.MainNotions.S.uMat (h' v))⁻¹ * Formalism.MainNotions.S.uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) * Formalism.MainNotions.S.uMat (h' v) := by
        rw [show Formalism.MainNotions.S.uMat ((h' v)⁻¹ * ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) * h' v) =
          Formalism.MainNotions.S.uMat (h' v)⁻¹ * Formalism.MainNotions.S.uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) * Formalism.MainNotions.S.uMat (h' v) from rfl,
          Formalism.L2.SG.RealConjugatorData.uMat_inv']
      have hz'' : ((PP).T ((PP).τ.symm v)).base.z' = (PP).Qi v *ᵥ rv X.B.I v (X.zR u') := hz'
      rw [hcoe, hz'']
      have hHu : IsUnit (Formalism.MainNotions.S.uMat (h' v)).det :=
        Matrix.isUnit_det_of_right_inverse (Formalism.L2.SG.RealConjugatorData.uMat_mul_inv (h' v))
      erw [Formalism.L2.SG.StandardCoordinates.coord_conj v hl hT' u' _ _ (h' v).2 hHu
        (fun a => hD.2.1 v _ (Or.inl (Or.inl ⟨a, rfl⟩))) (hD.2.1 v _ (Or.inr rfl))
        (fun a => hD.2.1 v _ (Or.inl (Or.inr ⟨a, rfl⟩))) ⟨q.1.1.val, ha⟩ q.1.2]
      have hgen : stCoordV X u' w (gamW X u u' w) v y (idxE q) =
          c ^ (D.R.rS - q.1.1.val) / c ^ (D.R.rS - q.1.2.val) *
          (((PP).Qi v * Formalism.MainNotions.S.uMat ((gamW X u u' w v)⁻¹ * y * gamW X u u' w v) * (PP).Q v) *ᵥ
            Formalism.QuantumDeterminants.fvec D.R.k D.R.rS ((PP).Qi v *ᵥ rv X.B.I v (X.zR u')) q.1.2)
            (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨q.1.1.val, ha⟩) := by
        have h1 := Formalism.L2.SG.StandardCoordinates.stCoordV_gen v hl hT' u' w (gamW X u u' w) y (idxE q)
        rw [← hc] at h1
        exact h1
      rw [hgen]
      simp only [hsP]
      field_simp
      rfl
    rw [← Measure.map_map hGm hstm, hpin]
    unfold muStabV
    rw [Formalism.L2.SG.PiMeasureScaling.pi_reindex_scale idxE _ ENNReal.ofReal_ne_top (fun q => sP q.1) (fun q => hsP0 _)]
    congr 1
    have hpos_rd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _
    have hk : D.host.ka = 2 * Real.pi / D.host.rdE := by
      simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
      have hπ := Real.pi_ne_zero
      have := hpos_rd.ne'
      first | (field_simp; done) | (field_simp; ring)
    have hgX : (X.B.g : ℝ) = ((PP).S.g : ℝ) := by
      show (X.B.g : ℝ) = ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ)
      rw [X.g_eq]
    set y : ℝ := D.host.rdE * ((PP).S.g : ℝ) / (2 * Real.pi) with hy
    have hy0 : 0 < y := by have := Real.pi_pos; positivity
    have hcy : c = ((y : ℝ) : ℂ) * (-Complex.I) := by
      rw [hc, hlam, hy]; push_cast; ring
    have hnc : Complex.normSq c = y ^ 2 := by
      rw [hcy, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_neg, Complex.normSq_I]; ring
    have hkap : Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) = y⁻¹ := by
      rw [← Formalism.L2.SG.BlockScaling.rdE_eq_rd', hy]
      unfold Formalism.FourierDecayAlt.D.kapG
      have := Real.pi_pos
      first | (field_simp; done) | (field_simp; ring)
    set F : ℕ → ℝ := fun m => Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) ^ (1 - 2 * (m : ℤ)) / Real.pi
      with hF
    have hF0 : ∀ m, 0 ≤ F m := fun m => div_nonneg (zpow_nonneg (by rw [hkap]; positivity) _) Real.pi_pos.le
    have hterm : ∀ q ∈ Formalism.MainNotions.S.rootPat pN, ENNReal.ofReal (D.host.ka / X.B.g / Real.pi) *
        ENNReal.ofReal (Complex.normSq (sP q))⁻¹ = ENNReal.ofReal (F (q.2.val - q.1.val)) := by
      intro q hq
      simp only [Formalism.MainNotions.S.rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      have hab := Fin.lt_def.1 hq.1
      have hπ := Real.pi_pos
      rw [← ENNReal.ofReal_mul (by rw [hk, hgX]; positivity)]
      congr 1
      simp only [hsP, map_div₀, map_pow, hnc, hF, hkap, hk, hgX]
      have e : D.R.rS - q.1.val = (q.2.val - q.1.val) + (D.R.rS - q.2.val) := by have := q.2.isLt; omega
      rw [e, pow_add, _root_.inv_zpow', neg_sub, zpow_sub₀ hy0.ne', zpow_one, show (2 * ((q.2.val - q.1.val : ℕ) : ℤ)) =
        ((2 * (q.2.val - q.1.val) : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, hy]
      have h1 : (D.host.rdE * ((PP).S.g : ℝ) / (2 * Real.pi)) ≠ 0 := hy0.ne'
      first | (field_simp; done) | (field_simp; ring)
    rw [Finset.prod_coe_sort (Formalism.MainNotions.S.rootPat pN) (fun q => ENNReal.ofReal (D.host.ka / X.B.g / Real.pi) *
      ENNReal.ofReal (Complex.normSq (sP q))⁻¹), Finset.prod_congr rfl hterm,
      ← ENNReal.ofReal_prod_of_nonneg (fun q _ => hF0 _), Formalism.L2.SG.TriangularProducts.prod_rootPat pN F]
    congr 1
    unfold Formalism.FourierDecayAlt.D.bSt
    rw [hpN, List.map_map]
    have hfst : p'.map Prod.fst = (Formalism.FourierDecayAlt.C.loc ((PP).S.emb ((PP).τ.symm v)) p).map Prod.fst := by
      rw [hp', Formalism.L2.SG.BlockScaling.toStd_fst]
    have e1 : ((fun b : ℂ × ℕ => ∏ m ∈ Finset.Ico 1 b.2, F m ^ (b.2 - m)) ∘ Prod.swap) =
        (fun s => ∏ m ∈ Finset.Ico 1 s, F m ^ (s - m)) ∘ Prod.fst := rfl
    rw [e1, ← List.map_map, hfst, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, hF]
    exact (Formalism.L2.SG.BlockScaling.ico_int a.1
      (fun z : ℤ => Formalism.FourierDecayAlt.D.kapG ((PP).S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) ^ (1 - 2 * z) / Real.pi)).symm
  have := Formalism.L2.SG.ModelMeasure.mp_modelK pN ((PP).T ((PP).τ.symm v)).base hδG (Formalism.MainNotions.BigCellDensity.dPt_ne pN) hdm hZ _
    hconc _ hmap
  rw [this, ← hw']
  rfl

end ZsMq

end Formalism.L2.SG.Pf.Carrier

end
