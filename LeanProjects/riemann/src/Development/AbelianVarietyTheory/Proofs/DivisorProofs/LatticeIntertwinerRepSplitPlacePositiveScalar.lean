import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairAction
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatSplitF

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem conj_conj_of_cm (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [GlobalTheory.SplitInvFormF.cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [GlobalTheory.SplitInvFormF.cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hS.2)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y

theorem symplOF_actOF (hS : IsHermND σ JS) (ξ₀ : E) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF hS]

theorem gamFF_rhoFF (hS : IsHermND σ JS) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (p : GAF σ JS × GAF σ JT)
    (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  rw [gamFF, gamFF, coe_rhoFF, coe_rhoFF, symplOF_actOF hS]

theorem off_smul_mtF {e : AEF F E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : (e + cAF σ e) • (mtF σ J g - 1) = mtF σ J g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem off_smul_mtF_inv {e : AEF F E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : mtF σ J g * mtF σ J g⁻¹ = 1 := by
    unfold mtF
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← h, ← Matrix.smul_mul, off_smul_mtF hg, Matrix.smul_mul, Matrix.one_mul]

theorem off_smul_actOF {e : AEF F E} {g : GAF σ JS} {h : GAF σ JT} (hg : SuppAtF σ e JS g) (hh : SuppAtF σ e JT h)
    (u : WOF F E nS nT) : (1 - (e + cAF σ e)) • actOF σ JS JT g h u = (1 - (e + cAF σ e)) • u := by
  unfold actOF
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, off_smul_mtF hh, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, off_smul_mtF_inv hg, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.FinLatSplitF

open GlobalTheory.FinLatF GlobalTheory.FinLatSplitF in

theorem GlobalTheory.FinLatF.isLatRepF_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
          ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
            (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
              ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
            ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, h) f) = (r : ℂ) * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hL e he g k hg hk
  have hσ : ∀ x, σ (σ x) = x := conj_conj_of_cm hB.cm
  have he' : IsSplitIdemF σ (cAF σ e) := isSplitIdemF_conj he
  have hm : ∀ (a b : AEF F E) (x : XFF F E nS nT), mulFF a (mulFF b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hcm : ∀ (a : AEF F E) (x : XFF F E nS nT),
      rhoFF σ JS JT (g, k) (mulFF a x) = mulFF a (rhoFF σ JS JT (g, k) x) :=
    fun a x => XFF.ext (actOF_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opFF hσ hS hT hξ hc hL.hw) lam _ hL.sd hL.span (rhoFF σ JS JT (g, k))
    (gamFF_rhoFF hS ξ₀ B.ψ _) (hL.sd' _) (hL.fin _) (Om (g, k)) (hL.op _) (hL.vac _) (mulFF e) (mulFF (cAF σ e))
    (fun x => by rw [hm, he.1]; rfl) (fun x => by rw [hm, he'.1]; rfl)
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamFF, gamFF, coe_mulFF, coe_mulFF, symplOF_smul σ JS JT hσ])
    (fun a ha => (hL.splitStab e he a ha).1) (fun a ha => (hL.splitStab e he a ha).2) (hcm e) (hcm _)
    (fun x => XFF.ext (by
      have := off_smul_actOF hg hk (x : WOF F E nS nT)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := hL.fin (g, k)
  have hl := hL.sqrt _ hi (fun q hq hin => hL.splitIdx e he g k hg hk q hq hin)
  refine ⟨(Real.sqrt (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ).subtype) (fun u m => by
    have hu : ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT) ∈ GlobalTheory.SplitInvFormF.conjHalf σ e nS nT :=
      fun i j => by
        show cAF σ e * (cAF σ e * (u : WOF F E nS nT) i j) = cAF σ e * (u : WOF F E nS nT) i j
        rw [← mul_assoc, he'.1]
    have hwu : (intAF F w • ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT)) ∈
        GlobalTheory.SplitInvFormF.conjHalf σ e nS nT := fun i j => by
      show cAF σ e * (intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)) =
        intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)
      rw [mul_left_comm, ← mul_assoc (cAF σ e), he'.1]
    show ℓ (opFF hc w (mulFF (cAF σ e) u) m : WOF F E nS nT → ℂ) = ℓ m
    rw [coe_opFF, phaseF, GlobalTheory.SplitInvFormF.symplOHF_half he hwu hu, neg_zero, AddChar.map_zero_eq_one, one_smul]
    exact h1 _ hu _ m.2) f
  rw [hl] at this
  push_cast
  exact this

end
