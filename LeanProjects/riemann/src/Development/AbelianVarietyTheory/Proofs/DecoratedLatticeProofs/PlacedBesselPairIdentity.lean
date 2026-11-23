import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterAdelicUnitaryGroupFinitePartScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseMovesVectorZStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwistStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.MiTop

theorem lattice_ratio_vector_of_scalar_factorisation {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (e c θ θ' : R)
    (X X' Sm Sm' Kk Z : GL n R) (hZ : Z.val = c • (1 : Matrix n n R))
    (hT : X⁻¹ * Sm = Z * (X'⁻¹ * Sm') * Kk) (zY zY' Γ : n → R)
    (hm : e • Matrix.mulVec (Sm⁻¹).val zY = e • (θ • Γ)) (hm' : e • Matrix.mulVec (Sm'⁻¹).val zY' = e • (θ' • Γ)) :
    e • ((θ * c) • Matrix.mulVec ((X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹).val (Matrix.mulVec (X'⁻¹).val zY')) =
      e • (θ' • Matrix.mulVec (X⁻¹).val zY) := by
  set M := (X'⁻¹ * Sm') * Kk * (X'⁻¹ * Sm')⁻¹ with hM
  have hg : Z * M * X'⁻¹ = (X⁻¹ * Sm) * Sm'⁻¹ := by
    rw [hM, hT]; group
  have h2 : c • Matrix.mulVec M.val (Matrix.mulVec (X'⁻¹).val zY') = Matrix.mulVec (Z * M * X'⁻¹).val zY' := by
    have : (Z * M * X'⁻¹).val = c • (M.val * (X'⁻¹).val) := by
      rw [Units.val_mul, Units.val_mul, hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
    rw [this, Matrix.smul_mulVec, Matrix.mulVec_mulVec]
  have h3 : e • (θ • Matrix.mulVec (Sm'⁻¹).val zY') = e • (θ' • Matrix.mulVec (Sm⁻¹).val zY) := by
    rw [smul_comm e θ (Matrix.mulVec (Sm'⁻¹).val zY'), hm', smul_comm e θ' (Matrix.mulVec (Sm⁻¹).val zY), hm,
      smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [mul_smul, h2, hg, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, ← Matrix.mulVec_smul, h3,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Units.val_mul]
  congr 3
  group

theorem redFn_scalar_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (c : E ⊗[F] Formalism.L2.Herm.Af F) (hx : x ∈ Formalism.L2.DIV.St β)
    (hc : x.val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (i₀ : Fin n) :
    ∃ hci : c ∈ Formalism.L2.Herm.intAf F E,
      (Formalism.L2.DIV.resS F PP ⟨c, hci⟩ = 1 → Formalism.L2.DIV.redFn β PP x = 1) := by
  obtain ⟨y, rfl⟩ := hx
  have hy : (Formalism.L2.DIV.intGL F E n y).val = c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
    have e1 : Formalism.L2.DIV.intGL F E n y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
      simp only [Formalism.L2.DIV.frGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, ((y.val i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (c • (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) i j := fun i j => by
    rw [← hy]; rfl
  have hci : c ∈ Formalism.L2.Herm.intAf F E := by
    have h := hent i₀ i₀
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
    rw [← h]; exact (y.val i₀ i₀).2
  refine ⟨hci, fun h1 => ?_⟩
  rw [Formalism.L2.DIV.redFn_frGL]
  apply Units.ext
  ext i j
  have hyij : y.val i j = if i = j then ⟨c, hci⟩ else 0 := by
    apply Subtype.ext
    rw [hent i j, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  show Formalism.L2.DIV.resS F PP (y.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [hyij, Matrix.one_apply]
  split_ifs <;> simp [h1]

set_option maxHeartbeats 2000000 in

theorem centralRatio_red_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ u u' (f : FamCh W u) (f' : FamCh W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), GlobalTheory.MiTop.PlacedP f B → GlobalTheory.MiTop.PlacedP f' B' → ∀ a₀ a a₀' a', IsAt f B a₀ a → IsAt f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ rJ W, tOf f B a₀ a = z * tOf f' B' a₀' a' * k → ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1 := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u u' f f' B B' hPl hPl' a₀ a a₀' a' hA hA' z hzf hzc k hk heq PP hPP
  classical
  by_cases hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0)
  swap
  · unfold Formalism.L2.DIV.redFn Formalism.L2.DIV.ext1
    rw [dif_neg hS]
  rcases Nat.eq_zero_or_pos (Yc D 0).rank with h0 | hpos
  · apply Units.ext; ext i; exact absurd i.2 (by omega)
  obtain ⟨c, hc⟩ := GlobalTheory.T.center_adelicUnitaryGroup_finitePart_scalar (Yc D 0) (show GA D (Yc D 0) from z) hzc hzf
  obtain ⟨hci, hfin⟩ := redFn_scalar_eq_one (W.Q.Rl.βY 0) PP _ c hS hc ⟨0, hpos⟩
  apply hfin
  obtain ⟨-, hconj⟩ := hA'.2.2.2
  have hκ : tOf f' B' a₀' a' * k * (tOf f' B' a₀' a')⁻¹ ∈ rowJ W.S.X W.Q.instEq := by
    have := ((hconj k).1).1 hk
    simpa using this
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.T.base_moves_vector_z_alt W hP hr PP hPP
  obtain ⟨θ, hθ, hθ1, hm⟩ := hΓ u f B (by first | exact hPl | exact PlacedP.placed f B hPl) a₀ a hA
  obtain ⟨θ', hθ', hθ1', hm'⟩ := hΓ u' f' B' (by first | exact hPl' | exact PlacedP.placed f' B' hPl') a₀' a' hA'
  have hmul : ∀ x y : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x * y : GA D (D.sp.Y 0))) =
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x) * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y) :=
    fun x y => map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) x y
  have hinv : ∀ x : GA D (D.sp.Y 0), Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (x⁻¹ : GA D (D.sp.Y 0))) =
      (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from x))⁻¹ :=
    fun x => map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) x
  have ht : ∀ (u : D.what₂.Word) (f : FamCh W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) a₀ a,
      Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f B a₀ a) =
        (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u)))⁻¹ *
          Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from embA B.d B.o (a₀ * a) * (show GA D (D.sp.Y 0) from f.g.b 0)) := by
    intro u f B a₀ a
    unfold tOf
    rw [mul_assoc, hmul, hinv]
  have hT := congrArg (fun g : GA D (D.sp.Y 0) => Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from g)) heq
  simp only [hmul, ht] at hT
  have hcong := GlobalTheory.T.row_level_integral_twist W hP hr u u' _ hκ (θ * c) θ' (Subring.mul_mem _ hθ hci) hθ' PP hPP (fun ei hei => by
    have key := lattice_ratio_vector_of_scalar_factorisation (toEAf D ei) c θ θ' _ _ _ _ _ _ hc hT _ _ Γ (hm ei hei) (hm' ei hei)
    have hκE : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (tOf f' B' a₀' a' * k * (tOf f' B' a₀' a')⁻¹ : GA D (D.sp.Y 0))) =
        Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f' B' a₀' a') * Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from k) *
          (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from tOf f' B' a₀' a'))⁻¹ :=
      ((map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _).trans (congrArg₂ (· * ·) (map_mul (Formalism.IndefR.Lev.finE (Yc D 0)) _ _)
        (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) _)))
    rw [ht u' f' B' a₀' a'] at hκE
    rw [← hκE] at key
    exact key)
  have e1 : (⟨θ * c, Subring.mul_mem _ hθ hci⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨θ, hθ⟩ * ⟨c, hci⟩ := rfl
  rw [e1, map_mul, hθ1, hθ1', one_mul] at hcong
  exact hcong

end GlobalTheory.MiTop

end
