import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerVal
open MvPolynomial

theorem deX_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k') (N : ℕ) (nu : Lt → YoungDiagram)
    (y : Lt → Fin N → ℕ → k) : MvPolynomial.map f (GL3Columns.DeX N nu y) = GL3Columns.DeX N nu (fun s a j => f (y s a j)) := by
  unfold GL3Columns.DeX
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  simp [map_sum, map_mul, map_C, map_X]

theorem dual_map_eval {σ V k : Type} [Field k] (χ : Module.Dual k (MvPolynomial σ k)) (p : MvPolynomial σ (MvPolynomial V k)) (x : V → k) :
    MvPolynomial.eval x (∑ m ∈ p.support, coeff m p * C (χ (monomial m 1))) = χ (MvPolynomial.map (MvPolynomial.eval x) p) := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, map_monomial]
  rw [show monomial m (MvPolynomial.eval x (coeff m p)) = (MvPolynomial.eval x (coeff m p)) • (monomial m 1 : MvPolynomial σ k) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

def uFr : Bool × HH D → Fin N → ℕ → MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  fun s a j => if h : j < N then X (tauPl D s, a, ⟨j, h⟩) else 0

def canPol (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) : MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  ∑ m ∈ (GL3Columns.DeX N nu (uFr w N)).support, coeff m (GL3Columns.DeX N nu (uFr w N)) * C (χ (monomial m 1))

theorem canM_apply (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := rfl

theorem canM_eq_eval (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (canPol w N nu χ) := by
  have e1 : (fun s a j => MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (uFr w N s a j)) =
      fun s => GL3Columns.colsOf (y (tauPl D s)) := by
    funext s a j
    unfold uFr GL3Columns.colsOf
    split_ifs <;> simp
  unfold canPol
  rw [dual_map_eval, deX_map, e1, canM_apply]

theorem canM_ker (hfit : ∀ s c, (nu s).colLen c ≤ N) (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)))
    (h0 : ∀ y, canM D w N nu χ y = 0) (J : KM.ColChoice N nu) :
    χ (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0 := by
  refine GL3Columns.wwInj_holds D (D.what₂.places.resChar w) N nu χ (fun y => ?_) J
  let e := Equiv.ofBijective (tauPl D) (Formalism.L2.DIV.tauPl_bijective D)
  have h1 : χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ)) (tauPl D s))) = 0 :=
    h0 (fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ))
  refine Eq.trans (congrArg χ ?_) h1
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (hfit s c)
  have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
  simp only [Matrix.of_apply, GL3Columns.colsOf, dif_pos hj, hs]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

theorem colsOf_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {M : ℕ} (Y : Matrix (Fin M) (Fin M) k) (a : Fin M) (j : ℕ) :
    f (GL3Columns.colsOf Y a j) = GL3Columns.colsOf (Y.map f) a j := by
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem onMin_canInv_mem (hfit : ∀ s c, (nu s).colLen c ≤ N) (F : FrP D w N → Cw D w) (hF : F ∈ LinearMap.range (canM D w N nu))
    (hrat : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL, ∃ x, F (fun τ => (y τ).map (P.iL w)) = P.iL w x)
    (J : KM.ColChoice N nu) : ∃ b : D.what₂.LL, onMin D w N nu (canInv D w N nu F) J = P.iL w b := by
  set ψ := canInv D w N nu F with hψdef
  have hψ : canM D w N nu ψ = F := canInv_spec D w N nu F hF
  letI : Algebra D.what₂.LL (Cw D w) := (P.iL w).toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap D.what₂.LL (Cw D w))
    (LinearMap.ker_eq_bot.2 (P.iL w).injective)
  let ρ : Cw D w → Cw D w := fun z => P.iL w (π z)
  have ρ_add : ∀ a b, ρ (a + b) = ρ a + ρ b := fun a b => by
    simp only [ρ, map_add]
  have ρ_mul : ∀ x z, ρ (P.iL w x * z) = P.iL w x * ρ z := fun x z => by
    have : P.iL w x * z = x • z := by rw [Algebra.smul_def]; rfl
    simp only [ρ, this, map_smul, smul_eq_mul, map_mul]
  have ρ_fix : ∀ x, ρ (P.iL w x) = P.iL w x := fun x => by
    have := LinearMap.congr_fun hπ x
    simp only [ρ]
    exact congrArg (P.iL w) this
  let ψ' : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) :=
    (MvPolynomial.basisMonomials _ (Cw D w)).constr (Cw D w) fun m => ρ (ψ (monomial m 1))
  have ψ'_mon : ∀ m, ψ' (monomial m 1) = ρ (ψ (monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials ((Bool × HH D) × ℕ × Fin N) (Cw D w)).constr_basis (Cw D w)
      (fun m => ρ (ψ (monomial m 1))) m
    rw [MvPolynomial.coe_basisMonomials] at this
    exact this
  have key : ∀ q : MvPolynomial ((Bool × HH D) × ℕ × Fin N) D.what₂.LL,
      ψ' (MvPolynomial.map (P.iL w) q) = ρ (ψ (MvPolynomial.map (P.iL w) q)) := by
    intro q
    induction q using MvPolynomial.induction_on' with
    | monomial m x =>
      have e : MvPolynomial.map (P.iL w) (monomial m x) = P.iL w x • (monomial m 1 : MvPolynomial _ (Cw D w)) := by
        rw [map_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [e, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ρ_mul, ψ'_mon]
    | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq, ρ_add]
  have hpt : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL,
      canM D w N nu ψ' (fun τ => (y τ).map (P.iL w)) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w)) := by
    intro y
    have e : (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ => (y τ).map (P.iL w)) (tauPl D s))) =
        MvPolynomial.map (P.iL w) (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := by
      rw [deX_map]
      congr 1
      funext s a j
      rw [colsOf_map]
    rw [canM_apply, canM_apply, e, key, ← e]
    change ρ (canM D w N nu ψ (fun τ => (y τ).map (P.iL w))) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w))
    obtain ⟨x, hx⟩ := hrat y
    rw [hψ, hx, ρ_fix]
  have hCZ : Set.Infinite (Set.range (Nat.cast : ℕ → Cw D w)) := Set.infinite_range_of_injective Nat.cast_injective
  have hpol : canPol w N nu (ψ' - ψ) = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → Cw D w)) (fun _ => hCZ) fun x hx => ?_
    choose n hn using fun v => hx v (Set.mem_univ v)
    have e : (fun v : GL3Theta.FrV D N => x v) = fun v => ((fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w)) :
        FrP D w N) v.1 v.2.1 v.2.2 := by
      funext v
      simp [hn]
    have h1 := canM_eq_eval w N nu (ψ' - ψ) (fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w))
    simp only [map_sub, Pi.sub_apply, hpt, sub_self] at h1
    rw [map_zero, show x = _ from e]
    exact h1.symm
  have h0 : ∀ y, canM D w N nu (ψ' - ψ) y = 0 := fun y => by
    rw [canM_eq_eval, hpol, map_zero]
  have hJ := canM_ker w N nu hfit (ψ' - ψ) h0 J
  have eJ : MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J) =
      MvPolynomial.map (P.iL w) (MvPolynomial.map (Int.castRingHom D.what₂.LL) (KM.nablaX N nu J)) := by
    rw [MvPolynomial.map_map, RingHom.ext_int ((P.iL w).comp (Int.castRingHom _)) (Int.castRingHom _)]
  rw [LinearMap.sub_apply, sub_eq_zero, eJ, key] at hJ
  exact ⟨π (ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J))), by
    show ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J)) = _
    rw [eJ]
    exact hJ.symm⟩

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

theorem colLen_le_of_fits {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} {ν : D.what₂.Tau → Fin N → ℕ} (h : NuFits D nu ν) :
    ∀ s c, (nu s).colLen c ≤ N := by
  intro s c
  by_contra hc
  have hm : (N, c) ∈ nu s := (nu s).mem_iff_lt_colLen.2 (lt_of_not_ge hc)
  have h1 := (nu s).mem_iff_lt_rowLen.1 hm
  rw [h.2 s N le_rfl] at h1
  exact Nat.not_lt_zero _ h1

theorem tgtFun_rat {D : D7} (P : Examples₂.EntPl D) (Bs : PlaceMatrixFamily D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ)
    (c' : (D.chTw u μ).cls (i + 1)) (hE : ∀ τ j k, ∃ x : D.what₂.LL, Bs u μ w (i + 1) c' τ j k = P.iL w x) (v : polV D u (i + 1))
    (y : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.what₂.LL) :
    ∃ x, tgtFun P Bs u μ w i c' v (fun τ => (y τ).map (P.iL w)) = P.iL w x := by
  choose B' hB' using hE
  have hB : Bs u μ w (i + 1) c' = fun τ => (Matrix.of (B' τ)).map (P.iL w) := by
    funext τ
    ext j k
    exact hB' τ j k
  refine ⟨(∏ τ, (Matrix.of (B' τ)).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL), ?_⟩
  show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * (y k.1).map (P.iL w)) k.2.1 k.2.2)
      (MvPolynomial.map (P.iL w) (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)) = _
  rw [hB, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  · have h2 := MvPolynomial.eval₂_comp_left (P.iL w) (RingHom.id D.what₂.LL)
      (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)
    refine Eq.trans ?_ h2.symm
    rw [MvPolynomial.eval_map, RingHom.comp_id]
    congr 1
    funext k
    rw [Function.comp_apply, ← Matrix.map_mul]
    rfl

end GlobalTheory.KerVal

theorem GlobalTheory.KerVal.prTC_val : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  intro B X I _ _ l Z _ Y O Pl Bs _ _ _ hEnt _ _ u μ w hw i hi c' v' J
  obtain ⟨b, hb⟩ := GlobalTheory.KerVal.onMin_canInv_mem Pl w _ _
    (GlobalTheory.KerVal.colLen_le_of_fits (nuFits_tgt (I.rec7 l Z) u i hi))
    (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v'))
    (canT_of Pl Bs (GlobalTheory.T.toy_entPl_canOnto _ Pl) u μ w i hi c' (secC O u μ (i + 1) v'))
    (GlobalTheory.KerVal.tgtFun_rat Pl Bs u μ w i c' (hEnt u μ w hw (i + 1) hi c') (secC O u μ (i + 1) v')) J
  exact ⟨b, congrArg norm hb⟩
