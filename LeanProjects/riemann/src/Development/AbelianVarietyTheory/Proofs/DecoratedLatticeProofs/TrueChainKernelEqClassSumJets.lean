import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

set_option maxHeartbeats 4000000

namespace GlobalTheory.AdForm.KerVal

theorem eval_jetLin_jetC {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℂ) (Θ : VCx ι a b → ℂ) (y : ι → Matrix (Fin b) (Fin b) ℂ)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ) :
    MvPolynomial.eval (fun x : ι × Fin b × Fin b => y x.1 x.2.1 x.2.2) (jetLin (jetC c Θ) Q) =
      jetL c Θ (MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial m r =>
    have h1 : jetLin (jetC c Θ) (MvPolynomial.monomial m r) = r • MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
        (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) := by
      have := (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) ℂ).constr_basis ℂ (fun m =>
        (MvPolynomial.monomial (Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn)
          (jetC c Θ (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn)) : MvPolynomial (ι × Fin b × Fin b) ℂ)) m
      rw [show (MvPolynomial.monomial m r : MvPolynomial _ ℂ) = r • MvPolynomial.monomial m 1 by simp [MvPolynomial.smul_monomial], map_smul]
      congr 1
    have h2 : MvPolynomial.aeval (Sum.elim (fun x : ι × Fin b × Fin b => (MvPolynomial.C (y x.1 x.2.1 x.2.2) : FP ι a b))
        MvPolynomial.X) (MvPolynomial.monomial m r) = (r * ∏ x : ι × Fin b × Fin b, y x.1 x.2.1 x.2.2 ^ m (Sum.inl x)) •
          MvPolynomial.monomial (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) 1 := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (by simp)]
      simp [MvPolynomial.smul_eq_C_mul, mul_assoc]
    rw [h1, h2, MvPolynomial.smul_eval, LinearMap.map_smul, jetL_monomial, MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    simp
    ring

theorem kmap_val {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ) (hab : B.R.N i ≤ B.R.N (i + 1)) (c : (I.chain l u a).cls i)
    (c' : (I.chain l u a).cls (i + 1)) (ψ : (I.chain l u a).Y i → ℂ) (Q : PY (I.rec7 l Z).what₂.Tau (B.R.N i))
    (hψ : ∀ y : (I.chain l u a).Y i, ψ y = evalAt y.1 Q * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ))
    (y' : (I.chain l u a).Y (i + 1)) :
    (I.chain l u a).Kmap i c c' ψ y' =
      A.abelian₂ i c c' (subY hab y'.1 Q) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  have h1 : (I.chain l u a).sharp i ψ = fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0
      (fun τ => ((fr0 B.fields.emb B.embLL (B.R.N i)).1 τ)⁻¹) Q := by
    funext y
    have e := hψ y
    show (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ψ y =
      (∏ τ, ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 τ).det ^ (0 : ℤ)) *
        MvPolynomial.eval (fun x => ((1 : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) ℂ)⁻¹ * y.1 x.1) x.2.1 x.2.2) Q
    rw [e]
    simp only [inv_one, Matrix.one_mul, zpow_zero, Finset.prod_const_one, one_mul]
    have : (∏ τ, (y.1 τ).det ^ (I.chain l u a).sSharp i τ) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun τ _ => by rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (y.2 τ).ne_zero)]
    exact (mul_left_comm _ _ _).trans ((congrArg _ this).trans (mul_one _))
  have h2 : (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y' =
      jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) := by
    rw [h1]
    refine Eq.trans ?_ ((eval_jetLin_jetC (ι := B.fields.Tau) I.J.cD _ y'.1 (subD ℂ _ _ _ Q)).trans
      (congrArg _ (subY_eq_subD hab y'.1 Q).symm))
    have h3 := Formalism.L2.Col.polOf_fnOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i)) Q
    refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1 ((I.chIn u a).jet i c c' P) y') h3).trans ?_
    simp [fnOf, jetMap]
    rfl
  show ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * ((∏ τ, (y'.1 τ).det ^ (I.chain l u a).sDiv i τ)⁻¹ *
    (I.chIn u a).unf B.fields.emb B.embLL i c c' ((I.chain l u a).sharp i ψ) y') =
    ((I.chIn u a).rho i c * (I.chIn u a).rho' i c') * jetL I.J.cD (I.th u a i _ _ ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c')) (subY hab y'.1 Q) *
      ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ)
  rw [h2]
  simp only [_root_.zpow_neg, Finset.prod_inv_distrib]
  ring

theorem kernel_classSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  intro B X I _ _ l Z u a Ch A _ i _ hab φ Fc hφ c' y'
  haveI : Fintype ((I.chain l u a).cls i) := (I.chain l u a).clsFin i
  unfold ColumnChain.K Formalism.ThetaLiftIndependence.kerOpM
  rw [finsum_eq_sum_of_fintype, Finset.sum_apply]
  refine Finset.sum_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _)) fun c _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, kmap_val A i hab c c' (φ c) (Fc c) (hφ c) y', ColumnChain.wt]
  ring

end GlobalTheory.AdForm.KerVal
