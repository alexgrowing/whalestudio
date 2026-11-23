import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodProjProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem monicOf_injective {g N : ℕ} [Fact g.Prime] :
    Function.Injective fun c : Fin N → ZMod g => (Formalism.CyclotomicNorms.monicOf c : (ZMod g)[X]) := by
  intro c c' h
  funext i
  have key := congrArg (fun p : (ZMod g)[X] => p.coeff (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt i.isLt, if_false, zero_add] at key
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl,
    Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl] at key

open Classical in

theorem sum_good {g N m : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] [Fintype (ι → Fin N → ZMod g)]
    (ch : ι → Fin m → (ZMod g)ˣ) (h : (ι → (ZMod g)[X]) → ℂ) :
    (∑ a : ι → Fin N → ZMod g, if GlobalTheory.BadShare.Good g N ch (fun v => Formalism.CyclotomicNorms.monicOf (a v)) then
      h (fun v => Formalism.CyclotomicNorms.monicOf (a v)) else 0) = ∑ F ∈ GlobalTheory.BadShare.goodSet g N ch, h F := by
  have hinj : Function.Injective fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) :=
    by
      intro a b hab
      funext v
      have hv : Formalism.CyclotomicNorms.monicOf (a v) = (Formalism.CyclotomicNorms.monicOf (b v) : (ZMod g)[X]) := congrFun hab v
      exact monicOf_injective (g := g) (N := N) hv
  have hset : GlobalTheory.BadShare.goodSet g N ch =
      (Finset.univ.filter fun a : ι → Fin N → ZMod g => GlobalTheory.BadShare.Good g N ch fun v => Formalism.CyclotomicNorms.monicOf (a v)).image
        fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) := by
    ext F
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hF
      have hG := GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF
      have hsq := (GlobalTheory.BadShare.good_iff.1 hG).1
      have hc : ∀ v, ∃ c : Fin N → ZMod g, Formalism.CyclotomicNorms.monicOf c = F v := by
        intro v
        have hv := hsq v
        rw [GlobalTheory.BadShare.sqSet_eq_monicOf, Finset.mem_filter, Finset.mem_image] at hv
        obtain ⟨c, -, hc⟩ := hv.1
        exact ⟨c, hc⟩
      choose a ha using hc
      have hMa : (fun v => Formalism.CyclotomicNorms.monicOf (a v)) = F := funext ha
      refine ⟨a, ?_, hMa⟩
      rw [hMa]
      exact hG
    · rintro ⟨a, hG, rfl⟩
      exact GlobalTheory.BadShare.mem_goodSet_iff_good.2 hG
  rw [hset, Finset.sum_image (fun a _ b _ e => hinj e), Finset.sum_filter]

theorem sum_sigma_two {P : Fin 2 → Type} {A : Fin 2 → Type} [Fintype (∀ kv : (Σ k : Fin 2, P k), A kv.1)]
    [Fintype (P 0 → A 0)] [Fintype (P 1 → A 1)] (f0 : (P 0 → A 0) → ℂ) (f1 : (P 1 → A 1) → ℂ) :
    (∑ a : (∀ kv : (Σ k : Fin 2, P k), A kv.1), f0 (fun v => a ⟨0, v⟩) * f1 (fun v => a ⟨1, v⟩)) =
      (∑ a, f0 a) * ∑ b, f1 b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.piCurry fun (k : Fin 2) (_ : P k) => A k).trans
    (piFinTwoEquiv fun k => P k → A k)) _ _ (fun a => rfl)

theorem goodProjector_coeff_eq_prod_at_two_typePrimes : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  intro D τ hτ γ
  classical
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
    unfold NTypes.e0
    rfl
  let f : ∀ k : Fin 2, (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) → ℂ := fun k b =>
    if GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (b v)) then
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (b v))).coeff (γ ⟨k, v⟩) else 0
  have hsplit : ∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
        f 0 (fun v => a ⟨0, v⟩) * f 1 (fun v => a ⟨1, v⟩) := by
    intro a
    have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
        ∀ k : Fin 2, GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
      unfold NTypes.goodTuple GlobalTheory.BadShare.Good
      exact Iff.rfl
    rw [Fintype.prod_sigma, Fin.prod_univ_two]
    by_cases h0 : GlobalTheory.BadShare.Good (D.host.g 0) D.R.r (D.nd.chiT 0) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
      by_cases h1 : GlobalTheory.BadShare.Good (D.host.g 1) D.R.r (D.nd.chiT 1) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
      simp [f, hg, Fin.forall_fin_two, h0, h1]
  have hk : ∀ k : Fin 2, ∑ b, f k b = GlobalTheory.BadShare.eGood (fun _ => τ k) (D.nd.chiT k) (fun v => γ ⟨k, v⟩) := by
    intro k
    refine (Eq.trans ?_ (sum_good (g := D.host.g k) (N := D.R.r) (D.nd.chiT k)
      (fun F => ∏ v, (D.ntypes.eSer k (F v)).coeff (γ ⟨k, v⟩)))).trans ?_
    · rfl
    · unfold GlobalTheory.BadShare.eGood
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun F hF => ?_)
      have hsq := (GlobalTheory.BadShare.good_iff.1 (GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF)).1
      unfold GlobalTheory.BadShare.tens
      exact Finset.prod_congr rfl fun v _ => hτ k (F v) (hsq v) (γ ⟨k, v⟩)
  rw [he, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ hsplit,
    sum_sigma_two (P := fun k => D.nd.PlG k) (A := fun k => Fin D.R.r → ZMod (D.host.g k)) (f 0) (f 1), hk 0, hk 1]

end GlobalTheory.GoodProjProd

end
