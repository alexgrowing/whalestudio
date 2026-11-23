import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VacuumFockVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix Complex
open GlobalTheory.Chain GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars
open GlobalTheory.Ker (ipO)
open scoped Classical ComplexConjugate

namespace GlobalTheory.VacuumFockLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem multiFact_add_single {ι : Type} (k : ι →₀ ℕ) (v : ι) :
    multiFact (k + Finsupp.single v 1) = (k v + 1) * multiFact k := by
  classical
  have hsub : (k + Finsupp.single v 1).support ⊆ insert v k.support := by
    intro i hi
    rw [Finsupp.mem_support_iff] at hi
    by_cases h : i = v
    · exact h ▸ Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr ?_)
      simpa [Finsupp.single_apply, Ne.symm h] using hi
  have h1 : multiFact k = ∏ i ∈ insert v k.support, (k i).factorial :=
    Finsupp.prod_of_support_subset _ (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)
  have h2 : multiFact (k + Finsupp.single v 1) =
      ∏ i ∈ insert v k.support, ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial :=
    Finsupp.prod_of_support_subset _ hsub _ (fun _ _ => Nat.factorial_zero)
  rw [h1, h2, ← Finset.mul_prod_erase _ (fun i => ((k + Finsupp.single v 1 : ι →₀ ℕ) i).factorial)
      (Finset.mem_insert_self v k.support),
    ← Finset.mul_prod_erase _ (fun i => (k i).factorial) (Finset.mem_insert_self v k.support), ← mul_assoc]
  congr 1
  · simp [Nat.factorial_succ]
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ v := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, Ne.symm hne]

theorem multiIndex_induction {ι : Type} {p : (ι →₀ ℕ) → Prop} (h0 : p 0)
    (h1 : ∀ k v, p k → p (k + Finsupp.single v 1)) (k : ι →₀ ℕ) : p k := by
  refine Finsupp.induction k h0 fun a b g _ _ ih => ?_
  have key : ∀ n : ℕ, p (Finsupp.single a n + g) := by
    intro n
    induction n with
    | zero => simpa using ih
    | succ n ihn =>
      have e : Finsupp.single a (n + 1) + g = (Finsupp.single a n + g) + Finsupp.single a 1 := by
        rw [add_right_comm, ← Finsupp.single_add]
      rw [e]
      exact h1 _ _ ihn
  exact key b

private theorem foldr_eq_of_perm_of_comm {ι Y : Type} (F : ι → Y → Y) (hF : ∀ i j y, F i (F j y) = F j (F i y))
    {l₁ l₂ : List ι} (p : l₁.Perm l₂) (y : Y) : l₁.foldr F y = l₂.foldr F y := by
  induction p generalizing y with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x z l => simp only [List.foldr_cons]; exact hF _ _ _
  | trans _ _ ih1 ih2 => exact (ih1 y).trans (ih2 y)

private theorem foldr_coe_eq_coe_foldr {ι X : Type} (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g) (g : M) (l : List ι) :
    l.foldr (fun i h => A i h) (g : X → ℂ) = ((l.foldr (fun i h => a i h) g : M) : X → ℂ) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih, hA]

private theorem pureTensorL_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (u : ι →₀ ℕ)
    (c : ℂ) : pureTensorL A f (MvPolynomial.monomial u c) = c • opPow A u f := by
  have e : MvPolynomial.monomial u c = c • MvPolynomial.basisMonomials ι ℂ u := by
    simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]

theorem fock_of_ccr {ι X : Type} (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a b : ι → Module.End ℂ M) (hA : ∀ i (g : M), A i g = a i g)
    (haa : ∀ i j g, a i (a j g) = a j (a i g))
    (hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g)
    (f : M) (hf : ∀ i, b i f = 0) :
    (∀ Q, pureTensorL A (f : X → ℂ) Q ∈ M) ∧
    ∀ ip : (X → ℂ) → (X → ℂ) → ℂ, (∀ x y z : M, ip (x + y) z = ip x z + ip y z) →
      (∀ (c : ℂ) x z, ip (c • x) z = c * ip x z) → (∀ x, ip x 0 = 0) →
      (∀ i (x y : M), ip (a i x) y = ip x (b i y)) → (∀ i (x y : M), ip x (a i y) = ip (b i x) y) →
      ∀ (β : ι →₀ ℕ) Q, ip (pureTensorL A (f : X → ℂ) Q) (pureTensorL A (f : X → ℂ) (MvPolynomial.monomial β 1)) =
        Q.coeff β * ((multiFact β : ℂ) * ip f f) := by
  classical
  obtain ⟨P, hPdef⟩ : ∃ P : (ι →₀ ℕ) → M,
      ∀ k, P k = (Finsupp.toMultiset k).toList.foldr (fun i h => a i h) f := ⟨_, fun _ => rfl⟩
  have hP : ∀ k, opPow A k (f : X → ℂ) = (P k : X → ℂ) := by
    intro k
    unfold opPow
    rw [hPdef]
    exact foldr_coe_eq_coe_foldr M A a hA f _
  have hP0 : P 0 = f := by
    rw [hPdef]
    simp
  have hPs : ∀ k v, P (k + Finsupp.single v 1) = a v (P k) := by
    intro k v
    rw [hPdef, hPdef]
    have hp : ((Finsupp.toMultiset (k + Finsupp.single v 1)).toList).Perm (v :: (Finsupp.toMultiset k).toList) := by
      rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList, map_add,
        Finsupp.toMultiset_single, one_nsmul, add_comm, Multiset.singleton_add]
    rw [foldr_eq_of_perm_of_comm (fun i h => a i h) (fun i j y => haa i j y) hp]
    rfl
  have hb0 : ∀ k v, k v = 0 → b v (P k) = 0 := by
    intro k
    refine multiIndex_induction (p := fun k => ∀ v, k v = 0 → b v (P k) = 0) ?_ ?_ k
    · intro v _
      rw [hP0]
      exact hf v
    · intro k w ih v hv
      have hvw : v ≠ w := by
        intro h
        subst h
        simp at hv
      have hkv : k v = 0 := by simpa [Finsupp.single_apply, Ne.symm hvw] using hv
      rw [hPs, hba, ih v hkv, map_zero, if_neg hvw, zero_smul, add_zero]
  have hb1 : ∀ k v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k := by
    intro k
    refine multiIndex_induction
      (p := fun k => ∀ v, b v (P (k + Finsupp.single v 1)) = ((k v + 1 : ℕ) : ℂ) • P k) ?_ ?_ k
    · intro v
      rw [hPs 0 v, hba, hP0, hf, map_zero, zero_add, if_pos rfl, one_smul]
      simp
    · intro k w ih v
      rw [add_right_comm, hPs (k + Finsupp.single v 1) w, hba, ih v, map_smul, ← hPs k w]
      by_cases hvw : v = w
      · subst hvw
        rw [if_pos rfl, ← add_smul, Finsupp.add_apply, Finsupp.single_eq_same]
        congr 1
        push_cast
        ring
      · rw [if_neg hvw, zero_smul, add_zero]
        have e : (k + Finsupp.single w 1 : ι →₀ ℕ) v = k v := by simp [Finsupp.single_apply, Ne.symm hvw]
        rw [e]
  have hmono : ∀ u c, pureTensorL A (f : X → ℂ) (MvPolynomial.monomial u c) = c • (P u : X → ℂ) := by
    intro u c
    rw [pureTensorL_monomial, hP]
  have hmem : ∀ Q, pureTensorL A (f : X → ℂ) Q ∈ M := by
    intro Q
    induction Q using MvPolynomial.induction_on'
    · rename_i u c
      rw [hmono]
      exact M.smul_mem c (P u).2
    · rename_i p q hp hq
      rw [map_add]
      exact M.add_mem hp hq
  refine ⟨hmem, ?_⟩
  intro ip hadd hsmul hzero hadj1 hadj2 β Q
  have hip0 : ∀ z, ip 0 z = 0 := by
    intro z
    have h := hsmul 0 0 z
    rwa [zero_smul, zero_mul] at h
  have hG : ∀ β α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0 := by
    intro β
    refine multiIndex_induction
      (p := fun β => ∀ α, ip (P α : X → ℂ) (P β) = if α = β then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ β
    · intro α
      refine multiIndex_induction
        (p := fun α => ip (P α : X → ℂ) (P 0) = if α = 0 then (multiFact α : ℂ) * ip f f else 0) ?_ ?_ α
      · simp [hP0, multiFact]
      · intro α v _
        rw [hPs, hadj1, hP0, hf]
        have hne : α + Finsupp.single v 1 ≠ 0 := by
          intro h
          have := congrArg (fun g : ι →₀ ℕ => g v) h
          simp at this
        rw [if_neg hne]
        simpa using hzero _
    · intro β v ih α
      rw [hPs, hadj2]
      by_cases hα : α v = 0
      · rw [hb0 α v hα]
        have hne : α ≠ β + Finsupp.single v 1 := by
          intro h
          rw [h] at hα
          simp at hα
        rw [if_neg hne]
        simpa using hip0 _
      · obtain ⟨α', rfl⟩ : ∃ α', α = α' + Finsupp.single v 1 := by
          refine ⟨α - Finsupp.single v 1, ?_⟩
          ext w
          by_cases hw : w = v
          · subst hw
            simp
            omega
          · simp [Finsupp.single_apply, Ne.symm hw]
        rw [hb1, Submodule.coe_smul, hsmul, ih α', multiFact_add_single]
        by_cases he : α' = β
        · subst he
          rw [if_pos rfl, if_pos rfl]
          push_cast
          ring
        · have hne : α' + Finsupp.single v 1 ≠ β + Finsupp.single v 1 := fun h => he (add_right_cancel h)
          rw [if_neg he, if_neg hne, mul_zero]
  rw [hmono β 1, one_smul]
  induction Q using MvPolynomial.induction_on'
  · rename_i u c
    rw [hmono, hsmul, hG, MvPolynomial.coeff_monomial]
    by_cases h : u = β
    · subst h
      simp
    · simp [h]
  · rename_i p q hp hq
    rw [map_add, MvPolynomial.coeff_add, add_mul, ← hp, ← hq]
    exact hadd ⟨_, hmem p⟩ ⟨_, hmem q⟩ (P β)

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

def sgnAt (M : DSModel V S) (τ : D.what₂.Tau) (a : Fin V.rank) : ℝ := if M.ε τ a then 1 else -1

theorem sgnAt_cases (M : DSModel V S) (τ : D.what₂.Tau) (a : Fin V.rank) : sgnAt M τ a = 1 ∨ sgnAt M τ a = -1 := by
  unfold sgnAt
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Jm_eq (M : DSModel V S) (τ : D.what₂.Tau) : Formalism.REAL.Jm (M.ε τ) = diagonal fun a => (sgnAt M τ a : ℂ) := by
  unfold Formalism.REAL.Jm sgnAt
  congr 1
  funext a
  split_ifs <;> simp

theorem onb_det (M : DSModel V S) (τ : D.what₂.Tau) : IsUnit (onb M τ).det := by
  unfold onb
  exact Matrix.isUnit_nonsing_inv_det_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem cart_mul_onb (M : DSModel V S) (τ : D.what₂.Tau) :
    cart M τ * onb M τ = onb M τ * diagonal fun a => (sgnAt M τ a : ℂ) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold cart onb
  rw [← Jm_eq, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem onb_gram (M : DSModel V S) (τ : D.what₂.Tau) :
    (onb M τ)ᴴ * gramAt D V τ * onb M τ = diagonal fun a => (sgnAt M τ a : ℂ) := by
  have hu : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  unfold onb
  rw [← M.fr_gram τ, ← Jm_eq]
  have e : ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_nonsing_inv _ hu]
  simp

def uMap (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  unitMap (onb M l.1) (onb M' l.1) l.2.1 l.2.2

def uSgn (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) : ℝ := sgnAt M' l.1 l.2.1 * sgnAt M l.1 l.2.2

theorem uSgn_cases (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) :
    uSgn M M' l = 1 ∨ uSgn M M' l = -1 := by
  unfold uSgn
  rcases sgnAt_cases M' l.1 l.2.1 with h | h <;> rcases sgnAt_cases M l.1 l.2.2 with h' | h' <;>
    norm_num [h, h']

theorem cplxO_uMap (M : DSModel V S) (M' : DSModel W S') (l : FVar D W.rank V.rank) :
    cplxO (cart M l.1) (cart M' l.1) (uMap M M' l) = (I * uSgn M M' l) • uMap M M' l := by
  unfold uMap uSgn
  rw [GlobalTheory.FockVecInj.cplxO_unitMap (onb_det M l.1) (cart_mul_onb M l.1) (cart_mul_onb M' l.1)]
  congr 1
  push_cast
  ring

theorem commScalar_uMap (M : DSModel V S) (M' : DSModel W S') (c c' : ℂ) (k l : FVar D W.rank V.rank) :
    commScalar V W k.1 l.1 (c • uMap M M' k) (c' • uMap M M' l) =
      if k = l then -(2 * Real.pi * I) * ((2 * (tauE D k.1 D.host.xi0 * (c * conj c' * uSgn M M' k)).re : ℝ) : ℂ)
      else 0 := by
  classical
  obtain ⟨τ, i, j⟩ := k
  obtain ⟨τ', i', j'⟩ := l
  unfold commScalar
  by_cases hτ : τ = τ'
  · subst hτ
    have hε : ∀ (N : Type) [Fintype N] (g : N → ℝ), (∀ a, g a = 1 ∨ g a = -1) → ∀ a, (g a : ℂ) * (g a : ℂ) = 1 := by
      intro N _ g hg a
      rcases hg a with h | h <;> simp [h]
    have ht := GlobalTheory.FockVecInj.trace_unitMap (hε _ _ (sgnAt_cases M τ)) (onb_gram M τ) (onb_gram M' τ) i j i' j'
    unfold symplAt hermAt uMap uSgn
    simp only [if_true, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [ht]
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      simp only [and_self, if_true]
      push_cast
      simp only [Complex.star_def]
      ring_nf
    · have hne : (τ, i, j) ≠ (τ, i', j') := by
        intro he
        simp only [Prod.mk.injEq, true_and] at he
        exact hij he
      simp [hij, hne]
  · have hne : (τ, i, j) ≠ (τ', i', j') := by
      intro he
      simp only [Prod.mk.injEq] at he
      exact hτ he.1
    simp [hτ, hne]

theorem fockScale_sq (τ : D.what₂.Tau) :
    (fockScale D τ : ℂ) * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
  have hre : (tauE D τ D.host.xi0).re = 0 := GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero τ
  have him : 0 < (tauE D τ D.host.xi0).im := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hz : tauE D τ D.host.xi0 = ((tauE D τ D.host.xi0).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  have hn : ‖tauE D τ D.host.xi0‖ = (tauE D τ D.host.xi0).im := by
    rw [hz]
    simp [abs_of_pos him]
  have h2 : fockScale D τ * fockScale D τ = 8 * Real.pi * (tauE D τ D.host.xi0).im := by
    unfold fockScale
    rw [hn]
    have h0 : 0 ≤ 2 * Real.pi * (tauE D τ D.host.xi0).im := by positivity
    have hs := Real.mul_self_sqrt h0
    linear_combination 4 * hs
  exact_mod_cast h2

theorem fockScale_ne (τ : D.what₂.Tau) : (fockScale D τ : ℂ) ≠ 0 := by
  intro h
  have h2 := fockScale_sq (D := D) τ
  rw [h, zero_mul] at h2
  have him : 0 < (tauE D τ D.host.xi0).im := Formalism.L2.Theta.xi_zero_im_pos D τ
  have hp : (0 : ℝ) < 8 * Real.pi * (tauE D τ D.host.xi0).im := by positivity
  have h3 : (8 * Real.pi * (tauE D τ D.host.xi0).im : ℝ) = 0 := by exact_mod_cast h2.symm
  exact hp.ne' h3

variable (V W) in

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) : Submodule ℂ (WO V W → ℂ) where
  carrier := {g | IsThetaFunO ψ V W g}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

theorem fockLaws {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (hsk : DerSkew ψ θ V W) (hco : DerComm ψ θ V W) (M : DSModel V S) (M' : DSModel W S') {f : WO V W → ℂ}
    (hf : IsVacVec ψ θ M M' f) : FockLaws ψ θ M M' f := by
  classical
  have hdR_th : ∀ τ z (g : thetaSub V W ψ), IsThetaFunO ψ V W (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g) :=
    fun τ z g => (hsk τ z).2.1 _ g.2
  obtain ⟨Dop, hDop⟩ : ∃ Dop : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ → Module.End ℂ (thetaSub V W ψ),
      ∀ p g, (Dop p g : WO V W → ℂ) = Formalism.IndefR.Datum.dRho (heisO ψ V W) θ p.1 p.2 g :=
    ⟨fun p =>
      { toFun := fun g => ⟨_, hdR_th p.1 p.2 g⟩
        map_add' := fun g g' => Subtype.ext (GlobalTheory.Size.dRho_add hψ hθ p.1 p.2 g.2 g'.2)
        map_smul' := fun c g => Subtype.ext (GlobalTheory.Size.dRho_smul p.1 p.2 c g) }, fun _ _ => rfl⟩
  have hDc : ∀ p q g, Dop p (Dop q g) = Dop q (Dop p g) + commScalar V W p.1 q.1 p.2 q.2 • g := by
    intro p q g
    apply Subtype.ext
    have h := (hco p.1 q.1 p.2 q.2).2 g g.2
    simp only [Submodule.coe_add, Submodule.coe_smul, hDop]
    rw [← h]
    abel
  obtain ⟨a, ha⟩ : ∃ a : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, a k =
      ((fockScale D k.1 : ℂ)⁻¹) • (Dop (k.1, (1 : ℂ) • uMap M M' k) -
        I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k)) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : FVar D W.rank V.rank → Module.End ℂ (thetaSub V W ψ), ∀ k, b k =
      (-((fockScale D k.1 : ℂ)⁻¹)) • (Dop (k.1, (1 : ℂ) • uMap M M' k) +
        I • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k)) := ⟨_, fun _ => rfl⟩
  have hA : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k g = (a k g : WO V W → ℂ) := by
    intro k g
    rw [ha]
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, hDop, one_smul]
    rw [← cplxO_uMap]
    rfl
  have hB : ∀ k (g : thetaSub V W ψ), GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k g = (b k g : WO V W → ℂ) := by
    intro k g
    rw [hb]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hDop, one_smul]
    rw [← cplxO_uMap]
    rfl
  have hfb : ∀ k, b k ⟨f, hf.theta⟩ = 0 := by
    intro k
    apply Subtype.ext
    rw [← hB]
    have h := hf.vac k.1 (uMap M M' k)
    unfold annih at h
    show GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp ψ θ M M' k f = 0
    unfold GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.annOp annih
    rw [show unitMap (onb M k.1) (onb M' k.1) k.2.1 k.2.2 = uMap M M' k from rfl, h, smul_zero]
  have S1 : ∀ i j : FVar D W.rank V.rank, (fockScale D i.1 : ℂ)⁻¹ * (fockScale D j.1 : ℂ)⁻¹ *
      (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) -
        commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) -
        I * (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) +
          commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((1 : ℂ) • uMap M M' j))) = 0 := by
    intro i j
    simp only [commScalar_uMap]
    by_cases hij : i = j
    · subst hij
      obtain ⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by
        refine ⟨(tauE D i.1 D.host.xi0).im, ?_⟩
        apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]
      simp only [if_true, hy]
      rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> simp
    · simp [hij]
  have S2 : ∀ i j : FVar D W.rank V.rank, -(fockScale D i.1 : ℂ)⁻¹ * ((fockScale D j.1 : ℂ)⁻¹ *
      (commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((1 : ℂ) • uMap M M' j) +
        commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j) +
        I * (commScalar V W i.1 j.1 ((I * (uSgn M M' i : ℂ)) • uMap M M' i) ((1 : ℂ) • uMap M M' j) -
          commScalar V W i.1 j.1 ((1 : ℂ) • uMap M M' i) ((I * (uSgn M M' j : ℂ)) • uMap M M' j)))) =
      if i = j then 1 else 0 := by
    intro i j
    simp only [commScalar_uMap]
    by_cases hij : i = j
    · subst hij
      obtain ⟨y, hy⟩ : ∃ y : ℝ, tauE D i.1 D.host.xi0 = (y : ℂ) * I := by
        refine ⟨(tauE D i.1 D.host.xi0).im, ?_⟩
        apply Complex.ext <;> simp [GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero i.1]
      have hF := fockScale_sq (D := D) i.1
      have hF0 := fockScale_ne (D := D) i.1
      rw [hy] at hF
      simp only [if_true, hy]
      rcases uSgn_cases M M' i with hs | hs <;> rw [hs] <;> clear * - hF hF0 <;> simp at hF ⊢ <;> field_simp <;>
        linear_combination (-1 : ℂ) * hF + (-8 * (Real.pi : ℂ) * (y : ℂ)) * Complex.I_sq
    · simp [hij]
  have haa : ∀ i j g, a i (a j g) = a j (a i g) := by
    intro i j g
    have h1 := (GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc
      (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i)
      (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j)
      ((fockScale D i.1 : ℂ)⁻¹) ((fockScale D j.1 : ℂ)⁻¹) g).1
    simp only [S1 i j, zero_smul, add_zero] at h1
    rw [ha i, ha j]
    exact h1
  have hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g := by
    intro i j g
    have h2 := (GlobalTheory.FockVecInj.ccr_of_comm Dop (fun p q => commScalar V W p.1 q.1 p.2 q.2) hDc
      (i.1, (1 : ℂ) • uMap M M' i) (i.1, (I * (uSgn M M' i : ℂ)) • uMap M M' i)
      (j.1, (1 : ℂ) • uMap M M' j) (j.1, (I * (uSgn M M' j : ℂ)) • uMap M M' j)
      1 ((fockScale D j.1 : ℂ)⁻¹) g).2
    rw [hb i, ha j]
    simp only [LinearMap.smul_apply] at h2 ⊢
    rw [h2, map_smul, ← S2 i j]
    module
  have hmain := fock_of_ccr (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b hA haa
    (fun i j g => by convert hba i j g)
    ⟨f, hf.theta⟩ hfb
  have hpt : ∀ P, ptOf ψ θ M M' f P = pureTensorL (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) f P := fun _ => rfl
  refine ⟨fun P => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpt]
    exact hmain.1 P
  · intro l l' g hg
    rw [hA l' ⟨g, hg⟩, hA l, hA l ⟨g, hg⟩, hA l', haa]
  · intro l l' g hg
    rw [hA l' ⟨g, hg⟩, hB l, hB l ⟨g, hg⟩, hA l', hba, Submodule.coe_add, add_sub_cancel_left, Submodule.coe_smul]
    split_ifs <;> simp
  · intro μ 𝓕 hμ h𝓕 α β
    have hadd : ∀ x y z : thetaSub V W ψ, ipO μ 𝓕 ((x : WO V W → ℂ) + y) z = ipO μ 𝓕 x z + ipO μ 𝓕 y z :=
      fun x y z => GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 x.2 y.2 z.2
    have hsm : ∀ (c : ℂ) (x z : WO V W → ℂ), ipO μ 𝓕 (c • x) z = c * ipO μ 𝓕 x z :=
      fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z
    have hz : ∀ x : WO V W → ℂ, ipO μ 𝓕 x 0 = 0 := by
      intro x
      have h := GlobalTheory.Size.ipO_smul_right μ 𝓕 0 x 0
      rwa [zero_smul, map_zero, zero_mul] at h
    have hskw : ∀ p (x y : thetaSub V W ψ), ipO μ 𝓕 (Dop p x : WO V W → ℂ) y = -ipO μ 𝓕 x (Dop p y) := by
      intro p x y
      rw [hDop, hDop]
      exact (hsk p.1 p.2).2.2 μ 𝓕 hμ h𝓕 x y x.2 y.2
    have hsplit : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ),
        ipO μ 𝓕 ((c • Dop p x + c' • Dop q x : thetaSub V W ψ) : WO V W → ℂ) y =
          c * ipO μ 𝓕 x (Dop p y) * (-1) + c' * ipO μ 𝓕 x (Dop q y) * (-1) := by
      intro c c' p q x y
      rw [Submodule.coe_add, hadd, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, hskw, hskw]
      ring
    have hsplit' : ∀ (c c' : ℂ) (p q : D.what₂.Tau × Matrix (Fin W.rank) (Fin V.rank) ℂ) (x y : thetaSub V W ψ),
        ipO μ 𝓕 (x : WO V W → ℂ) ((c • Dop p y + c' • Dop q y : thetaSub V W ψ) : WO V W → ℂ) =
          conj c * ipO μ 𝓕 x (Dop p y) + conj c' * ipO μ 𝓕 x (Dop q y) := by
      intro c c' p q x y
      rw [Submodule.coe_add, GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 x.2 (c • Dop p y).2 (c' • Dop q y).2,
        Submodule.coe_smul, Submodule.coe_smul, GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_right]
    have hcr : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), a k x = ((fockScale D k.1 : ℂ)⁻¹) • Dop (k.1, (1 : ℂ) • uMap M M' k) x +
        (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x := by
      intro k x
      rw [ha]
      simp only [LinearMap.smul_apply, LinearMap.sub_apply]
      module
    have han : ∀ (k : FVar D W.rank V.rank) (x : thetaSub V W ψ), b k x = (-((fockScale D k.1 : ℂ)⁻¹)) • Dop (k.1, (1 : ℂ) • uMap M M' k) x +
        (-((fockScale D k.1 : ℂ)⁻¹ * I)) • Dop (k.1, (I * (uSgn M M' k : ℂ)) • uMap M M' k) x := by
      intro k x
      rw [hb]
      simp only [LinearMap.smul_apply, LinearMap.add_apply]
      module
    have hcj : ∀ k : FVar D W.rank V.rank, conj ((fockScale D k.1 : ℂ)⁻¹) = (fockScale D k.1 : ℂ)⁻¹ := by
      intro k
      rw [map_inv₀, Complex.conj_ofReal]
    have hadj1 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (a k x : WO V W → ℂ) y = ipO μ 𝓕 x (b k y) := by
      intro k x y
      rw [hcr, han, hsplit, hsplit']
      simp only [map_neg, map_mul, hcj, Complex.conj_I]
      ring
    have hadj2 : ∀ k (x y : thetaSub V W ψ), ipO μ 𝓕 (x : WO V W → ℂ) (a k y) = ipO μ 𝓕 (b k x) y := by
      intro k x y
      rw [hcr, han, hsplit, hsplit']
      simp only [map_neg, map_mul, hcj, Complex.conj_I]
      ring
    rw [hpt, hpt, hmain.2 (ipO μ 𝓕) hadd hsm hz hadj1 hadj2 β (MvPolynomial.monomial α 1),
      MvPolynomial.coeff_monomial]
    by_cases h : α = β
    · subst h
      simp
    · simp [h]
  · have hinj := GlobalTheory.FockVecInj.injective_of_canonicalCommutation (thetaSub V W ψ) (fun k => GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.creOp ψ θ M M' k) a b
      (fun _ => (1 : ℂ)) hA haa (fun i j g => by convert hba i j g) (fun _ => one_ne_zero) ⟨f, hf.theta⟩ hfb
      (fun h => hf.ne (congrArg Subtype.val h))
    intro P Q hPQ
    exact hinj hPQ

theorem vacuumFock_of_thetaSquareIntegrable (D : D7) (h : ThetaSquareIntegrable D) : VacuumFock D := by
  intro V W S S' M M' ψ θ hψ hθ f hf
  obtain ⟨-, hV⟩ := h V W
  obtain ⟨-, -, hD⟩ := hV ψ hψ
  exact fockLaws hψ hθ (hD θ hθ).1 (hD θ hθ).2.1 M M' hf

end GlobalTheory.VacuumFockLaws

end
