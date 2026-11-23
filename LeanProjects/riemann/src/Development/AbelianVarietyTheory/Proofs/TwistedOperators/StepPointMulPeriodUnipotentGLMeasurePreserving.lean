import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationGdetKapAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SecondCountableLocal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section

namespace GlobalTheory.TopLevelInv
namespace StepMove

section Alg

variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open Classical in

def varPart (e : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  Matrix.of fun r s => if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e ⟨(r, s), h⟩ else 0

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem stepPt_eq_add (x₀ : Matrix n n' k) (e : StepVar n c n' → k) : stepPt x₀ e = basePt c x₀ + varPart e := rfl

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem varPart_var (e : StepVar n c n' → k) (a : StepVar n c n') : varPart e a.1.1 a.1.2 = e a := by
  simp [varPart, a.2]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem varPart_nonvar (e : StepVar n c n' → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) : varPart e r s = 0 := by
  simp [varPart, h]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem basePt_var (x₀ : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c x₀ r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp [Free, Kept, basePt] at h ⊢
  all_goals omega

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem eq_stepPt_of (x₀ : Matrix n n' k) (Y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (h : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → Y r s = basePt c x₀ r s) :
    Y = stepPt x₀ (fun a => Y a.1.1 a.1.2) := by
  ext r s
  by_cases hv : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · rw [stepPt_eq_add, Matrix.add_apply, basePt_var x₀ hv, zero_add]
    exact (varPart_var (fun a => Y a.1.1 a.1.2) ⟨(r, s), hv⟩).symm
  · rw [stepPt_eq_add, Matrix.add_apply, varPart_nonvar _ hv, add_zero, h r s hv]

def linV (g : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k) : Matrix (StepVar n c n') (StepVar n c n') k :=
  Matrix.of fun a b => if b.1.1 = a.1.1 then g b.1.2 a.1.2 else 0

open Classical in
theorem varPart_mul_apply (e : StepVar n c n' → k) (g : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)
    (a : StepVar n c n') : (varPart e * g) a.1.1 a.1.2 = (linV g).mulVec e a := by
  have h1 : (linV g).mulVec e a = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
      (if b.1 = a.1.1 then g b.2 a.1.2 else 0) * varPart e b.1 b.2 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
      (fun b _ => by rw [varPart_nonvar _ b.2, mul_zero]), add_zero]
    simp only [Matrix.mulVec, dotProduct, linV, of_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [varPart_var]
  rw [h1, Fintype.sum_prod_type, Finset.sum_eq_single a.1.1]
  · simp [Matrix.mul_apply, mul_comm]
  · intro r' _ hr
    simp [hr]
  · simp

open Classical in

theorem det_linV {q : ℕ} {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN q g) : (linV (n := n) g.val).det = 1 := by
  rw [← det_transpose]
  refine GlobalTheory.RootExSource.det_eq_one_of_unip (fun a => lev q a.1.2) _ fun a b hab => ?_
  rcases a with ⟨⟨r, s⟩, ha⟩
  rcases b with ⟨⟨r', s'⟩, hb⟩
  simp only [linV, transpose_apply, of_apply]
  rw [hg _ _ hab]
  by_cases h1 : r = r' <;> by_cases h2 : s = s' <;> simp [Matrix.one_apply, h1, h2]

omit [Fintype n] [DecidableEq n] in

theorem mul_gen_nonvar {q : ℕ} (hq : q = c / 2 + 1 ∨ (c % 2 = 1 ∧ q = c / 2 + 2)) {g : GL (n' ⊕ Fin (c + 1)) k}
    (hg : InN q g) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1))
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) : (stepPt x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [GlobalTheory.RootExSource.mul_apply_of_inN hg, stepPt_eq_add, Matrix.add_apply, varPart_nonvar _ hv, add_zero,
    Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ (Free (c / 2 + 1) (r, s') ∨ Kept (r, s')) ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, Kept, GlobalTheory.RootEx.lev, basePt, Nat.even_iff, Nat.odd_iff, Fin.ext_iff] at hv h' ⊢ <;> omega
    rw [Matrix.add_apply, varPart_nonvar _ this.1, this.2, add_zero, zero_mul]
  · rfl

end Alg

section Meas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem exists_affine_mp {ι : Type} [Fintype ι] [DecidableEq ι] (ν : Measure k) [ν.IsAddHaarMeasure]
    (M : Matrix ι ι k) (u : kˣ) (hu : (u : k) = M.det) (hv : valuation k (u : k) = 1) (b : ι → k) :
    ∃ φ : (ι → k) ≃ᵐ (ι → k), MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) ∧
      ∀ e, φ e = M.mulVec e + b := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hm : ∀ A : Matrix ι ι k, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hdet : IsUnit M.det := hu ▸ u.isUnit
  let φ : (ι → k) ≃ᵐ (ι → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec (e - b)
      left_inv := fun e => by simp [mulVec_mulVec, nonsing_inv_mul _ hdet]
      right_inv := fun e => by simp [mulVec_mulVec, mul_nonsing_inv _ hdet]
      measurable_toFun := (hm M).add_const b
      measurable_invFun := (hm _).comp (measurable_id.sub_const b) }
  refine ⟨φ, ⟨φ.measurable, ?_⟩, fun e => rfl⟩
  have h1 : distribHaarChar k u = 1 := by
    have := GlobalTheory.SplitWeil.nabs_eq_one_of_valuation_eq_one hv
    unfold nabs at this
    exact_mod_cast this
  have h2 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M u hu
  rw [h1, ENNReal.coe_one, one_smul] at h2
  have e1 : (φ : (ι → k) → (ι → k)) = (fun e => b + e) ∘ M.mulVec := by
    funext e; exact add_comm _ _
  rw [e1, ← Measure.map_map (measurable_const_add b) (hm M), h2]
  exact map_add_left_eq_self _ b

theorem exists_blocks_mp {F m J : Type} [Fintype F] [Fintype m] [DecidableEq m] [Fintype J]
    (ν : Measure k) [ν.IsAddHaarMeasure] (ι : m × J → F) (hι : Function.Injective ι)
    (A : Matrix m m k) (u : kˣ) (hu : A.det = u) (hv : valuation k (u : k) = 1) (T : (F → k) → (F → k))
    (h1 : ∀ e r j, T e (ι (r, j)) = ∑ s, A r s * e (ι (s, j)))
    (h2 : ∀ e f, f ∉ Set.range ι → T e f = e f) :
    ∃ φ : (F → k) ≃ᵐ (F → k), MeasurePreserving φ (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) ∧
      ∀ e, φ e = T e := by
  classical
  let σ : (m × J) ⊕ {f // f ∉ Set.range ι} ≃ F :=
    (Equiv.sumCongr (Equiv.ofInjective ι hι) (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ Set.range ι))
  have σl : ∀ x, σ (Sum.inl x) = ι x := fun x => rfl
  have σr : ∀ x, σ (Sum.inr x) = x.1 := fun x => rfl
  let G : Matrix F F k := Matrix.reindex σ σ (fromBlocks (blockDiagonal fun _ : J => A) 0 0 1)
  have hG : G.det = (u ^ Fintype.card J : kˣ) := by
    simp [G, det_blockDiagonal, hu]
  have hT : ∀ e, T e = G.mulVec e := by
    intro e
    funext x
    obtain ⟨y, rfl⟩ := σ.surjective x
    rw [Matrix.mulVec, dotProduct, ← σ.sum_comp]
    rcases y with ⟨r, j⟩ | y
    · have : σ.symm (ι (r, j)) = Sum.inl (r, j) := by rw [← σl]; simp
      simp [G, this, σl, σr, h1, Fintype.sum_sum_type, Fintype.sum_prod_type, blockDiagonal_apply]
    · rw [σr, h2 _ _ y.2]
      have : σ.symm y.1 = Sum.inr y := by rw [← σr]; simp
      simp [G, this, Fintype.sum_sum_type, Matrix.one_apply, σr]
  obtain ⟨φ, hφ, hφe⟩ := exists_affine_mp ν G (u ^ Fintype.card J) hG.symm
    (by rw [Units.val_pow_eq_pow_val, map_pow, hv, one_pow]) 0
  exact ⟨φ, hφ, fun e => by rw [hφe, add_zero, hT]⟩

end Meas

section Step

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
  (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (n' : Type) [Fintype n'] [DecidableEq n']

def movers : Subgroup (GL (n' ⊕ Fin (c + 1)) k) where
  carrier := {g | ∀ x₀ : Matrix n n' k, ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k),
    MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧ ∀ e, stepPt x₀ e * g.val = stepPt x₀ (φ e)}
  one_mem' x₀ := ⟨MeasurableEquiv.refl _, MeasurePreserving.id _, fun e => by simp⟩
  mul_mem' {g h} hg hh x₀ := by
    obtain ⟨φ, hφ, hφe⟩ := hg x₀
    obtain ⟨χ, hχ, hχe⟩ := hh x₀
    exact ⟨φ.trans χ, hχ.comp hφ, fun e => by
      rw [Units.val_mul, ← Matrix.mul_assoc, hφe, hχe]; rfl⟩
  inv_mem' {g} hg x₀ := by
    obtain ⟨φ, hφ, hφe⟩ := hg x₀
    refine ⟨φ.symm, hφ.symm φ, fun e => ?_⟩
    conv_lhs => rw [← φ.apply_symm_apply e, ← hφe]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

variable {ν n c n'}

open Classical in
theorem mem_movers_of_inN {q : ℕ} (hq : q = c / 2 + 1 ∨ (c % 2 = 1 ∧ q = c / 2 + 2))
    {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN q g) : g ∈ movers ν n c n' := by
  intro x₀
  obtain ⟨φ, hφ, hφe⟩ := exists_affine_mp ν (linV (n := n) g.val) 1 (by rw [det_linV hg]; rfl)
    (by simp) (fun a => (basePt c x₀ * g.val) a.1.1 a.1.2)
  refine ⟨φ, hφ, fun e => ?_⟩
  rw [eq_stepPt_of x₀ (stepPt x₀ e * g.val) (mul_gen_nonvar hq hg x₀ e)]
  congr 1
  funext a
  rw [hφe, stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, varPart_mul_apply, Pi.add_apply, add_comm]

theorem symN_le_movers : symN k n' (c + 1) ≤ movers ν n c n' := by
  refine sup_le ((Subgroup.closure_le _).2 fun g hg => mem_movers_of_inN ?_ hg)
    ((Subgroup.closure_le _).2 fun g hg => mem_movers_of_inN ?_ hg)
  · omega
  · omega

open Classical in

theorem exists_embX_mp (κ : GL n' k) (hκ : valuation k (gdet κ : k) = 1) (x₀ : Matrix n n' k) :
    ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
      ∀ e, stepPt x₀ e * (embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  have hgv : (embX (c + 1) κ).val = fromBlocks κ.val 0 0 1 := rfl
  let ι : n' × {l : Fin c // l.val + 1 < c / 2 + 1 ∨ (Odd c ∧ l.val = c / 2)} → StepVar n c n' :=
    fun x => ⟨(Sum.inr x.2.1, Sum.inl x.1), x.2.2⟩
  have hι : Function.Injective ι := by
    rintro ⟨a, b, hb⟩ ⟨a', b', hb'⟩ h
    have h' := congrArg Subtype.val h
    simp only [ι, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  let T : (StepVar n c n' → k) → (StepVar n c n' → k) := fun e a => (varPart e * (embX (c + 1) κ).val) a.1.1 a.1.2
  obtain ⟨φ, hφ, hφe⟩ := exists_blocks_mp ν ι hι κ.valᵀ (gdet κ) (by rw [det_transpose]; rfl) hκ T
    (fun e r j => by
      simp only [T, ι, hgv, GlobalTheory.RootEx.OpELevi.right_inl]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [varPart_var e ⟨(Sum.inr j.1, Sum.inl t), j.2⟩])
    (fun e f hf => by
      rcases f with ⟨⟨r, s | s⟩, hrs⟩
      · rcases r with r | r
        · exact (hrs.elim (fun h => h.elim) (fun h => h.elim))
        · exact (hf ⟨(s, ⟨r, hrs⟩), rfl⟩).elim
      · simp only [T, hgv, GlobalTheory.RootEx.OpELevi.right_inr]
        exact varPart_var e ⟨(r, Sum.inr s), hrs⟩)
  refine ⟨φ, hφ, fun e => ?_⟩
  have hb : basePt c x₀ * (embX (c + 1) κ).val = basePt c (x₀ * κ.val) := by
    simp [hgv, basePt, fromBlocks_multiply]
  have hnv : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (varPart e * (embX (c + 1) κ).val) r s = 0 := by
    intro r s hv
    rcases s with s | s
    · rw [hgv, GlobalTheory.RootEx.OpELevi.right_inl]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [varPart_nonvar, mul_zero]
      rcases r with r | r
      · exact hv
      · exact hv
    · rw [hgv, GlobalTheory.RootEx.OpELevi.right_inr, varPart_nonvar _ hv]
  rw [eq_stepPt_of (x₀ * κ.val) (stepPt x₀ e * (embX (c + 1) κ).val) (fun r s hv => by
    rw [stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, hb, hnv r s hv, add_zero])]
  congr 1
  funext a
  rw [hφe, stepPt_eq_add, Matrix.add_mul, Matrix.add_apply, hb, basePt_var _ a.2, zero_add]

end Step

end StepMove

theorem stepPt_mul_symN_embX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n' (c + 1), ∀ κ : GL n' k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, stepPt x₀ e * (v * embX (c + 1) κ).val = stepPt (x₀ * κ.val) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  obtain ⟨φ, hφ, hφe⟩ := StepMove.symN_le_movers (ν := ν) (n := n) hv x₀
  obtain ⟨χ, hχ, hχe⟩ := StepMove.exists_embX_mp (ν := ν) (c := c) κ hκ x₀
  exact ⟨φ.trans χ, hχ.comp hφ, fun e => by
    rw [Units.val_mul, ← Matrix.mul_assoc, hφe, hχe]; rfl⟩

end GlobalTheory.TopLevelInv
