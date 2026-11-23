import Mathlib
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

open Formalism.L2.DIV Formalism.BasicNotions NumberField

namespace GlobalTheory

open NumberField in
private lemma blockAct_map_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K₀)
    (P : MvPolynomial (ι × Fin n × Fin n) K₀) :
    _root_.Formalism.GradedWeylDivisibility.blockAct K U (MvPolynomial.map K₀.subtype P) ∈ (MvPolynomial.map K₀.subtype).range := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  | add p q hp hq =>
    rw [map_add, map_add]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul, map_mul, MvPolynomial.map_X, _root_.Formalism.L2.DIV.blockAct_X]
    refine mul_mem hp (sum_mem fun b _ => mul_mem ?_ ?_)
    · exact ⟨MvPolynomial.C ⟨U v.1 v.2.1 b, hU _ _ _⟩, by simp⟩
    · exact ⟨MvPolynomial.X (v.1, b, v.2.2), by simp⟩

open NumberField in
private lemma actP_mem_range_map_of_entries_mem {K : Type} [Field K] (K₀ : Subfield K) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (g : ι → GL (Fin n) K)
    (hg : ∀ τ a b, (g τ : Matrix (Fin n) (Fin n) K) a b ∈ K₀)
    {F : _root_.Formalism.L2.DIV.Pol K ι n} (hF : F ∈ (MvPolynomial.map K₀.subtype).range) :
    _root_.Formalism.L2.DIV.actP lam g F ∈ (MvPolynomial.map K₀.subtype).range := by
  obtain ⟨P, rfl⟩ := hF
  have hdet : ∀ τ, (g τ : Matrix (Fin n) (Fin n) K).det ∈ K₀ := by
    intro τ
    have hM : (g τ : Matrix (Fin n) (Fin n) K) =
        (Matrix.of fun a b => (⟨(g τ : Matrix _ _ K) a b, hg τ a b⟩ : K₀)).map K₀.subtype := by
      ext a b; rfl
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hd : _root_.Formalism.L2.DIV.detTwK lam g ∈ K₀ := by
    rw [_root_.Formalism.L2.DIV.detTw_eq]
    exact prod_mem fun τ _ => by
      first | exact pow_mem (hdet τ) _ | exact zpow_mem (hdet τ) _
  unfold _root_.Formalism.L2.DIV.actP _root_.Formalism.L2.DIV.trAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul]
  refine mul_mem ⟨MvPolynomial.C ⟨_, hd⟩, by simp⟩ (blockAct_map_mem_range_map_of_entries_mem K₀ _ ?_ P)
  intro τ a b
  exact hg τ b a

open NumberField in

theorem _root_.GlobalTheory.coefAction_repr_mem_subfield : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (K₀ : Subfield K) (lam : ι → _root_.Formalism.BasicNotions.DomWeight n), (∀ τ x, emb τ x ∈ K₀) → ∀ (g : GL (Fin n) E) i j, (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoV emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ ∧ (_root_.Formalism.L2.DIV.bVV K lam).repr (_root_.Formalism.L2.DIV.rhoVr emb lam g (_root_.Formalism.L2.DIV.bVV K lam j)) i ∈ K₀ := by
  intro E K ι _ _ _ _ _ n emb K₀ lam hemb γ i j
  classical
  have hbase : ∀ l, _root_.Formalism.L2.DIV.bVVfun K lam l ∈ (MvPolynomial.map K₀.subtype).range := by
    intro l
    obtain ⟨P, hP⟩ := _root_.Formalism.L2.DIV.bVVfun_int K lam l
    rw [hP]
    exact _root_.Formalism.L2.DIV.fk_int_mem K₀ P
  have key : ∀ x : _root_.Formalism.L2.DIV.VV K lam, (x : _root_.Formalism.L2.DIV.Pol K ι n) ∈ (MvPolynomial.map K₀.subtype).range →
      (_root_.Formalism.L2.DIV.bVV K lam).repr x i ∈ K₀ := by
    intro x hx
    refine _root_.Formalism.L2.DIV.fk_descent K₀ (_root_.Formalism.L2.DIV.bVVfun K lam) (_root_.Formalism.L2.DIV.bVVfun_spec K lam).1 hbase (fun l => (_root_.Formalism.L2.DIV.bVV K lam).repr x l) ?_ i
    have hs := congrArg Subtype.val ((_root_.Formalism.L2.DIV.bVV K lam).sum_repr x)
    rw [Submodule.coe_sum] at hs
    simp only [Submodule.coe_smul, _root_.Formalism.L2.DIV.bVV_coe] at hs
    rw [hs]
    exact hx
  have hj : ((_root_.Formalism.L2.DIV.bVV K lam j : _root_.Formalism.L2.DIV.VV K lam) : _root_.Formalism.L2.DIV.Pol K ι n) ∈
      (MvPolynomial.map K₀.subtype).range := by
    rw [_root_.Formalism.L2.DIV.bVV_coe]; exact hbase j
  constructor
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoV
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [_root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _
  · apply key
    unfold _root_.Formalism.L2.DIV.rhoVr
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.rhoK_coe]
    refine actP_mem_range_map_of_entries_mem K₀ lam _ ?_ hj
    intro τ a b
    rw [MonoidHom.comp_apply, _root_.Formalism.L2.DIV.invTrK_coe, _root_.Formalism.L2.DIV.embGL_inv, _root_.Formalism.L2.DIV.embGL_coe]
    exact hemb τ _

end GlobalTheory
