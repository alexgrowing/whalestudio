import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RankTwoDimensionFormula.DimFormCOfThree

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt

namespace PI.UnitaryDimensionFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def cj {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : Hfin X u) : X.B.I.Gf :=
  (X.xu u)⁻¹ * (s : X.B.I.Gf) * X.xu u

def UniSub : Prop :=
  ∀ (F : Type) [Field F] (k : ℕ) (x y : GL (Fin k) F), Formalism.L2.SG.GGMirabolic.IsUni k x →
    Formalism.L2.SG.GGMirabolic.IsUni k y →
      Formalism.L2.SG.GGMirabolic.IsUni k (x * y) ∧ Formalism.L2.SG.GGMirabolic.IsUni k x⁻¹

def IdxHom : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    levi Y.TR (1 : X.B.I.Gf) = 1 ∧
    (∀ s t : Hfin X u, cj X u s ∈ X.B.I.Kset → cj X u t ∈ X.B.I.Kset →
      levi Y.TR (cj X u (s * t)) = levi Y.TR (cj X u s) * levi Y.TR (cj X u t)) ∧
    ∀ s : Hfin X u, cj X u s ∈ X.B.I.Kset → s ∈ Ku X u Y.hK →
      ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (levi Y.TR (cj X u s) v)

def IdxSurj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ A : Iof Y.TR, ∃ s : Hfin X u, cj X u s ∈ X.B.I.Kset ∧ levi Y.TR (cj X u s) = A

variable {D : D7} {X : HidaSetting D}

theorem kset_inv {m : X.B.I.Gf} (hm : m ∈ X.B.I.Kset) : m⁻¹ ∈ X.B.I.Kset := by
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm ⊢
  simpa using (Formalism.UG.stabGL X.B.I.Lf).inv_mem hm

theorem cj_inv (u : D.what₂.Word) (s : Hfin X u) : cj X u s⁻¹ = (cj X u s)⁻¹ := by
  simp [cj, mul_assoc]

theorem cj_one (u : D.what₂.Word) : cj X u 1 = 1 := by
  simp [cj]

theorem latS_mul_K {u : D.what₂.Word} (h : X.B.I.Gf) (s : Hfin X u) (hs : cj X u s ∈ X.B.I.Kset) :
    latS X u (h * (s : X.B.I.Gf)) = latS X u h := by
  ext y
  simp only [latS, Set.mem_setOf_eq]
  have e : (h * (s : X.B.I.Gf) * X.xu u)⁻¹ = (cj X u s)⁻¹ * (h * X.xu u)⁻¹ := by
    simp only [cj]; group
  have hm := kset_inv hs
  simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm
  have e2 : X.B.I.fmat ((cj X u s)⁻¹ * (h * X.xu u)⁻¹) =
      X.B.I.fmat (cj X u s)⁻¹ * X.B.I.fmat (h * X.xu u)⁻¹ := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  rw [e, e2, ← Matrix.mulVec_mulVec]
  exact (hm _).symm

def Uprod (hU : UniSub) (TR : TypedRed X) : Subgroup (Iof TR) where
  carrier := {x | ∀ v, Formalism.L2.SG.GGMirabolic.IsUni D.R.k (x v)}
  one_mem' := fun _ => Formalism.L2.SG.GGMirabolic.isUni_one
  mul_mem' := fun {a b} ha hb v => (hU _ _ _ _ (ha v) (hb v)).1
  inv_mem' := fun {a} ha v => (hU _ _ _ _ (ha v) (ha v)).2

theorem card_Uprod (hU : UniSub) (TR : TypedRed X) :
    Nat.card (Uprod hU TR) = ∏ v, Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k := by
  have e : ↥(Uprod hU TR) ≃ ∀ v, {x : GL (Fin D.R.k) (TR.Fq v) // Formalism.L2.SG.GGMirabolic.IsUni D.R.k x} :=
    Equiv.subtypePiEquivPi
  rw [Nat.card_congr e, Nat.card_pi]
  rfl

theorem card_Iof (TR : TypedRed X) :
    Nat.card (Iof TR) = ∏ v, Fintype.card (GL (Fin D.R.k) (TR.Fq v)) := by
  rw [Nat.card_pi]
  simp [Nat.card_eq_fintype_card]

theorem gamma_one_eq_card (hU : UniSub) (TR : TypedRed X) :
    Gam1 TR = (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) := by
  have hU0 : ∀ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) ≠ 0 := by
    intro v
    have : Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k ≠ 0 := by
      unfold Formalism.L2.SG.GGMirabolic.cardU
      exact Nat.card_ne_zero.mpr ⟨⟨⟨1, Formalism.L2.SG.GGMirabolic.isUni_one⟩⟩, inferInstance⟩
    exact_mod_cast this
  have h1 : ∀ v, Formalism.L2.SG.GGMirabolic.gam (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) =
      (((Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) : ℝ) : ℂ) := by
    intro v
    have hp : Formalism.L2.SG.GGMirabolic.psiNat (TR.psi0 v) (1 : GL (Fin D.R.k) (TR.Fq v)) = 1 := by
      rw [Formalism.L2.SG.GGMirabolic.psiNat, if_pos Formalism.L2.SG.GGMirabolic.isUni_one, Formalism.L2.SG.GGMirabolic.psiU]
      convert AddChar.map_zero_eq_one (TR.psi0 v)
      unfold Formalism.L2.SG.GGMirabolic.superdiag
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with hj
      · show (1 : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) i j = 0
        exact Matrix.one_apply_ne (fun hij => by subst hij; omega)
      · rfl
    rw [Formalism.L2.SG.GGMirabolic.gam]
    simp only [mul_one, mul_inv_cancel, hp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    push_cast
    rw [div_eq_inv_mul]
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Uprod hU TR)
  rw [card_Iof, card_Uprod] at hq
  have hq' : (Nat.card (Iof TR ⧸ Uprod hU TR) : ℝ) =
      (∏ v, (Fintype.card (GL (Fin D.R.k) (TR.Fq v)) : ℝ)) /
        ∏ v, (Formalism.L2.SG.GGMirabolic.cardU (TR.Fq v) D.R.k : ℝ) := by
    rw [eq_div_iff (Finset.prod_ne_zero_iff.mpr fun v _ => hU0 v)]
    exact_mod_cast hq.symm
  rw [hq', ← Finset.prod_div_distrib]
  simp only [Formalism.L2.SG.TermOp.Gam1, Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, h1]
  rw [← Complex.ofReal_prod, Complex.ofReal_re]

theorem indexGe_of (hU : UniSub) (hH : IdxHom) (hS : IdxSurj) : IndexGe := by
  intro D X Y u hT Λ hΛ
  classical
  have hlat0 : latS X u (((Y.cs u).h ((Y.cs u).base Λ) : Hfin X u) : X.B.I.Gf) = (Λ : Set (VS D).V) := by
    rw [← lamOf_eq_latS (Y.cs u) ((Y.cs u).base Λ), (Y.cs u).base_lam Λ hΛ]
  have hKmul : ∀ m m' : X.B.I.Gf, m ∈ X.B.I.Kset → m' ∈ X.B.I.Kset → m * m' ∈ X.B.I.Kset := by
    intro m m' hm hm'
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hm hm' ⊢
    simpa using (Formalism.UG.stabGL X.B.I.Lf).mul_mem hm hm'
  have cj_mul : ∀ a b : Hfin X u, cj X u (a * b) = cj X u a * cj X u b := by
    intro a b
    simp only [cj, Subgroup.coe_mul]
    group
  obtain ⟨hl1, hlmul, hluni⟩ := hH D X Y u hT
  choose s hsK hsA using hS D X Y u hT
  let e : Fin (Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR)) ≃ (Iof Y.TR ⧸ Uprod hU Y.TR) :=
    (Finite.equivFin _).symm
  refine ⟨Nat.card (Iof Y.TR ⧸ Uprod hU Y.TR),
    fun i => (Y.cs u).h ((Y.cs u).base Λ) * s (Quotient.out (e i)), ?_, ?_, ?_⟩
  · exact le_of_eq (gamma_one_eq_card hU Y.TR)
  · intro i
    rw [Subgroup.coe_mul, latS_mul_K _ _ (hsK _), hlat0]
  · intro i j hij
    have hAi := hsA (Quotient.out (e i))
    have hAj := hsA (Quotient.out (e j))
    have hKa := hsK (Quotient.out (e i))
    have hKb := hsK (Quotient.out (e j))
    set a := s (Quotient.out (e i)) with ha
    set b := s (Quotient.out (e j)) with hb
    have hab : a⁻¹ * b ∈ Ku X u Y.hK := by
      have : ((Y.cs u).h ((Y.cs u).base Λ) * a)⁻¹ * ((Y.cs u).h ((Y.cs u).base Λ) * b) = a⁻¹ * b := by
        group
      rwa [this] at hij
    have hKai : cj X u a⁻¹ ∈ X.B.I.Kset := by
      rw [cj_inv]
      exact kset_inv hKa
    have hKab : cj X u (a⁻¹ * b) ∈ X.B.I.Kset := by
      rw [cj_mul]
      exact hKmul _ _ hKai hKb
    have hinv : levi Y.TR (cj X u a⁻¹) = (levi Y.TR (cj X u a))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hlmul _ _ hKai hKa, inv_mul_cancel, cj_one, hl1]
    have hmem : (Quotient.out (e i))⁻¹ * Quotient.out (e j) ∈ Uprod hU Y.TR := by
      have h2 := hluni _ hKab hab
      rw [hlmul _ _ hKai hKb, hinv, hAi, hAj] at h2
      exact h2
    apply e.injective
    rw [← QuotientGroup.out_eq' (e i), ← QuotientGroup.out_eq' (e j)]
    exact QuotientGroup.eq.mpr hmem

end PI.UnitaryDimensionFormula
