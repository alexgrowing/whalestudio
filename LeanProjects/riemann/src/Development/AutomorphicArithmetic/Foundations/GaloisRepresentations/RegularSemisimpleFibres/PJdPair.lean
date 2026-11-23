import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseOneProdIcoStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma deg_app (a b : List (ℕ × ℕ)) : deg (a ++ b) = deg a + deg b := by
  simp [GlobalTheory.Shin.deg]

private lemma deg_rep (t c : ℕ) : deg (List.replicate t ((1 : ℕ), c)) = t := by
  simp [GlobalTheory.Shin.deg]

private lemma expand_cons' (p : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    expand (p :: D) = List.replicate p.1 (1, p.2) ++ expand D := by
  simp [UpperTheory.Gal.InertialTypesAlt.expand]

private lemma cusp_one_ne {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ)
    (hm : 0 < m) : cusp θ m k 1 ≠ 0 := by
  have h := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico F (Fin m → F) (GlobalTheory.CuspGL.rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow F θ k).2 (by simpa using hm)
  simp only [cusp, psiG, Units.val_one, Matrix.toLin'_one]
  erw [h]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  rw [sub_ne_zero]
  intro heq
  have h2 : ((Nat.card F ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    exact heq.symm
  norm_cast at h2
  have h3 := Nat.one_lt_pow (by omega : i ≠ 0) hq
  omega

private lemma pairs_self {G : Type} [Group G] [Finite G] (Y : G → ℂ) (h : Y 1 ≠ 0) : Pairs Y Y := by
  haveI : Fintype G := Fintype.ofFinite G
  unfold Pairs
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ g : G, 0 ≤ (star (Y g) * Y g).re := by
    intro g
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have hpos : 0 < (star (Y 1) * Y 1).re := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr h
  have : 0 < ∑ g : G, (star (Y g) * Y g).re :=
    Finset.sum_pos' (fun g _ => hnn g) ⟨1, Finset.mem_univ _, hpos⟩
  linarith

private lemma happ (hA : JAppend) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (R M : List (ℕ × ℕ)) (t b n : ℕ) (hR : deg R = t) (hM : deg M = b) (hn : n = t + b) :
    J θ (R ++ M) n = hc t b (J θ R t) (J θ M b) n := by
  subst hR hM hn
  exact hA F θ R M _ rfl

private lemma char_cast {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (M : List (ℕ × ℕ)) {n m : ℕ}
    (e : n = m) (h : GlobalTheory.BI.IsChar ℂ ℂ (J θ M n)) : GlobalTheory.BI.IsChar ℂ ℂ (J θ M m) := by
  subst e
  exact h

private lemma J_one_ne (h1 : HcOne) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (M : List (ℕ × ℕ)) (hM : ∀ p ∈ M, 0 < p.1) : J θ M (deg M) 1 ≠ 0 := by
  induction M with
  | nil =>
    rw [J_nil]
    exact one_ne_zero
  | cons p M ih =>
    have hp : 0 < p.1 := hM p (by simp)
    have hM' : ∀ x ∈ M, 0 < x.1 := fun x hx => hM x (by simp [hx])
    rw [J_cons]
    exact h1 F p.1 (deg M) _ (by simp [GlobalTheory.Shin.deg]) _ _ (cusp_one_ne θ p.1 p.2 hp) (ih hM')

theorem UpperTheory.Gal.InertialTypesAlt.jdPair :
    JAppend → HcOne → HcPair → DetPair → JDChar → JDPair := by
  intro hA h1 hP hD hC F _ _ θ hθ a ha hq
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq2, hDp, hLp⟩ := ha
  have hL0 : ∀ x ∈ L, 0 < x.1 := fun x hx => (hLp x hx).1
  have charJ : ∀ M : List (ℕ × ℕ), (∀ x ∈ M, 0 < x.1 ∧ Reg q x.1 x.2) → ∀ n, n = deg M →
      GlobalTheory.BI.IsChar ℂ ℂ (J θ M n) := by
    intro M hM n hn
    have hc := (hC F θ hθ).2 ⟨q, [], M⟩ ⟨hq2, by simp, hM⟩ hq
    simp only [Lbl.D, Lbl.L, Lbl.rk] at hc
    rw [JD_nil] at hc
    exact char_cast θ M (by simp [GlobalTheory.Shin.deg] at hn ⊢; omega) hc
  have key : ∀ E : List (ℕ × ℕ), (∀ x ∈ E, 0 < x.1) →
      deg (expand E ++ L) = deg E + deg L ∧
        Pairs (J θ (expand E ++ L) (deg E + deg L)) (JD θ E L (deg E + deg L)) := by
    intro E
    induction E with
    | nil =>
      intro _
      have e1 : expand [] ++ L = L := by simp [UpperTheory.Gal.InertialTypesAlt.expand]
      have e2 : deg ([] : List (ℕ × ℕ)) = 0 := by simp [GlobalTheory.Shin.deg]
      rw [e1, e2, zero_add, JD_nil]
      exact ⟨rfl, pairs_self _ (J_one_ne h1 θ L hL0)⟩
    | cons p E ih =>
      intro hp
      have hp1 : 0 < p.1 := hp p (by simp)
      have hE : ∀ x ∈ E, 0 < x.1 := fun x hx => hp x (by simp [hx])
      obtain ⟨hdeg, hpair⟩ := ih hE
      have hdc : deg (p :: E) = p.1 + deg E := by simp [GlobalTheory.Shin.deg]
      have hexp : ∀ x ∈ expand E ++ L, 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.mem_flatMap, List.mem_replicate] at h
          obtain ⟨y, -, -, rfl⟩ := h
          exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
        · exact hLp x h
      have hrep : ∀ x ∈ List.replicate p.1 ((1 : ℕ), p.2), 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rw [List.mem_replicate] at hx
        rw [hx.2]
        exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
      rw [expand_cons', List.append_assoc, deg_app, deg_rep, hdeg, hdc]
      refine ⟨by omega, ?_⟩
      rw [happ hA θ _ _ p.1 (deg E + deg L) _ (deg_rep _ _) hdeg (by omega), JD_cons]
      refine hP F p.1 _ _ (by omega) _ _ _ _ ((hC F θ hθ).1 _ _)
        (charJ _ hrep _ (deg_rep _ _).symm) ((hC F θ hθ).2 ⟨q, E, L⟩ ⟨hq2, hE, hLp⟩ hq)
        (charJ _ hexp _ hdeg.symm) (hD F θ p.1 p.2) hpair
  exact key D hDp
