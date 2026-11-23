import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Development.AbelianVarietyTheory.Definitions.Foundations.UnitarySixTwoHarishChandraParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormulaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParamRegularCardMinusCountStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardWeightSetGridEqGridRowSpaceRankStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.SignedHC
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

theorem jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext a; cases ε a <;> simp

theorem jm_submatrix {n : ℕ} (ε : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    (Formalism.REAL.Jm ε).submatrix σ σ = Formalism.REAL.Jm (ε ∘ σ) := by
  ext a b
  simp [Formalism.REAL.Jm, Matrix.diagonal_apply, σ.injective.eq_iff]

theorem gram_submatrix {n : ℕ} (O G : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    (O.submatrix id σ)ᴴ * G * O.submatrix id σ = (Oᴴ * G * O).submatrix σ σ := by
  ext a b
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem mul_submatrix_cols {n : ℕ} (C O : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    C * O.submatrix id σ = (C * O).submatrix id σ := by
  ext a b
  simp [Matrix.mul_apply]

theorem submatrix_mul_jm {n : ℕ} (O : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (σ : Equiv.Perm (Fin n)) :
    (O * Formalism.REAL.Jm ε).submatrix id σ = O.submatrix id σ * Formalism.REAL.Jm (ε ∘ σ) := by
  rw [← jm_submatrix, Matrix.submatrix_mul_equiv]

theorem isUnit_of_gram {n : ℕ} {O G : Matrix (Fin n) (Fin n) ℂ} {ε : Fin n → Bool} (h : Oᴴ * G * O = Formalism.REAL.Jm ε) :
    IsUnit O := by
  refine IsUnit.of_mul_eq_one_right (Formalism.REAL.Jm ε * (Oᴴ * G)) ?_
  rw [Matrix.mul_assoc, h, jm_mul_jm]

theorem card_false_of_gram {D : D7} {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) {O : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {ε : Fin V.rank → Bool} (h : Oᴴ * gramAt D V τ * O = Formalism.REAL.Jm ε) :
    (Finset.univ.filter fun a => ε a = false).card = (V.sig (tauE D τ)).2 :=
  (Formalism.UG.P.signature_unique _ _ _ _ _ _ (GlobalTheory.AutInhab.hasSignature_of_frame (isUnit_of_gram h) h) (hV (tauE D τ))).2

theorem exists_perm_of_card_false {n : ℕ} (ε ε' : Fin n → Bool)
    (h : (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun a => ε' a = false).card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, ε (σ a) = ε' a := by
  have hc : ∀ f : Fin n → Bool, (Finset.univ.filter fun a => f a = true).card +
      (Finset.univ.filter fun a => f a = false).card = n := fun f => by
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a => f a = true)
    simpa using this
  have e : ∀ c : Bool, Fintype.card {a // ε' a = c} = Fintype.card {a // ε a = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    cases c
    · exact h.symm
    · have h1 := hc ε; have h2 := hc ε'; omega
  let σ : Fin n ≃ Fin n := Equiv.ofFiberEquiv (f := ε') (g := ε) fun c => Fintype.equivOfCardEq (e c)
  exact ⟨σ, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_isEnum_of_regular {n : ℕ} {S : SPar} (hS : SignedHC.IsRegular S) (hc : S.card = n) :
    ∃ (lam : Fin n → ℝ) (ε : Fin n → Bool), IsEnum S lam ε ∧
      (Finset.univ.filter fun a => ε a = false).card = SignedHC.nMinus S := by
  have hc' : (entries S).card = n := (SignedHC.IsRegular.card_entries hS).trans hc
  have hinj : Function.Injective (descEnum (entries S) hc') := (strictAnti_descEnum _ hc').injective
  have hS' : S = Finset.univ.image fun a => (descEnum _ hc' a, sign S (descEnum _ hc' a)) := by
    conv_lhs => rw [SignedHC.IsRegular.eq_ofSign hS, ← image_descEnum _ hc', ofSign, Finset.image_image]
    rfl
  refine ⟨fun a => (descEnum _ hc' a : ℝ), fun a => sign S (descEnum _ hc' a),
    ⟨fun a b h => by simpa using strictAnti_descEnum _ hc' h, _, fun _ => rfl, hS'⟩, ?_⟩
  rw [SignedHC.nMinus]
  conv_rhs => rw [hS']
  rw [Finset.filter_image, Finset.card_image_of_injective _ (fun a b h => hinj (congrArg Prod.fst h))]

theorem dualPar_shift_eq (c : ℚ) (S : SPar) : dualPar (shift c S) = S.image fun x => (-(x.1 + c), x.2) := by
  simp only [dualPar, shift, Finset.image_image]
  rfl

theorem dualPar_shift_inj (c : ℚ) : Function.Injective fun x : ℚ × Bool => (-(x.1 + c), x.2) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  simp only [Prod.mk.injEq, neg_inj, add_left_inj] at h
  rw [h.1, h.2]

theorem dualPar_shift_counts (c : ℚ) {S : SPar} (hS : SignedHC.IsRegular S) :
    SignedHC.IsRegular (dualPar (shift c S)) ∧ (dualPar (shift c S)).card = S.card ∧ nMinus (dualPar (shift c S)) = SignedHC.nMinus S := by
  rw [dualPar_shift_eq]
  refine ⟨?_, Finset.card_image_of_injective _ (dualPar_shift_inj c), ?_⟩
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    simp only [neg_inj, add_left_inj] at hxy
    exact hS a ha b hb hxy
  · rw [SignedHC.nMinus, SignedHC.nMinus, Finset.filter_image, Finset.card_image_of_injective _ (dualPar_shift_inj c)]

theorem plus_counts (E : Finset ℚ) : SignedHC.IsRegular (plus E) ∧ (plus E).card = E.card ∧ nMinus (plus E) = 0 := by
  refine ⟨SignedHC.isRegular_plus E, Finset.card_image_of_injective _ fun a b h => congrArg Prod.fst h, ?_⟩
  rw [SignedHC.nMinus, plus, Finset.filter_image]
  simp

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem exists_perm_onb {D : D7} {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) {S : SPar}
    (hS : SignedHC.IsRegular S) (hc : S.card = V.rank) (hm : SignedHC.nMinus S = (V.sig (tauE D τ)).2)
    {O C : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : ∃ ε : Fin V.rank → Bool, Oᴴ * gramAt D V τ * O = Formalism.REAL.Jm ε ∧ C * O = O * Formalism.REAL.Jm ε) :
    ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum S lam ε ∧
      (O.submatrix id σ)ᴴ * gramAt D V τ * O.submatrix id σ = Formalism.REAL.Jm ε ∧
      C * O.submatrix id σ = O.submatrix id σ * Formalism.REAL.Jm ε := by
  obtain ⟨ε, h1, h2⟩ := h
  obtain ⟨lam, ε', hE, hc'⟩ := exists_isEnum_of_regular hS hc
  obtain ⟨σ, hσ⟩ := exists_perm_of_card_false ε ε' (by rw [card_false_of_gram hV τ h1, hc', hm])
  have e : ε ∘ σ = ε' := funext hσ
  refine ⟨σ, lam, ε', hE, ?_, ?_⟩
  · rw [gram_submatrix, h1, jm_submatrix, e]
  · rw [mul_submatrix_cols, h2, submatrix_mul_jm, e]

theorem cart_eq_one {D : D7} {V : HSp D} (hV : V.SigOK) (τ : D.what₂.Tau) (h0 : (V.sig (tauE D τ)).2 = 0)
    {O C : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : ∃ ε : Fin V.rank → Bool, Oᴴ * gramAt D V τ * O = Formalism.REAL.Jm ε ∧ C * O = O * Formalism.REAL.Jm ε) : C = 1 := by
  obtain ⟨ε, h1, h2⟩ := h
  have hc := card_false_of_gram hV τ h1
  rw [h0, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
  have hJ : Formalism.REAL.Jm ε = 1 := by
    rw [Formalism.REAL.Jm, ← Matrix.diagonal_one]
    congr 1; funext a
    have := hc (Finset.mem_univ a)
    cases hε : ε a <;> simp_all
  rw [hJ, Matrix.mul_one] at h2
  obtain ⟨u, hu⟩ := isUnit_of_gram h1
  calc C = C * ((u : Matrix (Fin V.rank) (Fin V.rank) ℂ) * ↑u⁻¹) := by rw [Units.mul_inv, Matrix.mul_one]
    _ = (C * O) * ↑u⁻¹ := by rw [← hu, Matrix.mul_assoc]
    _ = 1 := by rw [h2, ← hu, Units.mul_inv]

end GlobalTheory.GridJoin

namespace GlobalTheory.GridJoin

theorem parV_counts (D : D7) (hH : HostHyp D) (τ : D.what₂.Tau) {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ D.R.m) (h3 : j ≤ D.R.m) :
    SignedHC.IsRegular (GlobalTheory.Grid.parV D i j τ) ∧ (GlobalTheory.Grid.parV D i j τ).card = GlobalTheory.Grid.rkV D i j ∧
      SignedHC.nMinus (GlobalTheory.Grid.parV D i j τ) = (D.R.m - j) / 2 := by
  obtain ⟨hr, hc⟩ := GlobalTheory.T.gridParameter_regular_card_eq_rankFormula D hH τ i j h1 h2 h3
  obtain ⟨a, b, c⟩ := dualPar_shift_counts (if Odd (i + j) then -(1 / 2) else 0) hr
  exact ⟨a, b.trans hc, c.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i j)⟩

theorem parP_counts (D : D7) (hH : HostHyp D) (τ : D.what₂.Tau) {i : ℕ} (h : i ≤ D.R.m) :
    SignedHC.IsRegular (GlobalTheory.Grid.parP D i τ) ∧ (GlobalTheory.Grid.parP D i τ).card = GlobalTheory.Grid.rkP D i ∧
      SignedHC.nMinus (GlobalTheory.Grid.parP D i τ) = (D.R.m - i + 1) / 2 :=
  GlobalTheory.T.gridParam_regular_card_minusCount D hH τ i h

theorem parXp_counts (D : D7) (hH : HostHyp D) (τ : D.what₂.Tau) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    SignedHC.IsRegular (GlobalTheory.Grid.parXp D j τ) ∧ (GlobalTheory.Grid.parXp D j τ).card = GlobalTheory.Grid.rkX D j ∧
      SignedHC.nMinus (GlobalTheory.Grid.parXp D j τ) = 0 := by
  obtain ⟨a, b, c⟩ := plus_counts ((GlobalTheory.Grid.grid D τ).weightX j)
  exact ⟨a, b.trans (GlobalTheory.T.card_weightSet_grid_eq_gridRowSpaceRank D hH τ j h1 h2), c⟩

theorem exists_weil_ordered : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts},
    HostHyp D → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R →
    ∃ W' : G'.Weil, W'.Over R ∧ W'.ψ = W.ψ ∧ W'.θ = W.θ ∧ W'.cart = W.cart ∧ W'.om = W.om ∧ W'.vac = W.vac ∧
      W'.cosVec = W.cosVec ∧ (∀ j, W'.onb (.grid 0 j) = W.onb (.grid 0 j)) ∧
      (∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → X ≠ .top 0 → ∀ τ,
        ∃ σ : Equiv.Perm (Fin (G'.V X).rank), W'.onb X τ = (W.onb X τ).submatrix id σ) ∧
      (∀ τ, ∃ σ : Equiv.Perm (Fin (G'.V (.core D.R.m)).rank),
        W'.onb (.top 0) τ = (W.onb (.core D.R.m) τ).submatrix id σ) ∧
      (∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ)
        (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧
        (W'.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W'.onb (.grid i j) τ = Formalism.REAL.Jm ε) ∧
      (∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool),
        IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧
        (W'.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W'.onb (.core i) τ = Formalism.REAL.Jm ε) ∧
      (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool),
        IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧
        (W'.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W'.onb (.top j) τ = Formalism.REAL.Jm ε) ∧
      W'.cart (.top 0) = W'.cart (.core D.R.m) ∧ W'.onb (.top 0) = W'.onb (.core D.R.m) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc hH _ G' W hW
  classical
  let Good : ∀ X : GlobalTheory.ChiGrid.Node, SPar → D.what₂.Tau → Equiv.Perm (Fin (G'.V X).rank) → Prop := fun X S τ σ =>
    ∃ (lam : Fin (G'.V X).rank → ℝ) (ε : Fin (G'.V X).rank → Bool), IsEnum S lam ε ∧
      ((W.onb X τ).submatrix id σ)ᴴ * gramAt D (G'.V X) τ * (W.onb X τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      W.cart X τ * (W.onb X τ).submatrix id σ = (W.onb X τ).submatrix id σ * Formalism.REAL.Jm ε
  have key : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → ∀ (S : SPar) τ,
      SignedHC.IsRegular S → S.card = X.rank D → SignedHC.nMinus S = X.neg D.R.m → ∃ σ, Good X S τ σ := by
    intro X hX h0 S τ hS hc hm
    have hv := G'.isV hX h0
    exact exists_perm_onb hv.sigOK τ hS (hc.trans hv.rank.symm) (by rw [hv.sig, hm]) (W.onb_is X hX τ)
  have eV : ∀ i j τ, ∃ σ, (1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m) → Good (.grid i j) (GlobalTheory.Grid.parV D i j τ) τ σ := by
    intro i j τ
    by_cases h : 1 ≤ i ∧ i ≤ D.R.m ∧ j ≤ D.R.m
    · obtain ⟨hr, hc, hm⟩ := parV_counts D hH τ h.1 h.2.1 h.2.2
      obtain ⟨σ, hσ⟩ := key (.grid i j) ⟨h.2.1, h.2.2⟩ (fun j' e => by cases e; omega) _ τ hr hc hm
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  have eP : ∀ i τ, ∃ σ, i ≤ D.R.m → Good (.core i) (GlobalTheory.Grid.parP D i τ) τ σ := by
    intro i τ
    by_cases h : i ≤ D.R.m
    · obtain ⟨hr, hc, hm⟩ := parP_counts D hH τ h
      obtain ⟨σ, hσ⟩ := key (.core i) h (fun j' e => GlobalTheory.ChiGrid.Node.noConfusion e) _ τ hr hc hm
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  have eX : ∀ j τ, ∃ σ, (1 ≤ j ∧ j ≤ D.R.m) → Good (.top j) (GlobalTheory.Grid.parXp D j τ) τ σ := by
    intro j τ
    by_cases h : 1 ≤ j ∧ j ≤ D.R.m
    · obtain ⟨hr, hc, hm⟩ := parXp_counts D hH τ h.1 h.2
      obtain ⟨σ, hσ⟩ := key (.top j) h.2 (fun j' e => GlobalTheory.ChiGrid.Node.noConfusion e) _ τ hr hc hm
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose σV hσV using eV
  choose σP hσP using eP
  choose σX hσX using eX

  have hcartP : ∀ τ, W.cart (.core D.R.m) τ = 1 := fun τ => by
    have hv := G'.isV (X := .core D.R.m) le_rfl (fun j e => GlobalTheory.ChiGrid.Node.noConfusion e)
    refine cart_eq_one hv.sigOK τ ?_ (W.onb_is _ le_rfl τ)
    rw [hv.sig]
    show (D.R.m - D.R.m + 1) / 2 = 0
    omega
  have hcart0 : ∀ τ, W.cart (.top 0) τ = 1 := fun τ => by
    have hv := G'.isV (X := .top 0) (Nat.zero_le _) (fun j e => GlobalTheory.ChiGrid.Node.noConfusion e)
    exact cart_eq_one hv.sigOK τ (by rw [hv.sig]; rfl) (W.onb_is _ (Nat.zero_le _) τ)
  let onb' : ∀ X : GlobalTheory.ChiGrid.Node, D.what₂.Tau → Matrix (Fin (G'.V X).rank) (Fin (G'.V X).rank) ℂ := fun X =>
    match X with
    | .grid 0 j => W.onb (.grid 0 j)
    | .grid (i + 1) j => fun τ => (W.onb (.grid (i + 1) j) τ).submatrix id (σV (i + 1) j τ)
    | .core i => fun τ => (W.onb (.core i) τ).submatrix id (σP i τ)
    | .top 0 => fun τ => (W.onb (.core D.R.m) τ).submatrix id (σP D.R.m τ)
    | .top (j + 1) => fun τ => (W.onb (.top (j + 1)) τ).submatrix id (σX (j + 1) τ)
  have honb : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → ∀ τ, ∃ ε : Fin (G'.V X).rank → Bool,
      (onb' X τ)ᴴ * gramAt D (G'.V X) τ * onb' X τ = Formalism.REAL.Jm ε ∧
        W.cart X τ * onb' X τ = onb' X τ * Formalism.REAL.Jm ε := by
    intro X hX τ
    rcases X with ⟨_ | i, j⟩ | i | _ | j
    · exact W.onb_is _ hX τ
    · obtain ⟨-, ε, -, h1, h2⟩ := hσV (i + 1) j τ ⟨by omega, hX.1, hX.2⟩
      exact ⟨ε, h1, h2⟩
    · obtain ⟨-, ε, -, h1, h2⟩ := hσP i τ hX
      exact ⟨ε, h1, h2⟩
    · obtain ⟨-, ε, -, h1, h2⟩ := hσP D.R.m τ le_rfl
      refine ⟨ε, h1, ?_⟩
      rw [hcartP] at h2
      rw [hcart0]
      exact h2
    · obtain ⟨-, ε, -, h1, h2⟩ := hσX (j + 1) τ ⟨by omega, hX⟩
      exact ⟨ε, h1, h2⟩
  let W' : G'.Weil := { W with onb := onb', onb_is := honb }
  refine ⟨W', ⟨hW.ψ, hW.θ, hW.cartY, hW.cartX, hW.onbY, hW.onbX, hW.omY, hW.omX⟩, rfl, rfl, rfl, rfl, rfl, rfl,
    fun j => rfl, ?_, fun τ => ⟨σP D.R.m τ, rfl⟩, ?_, ?_, ?_, ?_, funext fun τ => rfl⟩
  · intro X hX h0 h1 τ
    rcases X with ⟨_ | i, j⟩ | i | _ | j
    · exact absurd rfl (h0 j)
    · exact ⟨σV (i + 1) j τ, rfl⟩
    · exact ⟨σP i τ, rfl⟩
    · exact absurd rfl h1
    · exact ⟨σX (j + 1) τ, rfl⟩
  · intro i j h1 h2 h3 τ
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨lam, ε, hE, he, -⟩ := hσV (i + 1) j τ ⟨h1, h2, h3⟩
    exact ⟨lam, ε, hE, he⟩
  · intro i h τ
    obtain ⟨lam, ε, hE, he, -⟩ := hσP i τ h
    exact ⟨lam, ε, hE, he⟩
  · intro j h1 h2 τ
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨lam, ε, hE, he, -⟩ := hσX (j + 1) τ ⟨h1, h2⟩
    exact ⟨lam, ε, hE, he⟩
  · funext τ
    show W.cart (.top 0) τ = W.cart (.core D.R.m) τ
    rw [hcart0, hcartP]
    rfl

end GlobalTheory.GridJoin
