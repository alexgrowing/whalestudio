import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeBelowComplexEmbeddingLabelIsMaximalCardStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegersApproximatingRootOfUnityTwistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelDirectionsIntegralBasisUnramifiedPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusActsOnTypeAtValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralLogHomDiagonalOfLimitStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section Abstract

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d d' : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
  {U : Matrix (Fin d) κ C} {L : Matrix κ (Fin d) C}

theorem cut_diagonal (hLU : L * U = 1) {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) :
    L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j = Matrix.diagonal fun b => t (j b) := by
  have h : L * (U * Matrix.diagonal t * L) * U = Matrix.diagonal t := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hLU, Matrix.one_mul, Matrix.mul_assoc, hLU, Matrix.mul_one]
  have h2 : L.submatrix j id * (U * Matrix.diagonal t * L) * U.submatrix id j =
      (L * (U * Matrix.diagonal t * L) * U).submatrix j j := by
    ext a b; simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [h2, h, Matrix.submatrix_diagonal _ _ hj]; rfl

theorem proj_eq {j : Fin d' → κ} (hj : Function.Injective j) (t : κ → C) (h1 : ∀ b, t (j b) = 1)
    (h0 : ∀ ℓ, (¬ ∃ b, j b = ℓ) → t ℓ = 0) :
    U.submatrix id j * L.submatrix j id = U * Matrix.diagonal t * L := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_of_injOn j hj.injOn (fun _ _ => by simp) (fun ℓ _ hℓ => ?_) fun b' _ => by rw [h1, mul_one]
  rw [h0 ℓ (by simpa using hℓ), mul_zero, zero_mul]

theorem diagonal_mulVec (hLU : L * U = 1) (t : κ → C) (ℓ : κ) :
    (U * Matrix.diagonal t * L).mulVec (fun e => U e ℓ) = t ℓ • fun e => U e ℓ := by
  have h : U * Matrix.diagonal t * L * U = U * Matrix.diagonal t := by rw [Matrix.mul_assoc, hLU, Matrix.mul_one]
  funext e
  have := congrFun (congrFun h e) ℓ
  rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
  simpa [Matrix.mulVec, dotProduct, mul_comm] using this

theorem coord_mulVec (hLU : L * U = 1) (j : Fin d' → κ) (ℓ : κ) (b : Fin d') :
    (L.submatrix j id).mulVec (fun e => U e ℓ) b = if j b = ℓ then 1 else 0 := by
  have := congrFun (congrFun hLU (j b)) ℓ
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem intSpan_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (u : β → Fin d → C) :
    intSpan v (fun a => u (e a)) = intSpan v u := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e.symm k), fun k => ha _, by rw [← e.sum_comp]; simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fun k => a (e k), fun k => ha _, by rw [← e.sum_comp]⟩

theorem nonempty_muAction (G : LogFGL v d) (p h : ℕ) (ty : Fin d → ZMod h)
    (hz : ∀ z : C, z ^ (p ^ h - 1) = 1 → ∃ φ, IsIntHom G G φ (Matrix.diagonal fun b => z ^ p ^ (ty b).val)) :
    Nonempty (MuAction G p h ty) := by
  classical
  choose φ hφ using hz
  refine ⟨⟨fun z => if hz : z ^ (p ^ h - 1) = 1 then φ z hz else 0, fun z hz a => ?_, fun z a => ?_, fun z hz a => ?_⟩⟩
  · rw [dif_pos hz]; exact (hφ z hz).2.1 a
  · split_ifs with hz
    · exact (hφ z hz).1 a
    · simp
  · rw [dif_pos hz, (hφ z hz).2.2 a]
    simp [Matrix.diagonal_apply, ite_smul]

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} [Fact p.Prime]

theorem exists_orbit (X : ValExt T p) (hp : UnramIn E p) (τ : E →+* ℂ) :
    ∃ h : ℕ, 0 < h ∧ Nat.card (𝓞 E ⧸ primeBelow io X τ) = p ^ h ∧ ∃ lab : ZMod h → (E →+* ℂ), IsOrbit io X τ lab ∧
      (∀ s a, X.v (embX io X (lab s) a - embX io X τ a ^ p ^ s.val) < 1) ∧
      ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∃ a₀ : 𝓞 E, X.v (embX io X τ a₀ - z) < 1 := by
  obtain ⟨-, h, h0, hc⟩ := GlobalTheory.T.primeBelowComplexEmbeddingLabel_isMaximal_card E H l c p T io X τ
  haveI := charP_residueField_of_irreducible X
  obtain ⟨hon, F, Fp, Fs, Fi, Fk⟩ := GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist (𝓞 E) _ p (red io X τ) h h0 (by rw [← primeBelow_eq_ker]; exact hc)
  obtain ⟨hi, hs⟩ := GlobalTheory.T.embeddingReducedResidueField_bijective_unramified E H l c p T io X hp
  choose lab hlab using fun s => hs (F s)
  refine ⟨h, h0, hc, lab, ⟨hi ?_, fun s a => ?_, fun s s' e => Fi ?_, fun σ => ?_⟩, fun s a => ?_, fun z hz => ?_⟩
  · rw [hlab]; ext a; rw [Fp]; simp
  · rw [← red_eq_pow_iff, hlab, hlab, Fs]
  · rw [← hlab, ← hlab, e]
  · rw [primeBelow_eq_ker, primeBelow_eq_ker, Fk]
    exact exists_congr fun s => by rw [← hlab, hi.eq_iff]
  · rw [← red_eq_pow_iff, hlab, Fp]
  · have hq : p ^ h - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow h0.ne' (Fact.out : p.Prime).one_lt)
    obtain ⟨z', hz'⟩ := X.ints.exists_of_le_one
      ((isIntV_iff X z).1 (le_of_eq (v_eq_zero_of_pow_eq_one hq hz).symm))
    have h1 : z' ^ p ^ h = z' := X.ints.hom_inj (by
      rw [map_pow, hz', ← Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_sub_ne_zero hq)), pow_succ, hz, one_mul])
    obtain ⟨a, ha⟩ := hon (residue X.O z') (by rw [← map_pow, h1])
    refine ⟨a, ?_⟩
    rw [← hz', ← algebraMap_embO, ← residue_eq_iff_v]
    exact ha

variable [StarRing (𝓞 E)] {y : IntFr Xo c T io} (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p)

theorem exists_hom_of_approx [DecidableEq (Lt1 Dw)] {L : Matrix (Lt1 Dw) (Fin (chD Ch.ch)) X.C}
    (hL : ∀ a b, IsIntV (vX_vp X) (L a b)) (hUL : (Matrix.of fun e ℓ => lieVec Ch X ℓ e) * L = 1)
    (t : (E →+* ℂ) → X.C) (ht : ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ, (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t σ)) :
    ∃ φ, IsIntHom (fgl Ch X) (fgl Ch X) φ
      ((Matrix.of fun e ℓ => lieVec Ch X ℓ e) * Matrix.diagonal (fun ℓ : Lt1 Dw => t ℓ.1) * L) := by
  refine GlobalTheory.T.isIntegralLogHom_diagonal_of_limit X.C (vX_vp X) _ (fgl Ch X) (Lt1 Dw) _ L (fun e ℓ => isIntV_jX X _) hL hUL _ fun r => ?_
  obtain ⟨a, ha⟩ := ht r
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integers_act_integralChart_eigenDirections E H Dw l Xo c p T io X y Ch a
  exact ⟨fun ℓ => embX io X ℓ.1 a, _, _, h1, h2, fun ℓ => ha ℓ.1⟩

theorem typedPartAt (hp : UnramIn E p) (τ : E →+* ℂ) : TypedPartAt Ch X τ := by
  classical
  obtain ⟨h, h0, hc, lab, horb, hpow, hroot⟩ := exists_orbit (io := io) X hp τ
  haveI : NeZero h := ⟨h0.ne'⟩
  obtain ⟨L, hL, hLU, hUL⟩ := GlobalTheory.T.label_directions_integral_basis_unramified_prime E H Dw l Xo c p T io X y Ch hp
  set U : Matrix (Fin (chD Ch.ch)) (Lt1 Dw) X.C := Matrix.of fun e ℓ => lieVec Ch X ℓ e with hU
  obtain ⟨-, -, hinj, hker⟩ := id horb

  let t : X.C → (E →+* ℂ) → X.C := fun z => Function.extend lab (fun s => z ^ p ^ s.val) 0
  have ht1 : ∀ z s, t z (lab s) = z ^ p ^ s.val := fun z s => hinj.extend_apply _ _ s
  have ht0 : ∀ z σ, (¬ ∃ s, lab s = σ) → t z σ = 0 := fun z σ hσ => Function.extend_apply' _ _ σ hσ
  have happ : ∀ z : X.C, z ^ (p ^ h - 1) = 1 → ∀ r : ℝ, ∃ a : 𝓞 E, ∀ σ,
      (r : WithTop ℝ) ≤ vX_vp X (embX io X σ a - t z σ) := by
    intro z hz r
    obtain ⟨a, h1, h2⟩ := GlobalTheory.T.exists_integers_approximating_root_of_unity_twists E H l c p T io X τ h h0 lab hpow z hz (hroot z hz) r
    refine ⟨a, fun σ => ?_⟩
    by_cases hσ : ∃ s, lab s = σ
    · obtain ⟨s, rfl⟩ := hσ
      rw [ht1]; exact h1 s
    · rw [ht0 z σ hσ, sub_zero]; exact h2 σ fun e => hσ ((hker σ).1 e)

  let K := Σ s : ZMod h, Fin (Dw.mult (lab s))
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let j₀ : K → Lt1 Dw := fun k => ⟨lab k.1, k.2⟩
  have hj₀ : Function.Injective j₀ := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ hk
    obtain rfl : s = s' := hinj (congrArg Sigma.fst hk)
    obtain rfl : k = k' := eq_of_heq (Sigma.mk.inj hk).2
    rfl
  let j : Fin (Fintype.card K) → Lt1 Dw := fun b => j₀ (e b)
  have hj : Function.Injective j := hj₀.comp e.injective
  have hjr : ∀ ℓ : Lt1 Dw, (∃ s, lab s = ℓ.1) → ∃ b, j b = ℓ := by
    rintro ⟨σ, k⟩ ⟨s, rfl⟩
    exact ⟨e.symm ⟨s, k⟩, congrArg j₀ (e.apply_symm_apply _)⟩
  have hIP : U.submatrix id j * L.submatrix j id = U * Matrix.diagonal (fun ℓ : Lt1 Dw => t 1 ℓ.1) * L :=
    proj_eq hj _ (fun b => by rw [show (j b).1 = lab (e b).1 from rfl, ht1, one_pow])
      fun ℓ hℓ => ht0 1 _ fun hs => hℓ (hjr ℓ hs)
  have hPI : L.submatrix j id * U.submatrix id j = 1 := by
    have := cut_diagonal hLU hj (fun _ => 1)
    rwa [Matrix.diagonal_one, Matrix.mul_one, hUL, Matrix.mul_one, Matrix.diagonal_one] at this
  have hco : (1 : Matrix _ _ X.C) - U.submatrix id j * L.submatrix j id =
      U * Matrix.diagonal (fun ℓ : Lt1 Dw => 1 - t 1 ℓ.1) * L := by
    rw [hIP, ← Matrix.diagonal_sub, Matrix.diagonal_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUL]
  obtain ⟨G', ⟨ι', hι⟩, ⟨π', hπ⟩⟩ := GlobalTheory.T.logarithmic_group_law_split_by_idempotent X.C (vX_vp X) _ _ (fgl Ch X) (U.submatrix id j) (L.submatrix j id)
    (fun a b => isIntV_jX X _) (fun a b => hL _ _) hPI
    (by rw [hIP]; exact exists_hom_of_approx Ch X hL hUL (t 1) (happ 1 (one_pow _)))
    (by
      rw [hco]
      refine exists_hom_of_approx Ch X hL hUL (fun σ => 1 - t 1 σ) fun r => ?_
      obtain ⟨a, ha⟩ := happ 1 (one_pow _) r
      refine ⟨1 - a, fun σ => ?_⟩
      rw [map_sub (embX io X σ), map_one, sub_sub_sub_cancel_left, AddValuation.map_sub_swap]
      exact ha σ)
  have hfix : ∀ ℓ : Lt1 Dw, (U.submatrix id j * L.submatrix j id).mulVec (lieVec Ch X ℓ) =
      t 1 ℓ.1 • lieVec Ch X ℓ := fun ℓ => by
    rw [hIP]; exact diagonal_mulVec hLU _ ℓ
  have hco' : ∀ (ℓ : Lt1 Dw) b, (L.submatrix j id).mulVec (lieVec Ch X ℓ) b = if j b = ℓ then 1 else 0 :=
    fun ℓ b => coord_mulVec hLU j ℓ b
  let q : ∀ s, {b : Fin (Fintype.card K) // (e b).1 = s} ≃ Fin (Dw.mult (lab s)) := fun s =>
    (e.subtypeEquiv (q := fun k : K => k.1 = s) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype s)
  have hq : ∀ s b, j b.1 = ⟨lab s, q s b⟩ := by
    rintro s ⟨b, rfl⟩; rfl
  refine ⟨h, h0, hc, lab, horb, _, G', fun b => (e b).1, U.submatrix id j, L.submatrix j id,
    ⟨⟨ι', hι⟩, ⟨π', hπ⟩, hPI, fun ℓ => ⟨fun hℓ => ?_, fun hℓ => ?_⟩⟩, nonempty_muAction _ _ _ _ fun z hz => ?_,
    fun s => ?_, fun s => ?_, fun s f hf => ⟨⟨fun a b => ?_, ?_⟩, fun a b hb => ?_, fun k => le_antisymm ?_ ?_⟩⟩
  · obtain ⟨s, hs⟩ := (hker _).1 hℓ
    rw [hfix, ← hs, ht1, one_pow, one_smul]
  · rw [hfix, ht0 1 _ fun hs => hℓ ((hker _).2 hs), zero_smul]
  · obtain ⟨φ, hφ⟩ := exists_hom_of_approx Ch X hL hUL (t z) (happ z hz)
    have := isIntHom_comp hι (isIntHom_comp hφ hπ)
    rw [cut_diagonal hLU hj] at this
    exact ⟨_, by simpa only [show ∀ b, (j b).1 = lab (e b).1 from fun _ => rfl, ht1] using this⟩
  · rw [← intSpan_equiv (q s)]
    congr 1
    funext b
    rw [← hq]; rfl
  · rw [Fintype.card_congr (q s), Fintype.card_fin, Dw.rank, Nat.add_sub_cancel]
    unfold Datum.mult InPsi
    congr
  · beta_reduce; rw [frame, hco']; unfold IsIntV; split_ifs <;> simp
  · choose r hr using fun a : Fin (rk f) => hjr ⟨f.1, Fin.castLE (rk_le f) a⟩ ⟨s, hf.symm⟩
    refine ⟨r, ?_⟩
    have : (Matrix.of fun a b => (L.submatrix j id).mulVec (frame Ch X f a) (r b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, frame, hco', hr, Matrix.one_apply]
      simp [eq_comm]
    rw [this]; simp
  · rw [frame, hco', if_neg]
    intro hb'
    exact hb (hinj ((congrArg Sigma.fst hb').trans hf))
  · exact GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hπ _
  · have := GlobalTheory.T.formalGroupDetPowDepth_le_of_integralLogHom X.C _ _ _ _ k _ _ _ _ hι fun a => (L.submatrix j id).mulVec (frame Ch X f a)
    simp only [Matrix.mulVec_mulVec, frame, hfix, hf, ht1, one_pow, one_smul] at this
    exact this

theorem formalGroupTypes : FormalGroupTypes := fun E _ _ _ H _ l _ c _ _ p _ hp T io X =>
  ⟨GlobalTheory.T.frobenius_acts_on_type_at_valuation E H l c p T io X, fun _ Ch τ => typedPartAt Ch X hp τ⟩

end GlobalTheory.PrimePart
