import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.FlatColLaw

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_iota (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem iota_mul (p : Place D k) (x : k) (m : AE D) : p.ι x * m = p.ι (x * p.π m) := by
  have h2 := p.ι_π (p.ι x * m)
  rw [map_mul, p.π_ι] at h2
  rw [h2, ← mul_assoc, e_iota]

theorem xi_ne (p : Place D k) : p.xi ≠ 0 := by
  have h : p.xi * p.pr D.host.xi0⁻¹ = 1 := by
    rw [Place.xi, Place.pr, Place.pr, ← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one,
      map_one]
  exact left_ne_zero_of_mul_eq_one h

theorem map_iota_mul (p : Place D k) {a b c : ℕ} (zk : Matrix (Fin a) (Fin b) k) (x : Mx D b c) :
    (zk.map p.ι : Mx D a b) ⬝ x = (zk * x.map p.π).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, iota_mul]

theorem trace_map_iota (p : Place D k) {a : ℕ} (x : Matrix (Fin a) (Fin a) k) :
    (x.map p.ι : Mx D a a).trace = p.ι x.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem map_iota_pi (p : Place D k) {a b : ℕ} (x : Matrix (Fin a) (Fin b) k) : (x.map p.ι).map p.π = x := by
  ext i j
  exact p.π_ι _

theorem hO_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : WO S T) (a : Mx D T.rank ρ) :
    hO S T w (d.extY T a) = pairS T (w ⬝ d.jX) a := by
  rw [d.hO_coordS]
  simp only [HypDec.extY_apply, Matrix.mul_assoc, HypDec.pY_jY, HypDec.pY_j0, HypDec.pY_jX, Matrix.mul_one,
    Matrix.mul_zero, pairS, hO_eq_trace S₀, adj_zero, Matrix.zero_mul, trace_zero, add_zero]

theorem pairS_giA_adj (T : HSp D) {ρ : ℕ} (x : Mx D T.rank ρ) (z : Mx D ρ T.rank) :
    pairS T x (giA T ⬝ adj z) = (z ⬝ x).trace := by
  rw [pairS, adj_mul, adj_adj, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem psi_sympl_extY (p : Place D k) {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (hχ : p.IsChar ψ ψk)
    {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (zk : Matrix (Fin ρ) (Fin T.rank) k) (w : WO S T) :
    ψ (symplO S T w (d.extY T (giA T ⬝ adj (zk.map p.ι : Mx D ρ T.rank)))) =
      (ψk ((zk * (w ⬝ d.jX : Mx D T.rank ρ).map p.π).trace) : ℂ) := by
  rw [hχ, symplO, hO_extY, pairS_giA_adj, map_iota_mul, trace_map_iota]
  rfl

theorem isHalf_mul_left {e : AE D} {a b c : ℕ} (x : Mx D a b) {y : Mx D b c} (h : IsHalf e y) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, h l j]

theorem isHalf_mul_right {e : AE D} {a b c : ℕ} {x : Mx D a b} (y : Mx D b c) (h : IsHalf e x) : IsHalf e (x ⬝ y) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [← mul_assoc, h i l]

theorem isHalf_adj (p : Place D k) {a b : ℕ} (zk : Matrix (Fin a) (Fin b) k) :
    IsHalf (cA D p.e) (adj (zk.map p.ι : Mx D a b)) := fun i j =>
  (map_mul (cA D) p.e (p.ι (zk j i))).symm.trans (congrArg (cA D) (e_iota p _))

theorem exists_mxAt (p : Place D k) : ∃ v : GlobalTheory.FinPl.Pl D, ∀ (a b : ℕ) (x : Mx D a b), IsHalf (cA D p.e) x →
    GlobalTheory.FinPl.MxAt (· = v) x := by
  obtain ⟨_, h0, v, ε, h1, h2⟩ := p.split
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  refine ⟨v, fun a b x hx i j => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  rw [← h2, add_mul, hx i j, ← hx i j, ← mul_assoc, h0, zero_mul, zero_add]

theorem trace_mul_uni {ρ : ℕ} (M : Mx D ρ ρ) (hM : ∀ i j, j < i → M i j = 0) (u : UX D ρ) :
    (M ⬝ u.1.1).trace = M.trace := by
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu := u.2
  rw [Matrix.diag_apply, Matrix.diag_apply, GlobalTheory.UniIndexPrime.diag_mul hM (fun a b h => (hu a b).1 h), (hu i i).2, mul_one]

theorem col_mul {K m l o o' : Type} [Field K] [Fintype l] (M : Matrix m l K) (E : Matrix l o K) (F : Matrix l o' K) (j : o)
    (j' : o') {κ : K} (hκ : κ ≠ 0) (h : ∀ x, F x j' = κ * E x j) (r : m) : (M * E) r j = κ⁻¹ * (M * F) r j' := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by field_simp

theorem row_mul {K m l o : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l o K) (i : Fin ρ) (j : o) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X) i j =
      if i = i₀ then a * (G * X) r j else 0 := by
  by_cases h : i = i₀ <;> simp [Matrix.mul_apply, h, Finset.mul_sum, mul_assoc]

theorem trace_row_mul {K m l : Type} [Field K] [Fintype l] {ρ : ℕ} (i₀ : Fin ρ) (a : K) (G : Matrix m l K) (r : m)
    (X : Matrix l (Fin ρ) K) :
    ((Matrix.of fun i' β => if i' = i₀ then a * G r β else 0 : Matrix (Fin ρ) l K) * X).trace = a * (G * X) r i₀ := by
  simp only [Matrix.trace, Matrix.diag_apply, row_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem law_dual_col : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D _ hFL _ k _ _ _ _ _ _ p ν _ ψ ψk hχ ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW _ hbes hjac Tm hTm r q hq b Φ Φ' hΦ'
  obtain ⟨i, rfl, hi, hfree⟩ := hq
  have hc : c = 2 * ρ := hjac.1
  have hκ : ∀ m : ℕ, s * p.xi ^ m ≠ 0 := fun m => mul_ne_zero hs (pow_ne_zero _ (xi_ne p))
  let i₀ : Fin ρ := ⟨i.val, hi⟩
  let zk : Matrix (Fin ρ) (Fin J.W.rank) k :=
    Matrix.of fun i' β => if i' = i₀ then b * (s * p.xi ^ (ρ - i.val)) * FW.γ r β else 0
  let a : Mx D J.W.rank ρ := giA J.W ⬝ adj (zk.map p.ι : Mx D ρ J.W.rank)
  have ha : IsHalf (cA D p.e) a := isHalf_mul_left _ (isHalf_adj p zk)
  have hy : IsHalf (cA D p.e) (B.d.extY J.W a) := isHalf_mul_right _ ha
  have hW : ∀ j : Fin ρ, (FW.γ * J.d.jX.map p.π) r j = (s * p.xi ^ (ρ - j.val))⁻¹ *
      (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inr ⟨j.val, by omega⟩) := fun j => by
    rw [← FW.γβ]
    exact col_mul _ _ _ _ _ (hκ _) (hjac.2.2.1 j ⟨j.val, by omega⟩ rfl) r
  have hB : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.extY J.W a)) = (ψk (b * t r (Sum.inr i)) : ℂ) := fun t => by
    rw [psi_sympl_extY p hχ, trace_row_mul, Place.up, map_iota_mul, map_iota_pi, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, FW.γβ, Matrix.one_mul,
      col_mul _ _ FV.β i₀ (Sum.inr i) (hκ _) (hbes.2.2.1 i₀ i rfl), Matrix.mul_assoc, FV.γβ, Matrix.mul_one, mul_assoc,
      mul_inv_cancel_left₀ (hκ _)]
  have hD : ψ (symplO B.V J.W (B.d.extX J.W (xZero J.d)) (B.d.extY J.W a)) =
      (ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) := by
    rw [psi_sympl_extY p hχ, trace_row_mul, HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, xZero, hW,
      mul_assoc, mul_inv_cancel_left₀ (hκ _)]
    congr 3
    rcases r with r | r
    · simp [basePt]
    · simp [basePt, Matrix.one_apply, Fin.ext_iff, i₀]
  have hU : GlobalTheory.FinPl.UInv J.W (xZero J.d) a := fun u => by
    rw [pairS_giA_adj, pairS_giA_adj, ← Matrix.mul_assoc]
    refine trace_mul_uni _ (fun i' j hj => ?_) u
    rw [map_iota_mul, Matrix.map_apply, row_mul]
    split_ifs with h
    · subst h
      rw [xZero, hW, Matrix.one_apply_ne, mul_zero, mul_zero, map_zero]
      rintro rfl
      exact hfree hj
    · exact map_zero _
  obtain ⟨v, hv⟩ := exists_mxAt p
  have hlaw := ((hFL ψ (· = v)).1 ρ B J st).Heisenberg₂.dual _ (hTm.theta Φ) a (hv _ _ a ha) hU
  have hmod := hTm.modul _ hy Φ ((ψk (b * basePt c (0 : Matrix n n' k) r (Sum.inr i)) : ℂ) • Φ') fun t => by
    rw [hB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hΦ', ← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul,
      ← mul_add, add_sub_cancel]
  rw [← hmod, hD, map_smul, GlobalTheory.HandHom.flatBF_smul] at hlaw
  exact smul_right_injective _ (Circle.coe_ne_zero _) hlaw

end GlobalTheory.FlatColLaw

end
