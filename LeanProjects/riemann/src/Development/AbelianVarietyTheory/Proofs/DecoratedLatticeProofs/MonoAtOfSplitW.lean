import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionCoreProjMulCoreEqOne

noncomputable section

section General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel Matrix NumberField
open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.SplitLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MonoSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

def prE : D.host.E →+* k := p.pr.comp (incA D)

def prC : D.host.E →+* k := (p.pr.comp (cA D)).comp (incA D)

def atW {n : ℕ} (u : Fin n → k) : Fin n → AE D := fun i => p.sec (u i)

theorem rat_sec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (u : Fin n → k) :
    rat M *ᵥ (fun i => p.sec (u i)) = fun i => p.sec ((M.map (prE p) *ᵥ u) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, rat, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, sec_mul_right, mul_comm]; rfl

theorem rat_csec {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → k) :
    rat M *ᵥ (fun i => cA D (p.sec (z i))) = fun i => cA D (p.sec ((M.map (prC p) *ᵥ z) i)) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, rat, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (prC p _), show prC p (M i j) = p.pr (cA D (incA D (M i j))) from rfl, ← sec_mul_right, RingHom.map_mul, cA_cA,
    mul_comm]

theorem form_eq (S : HSp D) (a b : Fin S.rank → k) :
    ∑ i, ∑ j, a i * p.pr (cA D (incA D (S.gram i j))) * b j = a ⬝ᵥ (S.gram.map (prC p)) *ᵥ b := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, mul_assoc]
  rfl

theorem rat_mem {S S' : HSp D} {L : Lat S} {L' : Lat S'} (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E)
    (M' : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hL : IsSelfDualC S L) (hL' : IsSelfDualC S' L')
    (hadj : S'.gram * M = M'ᴴ * S.gram)
    (h : ∀ u : Fin S.rank → k, atW p u ∈ latV S L (· = p.v) → atW p (M.map (prE p) *ᵥ u) ∈ latV S' L' (· = p.v))
    (h' : ∀ u : Fin S'.rank → k, atW p u ∈ latV S' L' (· = p.v) → atW p (M'.map (prE p) *ᵥ u) ∈ latV S L (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = p.v)) : rat M *ᵥ y ∈ latV S' L' (· = p.v) := by
  have e : y = (fun i => p.sec (p.pr (y i))) + fun i => cA D (p.sec (p.pr (cA D (y i)))) := by
    funext i
    rw [Pi.add_apply, p.sec_pr, p.sec_pr, RingHom.map_mul, cA_cA, ← add_mul, (idem_iff p _).1 (latV_supp hy i)]
  rw [e] at hy ⊢
  obtain ⟨h1, h2⟩ := (decomp hL _ _).1 hy
  rw [Matrix.mulVec_add, rat_sec, rat_csec]
  refine add_mem (h _ h1) ((csec_mem_iff hL' _).2 fun x hx => ?_)
  have h3 := (csec_mem_iff hL _).1 h2 _ (h' x hx)
  have hT : (M'ᴴ).map (prC p) = (M'.map (prE p))ᵀ := by
    ext i j
    change p.pr (cA D (incA D (star (M' j i)))) = p.pr (incA D (M' j i))
    rw [FrameLat.cA_incA, star_star]
  rw [form_eq] at h3 ⊢
  rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, hadj, Matrix.map_mul, hT, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

def SplitW {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) : Prop :=
  ∀ u : Fin S.rank → k, atW p u ∈ latV S L (· = p.v) ↔ (∀ i, (d.qX.map (prE p) *ᵥ u) i ∈ 𝒪[k]) ∧
    (∀ i, (d.qY.map (prE p) *ᵥ u) i ∈ 𝒪[k]) ∧ atW p (d.q0.map (prE p) *ᵥ u) ∈ latV S₀ L₀ (· = p.v)

theorem atW_zero {n : ℕ} : atW p (0 : Fin n → k) = 0 := by
  funext i; exact map_zero p.sec

theorem colProj_adj {S : HSp D} {ρ : ℕ} (f g : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    S.gram * colProj (gᴴ * S.gram) f i = (colProj (fᴴ * S.gram) g i)ᴴ * S.gram := by
  ext a l
  have h : star ((fᴴ * S.gram) i a) = (S.gram * f) a i := by
    rw [← Matrix.conjTranspose_apply, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [colProj, Matrix.of_apply, Matrix.conjTranspose_apply, star_mul, h]
  simp only [← mul_assoc, ← Finset.sum_mul]
  simp only [mul_assoc, ← Finset.mul_sum]
  rfl

theorem colProj_map {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (x : Fin m → k) :
    (colProj q f i).map (prE p) *ᵥ x = f.map (prE p) *ᵥ Pi.single i ((q.map (prE p) *ᵥ x) i) := by
  funext l
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.of_apply, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum, mul_assoc, RingHom.map_mul]

theorem map_mulVec {l m n : ℕ} (A : Matrix (Fin l) (Fin m) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E) (x : Fin n → k) :
    A.map (prE p) *ᵥ (B.map (prE p) *ᵥ x) = (A * B).map (prE p) *ᵥ x := by
  rw [Matrix.mulVec_mulVec, Matrix.map_mul]

theorem mz {m n : ℕ} : (0 : Matrix (Fin m) (Fin n) D.host.E).map (prE p) = 0 := Matrix.map_zero _ (map_zero _)

theorem mo {m : ℕ} : (1 : Matrix (Fin m) (Fin m) D.host.E).map (prE p) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem single_int {ρ : ℕ} (i : Fin ρ) {a : k} (ha : a ∈ 𝒪[k]) (j : Fin ρ) : (Pi.single i a : Fin ρ → k) j ∈ 𝒪[k] := by
  by_cases h : j = i
  · subst h; rw [Pi.single_eq_same]; exact ha
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem monoAt_of_splitW {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} (hL : IsSelfDualC S L)
    (hL₀ : IsSelfDualC S₀ L₀) (H : SplitW p d L L₀) : MonoAt d L L₀ p.v := by
  have hX : ∀ i u, atW p u ∈ latV S L (· = p.v) → atW p ((colProj d.qX d.e i).map (prE p) *ᵥ u) ∈ latV S L (· = p.v) := by
    intro i u hu
    rw [colProj_map, H, map_mulVec, map_mulVec, map_mulVec, SeeSaw.SplitLat.qX_e, SeeSaw.SplitLat.qY_e, SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, mo, mz, mz, Matrix.one_mulVec,
      Matrix.zero_mulVec, Matrix.zero_mulVec, atW_zero]
    exact ⟨single_int i (((H u).1 hu).1 i), fun _ => zero_mem _, zero_mem _⟩
  have hY : ∀ i u, atW p u ∈ latV S L (· = p.v) → atW p ((colProj d.qY d.e' i).map (prE p) *ᵥ u) ∈ latV S L (· = p.v) := by
    intro i u hu
    rw [colProj_map, H, map_mulVec, map_mulVec, map_mulVec, SeeSaw.SplitLat.qX_e', SeeSaw.SplitLat.qY_e', SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero, mo, mz, mz, Matrix.one_mulVec,
      Matrix.zero_mulVec, Matrix.zero_mulVec, atW_zero]
    exact ⟨fun _ => zero_mem _, single_int i (((H u).1 hu).2.1 i), zero_mem _⟩
  have hq : ∀ u, atW p u ∈ latV S L (· = p.v) → atW p (d.q0.map (prE p) *ᵥ u) ∈ latV S₀ L₀ (· = p.v) :=
    fun u hu => ((H u).1 hu).2.2
  have hi : ∀ u, atW p u ∈ latV S₀ L₀ (· = p.v) → atW p (d.i₀.map (prE p) *ᵥ u) ∈ latV S L (· = p.v) := by
    intro u hu
    rw [H, map_mulVec, map_mulVec, map_mulVec, SeeSaw.SplitLat.qX_i₀, SeeSaw.SplitLat.qY_i₀, SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one, mo, mz, Matrix.one_mulVec, Matrix.zero_mulVec]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _, hu⟩
  have a1 : S₀.gram * d.q0 = d.i₀ᴴ * S.gram := Matrix.mul_nonsing_inv_cancel_left _ _ (GlobalTheory.LatVac.gram_det_isUnit S₀)
  have a2 : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    have := congrArg Matrix.conjTranspose a1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      gram_conjTranspose] at this
    exact this.symm
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mem p _ _ hL hL (colProj_adj d.e d.e' i) (hX i) (hY i) hy
    · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mem p _ _ hL hL (colProj_adj d.e' d.e i) (hY i) (hX i) hy
    · exact rat_mem p d.q0 d.i₀ hL hL₀ a1 hq hi hy
  · rintro ⟨h1, h3, h2⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mem p d.i₀ d.q0 hL₀ hL a2 hi hq h2

theorem unit_mul_int {a x : k} (ha : valuation k a = 1) : a * x ∈ 𝒪[k] ↔ x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, ha, one_mul]

theorem splitW_of_frame {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {n : Type} [Fintype n]
    [DecidableEq n] (F : GlobalTheory.LocMod.Frame k S.rank (n ⊕ Fin (2 * ρ + 1))) (F₀ : GlobalTheory.LocMod.Frame k S₀.rank (n ⊕ Unit))
    (lam mu : Fin ρ → k) (hlam : ∀ i, valuation k (lam i) = 1) (hmu : ∀ i, valuation k (mu i) = 1)
    (c1 : ∀ r a, F.β r (Sum.inl a) = (d.i₀.map (prE p) * F₀.β) r (Sum.inl a))
    (c2 : ∀ j : Fin (2 * ρ + 1), j.val = ρ → ∀ r, F.β r (Sum.inr j) = (d.i₀.map (prE p) * F₀.β) r (Sum.inr ()))
    (c3 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val → ∀ r, F.β r (Sum.inr j) = lam i * prE p (d.e r i))
    (c4 : ∀ (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ → ∀ r, F.β r (Sum.inr j) = mu i * prE p (d.e' r i))
    (hF : GlobalTheory.SeeSaw.IntIn p S F L) (hF₀ : GlobalTheory.SeeSaw.IntIn p S₀ F₀ L₀) : SplitW p d L L₀ := by
  have tri : ∀ j : Fin (2 * ρ + 1), (∃ i : Fin ρ, j.val = i.val) ∨ j.val = ρ ∨ ∃ i : Fin ρ, j.val + i.val = 2 * ρ := by
    intro j
    have := j.2
    rcases lt_trichotomy j.val ρ with h | h | h
    · exact Or.inl ⟨⟨j.val, h⟩, rfl⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨2 * ρ - j.val, by omega⟩, by simp only; omega⟩)
  have k1 : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin S.rank) D.host.E) t a,
      (Q.map (prE p) * F.β) t (Sum.inl a) = ((Q * d.i₀).map (prE p) * F₀.β) t (Sum.inl a) := by
    intro m Q t a
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    simp only [c1]
  have k2 : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin S.rank) D.host.E) t (j : Fin (2 * ρ + 1)), j.val = ρ →
      (Q.map (prE p) * F.β) t (Sum.inr j) = ((Q * d.i₀).map (prE p) * F₀.β) t (Sum.inr ()) := by
    intro m Q t j hj
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    simp only [c2 j hj]
  have k3 : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin S.rank) D.host.E) t (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val = i.val →
      (Q.map (prE p) * F.β) t (Sum.inr j) = lam i * (Q * d.e).map (prE p) t i := by
    intro m Q t i j hj
    rw [Matrix.map_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    simp only [c3 i j hj, Matrix.map_apply, mul_left_comm]
  have k4 : ∀ {m : ℕ} (Q : Matrix (Fin m) (Fin S.rank) D.host.E) t (i : Fin ρ) (j : Fin (2 * ρ + 1)), j.val + i.val = 2 * ρ →
      (Q.map (prE p) * F.β) t (Sum.inr j) = mu i * (Q * d.e').map (prE p) t i := by
    intro m Q t i j hj
    rw [Matrix.map_mul, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    simp only [c4 i j hj, Matrix.map_apply, mul_left_comm]
  intro u
  obtain ⟨c, rfl⟩ : ∃ c, u = F.β *ᵥ c := ⟨F.γ *ᵥ u, by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]⟩
  have hX : ∀ t : Fin ρ, (d.qX.map (prE p) *ᵥ (F.β *ᵥ c)) t = lam t * c (Sum.inr ⟨t.val, by omega⟩) := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Sum.inr ⟨t.val, by omega⟩),
      k3 _ t t _ rfl, SeeSaw.SplitLat.qX_e, mo, Matrix.one_apply_eq, mul_one]
    · rintro (a | j) _ hne
      · rw [k1, SeeSaw.SplitLat.qX_i₀, mz, Matrix.zero_mul, Matrix.zero_apply, zero_mul]
      · rcases tri j with ⟨i, h⟩ | h | ⟨i, h⟩
        · rw [k3 _ t i j h, SeeSaw.SplitLat.qX_e, mo, Matrix.one_apply_ne, mul_zero, zero_mul]
          rintro rfl
          exact hne (congrArg Sum.inr (Fin.ext h))
        · rw [k2 _ t j h, SeeSaw.SplitLat.qX_i₀, mz, Matrix.zero_mul, Matrix.zero_apply, zero_mul]
        · rw [k4 _ t i j h, SeeSaw.SplitLat.qX_e', mz, Matrix.zero_apply, mul_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  have hY : ∀ t : Fin ρ, (d.qY.map (prE p) *ᵥ (F.β *ᵥ c)) t = mu t * c (Sum.inr ⟨2 * ρ - t.val, by omega⟩) := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct, Finset.sum_eq_single (Sum.inr ⟨2 * ρ - t.val, by omega⟩),
      k4 _ t t _ (by simp only; omega), SeeSaw.SplitLat.qY_e', mo, Matrix.one_apply_eq, mul_one]
    · rintro (a | j) _ hne
      · rw [k1, SeeSaw.SplitLat.qY_i₀, mz, Matrix.zero_mul, Matrix.zero_apply, zero_mul]
      · rcases tri j with ⟨i, h⟩ | h | ⟨i, h⟩
        · rw [k3 _ t i j h, SeeSaw.SplitLat.qY_e, mz, Matrix.zero_apply, mul_zero, zero_mul]
        · rw [k2 _ t j h, SeeSaw.SplitLat.qY_i₀, mz, Matrix.zero_mul, Matrix.zero_apply, zero_mul]
        · rw [k4 _ t i j h, SeeSaw.SplitLat.qY_e', mo, Matrix.one_apply_ne, mul_zero, zero_mul]
          rintro rfl
          exact hne (congrArg Sum.inr (Fin.ext (by simp only; omega)))
    · exact fun h => absurd (Finset.mem_univ _) h
  have h0 : d.q0.map (prE p) *ᵥ (F.β *ᵥ c) =
      F₀.β *ᵥ Sum.elim (fun a => c (Sum.inl a)) (fun _ => c (Sum.inr ⟨ρ, by omega⟩)) := by
    funext t
    rw [Matrix.mulVec_mulVec, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, Fintype.sum_sum_type,
      Fintype.sum_sum_type, Finset.sum_eq_single (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)), k2 _ t _ rfl]
    · simp only [k1, SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one, mo, Matrix.one_mul, Sum.elim_inl, Sum.elim_inr, Finset.univ_unique, Finset.sum_singleton]
    · intro j _ hne
      rcases tri j with ⟨i, h⟩ | h | ⟨i, h⟩
      · rw [k3 _ t i j h, SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, mz, Matrix.zero_apply, mul_zero, zero_mul]
      · exact absurd (Fin.ext h) hne
      · rw [k4 _ t i j h, SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero, mz, Matrix.zero_apply, mul_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ _) h
  rw [h0]
  refine (hF c).symm.trans (Iff.trans ?_ (and_congr Iff.rfl (and_congr Iff.rfl (hF₀ _))))
  simp only [hX, hY, unit_mul_int (hlam _), unit_mul_int (hmu _)]
  constructor
  · intro h
    exact ⟨fun _ => h _, fun _ => h _, by rintro (a | a) <;> exact h _⟩
  · rintro ⟨h1, h2, h3⟩ (a | j)
    · exact h3 (Sum.inl a)
    · rcases tri j with ⟨i, h⟩ | h | ⟨i, h⟩
      · have := h1 i
        rwa [show (⟨i.val, _⟩ : Fin (2 * ρ + 1)) = j from Fin.ext h.symm] at this
      · have := h3 (Sum.inr ())
        rwa [show j = (⟨ρ, by omega⟩ : Fin (2 * ρ + 1)) from Fin.ext h]
      · have := h2 i
        rwa [show (⟨2 * ρ - i.val, _⟩ : Fin (2 * ρ + 1)) = j from Fin.ext (by simp only; omega)] at this

theorem xi_unit (hU : p.UnitAA) : valuation k (prE p D.host.xi0) = 1 := by
  obtain ⟨h1, h2⟩ := hU.1 p.e (e_mem_intAt p)
  have key : ∀ a : D.host.E, incA D a * p.e ∈ intAt D (· = p.v) → valuation k (prE p a) ≤ 1 := fun a ha => by
    rw [← Valuation.mem_integer_iff]
    refine (p.int_iff _).2 ?_
    rw [show prE p a = p.pr (incA D a) from rfl, p.sec_pr, mul_comm]
    exact ha.2
  refine le_antisymm (key _ h1) ?_
  have h3 : valuation k (prE p D.host.xi0) * valuation k (prE p D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  rw [← h3]
  exact mul_le_of_le_one_right' (key _ h2)

end GlobalTheory.MonoSplit

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
