import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Finite

variable {F : Type} [Field F] {N : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def IsCuspLevi (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) : Prop :=
  ∀ c : Fin N → ℕ, (∃ i j, b i = b j ∧ c i ≠ c j) → ∀ x : W,
    (∀ m : Parabolic.levi F b, (m : GL (Fin N) F) ∈ FiniteGL.unipRadical F c → μ m x = x) → x = 0

def IsCuspPair (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) : Prop :=
  μ.IsIrreducible ∧ IsCuspLevi b μ

def Conj (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (b' : Fin N → ℕ) (μ' : Representation ℂ (Parabolic.levi F b') W') : Prop :=
  ∃ w : Equiv.Perm (Fin N), (∀ i j, b' (w i) = b' (w j) ↔ b i = b j) ∧ ∃ φ : W ≃ₗ[ℂ] W',
    ∀ (m : Parabolic.levi F b) (m' : Parabolic.levi F b') (x : W),
      (m' : GL (Fin N) F) = Parabolic.permGL F w * m * (Parabolic.permGL F w)⁻¹ → φ (μ m x) = μ' m' (φ x)

def HasChar (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W) (θ : Fˣ →* ℂˣ) : Prop :=
  ∃ i, (∀ j, b j = b i → j = i) ∧ ∀ m : Parabolic.levi F b,
    (∀ p q, (p ≠ i ∨ q ≠ i) → (m : GL (Fin N) F).val p q = (1 : Matrix (Fin N) (Fin N) F) p q) →
      ∀ x, μ m x = (θ (Matrix.GeneralLinearGroup.det (m : GL (Fin N) F)) : ℂ) • x

def IsCharFin (ρ : Representation ℂ (GL (Fin N) F) V) (θ : Fˣ →* ℂˣ) : Prop :=
  N = 1 ∧ ∀ g y, ρ g y = (θ (Matrix.GeneralLinearGroup.det g) : ℂ) • y

def Link (τ : Representation ℂ (GL (Fin N) F) V) (τ' : Representation ℂ (GL (Fin N) F) V') : Prop :=
  ∃ (b : Fin N → ℕ) (φ : (Parabolic.hcRes b τ).IntertwiningMap (Parabolic.hcRes b τ')), φ ≠ 0

def Occurs (b : Fin N → ℕ) (μ : Representation ℂ (Parabolic.levi F b) W)
    (τ : Representation ℂ (GL (Fin N) F) V) : Prop :=
  Parabolic.Embeds μ (Parabolic.hcRes b τ)

end Finite

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

abbrev LiftSp (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Type :=
  IndSp (part r t) ((extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)).comp
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)

def evAt (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) (g : GL (Fin (r + t)) k) :
    LiftSp t σ χW χV →ₗ[ℂ] V where
  toFun f := TensorProduct.rid ℂ V (f.1.1 g)
  map_add' f f' := map_add (TensorProduct.rid ℂ V) (f.1.1 g) (f'.1.1 g)
  map_smul' c f := map_smul (TensorProduct.rid ℂ V) c (f.1.1 g)

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

theorem evAt_apply (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g f = TensorProduct.rid ℂ V (f.1.1 g) := rfl

theorem evAt_lift (g x : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV g (liftRep t σ χW χV x f) = evAt t σ χW χV (g * x) f := rfl

theorem eq_zero_of_evAt (f : LiftSp t σ χW χV) (h : ∀ g, evAt t σ χW χV g f = 0) : f = 0 := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hg := h g
  rw [evAt_apply] at hg
  exact (LinearEquiv.map_eq_zero_iff _).mp hg

private theorem rid_extTensor_twist_detRep_eq_smul (g : GL (Fin r) k × GL (Fin t) k) (x : V ⊗[ℂ] ℂ) :
    TensorProduct.rid ℂ V (extTensor (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW) g x) =
      ((detChar (Fin r) (χW * χV⁻¹) g.1 * detChar (Fin t) χW g.2 : ℂˣ) : ℂ) •
        σ g.1 (TensorProduct.rid ℂ V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    simp only [extTensor_tmul, twist_apply, detRep, ofChar_apply, TensorProduct.rid_tmul, map_smul,
      Units.val_mul, mul_smul]
    simp only [smul_smul]
    congr 1
    ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem evAt_parab (p : parab k (part r t)) (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV (p * g) f =
      ((deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (part r t) p) *
        detChar (Fin r) (χW * χV⁻¹) (leviProj k (part r t) p false) *
        detChar (Fin t) χW (leviProj k (part r t) p true) : ℂˣ) : ℂ) •
        σ (leviProj k (part r t) p false) (evAt t σ χW χV g f) := by
  rw [evAt_apply, evAt_apply, parInd_law, map_smul]
  erw [rid_extTensor_twist_detRep_eq_smul]
  rw [← mul_smul, mul_assoc, Units.val_mul (deltaHalf k _ _)]
  rfl

theorem evAt_parab_ne_zero (p : parab k (part r t)) (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV)
    (h : evAt t σ χW χV (p * g) f ≠ 0) : evAt t σ χW χV g f ≠ 0 := by
  intro hg
  apply h
  rw [evAt_parab, hg, map_zero, smul_zero]

private theorem valuation_det_incl_eq_one {n : ℕ} (a : GL (Fin n) 𝒪[k]) :
    valuation k ((Matrix.GeneralLinearGroup.det (incl k n a) : kˣ) : k) = 1 := by
  rw [show incl k n a = Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) a from rfl,
    Matrix.GeneralLinearGroup.map_det]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  exact (Valuation.integer.integers _).one_of_isUnit (Units.isUnit _)

theorem detChar_incl {n : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) (a : GL (Fin n) 𝒪[k]) :
    detChar (Fin n) χ (incl k n a) = 1 := by
  rw [detChar_apply]
  exact h _ (valuation_det_incl_eq_one a)

theorem evAt_parab_int (hu : IsUnram (χW * χV⁻¹)) (p : GL (Fin (r + t)) k) (a : GL (Fin r) 𝒪[k])
    (d : GL (Fin t) 𝒪[k])
    (ha : ∀ i j, p.val (Fin.castAdd t i) (Fin.castAdd t j) = (incl k r a).val i j)
    (hd : ∀ i j, p.val (Fin.natAdd r i) (Fin.natAdd r j) = (incl k t d).val i j)
    (hc : ∀ i j, p.val (Fin.natAdd r i) (Fin.castAdd t j) = 0)
    (g : GL (Fin (r + t)) k) (f : LiftSp t σ χW χV) :
    evAt t σ χW χV (p * g) f =
      (detChar (Fin t) χW (incl k t d) : ℂ) • σ (incl k r a) (evAt t σ χW χV g f) := by
  have hp : p ∈ parab k (part r t) := by
    rw [mem_parab_two]
    intro j i
    exact hc j i
  have h1 := evAt_parab (σ := σ) (χW := χW) (χV := χV) ⟨p, hp⟩ g f
  have hL0 : leviProj k (part r t) ⟨p, hp⟩ false = incl k r a := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [leviProj_apply]
    exact ha i j
  have hL1 : leviProj k (part r t) ⟨p, hp⟩ true = incl k t d := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [leviProj_apply]
    exact hd i j
  have hδ : deltaHalf k (Two (Fin r) (Fin t)) (leviProj k (part r t) ⟨p, hp⟩) = 1 := by
    rw [deltaHalf_apply]
    apply Finset.prod_eq_one
    intro x _
    apply isUnram_absPow
    cases x
    · rw [hL0]
      exact valuation_det_incl_eq_one a
    · rw [hL1]
      exact valuation_det_incl_eq_one d
  rw [show p * g = ((⟨p, hp⟩ : parab k (part r t)) : GL (Fin (r + t)) k) * g from rfl, h1, hδ, hL0, hL1,
    detChar_incl hu a]
  simp only [one_mul]

def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

theorem red_surjective (n : ℕ) : Function.Surjective (red k n) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j =>
    Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪[k])) (g.val i j)
  have hM : M.map (IsLocalRing.residue 𝒪[k]) = g.val := by
    ext i j
    exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _
  have hdet : IsUnit M.det := by
    apply IsUnit.of_map (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact Matrix.isUnits_det_units g
  refine ⟨((Matrix.isUnit_iff_isUnit_det M).mpr hdet).unit, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [red_val]
  exact Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])) _

theorem mem_fixed_KOne {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {v : V} :
    v ∈ fixed π (KOne k (Fin n)) ↔ ∀ a : GL (Fin n) 𝒪[k], red k n a = 1 → π (incl k n a) v = v := by
  rw [GlobalTheory.Parabolic.mem_fixed]
  constructor
  · intro hv a ha
    exact hv _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem mem_fixed_KO {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {v : V} :
    v ∈ fixed π (KO k (Fin n)) ↔ ∀ a : GL (Fin n) 𝒪[k], π (incl k n a) v = v := by
  rw [GlobalTheory.Parabolic.mem_fixed]
  constructor
  · intro hv a
    exact hv _ ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    exact h a

def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)

theorem nice_one : Nice r t 1 ∅ := by
  refine ⟨fun i _ => rfl, fun i hi => ?_, fun _ => rfl⟩
  simp at hi

end Local

end GlobalTheory.TypeDim
