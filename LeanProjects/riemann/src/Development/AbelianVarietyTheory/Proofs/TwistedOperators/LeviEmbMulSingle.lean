import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GodementJacquetZeta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
omit [DecidableEq n] in

theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in

theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]

open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in

theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

def NoInert (π : Representation ℂ (GL n k) V) (θ : kˣ →* ℂˣ) : Prop :=
  ∀ (c : n → ℤ) (i : n), (∀ j, c j = c i → j = i) → ∀ v : V,
    (∀ u : kˣ, valuation k (u : k) = 1 →
      π (diagT k n (Pi.mulSingle i u)) v - (θ u : ℂ) • v ∈ twKer π (unipOf k c) 1) →
    v ∈ twKer π (unipOf k c) 1

def cut (I : Finset n) : n → ℤ := fun i => if i ∈ I then 0 else 1

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

def IsLaurent (ν : Measure k) (c : GL n k → ℂ) : Prop :=
  ∀ Φ ∈ SB (Matrix n n k), ∃ (b : ℝ) (N : ℕ) (Q : Polynomial ℂ), ∀ s : ℂ, b < s.re →
    Integrable (zetaIntegrand Φ c s) (volGL ν n) ∧
    (∫ g, zetaIntegrand Φ c s g ∂(volGL ν n)) * ((resCard k : ℂ) ^ (-s)) ^ N =
      Q.eval ((resCard k : ℂ) ^ (-s))

end Local

end GlobalTheory.InertSupp
