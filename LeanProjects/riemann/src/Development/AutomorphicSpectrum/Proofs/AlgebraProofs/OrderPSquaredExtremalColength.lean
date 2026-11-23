import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import ReciprocityTheory.DualLattices.CharTableIsUnit
import ReciprocityTheory.DualLattices.IsUnitDetOfSpanEq
import ReciprocityTheory.DualLattices.FourierMapSmulLambdaWeight
import ReciprocityTheory.DualLattices.VIntCastLtOneOfDvd
import ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsAddCharactersStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TensorProductHopfOrdersStatement

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.OrdSplit

section General

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem translate_mem (AA : HopfOrder (C := C) R N) (y : N) {g : N → C} (hg : g ∈ AA.carrier) :
    (fun x => g (x + y)) ∈ AA.carrier := by
  have key : ∀ F ∈ tensorSpan R AA.carrier, (fun x => F (x, y)) ∈ AA.carrier := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hF
      obtain ⟨r, hr⟩ := AA.le_int hb y
      have h : (fun x => a x * b y) = r • a := by
        funext x
        simp [Algebra.smul_def, hr, mul_comm]
      show (fun x => a x * b y) ∈ AA.carrier
      rw [h]
      exact AA.carrier.smul_mem r ha
    | zero => exact AA.carrier.zero_mem
    | add F G _ _ hF hG => exact AA.carrier.add_mem hF hG
    | smul c F _ hF => exact AA.carrier.smul_mem c hF
  exact key _ (AA.comul g hg)

def nearZero (v : Valuation C NNReal) (AA : HopfOrder (C := C) R N) : AddSubgroup N where
  carrier := {x | ∀ g ∈ AA.carrier, v (g x - g 0) < 1}
  zero_mem' := fun g _ => by simp
  add_mem' := by
    intro x y hx hy g hg
    have h1 := hx _ (translate_mem AA y hg)
    have h2 := hy g hg
    simp only [zero_add] at h1
    have h : g (x + y) - g 0 = (g (x + y) - g y) + (g y - g 0) := by ring
    rw [h]
    exact Valuation.map_add_lt v h1 h2
  neg_mem' := by
    intro x hx g hg
    have h1 := hx _ (AA.antipode g hg)
    simpa using h1

theorem exists_sep {v : Valuation C NNReal} (hv : v.Integers R) (AA : HopfOrder (C := C) R N)
    {y : N} (hy : y ∉ nearZero v AA) : ∃ h ∈ AA.carrier, h y = 0 ∧ v (h 0) = 1 := by
  have hy' : ∃ g ∈ AA.carrier, ¬ v (g y - g 0) < 1 := by
    by_contra hcon
    push_neg at hcon
    exact hy fun g hg => hcon g hg
  obtain ⟨g, hg, hn⟩ := hy'
  obtain ⟨r, hr⟩ := AA.le_int hg y
  obtain ⟨s, hs⟩ := AA.le_int hg 0
  refine ⟨g - r • 1, AA.carrier.sub_mem hg (AA.carrier.smul_mem r AA.one_mem), ?_, ?_⟩
  · simp [Algebra.smul_def, hr]
  · have h1 : v (g y - g 0) ≤ 1 := by
      rw [← hr, ← hs, ← map_sub]
      exact hv.map_le_one _
    have h2 : v (g y - g 0) = 1 := le_antisymm h1 (not_lt.1 hn)
    have h3 : (g - r • (1 : N → C)) 0 = -(g y - g 0) := by
      simp [Algebra.smul_def, hr]
    rw [h3, Valuation.map_neg, h2]

theorem prod_mem (AA : HopfOrder (C := C) R N) {T : Type} (s : Finset T) (f : T → N → C)
    (h : ∀ i ∈ s, f i ∈ AA.carrier) : ∏ i ∈ s, f i ∈ AA.carrier := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AA.one_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact AA.mul_mem _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem indicator_mem {v : Valuation C NNReal} (hv : v.Integers R) (AA : HopfOrder (C := C) R N) :
    Set.indicator (nearZero v AA : Set N) (1 : N → C) ∈ AA.carrier := by
  classical
  set K := nearZero v AA with hK
  have hsep : ∀ y : N, ∃ h ∈ AA.carrier, y ∉ K → h y = 0 ∧ v (h 0) = 1 := by
    intro y
    by_cases hy : y ∈ K
    · exact ⟨1, AA.one_mem, fun h => absurd hy h⟩
    · obtain ⟨h, hh, h1, h2⟩ := exists_sep hv AA hy
      exact ⟨h, hh, fun _ => ⟨h1, h2⟩⟩
  choose h hmem hh using hsep
  set P : N → C := ∏ y ∈ Finset.univ.filter (· ∉ K), h y with hP
  have hPm : P ∈ AA.carrier := prod_mem AA _ _ fun y _ => hmem y
  have hP0 : ∀ y, y ∉ K → P y = 0 := by
    intro y hy
    rw [hP, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩) (hh y hy).1
  have hP1 : v (P 0) = 1 := by
    rw [hP, Finset.prod_apply, map_prod]
    exact Finset.prod_eq_one fun y hy => (hh y (Finset.mem_filter.1 hy).2).2
  have hPk : ∀ k ∈ K, v (P k) = 1 := by
    intro k hk
    have h1 : v (P k - P 0) < v (P 0) := by
      rw [hP1]
      exact hk P hPm
    have h2 : P k = (P k - P 0) + P 0 := by ring
    rw [h2, Valuation.map_add_eq_of_lt_right v h1, hP1]
  choose r hr using fun k => AA.le_int hPm k
  set F : N → C := ∏ k ∈ Finset.univ.filter (· ∈ K), (P - r k • (1 : N → C)) with hF
  have hFm : F ∈ AA.carrier := prod_mem AA _ _ fun k _ =>
    AA.carrier.sub_mem hPm (AA.carrier.smul_mem _ AA.one_mem)
  have hF0 : ∀ x ∈ K, F x = 0 := by
    intro x hx
    rw [hF, Finset.prod_apply]
    refine Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩) ?_
    simp [Algebra.smul_def, hr]
  set u : C := ∏ k ∈ Finset.univ.filter (· ∈ K), (-(P k)) with hu
  have hF1 : ∀ x, x ∉ K → F x = u := by
    intro x hx
    rw [hF, Finset.prod_apply, hu]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [Algebra.smul_def, hr, hP0 x hx]
  have huv : v u = 1 := by
    rw [hu, map_prod]
    refine Finset.prod_eq_one fun k hk => ?_
    rw [Valuation.map_neg, hPk k (Finset.mem_filter.1 hk).2]
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, map_zero] at huv
    exact zero_ne_one huv
  obtain ⟨s, hs⟩ := hv.exists_of_le_one (show v u⁻¹ ≤ 1 by rw [map_inv₀, huv, inv_one])
  have hind : Set.indicator (K : Set N) (1 : N → C) = 1 - s • F := by
    funext x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem (show x ∈ (K : Set N) from hx)]
      simp [hF0 x hx]
    · rw [Set.indicator_of_notMem (show x ∉ (K : Set N) from hx)]
      simp [hF1 x hx, Algebra.smul_def, hs, hu0]
  rw [hind]
  exact AA.carrier.sub_mem AA.one_mem (AA.carrier.smul_mem s hFm)

theorem eq_of_le_of_hasColen {v : Valuation C NNReal} (hv : v.Integers R) {X : Type} [Fintype X]
    [DecidableEq X] {L M : Submodule R (X → C)} (hLM : L ≤ M) {c : NNReal} (hc : c ≠ 0)
    (hL : HasColen R v L c) (hM : HasColen R v M c) : L = M := by
  obtain ⟨P, rfl, hP⟩ := hL
  obtain ⟨Q, rfl, hQ⟩ := hM
  have hcol : ∀ j, ∃ a : X → R, ∑ i, a i • (fun x => Q x i) = fun x => P x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (hLM (Submodule.subset_span ⟨j, rfl⟩))
  choose a ha using hcol
  let A : Matrix X X R := Matrix.of fun i j => a j i
  have e1 : P = Q * A.map (algebraMap R C) := by
    ext x j
    rw [← congrFun (ha j) x]
    simp [Matrix.mul_apply, Matrix.map_apply, Finset.sum_apply, Algebra.smul_def, mul_comm, A]
  have hdet : v (algebraMap R C A.det) = 1 := by
    have h1 : P.det = Q.det * algebraMap R C A.det := by
      rw [e1, Matrix.det_mul]
      congr 1
      exact ((algebraMap R C).map_det A).symm
    have h2 := congrArg v h1
    rw [map_mul, hP, hQ] at h2
    exact (mul_left_cancel₀ hc (by rw [_root_.mul_one]; exact h2)).symm
  have hu : IsUnit A.det := by
    refine hv.isUnit_of_one ?_ hdet
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, map_zero] at hdet
    exact zero_ne_one hdet
  have e2 : Q = P * (A⁻¹).map (algebraMap R C) := by
    rw [e1, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv A hu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine le_antisymm hLM ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h3 : (fun x => Q x j) = ∑ i, (A⁻¹ i j) • (fun x => P x i) := by
    funext x
    rw [e2]
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun x => Q x j) ∈ Submodule.span R _
  rw [h3]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem intFun_eq_span (X : Type) [Fintype X] [DecidableEq X] :
    intFun (C := C) R X = Submodule.span R (Set.range fun j x => (1 : Matrix X X C) x j) := by
  refine le_antisymm ?_ ?_
  · intro f hf
    choose r hr using hf
    have h : f = ∑ j, r j • (fun x => (1 : Matrix X X C) x j) := by
      funext x
      simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def, hr]
    rw [h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩ x
    by_cases h : x = j
    · refine ⟨1, ?_⟩
      show algebraMap R C 1 = (1 : Matrix X X C) x j
      rw [h, Matrix.one_apply_eq, map_one]
    · refine ⟨0, ?_⟩
      show algebraMap R C 0 = (1 : Matrix X X C) x j
      rw [Matrix.one_apply_ne h, map_zero]

end General

theorem charTable_det_sq {C : Type} [Field C] (p : ℕ) [Fact p.Prime] (v : Valuation C NNReal)
    (e : ZMod p ≃ AddChar (ZMod p) C) :
    v (Matrix.of fun x j : ZMod p => e j x).det ^ 2 = v (p : C) ^ p := by
  set D : Matrix (ZMod p) (ZMod p) C := Matrix.of fun x j : ZMod p => e j x with hD
  set D' : Matrix (ZMod p) (ZMod p) C := Matrix.of fun j y : ZMod p => e j (-y) with hD'
  have hmul : D' * D = (p : C) • (1 : Matrix (ZMod p) (ZMod p) C) := by
    ext i j
    simp only [hD, hD', Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have h1 : ∀ x, e i (-x) * e j x = (e j * (e i)⁻¹) x := by
      intro x
      rw [AddChar.mul_apply, AddChar.inv_apply, mul_comm]
    simp only [h1]
    by_cases hij : i = j
    · subst hij
      simp [ZMod.card]
    · have h2 : e j * (e i)⁻¹ ≠ 1 := by
        intro h
        exact hij (e.injective (mul_inv_eq_one.1 h).symm)
      rw [AddChar.sum_eq_zero_of_ne_one h2]
      simp [hij]
  have hdet : D'.det * D.det = (p : C) ^ p := by
    rw [← Matrix.det_mul, hmul, Matrix.det_smul, Matrix.det_one, _root_.mul_one, ZMod.card]
  have hperm : D' = (D.transpose).submatrix id (Equiv.neg (ZMod p)) := by
    ext j y
    simp [hD, hD']
  have hv' : v D'.det = v D.det := by
    rw [hperm, Matrix.det_permute', Matrix.det_transpose, map_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.neg (ZMod p))) with h | h <;> simp [h]
  have h3 := congrArg v hdet
  rw [map_mul, map_pow, hv'] at h3
  rw [sq]
  exact h3

section Main

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

theorem exists_hasColen_tens (p : ℕ) [Fact p.Prime] (hv : v.Integers R) (hp : v (p : C) < 1) :
    ∃ c : NNReal, HasColen R v (tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C)
      (x : ZMod p) => ψ x)) (intFun R (ZMod p))) c ∧ c ^ 2 = v (p : C) ^ (p ^ 2) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := ReciprocityTheory.PGsh.Up.U3.exists_primRoot (p := p) (C := C)
  obtain ⟨e, -, -⟩ := ReciprocityTheory.PGsh.Up.U3.exists_charEquiv hζ
  let A₁ : HopfOrder (C := C) R (ZMod p) := multOrder' v hv e
  let A₂ : HopfOrder (C := C) R (ZMod p) := constOrder
  obtain ⟨AA, hcar, -, -, -, -, hcol⟩ := GlobalTheory.T.tensor_product_hopf_orders p C v R hv hp (ZMod p) (ZMod p) A₁ A₂
  have h1 : A₁.carrier = Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C)
      (x : ZMod p) => ψ x) := by
    show Submodule.span R (Set.range fun j : ZMod p => ((e j : AddChar (ZMod p) C) : ZMod p → C)) = _
    congr 1
    ext f
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨ψ, rfl⟩
      exact ⟨e.symm ψ, by simp⟩
  have h2 : A₂.carrier = intFun R (ZMod p) := by
    refine le_antisymm A₂.le_int ?_
    rw [intFun_eq_span, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨j, ?_⟩
    funext x
    by_cases h : x = j
    · subst h
      simp
    · simp [h, Matrix.one_apply]
  have hc₁ : HasColen R v A₁.carrier (v (Matrix.of fun x j : ZMod p => e j x).det) :=
    ⟨Matrix.of fun x j : ZMod p => e j x, rfl, rfl⟩
  have hc₂ : HasColen R v A₂.carrier 1 :=
    ⟨1, by rw [h2, intFun_eq_span], by simp⟩
  refine ⟨v (Matrix.of fun x j : ZMod p => e j x).det ^ Fintype.card (ZMod p) *
    1 ^ Fintype.card (ZMod p), ?_, ?_⟩
  · have h3 := hcol _ _ hc₁ hc₂
    rw [hcar, h1, h2] at h3
    exact h3
  · rw [ZMod.card, one_pow, _root_.mul_one, ← pow_mul, mul_comm p 2, pow_mul, charTable_det_sq,
      ← pow_mul, sq]

end Main

theorem ord_split : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → Fintype.card N = p ^ 2 → ∀ AA : HopfOrder (C := C) R N, ∀ cN, HasColen R v AA.carrier cN → cN ^ 2 = v (p : C) ^ (p ^ 2) → (∃ t : N, ∃ g ∈ AA.carrier, v (g t - g 0) = 1) → ∃ e : ZMod p × ZMod p ≃+ N, AA.carrier.map (LinearMap.funLeft R C (e : ZMod p × ZMod p → N)) = tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : (ZMod p)) => ψ x)) (intFun R (ZMod p)) := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN hcard AA cN hcol hcN ⟨t, g, hg, ht⟩
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hv0 : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 hp0
  have hpp : p ^ 2 ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have hcN0 : cN ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hcN
    exact pow_ne_zero _ hv0 hcN.symm
  set K := nearZero v AA with hKdef
  have htK : t ∉ K := by
    intro h
    have h1 := h g hg
    rw [ht] at h1
    exact lt_irrefl _ h1
  have hcoset : ∀ y : N, (fun x => Set.indicator (K : Set N) (1 : N → C) (x + y)) ∈ AA.carrier :=
    fun y => translate_mem AA y (indicator_mem hv AA)
  have hKne : ∃ k ∈ K, k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hint : intFun R N ≤ AA.carrier := by
      rw [intFun_eq_span, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have h1 := hcoset (-j)
      have h2 : (fun x => Set.indicator (K : Set N) (1 : N → C) (x + -j)) =
          fun x => (1 : Matrix N N C) x j := by
        funext x
        by_cases hx : x = j
        · subst hx
          simp [K.zero_mem]
        · have hx' : x + -j ∉ (K : Set N) := by
            intro h
            exact hx (by simpa [add_neg_eq_zero] using hcon _ h)
          rw [Set.indicator_of_notMem hx', Matrix.one_apply_ne hx]
      rw [h2] at h1
      exact h1
    have heq : AA.carrier = intFun R N := le_antisymm AA.le_int hint
    obtain ⟨B, hB, hBc⟩ := hcol
    have h1 := valuation_det_eq_of_span_eq_alt hv (P := (1 : Matrix N N C)) (Q := B) (by simp)
      ((intFun_eq_span N).symm.trans (heq.symm.trans hB))
    rw [hBc, Matrix.det_one, map_one] at h1
    rw [h1, one_pow] at hcN
    exact absurd hcN.symm (pow_lt_one₀ zero_le hp hpp).ne
  obtain ⟨k, hkK, hk0⟩ := hKne
  letI : Module (ZMod p) N := AddCommGroup.zmodModule hN
  have hsm : ∀ (a : ZMod p) (x : N), x ∈ K → a • x ∈ K := by
    intro a x hx
    have h1 : a • x = a.val • x := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      exact Nat.cast_smul_eq_nsmul (ZMod p) _ _
    rw [h1]
    exact K.nsmul_mem hx _
  let f : ZMod p × ZMod p →+ N :=
    { toFun := fun z => z.1 • k + z.2 • t
      map_zero' := by simp
      map_add' := by
        intro a b
        simp only [Prod.fst_add, Prod.snd_add, add_smul]
        abel }
  have hK2 : ∀ z, f z ∈ K ↔ z.2 = 0 := by
    rintro ⟨a, b⟩
    show a • k + b • t ∈ K ↔ b = 0
    constructor
    · intro h
      by_contra hb
      have h1 : b • t ∈ K := (K.add_mem_cancel_left (hsm a k hkK)).1 h
      have h2 := hsm b⁻¹ _ h1
      rw [smul_smul, inv_mul_cancel₀ hb, one_smul] at h2
      exact htK h2
    · rintro rfl
      simpa using hsm a k hkK
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ h
    have hb : b = 0 := (hK2 (a, b)).1 (by rw [h]; exact K.zero_mem)
    subst hb
    have h1 : a • k = 0 := by simpa [f] using h
    have ha : a = 0 := by
      by_contra ha
      exact hk0 (by rw [← one_smul (ZMod p) k, ← inv_mul_cancel₀ ha, mul_smul, h1, smul_zero])
    rw [ha]
    rfl
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [ZMod.card, hcard, sq]⟩
  let e : ZMod p × ZMod p ≃+ N := AddEquiv.ofBijective f hbij
  have he : ∀ z, e z = f z := fun _ => rfl
  refine ⟨e, ?_⟩
  have hQ : AA.carrier.map (LinearMap.funLeft R C (e : ZMod p × ZMod p → N)) =
      AA.carrier.map (pbE (C := C) (R := R) e : (N → C) →ₗ[R] (ZMod p × ZMod p → C)) := rfl
  set Q := AA.carrier.map (LinearMap.funLeft R C (e : ZMod p × ZMod p → N)) with hQdef
  have hQmul : ∀ a b, a ∈ Q → b ∈ Q → a * b ∈ Q := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, AA.mul_mem a b ha hb, rfl⟩

  have hQ1 : ∀ h ∈ Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x),
      (fun z : ZMod p × ZMod p => h z.1) ∈ Q := by
    intro h hh
    have hle : Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x) ≤
        Q.comap (LinearMap.funLeft R C (Prod.fst : ZMod p × ZMod p → ZMod p)) := by
      rw [Submodule.span_le]
      rintro _ ⟨ψ, rfl⟩
      let χ : AddChar N C := ψ.compAddMonoidHom
        ((AddMonoidHom.fst (ZMod p) (ZMod p)).comp e.symm.toAddMonoidHom)
      refine ⟨fun x => χ x, GlobalTheory.T.hopf_order_contains_add_characters p C v R hv hp N AA χ, ?_⟩
      funext z
      simp [χ, LinearMap.funLeft_apply]
    exact hle hh

  have hQ2 : ∀ h ∈ intFun (C := C) R (ZMod p), (fun z : ZMod p × ZMod p => h z.2) ∈ Q := by
    intro h hh
    have hle : intFun (C := C) R (ZMod p) ≤
        Q.comap (LinearMap.funLeft R C (Prod.snd : ZMod p × ZMod p → ZMod p)) := by
      rw [intFun_eq_span, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine ⟨_, hcoset (-(f (0, b))), ?_⟩
      funext z
      have h1 : e z + -(f (0, b)) = f (z.1, z.2 - b) := by
        rw [he, ← map_neg, ← map_add]
        congr 1
        ext <;> simp [sub_eq_add_neg]
      simp only [LinearMap.funLeft_apply, h1]
      by_cases hb : z.2 = b
      · have hm : f (z.1, z.2 - b) ∈ (K : Set N) := (hK2 _).2 (sub_eq_zero.2 hb)
        rw [Set.indicator_of_mem hm, hb, Matrix.one_apply_eq]
        rfl
      · have hm : f (z.1, z.2 - b) ∉ (K : Set N) := fun hc =>
          hb (sub_eq_zero.1 ((hK2 _).1 hc))
        rw [Set.indicator_of_notMem hm, Matrix.one_apply_ne hb]
    exact hle hh
  have hle : tens (Submodule.span R (Set.range fun (ψ : AddChar (ZMod p) C) (x : ZMod p) => ψ x))
      (intFun R (ZMod p)) ≤ Q := by
    rw [tens, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hQmul _ _ (hQ1 a ha) (hQ2 b hb)
  obtain ⟨c, hc, hc2⟩ := exists_hasColen_tens (R := R) p hv hp
  have hcc : c = cN := (pow_left_inj₀ zero_le zero_le two_ne_zero).1 (hc2.trans hcN.symm)
  subst hcc
  exact (eq_of_le_of_hasColen hv hle hcN0 hc (hQ ▸ hasColen_map v e _ _ hcol)).symm

end GlobalTheory.CompanionTheory.Ar.GR.OrdSplit
