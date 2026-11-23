import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.JetRangeLevelFactor
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinorsDisjointColumnsHarmonic

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaClaimsCompare

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor

section Minors

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)

def minor (R : Type) [CommRing R] (σ : T) (s : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  (Matrix.of fun i j : Fin (s + 1) =>
    (X ⟨σ, Fin.castLE s.isLt i, col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) R)).det

def minorsP (R : Type) [CommRing R] (a : T → ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ, ∏ s : Fin (r σ), minor r n col R σ s ^ (a σ s - a σ (s + 1))

theorem minorMonomial_map (a : T → ℕ → ℕ) :
    MvPolynomial.map (Int.castRingHom k) (minorsP r n col ℤ a) = minorsP r n col k a := by
  simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
  refine Finset.prod_congr rfl fun σ _ => Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext1 i j
  simp

theorem minorMonomial_coeff_mem (a : T → ℕ → ℕ) (O : Subring k) (m : Letter T r n →₀ ℕ) :
    (minorsP r n col k a).coeff m ∈ O := by
  rw [← minorMonomial_map, coeff_map]
  exact intCast_mem O _

theorem minorMonomial_ne_zero (hcol : ∀ σ, Function.Injective (col σ)) (a : T → ℕ → ℕ) :
    minorsP r n col k a ≠ 0 := by
  classical
  intro h
  have h1 : MvPolynomial.eval (fun ℓ : Letter T r n => if ℓ.2.2 = col ℓ.1 ℓ.2.1 then (1 : k) else 0)
      (minorsP r n col k a) = 1 := by
    simp only [minorsP, map_prod, map_pow, minor, RingHom.map_det]
    refine Finset.prod_eq_one fun σ _ => Finset.prod_eq_one fun s _ => ?_
    rw [show (MvPolynomial.eval _).mapMatrix _ = (1 : Matrix (Fin (s + 1)) (Fin (s + 1)) k) from ?_,
      Matrix.det_one, one_pow]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X, Matrix.one_apply,
      (hcol σ).eq_iff, (Fin.castLE_injective _).eq_iff, eq_comm]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem minorMonomial_mem_harmonic (cc : T → T) (isX : T → Prop)
    (hdis : ∀ τ, isX τ → ∀ i j, col τ i ≠ col (cc τ) j) (a : T → ℕ → ℕ) :
    minorsP r n col k a ∈ harmK r n k cc isX (fun _ => 1) := by
  classical
  let S : Set (Letter T r n) := {v | ∃ j, col v.1 j = v.2.2}
  have hS : minorsP r n col k a ∈ MvPolynomial.supported k S := by
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ ?_ _
    rw [minor, Matrix.det_apply']
    refine Subalgebra.sum_mem _ fun g _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.prod_mem _ fun a _ => ?_)
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : ∃ j, col (cc τ) j = b
    · obtain ⟨j', hj'⟩ := hb
      rw [minorHarm_pderiv_comm, minorHarm_pderiv_eq_zero hS, map_zero, smul_zero]
      rintro ⟨j, hj⟩
      exact hdis τ hτ j j' (hj.trans hj'.symm)
    · rw [minorHarm_pderiv_eq_zero hS (v := ⟨cc τ, i', b⟩) hb, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]

theorem rowShift_minor (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : k) (σ' : T) (s : Fin (r σ')) :
    rowShift r n k σ i i' t (minor r n col k σ' s) = minor r n col k σ' s := by
  classical
  rw [minor, AlgHom.map_det]
  by_cases h : ∃ u : Fin (s + 1), (⟨σ', Fin.castLE s.isLt u⟩ : Σ σ, Fin (r σ)) = ⟨σ, i⟩
  · obtain ⟨u, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := Sigma.mk.inj_iff.1 hu
    have hu'' : Fin.castLE s.isLt u = i := eq_of_heq hu'
    subst hu''
    have hi' : (i' : ℕ) < u := hi
    let u' : Fin (s + 1) := ⟨i', hi'.trans u.isLt⟩
    have hne : u ≠ u' := fun e => by
      have := congrArg Fin.val e
      simp only [u'] at this
      omega
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C t))
    congr 1
    ext1 x y
    by_cases hx : x = u
    · subst hx
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [if_pos ⟨_, rfl⟩]
      rfl
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X,
        Matrix.updateRow_ne hx]
      rw [if_neg]
      rintro ⟨b, hb⟩
      have := eq_of_heq (Sigma.mk.inj_iff.1 hb).2
      exact hx (Fin.castLE_injective s.isLt (congrArg Prod.fst this))
  · congr 1
    ext1 x y
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rowShift, aeval_X]
    rw [if_neg]
    rintro ⟨b, hb⟩
    obtain ⟨rfl, hb'⟩ := Sigma.mk.inj_iff.1 hb
    exact h ⟨x, by rw [show Fin.castLE s.isLt x = i from congrArg Prod.fst (eq_of_heq hb')]⟩

theorem minorMonomial_rowInvariant (a : T → ℕ → ℕ) : RowInv r n k (minorsP r n col k a) := by
  intro σ i i' hi t
  simp only [minorsP, map_prod, map_pow, rowShift_minor r n k col σ i i' hi t]

theorem minor_weighted (w : (Σ σ, Fin (r σ)) → ℕ) (σ : T) (s : Fin (r σ)) :
    (minor r n col k σ s).IsWeightedHomogeneous (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
      (∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩) := by
  rw [minor, Matrix.det_apply']
  refine IsWeightedHomogeneous.sum _ _ _ fun g _ => ?_
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (Finset.univ : Finset (Fin (s + 1)))
    (fun j => (X ⟨σ, Fin.castLE s.isLt (g j), col σ (Fin.castLE s.isLt j)⟩ : MvPolynomial (Letter T r n) k))
    (fun j => w ⟨σ, Fin.castLE s.isLt (g j)⟩) (fun j _ => isWeightedHomogeneous_X _ _ _)
  rw [Equiv.sum_comp g (fun j => w ⟨σ, Fin.castLE s.isLt j⟩)] at h
  have h2 := (isWeightedHomogeneous_C (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩)
    (((Equiv.Perm.sign g : ℤˣ) : ℤ) : k)).mul h
  simpa using h2

theorem gaps_sum (b : ℕ → ℕ) (hb : Antitone b) (N i : ℕ) (hi : i ≤ N) :
    ∑ s ∈ Finset.range N, (if i ≤ s then b s - b (s + 1) else 0) = b i - b N := by
  induction N, hi using Nat.le_induction with
  | base =>
    rw [Nat.sub_self]
    exact Finset.sum_eq_zero fun s hs => if_neg (by simpa using hs)
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, if_pos hN]
    have := hb hN
    have := hb (Nat.le_succ N)
    simp only [Nat.succ_eq_add_one] at this
    omega

theorem minorMonomial_rowDegree (a : T → ℕ → ℕ) (ha : ∀ σ, Antitone (a σ)) (h0 : ∀ σ, a σ (r σ) = 0) :
    RowDeg r n k a (minorsP r n col k a) := by
  classical
  intro m hm σ i
  let w : (Σ σ, Fin (r σ)) → ℕ := fun ℓ => if ℓ = ⟨σ, i⟩ then 1 else 0
  have h := IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
    fun σ' _ => IsWeightedHomogeneous.prod (R := k) (w := fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) Finset.univ _ _
      fun (s : Fin (r σ')) _ => (minor_weighted r n k col w σ' s).pow (a σ' s - a σ' (s + 1))
  have h1 := h (mem_support_iff.1 hm)
  have hL : Finsupp.weight (fun ℓ : Letter T r n => w ⟨ℓ.1, ℓ.2.1⟩) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
      Finset.sum_eq_single σ, Fintype.sum_prod_type, Finset.sum_eq_single i]
    · simp [w]
    · intro j _ hj
      simp [w, hj]
    · simp
    · intro σ' _ hσ
      simp [w, hσ]
    · simp
  rw [← hL, h1, Finset.sum_eq_single σ]
  · have e : ∀ s : Fin (r σ), (a σ s - a σ (s + 1)) • ∑ j : Fin (s + 1), w ⟨σ, Fin.castLE s.isLt j⟩ =
        if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0 := by
      intro s
      split_ifs with his
      · rw [Finset.sum_eq_single ⟨i, Nat.lt_succ_of_le his⟩]
        · simp [w]
        · intro j _ hj
          simp only [w]
          rw [if_neg]
          intro e
          have e' : Fin.castLE s.isLt j = i := eq_of_heq (Sigma.mk.inj_iff.1 e).2
          exact hj (Fin.ext (congrArg Fin.val e' :))
        · simp
      · rw [Finset.sum_eq_zero, smul_zero]
        intro j _
        simp only [w]
        rw [if_neg]
        intro e
        have := congrArg Fin.val (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
        have := j.isLt
        simp only [Fin.val_castLE] at *
        omega
    rw [Finset.sum_congr rfl fun s _ => e s,
      Fin.sum_univ_eq_sum_range (fun s => if (i : ℕ) ≤ s then a σ s - a σ (s + 1) else 0),
      gaps_sum _ (ha σ) _ _ i.isLt.le, h0, Nat.sub_zero]
  · intro σ' _ hσ
    simp [w, hσ]
  · simp

end Minors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra h0
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun e => ?_⟩
  rw [e] at hre
  simp only [Complex.zero_re, Complex.zero_im] at hre
  linarith

theorem not_inPsi_conjugate {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h, (rt0_conj_neg_ne_zero H).1] at h'
  exact (rt0_conj_neg_ne_zero H).2 (by linear_combination (-1 / 2 : ℂ) * h')

theorem mult_of_inPsi {τ : E →+* ℂ} (h : InPsi H τ) : Dw.mult τ = Dw.p := if_pos h

theorem mult_of_not_inPsi {τ : E →+* ℂ} (h : ¬ InPsi H τ) : Dw.mult τ = Dw.q := if_neg h

def trunc (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => if x.2 < Dw.mult x.1 then a x else 0

theorem trunc_row (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : trunc Dw a (τ, i) = a (τ, i) :=
  if_pos i.isLt

theorem rowsDominant_of_dom {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (h : Dom a n) : RowsDominant Dw a :=
  fun τ _ _ hij => h.1 τ hij

theorem antitone_trunc {a : (E →+* ℂ) × ℕ → ℕ} (h : RowsDominant Dw a) (τ : E →+* ℂ) :
    Antitone fun i => trunc Dw a (τ, i) := by
  intro i j hij
  simp only [trunc]
  split_ifs with hj hi hi
  · exact h τ (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem df_trunc (a : (E →+* ℂ) × ℕ → ℕ) : DF Dw (trunc Dw a) = DF Dw a := by
  simp only [DF, trunc_row]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem harmA_trunc (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    harmA (Dw := Dw) c (trunc Dw a) n = harmA (Dw := Dw) c a n := by
  ext P
  simp only [harmA, HaO, HHa, RowDeg, Set.mem_setOf_eq, trunc_row]

theorem exists_harmA_ne_zero {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : RowsDominant Dw a) (hn : Dw.p + Dw.q ≤ n) :
    ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0 := by
  classical
  let col : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n := fun τ i =>
    if h : InPsi H τ then ⟨i, by have := i.isLt; have := mult_of_inPsi (Dw := Dw) h; omega⟩
    else ⟨Dw.p + i, by have := i.isLt; have := mult_of_not_inPsi (Dw := Dw) h; omega⟩
  have hinj : ∀ τ, Function.Injective (col τ) := by
    intro τ i j hij
    have := congrArg Fin.val hij
    by_cases h : InPsi H τ
    · simp only [col, dif_pos h] at this
      exact Fin.ext this
    · simp only [col, dif_neg h] at this
      exact Fin.ext (by omega)
  have hdis : ∀ τ, InPsi H τ → ∀ i j, col τ i ≠ col (ComplexEmbedding.conjugate τ) j := by
    intro τ h i j hij
    have := congrArg Fin.val hij
    simp only [col, dif_pos h, dif_neg (not_inPsi_conjugate h)] at this
    have := i.isLt
    have := mult_of_inPsi (Dw := Dw) h
    omega
  rw [← harmA_trunc]
  exact ⟨minorsP Dw.mult n col c.F fun τ i => trunc Dw a (τ, i),
    ⟨⟨minorMonomial_mem_harmonic _ _ _ _ _ _ hdis _, minorMonomial_rowInvariant _ _ _ _ _,
      minorMonomial_rowDegree _ _ _ _ _ (antitone_trunc ha) fun τ => if_neg (lt_irrefl _)⟩,
      minorMonomial_coeff_mem _ _ _ _ _ _⟩, minorMonomial_ne_zero _ _ _ _ hinj _⟩

def LastPosAt (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) : Prop :=
  0 < Dw.p ∧ 0 < a (τ, Dw.p - 1)

def RowsOnly (Cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ a a' n, (∀ τ (i : Fin (Dw.mult τ)), a (τ, i) = a' (τ, i)) → Cusp a n = Cusp a' n

def ShapeOK {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ σ, GoodEmb c σ → r = Dw.p + Dw.q ∧
    ∀ k, ((U σ).X k).p0 = Dw.q ∧ ∀ τ : E →+* ℂ, τ ∈ ((U σ).X k).Ψ ↔ InPsi H τ

variable {Xo c}

def SomeGeneratorNeZeroEven (Xo : Moduli Dw l) (c : Coeff l) (nab : NabV Xo c) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (al : 𝓞 E) (q : ℕ), Even n → 0 < n → InJetRange Dw l a n al q →
    ∃ f ∈ thGen Xo c nab a n, f ≠ 0

end GlobalTheory.ThetaClaimsCompare
