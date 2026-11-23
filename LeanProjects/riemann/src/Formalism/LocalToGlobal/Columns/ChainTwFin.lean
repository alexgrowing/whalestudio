import Formalism.LocalToGlobal.Columns.ChainFrmOk
import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ
import Formalism.LocalToGlobal.Columns.ChainTwTop

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Approx

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem tfVal_mem {u : 𝓞 E} {N : ℕ} (hu : u ∈ P.asIdeal ^ N) : P.valuation E (algebraMap (𝓞 E) E u) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem P u N).mpr hu

theorem tfApprox (a : E) (ha : P.valuation E a ≤ 1) (N : ℕ) : ∃ r : 𝓞 E, P.valuation E (a - algebraMap (𝓞 E) E r) ≤ WithZero.exp (-(N : ℤ)) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := by
    first
      | exact pow_ne_zero _ P.ne_bot
  obtain ⟨t, htP, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPN
  have hc : algebraMap E (P.adicCompletion E) a ∈ P.adicCompletionIntegers E := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  obtain ⟨r, hr⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_local P
    (algebraMap E (P.adicCompletion E) a) hc t ht0
  refine ⟨r, ?_⟩
  rw [← map_sub] at hr
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hr
  exact hr.trans ((HeightOneSpectrum.intValuation_le_pow_iff_mem P t N).mpr htP)

end Approx

section Idx

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ)

def tfRed (g : ↥(GLint E n P)) : Fin n → Fin n → 𝓞 E ⧸ P.asIdeal ^ N := fun i j =>
  Ideal.Quotient.mk _ (tfApprox P _ (qsp_entry_int P g i j) N).choose

theorem tfRed_eq {g g' : ↥(GLint E n P)} (h : tfRed P N g = tfRed P N g') : lqPrinc P N ((g⁻¹ * g' : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
  classical
  have hmat : ∀ x : ↥(GLint E n P), ((toGLm E n x.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      LinearMap.toMatrix' ((x.1 : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) := fun x => rfl
  have hclose : ∀ l k, P.valuation E (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k) ≤ WithZero.exp (-(N : ℤ)) := by
    intro l k
    have hr := (tfApprox P _ (qsp_entry_int P g l k) N).choose_spec
    have hr' := (tfApprox P _ (qsp_entry_int P g' l k) N).choose_spec
    have hmk := congrFun (congrFun h l) k
    simp only [tfRed] at hmk
    have hrr := tfVal_mem P (Ideal.Quotient.eq.mp hmk)
    rw [map_sub] at hrr
    have e : ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
        ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k =
        (((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
          algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
        (-(algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g' l k) N).choose) +
          -(((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) l k -
            algebraMap (𝓞 E) E (tfApprox P _ (qsp_entry_int P g l k) N).choose)) := by ring
    rw [e]
    refine Valuation.map_add_le _ hr' (Valuation.map_add_le _ ?_ ?_)
    · rw [Valuation.map_neg]
      exact hrr
    · rw [Valuation.map_neg]
      exact hr
  have hM1 : ((toGLm E n (g⁻¹ * g').1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
        ((toGLm E n g'.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
    rw [Subgroup.coe_mul, map_mul, Units.val_mul]
  have hM2 : ((toGLm E n (g⁻¹).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *
      ((toGLm E n g.1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_one,
      Units.val_one]
  intro i j
  rw [← hmat (g⁻¹ * g'), hM1, ← hM2, ← Matrix.mul_sub, Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [Valuation.map_mul, Matrix.sub_apply]
  exact le_trans (mul_le_of_le_one_left' (qsp_entry_int P g⁻¹ i l)) (hclose l j)

theorem tfFinite_quot (hN : 0 < N) : Finite (𝓞 E ⧸ P.asIdeal ^ N) := by
  have hPN : P.asIdeal ^ N ≠ ⊥ := pow_ne_zero _ P.ne_bot
  first
    | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hPN)
    | exact Ideal.finiteQuotientOfFreeOfNeBot _ hPN

theorem tfFinite_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → g ∈ H) :
    Finite (↥(GLint E n P) ⧸ H) := by
  classical
  haveI := tfFinite_quot P N hN
  let q : Set.range (tfRed P N) → (↥(GLint E n P) ⧸ H) := fun v => QuotientGroup.mk v.2.choose
  refine Finite.of_surjective q ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    refine ⟨⟨tfRed P N g, g, rfl⟩, ?_⟩
    show QuotientGroup.mk _ = QuotientGroup.mk g
    rw [QuotientGroup.eq]
    apply hH
    exact tfRed_eq P N (⟨tfRed P N g, g, rfl⟩ : Set.range (tfRed P N)).2.choose_spec

theorem tfRoot_of_princ (hN : 0 < N) (H : Subgroup ↥(GLint E n P)) (lam : ↥H →* Kˣ)
    (hH : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ H, lam ⟨g, h⟩ = 1) (x : ↥H) :
    ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
  classical
  haveI := tfFinite_quot P N hN
  have key : ∀ k1 k2 : ℕ, k1 < k2 →
      tfRed P N ((x : ↥(GLint E n P)) ^ k1) = tfRed P N ((x : ↥(GLint E n P)) ^ k2) →
      ∃ m : ℕ, 0 < m ∧ lam x ^ m = 1 := by
    intro k1 k2 hlt heq
    have hp := tfRed_eq P N heq
    have hpow : ((x : ↥(GLint E n P)) ^ k1)⁻¹ * (x : ↥(GLint E n P)) ^ k2 =
        (x : ↥(GLint E n P)) ^ (k2 - k1) := by
      rw [inv_mul_eq_iff_eq_mul, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hpow] at hp
    obtain ⟨hmem, hlam⟩ := hH _ hp
    refine ⟨k2 - k1, by omega, ?_⟩
    have hx : (⟨(x : ↥(GLint E n P)) ^ (k2 - k1), hmem⟩ : ↥H) = x ^ (k2 - k1) := by
      apply Subtype.ext
      simp
    rw [← map_pow, ← hx, hlam]
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => tfRed P N ((x : ↥(GLint E n P)) ^ k))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key k1 k2 hlt heq
  · exact key k2 k1 hlt heq.symm

end Idx

section Pi

theorem tfPiChar {K : Type} [Field K] {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i))
    (lam : ∀ i, ↥(H i) →* Kˣ) (x : ↥(Subgroup.pi Set.univ H)) :
    piChar H lam x = ∏ i, lam i ⟨x.1 i, x.2 i (Set.mem_univ i)⟩ := by
  simp only [piChar, MonoidHom.finset_prod_apply, MonoidHom.comp_apply]
  rfl

end Pi

section Fam

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))} (Θ : LevQFam E K n Q)

theorem thetaOpen_finIdx (h : ThetaOpen Θ) (P : Q) : Finite (↥(GLint E n P.1) ⧸ (Θ P).H) := by
  obtain ⟨N, hN, hg⟩ := h P
  exact tfFinite_of_princ P.1 N hN (Θ P).H (fun g hgp => (hg g hgp).1)

theorem thetaOpen_root (h : ThetaOpen Θ) (c : ↥Θ.grp) : ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : Kˣ) : K) ^ m = 1 := by
  classical
  have hP : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ ^ m = 1 := by
    intro P
    obtain ⟨N, hN, hg⟩ := h P
    exact tfRoot_of_princ P.1 N hN (Θ P).H (Θ P).lam hg _
  choose m hm0 hm using hP
  have key : (Θ.chr c) ^ (∏ P, m P) = 1 := by
    have hc : Θ.chr c = ∏ P, (Θ P).lam ⟨c.1 P, c.2 P (Set.mem_univ P)⟩ :=
      tfPiChar (fun P => (Θ P).H) (fun P => (Θ P).lam) c
    rw [hc, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun P _ => ?_
    obtain ⟨d, hd⟩ : m P ∣ ∏ Q, m Q := Finset.dvd_prod_of_mem _ (Finset.mem_univ P)
    rw [hd, pow_mul, hm P, one_pow]
  refine ⟨∏ P, m P, Finset.prod_pos fun P _ => hm0 P, ?_⟩
  rw [← Units.val_pow_eq_pow_val, key, Units.val_one]

end Fam

section Tw

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

theorem thetaOpen_twIdxTop (hc : cst.Ok) (hQg : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hΘ : ∀ j, m2 + 1 < j → ThetaOpen (Θt j)) (j : ℕ)
    (b : (twIdxTop Ch sel mu cst m2 Λt Θt).β j) : ThetaOpen ((twIdxTop Ch sel mu cst m2 Λt Θt).levQ j b) := by
  unfold twIdxTop ChIdx.withTop at b ⊢
  obtain ⟨ob, hob⟩ := b
  cases ob with
  | some b' =>
    exact thetaOpen_twIdx (Ch := Ch) (sel := sel) (mu := mu) (cst := cst) hc hQg m2 j b'
  | none =>
    have hj : m2 + 1 < j := by
      simp only [Option.isSome_none] at hob
      by_contra hcon
      have h1 : j ≤ m2 + 1 := by omega
      simp [h1] at hob
    exact hΘ j hj

theorem chF_ok_twIdxTop (hX : X.Ok) (hc : cst.Ok) (hQg : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (hΘ : ∀ j, m2 + 1 < j → ThetaOpen (Θt j))
    (u : Pr.Word) (j : ℕ) : (chF W sel mu (twIdxTop Ch sel mu cst m2 Λt Θt) u j).Ok :=
  chF_ok_of_finIdx (W := W) (sel := sel) (mu := mu) (L := twIdxTop Ch sel mu cst m2 Λt Θt) hX u j
    (fun b P => thetaOpen_finIdx _ (thetaOpen_twIdxTop Ch sel mu cst m2 Λt Θt hc hQg hΘ j b) P)
    (fun b c => thetaOpen_root _ (thetaOpen_twIdxTop Ch sel mu cst m2 Λt Θt hc hQg hΘ j b) c)

end Tw

end Formalism.L2.Col
