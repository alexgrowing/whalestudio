import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitPlaceEqOfPlaceEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfBoundOnSets
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLiftN

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem unif_ne_zero {s : SplitPlace L} {ϖ : s.v.adicCompletion (maximalRealSubfield L)}
    (hϖ : IsUnif L s.v ϖ) : ϖ ≠ 0 := by
  rintro rfl
  have : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
  rw [map_zero] at this
  exact WithZero.exp_ne_zero this.symm

theorem tSet_subset_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k ⊆ tSet L n s ϖ' k := by
  rintro x ⟨hx, a, ha, b, hb, e⟩
  have h0 := unif_ne_zero hϖ'
  have h0' := unif_ne_zero hϖ
  set u := ϖ / ϖ' with hu
  have hu0 : u ≠ 0 := div_ne_zero h0' h0
  have hv : Valued.v u = 1 := by
    rw [hu, map_div₀]
    have e1 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have e2 : Valued.v ϖ' = WithZero.exp (-1 : ℤ) := hϖ'
    rw [e1, e2, div_self WithZero.exp_ne_zero]
  have hvi : Valued.v u⁻¹ = 1 := by rw [map_inv₀, hv, inv_one]
  let c : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u else 1
  let c' : Fin n → s.v.adicCompletion (maximalRealSubfield L) := fun i => if (i : ℕ) < k then u⁻¹ else 1
  have hcc : (fun i => c i * c' i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  have hcc' : (fun i => c' i * c i) = fun _ => 1 := by
    funext i; simp only [c, c']; split_ifs <;> simp [hu0]
  let dm : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
    ⟨Matrix.diagonal c, Matrix.diagonal c', by rw [Matrix.diagonal_mul_diagonal, hcc, Matrix.diagonal_one],
      by rw [Matrix.diagonal_mul_diagonal, hcc', Matrix.diagonal_one]⟩
  have hI : ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z ≤ 1 →
      z ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun z hz =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ s.v).2 hz
  have hdm : dm ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    rw [GlobalTheory.HeckeStdFacts.mem_GLint_iff]
    refine ⟨fun i j => hI _ ?_, fun i j => hI _ ?_⟩
    · show Valued.v (Matrix.diagonal c i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c]; split_ifs
        · rw [hv]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
    · show Valued.v (Matrix.diagonal c' i j) ≤ 1
      rw [Matrix.diagonal_apply]
      split_ifs
      · simp only [c']; split_ifs
        · rw [hvi]
        · rw [map_one]
      · rw [map_zero]; exact zero_le'
  have hdiag : Formalism.UG.diagJ n ϖ k = Formalism.UG.diagJ n ϖ' k * (dm : Matrix (Fin n) (Fin n) _) := by
    show _ = _ * Matrix.diagonal c
    rw [Formalism.UG.diagJ, Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [c]
    split_ifs
    · rw [hu]; field_simp
    · rw [one_mul]
  refine ⟨hx, a, ha, dm * b, mul_mem hdm hb, ?_⟩
  rw [e, Units.val_mul, hdiag]
  simp only [Matrix.mul_assoc]

theorem tSet_eq_of_unif (n : ℕ) (s : SplitPlace L) (ϖ ϖ' : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ)
    (hϖ : IsUnif L s.v ϖ) (hϖ' : IsUnif L s.v ϖ') : tSet L n s ϖ k = tSet L n s ϖ' k :=
  Set.Subset.antisymm (tSet_subset_of_unif n s ϖ ϖ' k hϖ hϖ') (tSet_subset_of_unif n s ϖ' ϖ k hϖ' hϖ)

theorem tN_eq_of_conj (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (J : Subgroup (GAf D.host.E n))
    (v : PlE D.host) (s s' : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (ϖ' : s'.v.adicCompletion (maximalRealSubfield D.host.E)) (k : ℕ) (hc : IsConjPl D.host v s.w)
    (hc' : IsConjPl D.host v s'.w) (hu : IsUnif D.host.E s.v ϖ) (hu' : IsUnif D.host.E s'.v ϖ') (f : GAf D.host.E n → W) :
    NG.tN J s ϖ k f = NG.tN J s' ϖ' k f := by
  have hw : s.w = s'.w := GlobalTheory.TwSys.ResidualCompare.isConjPl_unique hc hc'
  obtain rfl := GlobalTheory.SplitUniq.splitPlace_eq_of_w_eq _ s s' hw
  unfold NG.tN
  rw [tSet_eq_of_unif n s ϖ ϖ' k hu hu']

end GlobalTheory.HeckeLiftN

namespace GlobalTheory.HeckeLiftN

theorem heckeLift (D : D7) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) :
    HeckeStdPlain → GenHyp M C.Q → MtInput D M tup C.Q → HeckeLift0 (mt0 M) C.Q := by
  intro hP hG hI j w v k h1 h2 hg
  classical
  by_cases hex : ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ
  swap
  · exact ⟨0, fun s ϖ hc hu _ => absurd ⟨s, ϖ, hc, hu⟩ hex⟩
  obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex
  obtain ⟨B, hB, hBs⟩ := hG w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj' : j' < D.R.m := by omega
  set Mw := M (D.what₂.muTw w) (j' + 1) h1 h2 with hMw
  have hrat : ∀ x, ∃ x', Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x') =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) :=
    fun x => hI.rat w ⟨j', hj'⟩ v k s0 ϖ0 hg hc0 hu0 x
  obtain ⟨-, Plin, -, -⟩ := hP D.host.E D.R.nV Mw.wt Mw.J Mw.χ B Mw.J_open hB s0 ϖ0 k (hBs v k s0 hg hc0) hu0
    hg.2.2.2.2.1 hg.2.2.2.2.2
  have hTS : ∀ y, Mw.real y ∈ NG.TypeSp Mw.wt.ρ Mw.J Mw.χ := fun y => by
    rw [← Mw.real_range]; exact LinearMap.mem_range_self _ y
  have hRJ : Function.Injective fun x => Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x) :=
    Mw.real_inj.comp (Formalism.L2.jMt_injective _ _)
  have htN0 : NG.tN Mw.J s0 ϖ0 k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
    have := Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    rw [one_smul, add_zero, one_smul] at this
    simpa using this
  let T0 : D.what₂.MtL (D.what₂.muTw w) (j' + 1) → D.what₂.MtL (D.what₂.muTw w) (j' + 1) := fun x => (hrat x).choose
  have hT0 : ∀ x, Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
      NG.tN Mw.J s0 ϖ0 k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) := fun x => (hrat x).choose_spec
  have hadd : ∀ x y, T0 (x + y) = T0 x + T0 y := by
    intro x y
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (x + y))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x + T0 y))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y)) 1
    rw [one_smul, one_smul] at this
    rw [hT0, map_add, map_add, map_add, map_add, hT0, hT0, this]
  have hsmul : ∀ (a : D.what₂.LL) x, T0 (a • x) = a • T0 x := by
    intro a x
    apply hRJ
    show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 (a • x))) =
      Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (a • T0 x))
    have := Plin _ (hTS (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x)) 0 (Submodule.zero_mem _) (D.what₂.embLL a)
    rw [add_zero, htN0, add_zero] at this
    rw [hT0]
    simp only [LinearMap.map_smulₛₗ, RingHom.id_apply]
    rw [hT0, this]
  let T : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) (j' + 1)) :=
    { toFun := T0
      map_add' := hadd
      map_smul' := hsmul }
  refine ⟨T, fun s ϖ hc hu x => ?_⟩
  show Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) (T0 x)) =
    NG.tN Mw.J s ϖ k (Mw.real (D.what₂.jMt (D.what₂.muTw w) (j' + 1) x))
  rw [hT0]
  exact tN_eq_of_conj D Mw.J v s0 s ϖ0 ϖ k hc0 hc hu0 hu _

end GlobalTheory.HeckeLiftN
