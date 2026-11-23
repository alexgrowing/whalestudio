import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV

namespace GlobalTheory.JumpDims

open Module
open scoped TensorProduct

section Linear

variable {L U : Type} [Field L] [AddCommGroup U] [Module L U]

theorem exists_le_of_exh (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) : ∃ a, D ≤ F a := by
  obtain ⟨S, hS⟩ : D.FG := Module.Finite.iff_fg.mp inferInstance
  choose n hn using hexh
  obtain ⟨a, ha⟩ := (S.image n).bddBelow
  refine ⟨a, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact hanti (ha (Finset.mem_coe.mpr (Finset.mem_image_of_mem n hx))) (hn x)

theorem exists_inf_eq_bot_of_sep (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ a, D ⊓ F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional L ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  let a : ℤ := Function.argmin (fun a : ℤ => finrank L ↥(D ⊓ F a))
  have ha : ∀ b, finrank L ↥(D ⊓ F a) ≤ finrank L ↥(D ⊓ F b) := fun b =>
    Function.argmin_le (fun a : ℤ => finrank L ↥(D ⊓ F a)) b
  refine ⟨a, eq_bot_iff.mpr fun x hx => ?_⟩
  rw [Submodule.mem_bot]
  refine hsep x fun b => ?_
  rcases le_total a b with h | h
  · have : D ⊓ F b = D ⊓ F a :=
      Submodule.eq_of_le_of_finrank_le (inf_le_inf_left D (hanti h)) (ha b)
    exact (this ▸ hx : x ∈ D ⊓ F b).2
  · exact hanti h hx.2

theorem card_filter_succ (M : Multiset ℤ) (a : ℤ) :
    Multiset.card (M.filter (a ≤ ·)) = Multiset.card (M.filter (a + 1 ≤ ·)) + M.count a := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.count_cons, Multiset.card_add,
      Multiset.card_add, ih]
    split_ifs <;> simp <;> omega

theorem finrank_of_mult (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (M : Multiset ℤ)
    (hM : ∀ a, (finrank L ↥(D ⊓ F a) : ℤ) - finrank L ↥(D ⊓ F (a + 1)) = (M.count a : ℤ)) :
    finrank L D = Multiset.card M ∧
      ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := by
  let g : ℤ → ℤ := fun a => (finrank L ↥(D ⊓ F a) : ℤ) - Multiset.card (M.filter (a ≤ ·))
  have hstep : ∀ a, g (a + 1) = g a := fun a => by
    have h1 := hM a
    have h2 := card_filter_succ M a
    simp only [g]
    omega
  have hconst : ∀ a, g a = g 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
    | pred n ih => rw [← ih, ← hstep]; congr 1; ring
  obtain ⟨hi, hhi⟩ := exists_inf_eq_bot_of_sep D F hanti hsep
  obtain ⟨lo, hlo⟩ := exists_le_of_exh D F hanti hexh
  obtain ⟨u, hu⟩ := M.toFinset.bddAbove
  obtain ⟨l, hl⟩ := M.toFinset.bddBelow
  have hu' : ∀ x ∈ M, x ≤ u := fun x hx => hu (by simpa using hx)
  have hl' : ∀ x ∈ M, l ≤ x := fun x hx => hl (by simpa using hx)
  have h0 : g (max hi (u + 1)) = 0 := by
    have e1 : D ⊓ F (max hi (u + 1)) = ⊥ :=
      eq_bot_iff.mpr (hhi ▸ inf_le_inf_left D (hanti (le_max_left _ _)))
    have e2 : M.filter (max hi (u + 1) ≤ ·) = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx h => by
        have := hu' x hx
        have := le_max_right hi (u + 1)
        omega
    show (finrank L ↥(D ⊓ F (max hi (u + 1))) : ℤ) - Multiset.card (M.filter (max hi (u + 1) ≤ ·)) = 0
    rw [e1, e2]
    simp
  have hall : ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := fun a => by
    have : g a = 0 := by rw [hconst a, ← hconst (max hi (u + 1)), h0]
    simp only [g] at this
    omega
  refine ⟨?_, hall⟩
  have e1 : D ⊓ F (min lo l) = D := inf_eq_left.mpr (hlo.trans (hanti (min_le_left _ _)))
  have e2 : M.filter (min lo l ≤ ·) = M :=
    Multiset.filter_eq_self.mpr fun x hx => (min_le_right _ _).trans (hl' x hx)
  have := hall (min lo l)
  rwa [e1, e2] at this

end Linear

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem finite_of_isdR {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (h : Bw.IsdRW P r) :
    FiniteDimensional ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : Subsingleton (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hz : ∀ z : (Fin 0 → ↥Bw.LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hz x.1, hz y.1]
    haveI : Finite (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · haveI := (P.PD Bw.Kw).finK
    haveI : Module.Free ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos (by rw [h]; exact Nat.mul_pos Module.finrank_pos hm)

theorem dims_of_mult : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  intro D bkP i s v hv τ M hH hM
  have hdR := (hH v hv (Tgl i s) (Or.inr rfl)).1
  haveI := finite_of_isdR _ _ _ hdR
  haveI : FiniteDimensional _ ↥(Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ) :=
    Submodule.finiteDimensional_of_le (S₂ := Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      inf_le_left
  have key := finrank_of_mult (Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ)
    (Formalism.WeaklyAdmissibleFiltrations.FilV (PDv bkP i v hv)) (GlobalTheory.DRFil.FilV_antitone _) (GlobalTheory.DRFil.exists_mem_FilV _)
    (GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV _) M hM
  exact ⟨key.1, key.2 0⟩

end GlobalTheory.JumpDims
