import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemCommonRefinementStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExistsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemLevelGrowthStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace AdmExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem zeta_isIntegral (n : ℕ) (hn : n ≠ 0) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn).isIntegral (Nat.pos_of_ne_zero hn)).tower_top

theorem exists_idx {p : ℕ} (i₀ : Idx H p) (k : ℕ) (hk : 0 < k) :
    ∃ i : Idx H p, i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * k ∧ i₀.c.F ≤ i.c.F := by
  let l : Level H := { i₀.l with A := i₀.l.A * k, A_pos := Nat.mul_pos i₀.l.A_pos hk }
  have hA : l.A ≠ 0 := l.A_pos.ne'
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) hA
  let F : IntermediateField ℚ ℂ := i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M', zeta l.A}
  have hfin : FiniteDimensional ℚ F := by
    haveI := i₀.c.fin
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ)) :=
      IntermediateField.finiteDimensional_adjoin (by
        rintro x (rfl | rfl)
        · exact zeta_isIntegral _ hM
        · exact zeta_isIntegral _ hA)
    exact IntermediateField.finiteDimensional_sup _ _
  have h1 : i₀.c.F ≤ F := le_sup_left
  have h2 : IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ) ≤ F := le_sup_right
  let c : Coeff l :=
    { F := F
      fin := hfin
      conj := fun τ a => h1 (i₀.c.conj τ a)
      zeta_mem := h2 (IntermediateField.subset_adjoin _ _ (by simp))
      le := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro x (rfl | rfl)
        · exact h1 (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))
        · exact h2 (IntermediateField.subset_adjoin _ _ (by simp)) }
  exact ⟨⟨l, c, i₀.good⟩, rfl, rfl, rfl, h1⟩

theorem finite_steps (Dw : Datum H) : Finite {st // ∃ x, letterOf Dw st = some x} := by
  let f : Letter Dw ⊕ Fin (letters Dw).length → ((E →+* ℂ) × ℕ) ⊕ ℕ := fun a => match a with
    | .inl x => .inl (x.1, x.2)
    | .inr k => .inr k
  have : {st | ∃ x, letterOf Dw st = some x} ⊆ Set.range f := by
    rintro (⟨τ, k⟩ | k) ⟨x, hx⟩
    · by_cases h : k < Dw.mult τ
      · exact ⟨.inl ⟨τ, ⟨k, h⟩⟩, rfl⟩
      · simp [letterOf, h] at hx
    · have h : k < (letters Dw).length := by
        by_contra h
        simp only [letterOf] at hx
        rw [List.getElem?_eq_none (not_lt.1 h)] at hx
        cases hx
      exact ⟨.inr ⟨k, h⟩, rfl⟩
  exact ((Set.finite_range f).subset this).to_subtype

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) : D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simpa using this
  have h0 := H.sqrt_neg_disc_sq
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := fun z hz => by
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [pow_two] at hre him
    have : z.re = 0 := by
      by_contra hne
      have : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [sq_nonneg z.re]
    apply Complex.ext <;> simp [this]
  have hne : H.rt0 ≠ 0 := by
    intro h; rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0.symm
    exact hd.ne' (by exact_mod_cast this)
  have hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ (H.rt : E) = -τ (H.rt : E) := key _ h1
  unfold Datum.mult
  rw [hc]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h0.symm) with h | h
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this]
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this, add_comm]

theorem exists_letter (Dw : Datum H) (h : 1 ≤ Dw.p + Dw.q) : Nonempty (Letter Dw) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 := mult_add_mult_conj Dw τ
  by_cases h0 : 0 < Dw.mult τ
  · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
  · exact ⟨⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ, ⟨0, by omega⟩⟩⟩

theorem exists_adm [IsGalois ℚ E] (hB : HTBoundSt) {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) (i₀ : Idx H p) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hY : N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) (n : ℕ) (hn : 1 + 1 / ((p : ℝ) - 1) < n) :
    ∃ z : admitted Y i₀, z.n = n := by
  obtain ⟨i, hM, hMb, hA, hF⟩ := exists_idx i₀ (p ^ n) (pow_pos hp.pos n)
  have hd : i₀.l.Dvd i.l := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ dvd_mul_right _ _⟩
  have hpn : p ^ n ∣ i.l.A := hA ▸ dvd_mul_left _ _
  have hex : ∀ b st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧
      (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z b st x) := by
    intro b st x hx
    cases b
    · exact GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx
    · exact GlobalTheory.T.local_system_level_growth hB E H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx
  haveI := finite_steps Dw
  let T := Bool × {st // ∃ x, letterOf Dw st = some x}
  obtain ⟨x₀⟩ := exists_letter Dw hr
  haveI : Nonempty T := ⟨(false, ⟨.inl (x₀.1, x₀.2), x₀, by simp [letterOf]⟩)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = m + 1 := ⟨Nat.card T - 1, by have := Nat.card_pos (α := T); omega⟩
  let e : T ≃ Fin (m + 1) := Finite.equivFinOfCardEq hm
  choose Z hZi hZty hZl using fun t : T => hex t.1 t.2.1 t.2.2.choose t.2.2.choose_spec
  obtain ⟨Z', h1, h2, h3⟩ := GlobalTheory.T.local_system_common_refinement E H Dw Xo p W Y i₀ hp hW hY m (fun a => Z (e.symm a))
    (fun a => ⟨(hZi _).trans (hZi _).symm, (hZty _).trans (hZty _).symm⟩)
  have h1' : Z'.i = i := h1.trans (hZi _)
  have h2' := h2.trans (hZty _)
  have hl : ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z' b st x) := by
    intro b st x hx
    let t : T := (b, ⟨st, x, hx⟩)
    obtain ⟨f, hf⟩ := h3 (e t)
    have hxe : t.2.2.choose = x := Option.some.inj (t.2.2.choose_spec.symm.trans hx)
    have hl := hZl t
    rw [hxe] at hl
    refine GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY _ Z' f hf ?_ b st x hx ?_
    · intro τ k hk
      rw [hZty]
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    · rw [e.symm_apply_apply]
      exact hl
  refine ⟨⟨Z', ?_, n, ?_, fun b st x hx => (hl b st x hx).some⟩, rfl⟩
  · intro τ k hk
    rw [h2']
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  · rw [h1']
    exact ⟨hM, hMb, hA⟩

end AdmExist

theorem admEx_of_htBound : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), AdmEx S κ := by
  intro hB D A N j S κ p hp W hW n hn
  haveI := D.host.hostE_isGalois
  exact AdmExist.exists_adm hB (by have := S.rank_eq; have := S.two_le; omega) _ _ hp hW (S.sys.clauses p W hp hW) n hn

end GlobalTheory.ShFam.Pad
