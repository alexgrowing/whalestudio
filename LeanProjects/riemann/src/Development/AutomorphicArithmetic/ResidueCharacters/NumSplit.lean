import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AutomorphicArithmetic.ResidueCharacters.NumParameters

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.Num

theorem finrank_E_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  show 4 * D.R.ord = 2 * (2 * D.R.ord)
  ring

theorem mem_primesOver_of_mem {E : Type} [Field E] [NumberField E] {l : ℕ} (hl : l.Prime)
    {v : HeightOneSpectrum (𝓞 E)} (hv : v ∈ placesOver E l) :
    v.asIdeal ∈ (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
  have : Fact l.Prime := ⟨hl⟩
  have hmax := Int.ideal_span_isMaximal_of_prime l
  have := v.isPrime
  refine ⟨v.isPrime, ⟨?_⟩⟩
  apply hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
  have hv' : ((l : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
  simpa using hv'

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  haveI := Int.ideal_span_isMaximal_of_prime l
  have hfin : ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E)).Finite :=
    Set.toFinite _
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal)
      ((fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) ⁻¹' ((Ideal.span {(l : ℤ)}).primesOver (𝓞 E))) := by
    intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  exact (hfin.preimage hinj).subset (fun v hv => mem_primesOver_of_mem hl hv)

theorem nLam_pos (D : D7) (lam : HeightOneSpectrum (𝓞 D.host.E)) : 1 ≤ locDeg D.host.E lam := by
  unfold Formalism.MainNotions.N.locDeg
  have := lam.isPrime
  have h1 := Ideal.ramificationIdx_pos lam.asIdeal ℤ
  have h2 := Ideal.inertiaDeg_pos lam.asIdeal ℤ
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero h1.ne' h2.ne')

theorem sum_nLam_le (D : D7) {l : ℕ} (hl : l.Prime) :
    ∑ lam ∈ (placesOver_finite D.host.E hl).toFinset, (locDeg D.host.E lam : ℝ) ≤ 2 * D.R.f := by
  classical
  have : Fact l.Prime := ⟨hl⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(l : ℤ)}) (𝓞 D.host.E)
  rw [RingOfIntegers.rank, finrank_E_host] at hsum
  have hsum' : ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)).toFinset,
      q.ramificationIdx ℤ * q.inertiaDeg ℤ = 2 * D.R.f := by
    rw [← hsum]
    exact (Finset.sum_set_coe (f := fun q : Ideal (𝓞 D.host.E) => q.ramificationIdx ℤ * q.inertiaDeg ℤ) _).symm
  set G : Ideal (𝓞 D.host.E) → ℝ := fun q => ((q.ramificationIdx ℤ * q.inertiaDeg ℤ : ℕ) : ℝ) with hG
  set S := (placesOver_finite D.host.E hl).toFinset with hS
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 D.host.E) => v.asIdeal) (S : Set _) := by
    intro a _ b _ hab
    exact HeightOneSpectrum.ext hab
  calc ∑ lam ∈ S, (locDeg D.host.E lam : ℝ) = ∑ lam ∈ S, G lam.asIdeal := by
        refine Finset.sum_congr rfl (fun lam _ => ?_)
        simp [hG, Formalism.MainNotions.N.locDeg]
    _ = ∑ q ∈ S.image (fun v => v.asIdeal), G q := (Finset.sum_image hinj).symm
    _ ≤ ∑ q ∈ ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)).toFinset, G q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
          rw [Set.mem_toFinset]
          exact mem_primesOver_of_mem hl ((Set.Finite.mem_toFinset _).1 hv)
        · intro q _ _
          simp only [hG]
          positivity
    _ = 2 * D.R.f := by
        simp only [hG]
        rw [← Nat.cast_sum, hsum']
        push_cast
        ring

variable {D : D7}

theorem sum_locDeg_le (i : D.nd.Loc) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hS : ∀ v ∈ S, v ∈ placesOver D.host.E (D.nd.l i)) :
    ∑ w ∈ S, (locDeg D.host.E w : ℝ) ≤ 2 * D.R.f := by
  have hl := (D.nd.lPrime i).out
  refine le_trans ?_ (sum_nLam_le D hl)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro v hv
    exact (Set.Finite.mem_toFinset _).2 (hS v hv)
  · intro v _ _
    positivity

theorem card_le_sum_locDeg (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) :
    (S.card : ℝ) ≤ ∑ w ∈ S, (locDeg D.host.E w : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro v _
  exact_mod_cast nLam_pos D v

theorem vdel_nonneg (i : D.nd.Loc) : (0 : ℝ) ≤ (D.nd.vdel i : ℝ) := by
  have : (0 : ℚ) ≤ D.nd.vdel i := by
    unfold NData.vdel
    positivity
  exact_mod_cast this

theorem vdel_le (i : D.nd.Loc) {Λ : ℝ} (h : (D.nd.s0 i : ℝ) + 1 ≤ Λ) : (D.nd.vdel i : ℝ) ≤ D.R.t * Λ := by
  have := D.nd.lPrime i
  have h1 := LargeLevelLemmas.vdel_le i
  have hv : (padicValNat (D.nd.l i) D.R.t.factorial : ℚ) ≤ D.R.t := by
    exact_mod_cast padicValNat_factorial_le (D.nd.l i) D.R.t
  have h2 : D.nd.vdel i ≤ (D.R.t : ℚ) * ((D.nd.s0 i : ℚ) + 1) := by linarith
  have h3 : (D.nd.vdel i : ℝ) ≤ (D.R.t : ℝ) * ((D.nd.s0 i : ℝ) + 1) := by exact_mod_cast h2
  exact h3.trans (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _))

theorem split_arith {f m r t V Λ c y A A' k k' v e b h S : ℝ} (hm1 : 1 ≤ m) (hmf : m ≤ f) (hr0 : 0 ≤ r) (hrt : r ≤ t)
    (ht : 1 ≤ t) (hV : 1 ≤ V) (hΛ : 1 ≤ Λ) (hc : 1 ≤ c) (hA0 : 0 ≤ A) (hA : A ≤ 2 * f) (hA' : A' ≤ 2 * f)
    (hk0 : 0 ≤ k) (hk : k ≤ 2 * f) (hk' : k' ≤ 2 * f) (hv0 : 0 ≤ v) (hv : v ≤ t * Λ) (he0 : 0 ≤ e) (he : e ≤ c * y)
    (hb0 : 0 ≤ b) (hb : b ≤ c * t * f * V * Λ) (hh : h ≤ c * Λ)
    (hS : S ≤ A * (m * (2 * e + v)) + k * (e + 2 * v + 2 * (c * r * f * V * Λ))) :
    S + t * ((A' + 2 * k') * b) + 4 * V * (k + 1) * v + t * k * h ≤
      6 * c * f * m * y + 30 * c * f ^ 2 * t ^ 2 * V * Λ := by
  have hf : 1 ≤ f := hm1.trans hmf
  have hy : 0 ≤ c * y := he0.trans he
  have a1 : A * (m * (2 * e)) ≤ 4 * (c * f * m * y) := by
    calc A * (m * (2 * e)) ≤ (2 * f) * (m * (2 * (c * y))) := by gcongr
      _ = _ := by ring
  have a2 : k * e ≤ 2 * (c * f * m * y) := by
    calc k * e ≤ (2 * f) * (1 * (c * y)) := by rw [one_mul]; gcongr
      _ ≤ (2 * f) * (m * (c * y)) := by gcongr
      _ = _ := by ring
  have b1 : A * (m * v) ≤ 2 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc A * (m * v) ≤ (2 * f) * (f * (t * Λ)) := by gcongr
      _ = 2 * (1 * f ^ 2 * (t * 1) * 1 * Λ) := by ring
      _ ≤ 2 * (c * f ^ 2 * (t * t) * V * Λ) := by gcongr
      _ = _ := by ring
  have b2 : k * (2 * v) ≤ 4 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc k * (2 * v) ≤ (2 * f) * (2 * (t * Λ)) := by gcongr
      _ = 4 * (1 * (f * 1) * (t * 1) * 1 * Λ) := by ring
      _ ≤ 4 * (c * (f * f) * (t * t) * V * Λ) := by gcongr
      _ = _ := by ring
  have b3 : k * (2 * (c * r * f * V * Λ)) ≤ 4 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc k * (2 * (c * r * f * V * Λ)) ≤ (2 * f) * (2 * (c * t * f * V * Λ)) := by gcongr
      _ = 4 * (c * f ^ 2 * (t * 1) * V * Λ) := by ring
      _ ≤ 4 * (c * f ^ 2 * (t * t) * V * Λ) := by gcongr
      _ = _ := by ring
  have b4 : t * ((A' + 2 * k') * b) ≤ 6 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc t * ((A' + 2 * k') * b) ≤ t * ((6 * f) * (c * t * f * V * Λ)) := by gcongr; linarith
      _ = _ := by ring
  have b5 : 4 * V * (k + 1) * v ≤ 12 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc 4 * V * (k + 1) * v ≤ 4 * V * (3 * f) * (t * Λ) := by gcongr; linarith
      _ = 12 * (1 * (f * 1) * (t * 1) * V * Λ) := by ring
      _ ≤ 12 * (c * (f * f) * (t * t) * V * Λ) := by gcongr
      _ = _ := by ring
  have b6 : t * k * h ≤ 2 * (c * f ^ 2 * t ^ 2 * V * Λ) := by
    calc t * k * h ≤ t * k * (c * Λ) := by gcongr
      _ ≤ t * (2 * f) * (c * Λ) := by gcongr
      _ = 2 * (c * (f * 1) * (t * 1) * 1 * Λ) := by ring
      _ ≤ 2 * (c * (f * f) * (t * t) * V * Λ) := by gcongr
      _ = _ := by ring
  have e1 : A * (m * (2 * e + v)) + k * (e + 2 * v + 2 * (c * r * f * V * Λ)) =
      A * (m * (2 * e)) + A * (m * v) + k * e + k * (2 * v) + k * (2 * (c * r * f * V * Λ)) := by ring
  rw [e1] at hS
  linarith

theorem boundSplit_le (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) {c y Λ : ℝ} (hc : 1 ≤ c)
    (hs : (D.nd.s0 i : ℝ) + 1 ≤ Λ) (he : (e' : ℝ) ≤ c * y)
    (hc0 : ∀ u ∈ dc.col, (c0 u : ℝ) ≤ c * D.R.f * D.R.nV * Λ)
    (hW : ∀ u ∈ dc.col, (Br.h0W i u ρ π : ℝ) ≤ c * D.R.r * D.R.f * D.R.nV * Λ)
    (hB : (cB : ℝ) ≤ c * D.R.t * D.R.f * D.R.nV * Λ) (hh : (h0 D.nd i dc.col : ℝ) ≤ c * Λ) :
    (EmbeddingTypes.boundSplit i ρ π dc e' c0 cB : ℝ) ≤
      (Br.sPi D.loc D.nbr i ρ π : ℝ) +
        (6 * c * D.R.f * D.R.m * y + 30 * c * (D.R.f : ℝ) ^ 2 * (D.R.t : ℝ) ^ 2 * D.R.nV * Λ) +
        ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) +
        (padicValNat (D.nd.l i) (hE D.host) : ℝ) +
        (D.R.t : ℝ) * ((∑ v ∈ D.nd.Q i,
          lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) : ℚ) : ℝ) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, -⟩ := ranks D
  have hΛ : 1 ≤ Λ := by have : (0 : ℝ) ≤ D.nd.s0 i := Nat.cast_nonneg _; linarith
  have hrow := sum_locDeg_le i dc.row (fun v hv => (dc.cover v).1 (Or.inl hv))
  have hcol := sum_locDeg_le i dc.col (fun v hv => (dc.cover v).1 (Or.inr hv))
  have hr := card_le_sum_locDeg dc.row
  have hk := card_le_sum_locDeg dc.col
  have hsum : ∑ u ∈ dc.col, ((e' : ℝ) + (locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * ((e' : ℝ) + (D.nd.vdel i : ℝ)) +
        2 * (D.nd.vdel i : ℝ) + (Br.h0W i u ρ π : ℝ) + (locDeg D.host.E u : ℝ) * (D.R.m : ℝ) * (e' : ℝ) +
        (D.R.r : ℝ) * (c0 u : ℝ)) ≤
      (∑ u ∈ dc.col, (locDeg D.host.E u : ℝ)) * ((D.R.m : ℝ) * (2 * (e' : ℝ) + (D.nd.vdel i : ℝ))) +
        (dc.col.card : ℝ) * ((e' : ℝ) + 2 * (D.nd.vdel i : ℝ) + 2 * (c * D.R.r * D.R.f * D.R.nV * Λ)) := by
    rw [Finset.sum_mul, ← nsmul_eq_mul dc.col.card, ← Finset.sum_const, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have h4 := mul_le_mul_of_nonneg_left (hc0 u hu) (Nat.cast_nonneg (α := ℝ) D.R.r)
    have h5 := hW u hu
    nlinarith
  have key := split_arith r1 r2 (Nat.cast_nonneg _) r5 (by linarith) (by linarith) hΛ hc
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hcol hrow (Nat.cast_nonneg dc.col.card) (hk.trans hcol)
    (hr.trans hrow) (vdel_nonneg i) (vdel_le i hs) (Nat.cast_nonneg e') he (Nat.cast_nonneg cB) hB hh hsum
  have hrw : ∑ w ∈ dc.row, ((locDeg D.host.E w : ℝ) + 2) * (cB : ℝ) =
      ((∑ w ∈ dc.row, (locDeg D.host.E w : ℝ)) + 2 * (dc.row.card : ℝ)) * (cB : ℝ) := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  unfold EmbeddingTypes.boundSplit
  push_cast at key ⊢
  rw [hrw]
  linarith

end UpperTheory.N.Num

end
