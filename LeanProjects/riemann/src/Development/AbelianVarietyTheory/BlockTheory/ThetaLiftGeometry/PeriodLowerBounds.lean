import Mathlib
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodLowerBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain
open scoped BigOperators

def perBound {D : D7} (L : SizeData₂ D) (X : ErrX D) (C1 : ℝ) (i : Fin 2) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) : ℝ :=
  -(∑ j ∈ SizeData₂.lifts D, vNN X i u j w) -
    C1 * ((D.R.f : ℝ) * ((D.R.m : ℝ) * (D.R.N D.R.m : ℝ) * ((D.R.N D.R.m : ℝ) + (D.R.t : ℝ)) +
      (D.R.m : ℝ) ^ 3 * L.etaSz))

def PerGe_vw (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (φ : (D.div.Nu u).V)
    (F : D.what₂.Amb μ) (s : ℝ) : Prop :=
  ∃ y : D.what₂.LL, D.what₂.embLL y = D.what₂.perCol u μ (D.jN u φ) F ∧
    (y = 0 ∨ s ≤ (vAdd (D.plEq w) y : ℝ))

def ExpLe {D : D7} (L : SizeData₂ D) (X : ErrX D) (C1 : ℝ) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    L.sg u w ≤ perBound L X C1 i u w

def PeriodBound {D : D7} (L : SizeData₂ D) (X : ErrX D) (C1 : ℝ) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    D.what₂.places.resChar w ≠ (D.mem u).A.T → ∀ μ : D.what₂.Tup, DV.Used D μ →
    ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
      PerGe_vw D u μ w φ F (DV.ur D w (perBound L X C1 i u w))

def LinkRam {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    ∀ μ : D.what₂.Tup, DV.Used D μ → ∀ φ ∈ DV.MramL D u, ∀ F ∈ (D.what₂.Mtilde μ).carrier,
      PerGe_vw D u μ w φ F (DV.ur D w (L.sg u w))

def LinkNu {D : D7} (L : SizeData₂ D) : Prop :=
  ∀ (i : Fin 2) (w : D.what₂.places.Pl), D.what₂.places.resChar w = D.host.g i → ∀ u : D.what₂.Word,
    ∀ φ ∈ L.NuLat u, ∀ F ∈ (D.what₂.Mtilde (D.what₂.muAt w)).carrier,
      PerGe_vw D u (D.what₂.muAt w) w φ F (DV.ur D w (L.sg u w))

def ErrorExponentStatement (D : D7) (L : SizeData₂ D) (X : ErrX D) (lev : LevelData D) (K : Consts) (c : ErrC) (C1 : ℝ) : Prop :=
  L.FDef → ErrDefs D L X lev K c → 2 * C1 ≤ c.g →
    ExpLe L X C1 ∧ (PeriodBound L X C1 → LinkRam L ∧ (DV.NuDef D L → LinkNu L))

def Stmt : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (X : ErrX D) (lev : LevelData D) (K : Consts) (c : ErrC) (C1 : ℝ), ErrorExponentStatement D L X lev K c C1

def FamilyErrorExponentBound {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) : Prop :=
  2 * C1 ≤ Fm.cX.err.g → ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x),
    ExpLe (Fm.L x i) (Fm.ex x hx i).errX C1 ∧
      (PeriodBound (Fm.L x i) (Fm.ex x hx i).errX C1 → LinkRam (Fm.L x i) ∧ LinkNu (Fm.L x i))

theorem stmtFam_of (h : Stmt) {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) : FamilyErrorExponentBound Fm C1 := fun hC x hx i =>
  have h1 := h _ (Fm.L x i) (Fm.ex x hx i).errX (Fm.ex x hx i).lev Fm.GK Fm.cX.err C1
    (Fm.ex x hx i).fdef (Fm.ex x hx i).err hC
  ⟨h1.1, fun hP => ⟨(h1.2 hP).1, (h1.2 hP).2 (Fm.nuDef x hx i)⟩⟩

theorem T_ne_g {D : D7} (X : ErrX D) (u : D.what₂.Word) (i : Fin 2) : D.host.g i ≠ (D.mem u).A.T := by
  intro h
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.1 (X.piT_cong u)
  have hdiv : ∃ b : 𝓞 D.host.E, X.piT u = 1 + (D.host.g i : 𝓞 D.host.E) * b := by
    have hd : D.host.g i ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
      refine Dvd.dvd.mul_left (Dvd.dvd.pow ?_ two_ne_zero) _
      fin_cases i
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    obtain ⟨k, hk⟩ := hd
    refine ⟨k * a, ?_⟩
    rw [hk] at ha
    push_cast at ha
    linear_combination ha
  obtain ⟨b, hb⟩ := hdiv
  have hn := X.piT_norm u
  rw [← h, hb] at hn
  have hbi : IsIntegral ℤ (D.host.conj (b : D.host.E)) :=
    (IsIntegral.map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom b.isIntegral_coe)
  set b' : 𝓞 D.host.E := ⟨_, hbi⟩ with hb'
  have hu : (D.host.g i : 𝓞 D.host.E) * (1 - b - b' - D.host.g i * b * b') = 1 := by
    apply Subtype.ext
    have e : ((b' : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
    simp only [map_add, map_mul, map_one, map_natCast] at hn
    change algebraMap _ D.host.E ((D.host.g i : 𝓞 D.host.E) * (1 - b - b' - D.host.g i * b * b')) = algebraMap _ D.host.E (1 : 𝓞 D.host.E)
    simp only [map_sub, map_mul, map_one, map_natCast]
    change _ * (1 - (b : D.host.E) - (b' : D.host.E) - _ * (b : D.host.E) * (b' : D.host.E)) = 1
    rw [e]
    linear_combination -hn
  have hunit : IsUnit ((D.host.g i : ℤ)) := by
    have : IsUnit (algebraMap ℤ (𝓞 D.host.E) (D.host.g i : ℤ)) := by
      simpa using IsUnit.of_mul_eq_one _ hu
    exact isUnit_of_map_unit (algebraMap ℤ (𝓞 D.host.E)) _ this
  have := Int.isUnit_iff.1 hunit
  have h2 := (D.host.g_prime i).two_le
  omega

theorem expLe_of {D : D7} {L : SizeData₂ D} {X : ErrX D} {lev : LevelData D} {K : Consts} {c : ErrC} {C1 : ℝ}
    (hF : L.FDef) (hE : ErrDefs D L X lev K c) (hC : 2 * C1 ≤ c.g) : ExpLe L X C1 := by
  intro i w hw u
  have hT : D.what₂.places.resChar w ≠ (D.mem u).A.T := hw ▸ T_ne_g X u i
  have hmem : D.what₂.places.resChar w ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
    rw [hw]; fin_cases i <;> simp
  have hterm : ∀ j ∈ SizeData₂.lifts D, L.gainD j w + L.F j w - L.E u j w ≤
      -vNN X i u j w - c.g * (D.R.f : ℝ) * (Nm D ^ 2 + (D.R.m : ℝ) ^ 2 * L.etaSz) := by
    intro j hj
    have h1 : L.gainD j w = 0 := by
      unfold SizeData₂.gainD; rw [L.gain_g j w hmem]; simp
    have h2 : L.F j w = FTypeG D j := by
      rw [hF j hj w]; unfold Fval FvalP SizeData₂.gTypes; rw [if_pos hmem]
    have h3 : EatG L X c i u j w ≤ L.E u j w := by
      rw [hE.edef u j hj w]
      unfold Eval
      simp only [if_neg hT]
      have h0 : (0 : ℝ) ≤ (padicValNat (D.what₂.places.resChar w) (D.mem u).C.DGam : ℝ) := Nat.cast_nonneg _
      fin_cases i
      · rw [if_pos (by simpa using hw)]; simpa using h0
      · rw [if_neg (by rw [hw]; exact fun h => D.host.g_ne h.symm), if_pos (by simpa using hw)]; simpa using h0
    unfold EatG at h3
    linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const]
  unfold perBound Nm
  have hcard : (SizeData₂.lifts D).card = D.R.m := by simp [SizeData₂.lifts]
  rw [hcard, nsmul_eq_mul]
  have htN : (D.R.t : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have := D.R.two_le_m
    exact_mod_cast (by unfold Ranks.N; nlinarith : D.R.t ≤ D.R.N D.R.m)
  have hg : (10 : ℝ) ≤ c.g := hE.large.2.2
  have he := L.etaSz_pos
  set N : ℝ := (D.R.N D.R.m : ℝ)
  set t : ℝ := (D.R.t : ℝ)
  set m : ℝ := (D.R.m : ℝ)
  set f : ℝ := (D.R.f : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have ht : 0 ≤ t := Nat.cast_nonneg _
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hf : 0 ≤ f := Nat.cast_nonneg _
  have hA : 0 ≤ f * (m * N * (N + t) + m ^ 3 * L.etaSz) := by positivity
  have hB : f * (m * N * (N + t) + m ^ 3 * L.etaSz) ≤ 2 * (m * (f * (N ^ 2 + m ^ 2 * L.etaSz))) := by
    have a1 : 0 ≤ f * m * N * (N - t) := by have := sub_nonneg.2 htN; positivity
    have a2 : 0 ≤ f * m ^ 3 * L.etaSz := by positivity
    nlinarith
  have h1 : C1 * (f * (m * N * (N + t) + m ^ 3 * L.etaSz)) ≤ c.g / 2 * (f * (m * N * (N + t) + m ^ 3 * L.etaSz)) :=
    mul_le_mul_of_nonneg_right (by linarith) hA
  have h2 := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ c.g / 2)
  nlinarith

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodLowerBounds

end
