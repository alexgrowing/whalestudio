import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetDivZero
import Formalism.LocalToGlobal.LatticeGeometry.RealizationNorms.MkTauEmbInjective
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.FlagAmple.BorelWeil

theorem sum_smul_telescope {M : Type*} [AddCommGroup M] (f : ℕ → ℤ) (g : ℕ → M) (n : ℕ) :
    ∑ b ∈ Finset.range n, f b • g b =
      ∑ i ∈ Finset.Ico 1 n, (f i - f (i - 1)) • -(∑ a ∈ Finset.range i, g a) +
        f (n - 1) • ∑ a ∈ Finset.range n, g a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_range_succ, ih, Finset.sum_Ico_succ_top hn, Finset.sum_range_succ (fun a => g a),
        Nat.add_sub_cancel]
      simp only [smul_add, smul_neg, sub_smul]
      abel

theorem fin_telescope {M : Type*} [AddCommGroup M] (m : ℕ) (G : Fin m → M) (F : Fin m → ℤ) :
    ∑ a, F a • G a =
      ∑ i : {i : Fin m // 0 < (i : ℕ)}, (F i.1 - F ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.1.isLt⟩) •
          -(∑ a : Fin m, if (a : ℕ) < i.1 then G a else 0) +
        (if h : 0 < m then F ⟨m - 1, Nat.sub_lt h one_pos⟩ else 0) • ∑ a : Fin m, (if (a : ℕ) < m then G a else 0) := by
  set f' : ℕ → ℤ := fun n => if h : n < m then F ⟨n, h⟩ else 0 with hf'
  set g' : ℕ → M := fun n => if h : n < m then G ⟨n, h⟩ else 0 with hg'
  have inner : ∀ i, i ≤ m → (∑ a : Fin m, if (a : ℕ) < i then G a else 0) = ∑ a ∈ Finset.range i, g' a := by
    intro i hi
    calc (∑ a : Fin m, if (a : ℕ) < i then G a else 0)
        = ∑ a : Fin m, (fun a : ℕ => if a < i then g' a else 0) (a : ℕ) :=
          Finset.sum_congr rfl fun a _ => by simp [g']
      _ = ∑ a ∈ Finset.range m, (if a < i then g' a else 0) := Fin.sum_univ_eq_sum_range (fun a : ℕ => if a < i then g' a else 0) m
      _ = ∑ a ∈ Finset.range i, g' a := by
          rw [← Finset.sum_filter]
          congr 1
          ext a
          simp only [Finset.mem_filter, Finset.mem_range]
          omega
  have h1 : ∑ a, F a • G a = ∑ b ∈ Finset.range m, f' b • g' b := by
    rw [← Fin.sum_univ_eq_sum_range (fun b => f' b • g' b)]
    simp [f', g']
  rw [h1, sum_smul_telescope, inner m le_rfl]
  congr 1
  · symm
    calc ∑ i : {i : Fin m // 0 < (i : ℕ)}, (F i.1 - F ⟨i.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.1.isLt⟩) •
          -(∑ a : Fin m, if (a : ℕ) < i.1 then G a else 0)
        = ∑ i ∈ Finset.univ.filter (fun i : Fin m => 0 < (i : ℕ)),
            (F i - F ⟨i - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩) •
              -(∑ a : Fin m, if (a : ℕ) < i then G a else 0) :=
          (Finset.sum_subtype _ (fun x => by simp) (fun i : Fin m =>
            (F i - F ⟨i - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩) •
              -(∑ a : Fin m, if (a : ℕ) < i then G a else 0))).symm
      _ = ∑ i : Fin m, (fun i : ℕ => if 0 < i then (f' i - f' (i - 1)) • -(∑ a ∈ Finset.range i, g' a) else 0)
            (i : ℕ) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs with h
          · rw [inner i i.isLt.le]
            simp [f', i.isLt, show (i : ℕ) - 1 < m by omega, h.ne']
          · simp [h]
      _ = ∑ i ∈ Finset.range m, (if 0 < i then (f' i - f' (i - 1)) • -(∑ a ∈ Finset.range i, g' a) else 0) :=
          Fin.sum_univ_eq_sum_range (fun i : ℕ => if 0 < i then (f' i - f' (i - 1)) • -(∑ a ∈ Finset.range i, g' a) else 0) m
      _ = _ := by
          rw [← Finset.sum_filter]
          congr 1
          ext a
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
          omega
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · simp [f', hm]

end GlobalTheory.FlagAmple.BorelWeil

namespace GlobalTheory.FlagAmple.BorelWeil

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem exists_steps (C : FlagCpt Z e) (f : Letter Dw → ℤ)
    (hf : ∀ τ (a b : Fin (Dw.mult τ)), a < b → f ⟨τ, a⟩ < f ⟨τ, b⟩) :
    ∃ (w : Step Dw → ℕ) (c : (E →+* ℂ) → ℤ), (∀ x, 0 < w x) ∧
      divOf C f = ∑ x : Step Dw, (w x : ℤ) • -detDiv C x.1 (x.2.1 : ℕ) + ∑ τ, c τ • detDiv C τ (Dw.mult τ) := by
  have hlt : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), 0 < (i : ℕ) →
      f ⟨τ, ⟨i - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩⟩ < f ⟨τ, i⟩ := fun τ i hi =>
    hf τ _ _ (Fin.lt_def.2 (by simp only; omega))
  refine ⟨fun x => (f ⟨x.1, x.2.1⟩ - f ⟨x.1, ⟨x.2.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.2.1.isLt⟩⟩).toNat,
    fun τ => if h : 0 < Dw.mult τ then f ⟨τ, ⟨Dw.mult τ - 1, Nat.sub_lt h one_pos⟩⟩ else 0, ?_, ?_⟩
  · rintro ⟨τ, i, hi⟩
    exact Int.lt_toNat.2 (sub_pos.2 (hlt τ i hi))
  · simp only [divOf, Fintype.sum_sigma, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [fin_telescope (Dw.mult τ) (C.gr τ) (fun a => f ⟨τ, a⟩)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.toNat_of_nonneg (sub_nonneg.2 (hlt τ i.1 i.2).le)]
    rfl

end GlobalTheory.FlagAmple.BorelWeil

namespace GlobalTheory.FlagAmple.BorelWeil

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem letterOf_inl_eq_some (τ : E →+* ℂ) (k : ℕ) (x : Letter Dw) :
    letterOf Dw (.inl (τ, k)) = some x ↔ τ = x.1 ∧ k = x.2 := by
  obtain ⟨τ', a⟩ := x
  simp only [letterOf]
  constructor
  · intro h
    split_ifs at h with hk
    · obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 (Option.some.inj h)
      exact ⟨rfl, by simpa [Fin.ext_iff] using h2⟩
  · rintro ⟨rfl, rfl⟩
    rw [dif_pos a.isLt]

open Classical in

theorem rootEx_apply (τ : E →+* ℂ) (i : ℕ) (x : Letter Dw) :
    rootEx Dw τ i x = if i < Dw.p then (if τ = x.1 ∧ i = x.2 then 1 else 0)
      else -(if conjEmb τ = x.1 ∧ Dw.p + Dw.q - 1 - i = x.2 then 1 else 0) := by
  simp only [rootEx, rootSym]
  split_ifs <;> rw [expo_single] <;> simp_all [letterOf_inl_eq_some]

end Letters

end GlobalTheory.FlagAmple.BorelWeil

namespace GlobalTheory.FlagAmple.BorelWeil

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad

section Places

variable {D : D7} (A : Amb D)

theorem conj_cmHostRoot_ne_self : (starRingEnd ℂ) A.H.rt0 ≠ A.H.rt0 := by
  intro h
  have him : A.H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
  have hre := congrArg Complex.re A.H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  have : (0 : ℝ) < A.H.d := by exact_mod_cast A.H.d_prime.pos
  nlinarith [mul_self_nonneg A.H.rt0.re]

theorem conjEmb_tauEmb_rt (t : D.what₂.Tau) : conjEmb (DV.tauEmb D t) (A.H.rt : D.host.E) ≠ A.H.rt0 := by
  simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, A.cm t]
  exact conj_cmHostRoot_ne_self A

theorem exists_of_places (τ : D.host.E →+* ℂ) : ∃ t, DV.tauEmb D t = τ ∨ conjEmb (DV.tauEmb D t) = τ := by
  have hb : Function.Bijective fun t => InfinitePlace.mk (DV.tauEmb D t) :=
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨Formalism.L2.Geo.Rec.StarEmbeddingNorm.mk_tauEmb_injective D, (Formalism.L2.Geo.Rec.StarEmbeddingNorm.card_places D).symm⟩
  obtain ⟨t, ht⟩ := hb.2 (InfinitePlace.mk τ)
  refine ⟨t, ?_⟩
  rcases InfinitePlace.mk_eq_iff.1 ht with h | h
  · exact Or.inl h
  · right
    rw [← h]
    ext x
    simp [conjEmb, ComplexEmbedding.conjugate_coe_eq]

theorem exists_tauEmb (τ : D.host.E →+* ℂ) (h : τ (A.H.rt : D.host.E) = A.H.rt0) : ∃ t, DV.tauEmb D t = τ := by
  obtain ⟨t, h1 | h1⟩ := exists_of_places τ
  · exact ⟨t, h1⟩
  · exact absurd (h1 ▸ h) (conjEmb_tauEmb_rt A t)

theorem exists_conjEmb (τ : D.host.E →+* ℂ) (h : τ (A.H.rt : D.host.E) ≠ A.H.rt0) :
    ∃ t, conjEmb (DV.tauEmb D t) = τ := by
  obtain ⟨t, h1 | h1⟩ := exists_of_places τ
  · exact absurd (h1 ▸ A.cm t) h
  · exact ⟨t, h1⟩

end Places

end GlobalTheory.FlagAmple.BorelWeil

namespace GlobalTheory.FlagAmple.BorelWeil

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

section Coeff

variable {D : D7} {A : Amb D} {N j : ℕ} (S : Sig A N j) (μ : Fin N → ℤ)

open Classical in

theorem coeff_cm (τ : D.host.E →+* ℂ) (hτ : τ (A.H.rt : D.host.E) = A.H.rt0) (a : Fin (S.Dw.mult τ))
    (ha : (a : ℕ) < N) :
    ∑ y : DV.Rt D.what₂.Tau N, μ y.2 * rootEx S.Dw (DV.tauEmb D y.1) y.2 ⟨τ, a⟩ =
      ∑ t, if DV.tauEmb D t = τ then μ ⟨a, ha⟩ else 0 := by
  have hp : (a : ℕ) < S.Dw.p := by
    have := a.isLt
    simp only [Datum.mult, if_pos hτ] at this
    exact this
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single ⟨a, ha⟩]
  · rw [rootEx_apply, if_pos hp]
    by_cases h : DV.tauEmb D t = τ <;> simp [h]
  · intro i _ hi
    rw [rootEx_apply]
    split_ifs with h1 h2 h3
    · exact absurd (Fin.ext h2.2) hi
    · simp
    · exact absurd (h3.1 ▸ hτ) (conjEmb_tauEmb_rt A t)
    · simp
  · simp

open Classical in

theorem coeff_conj (τ : D.host.E →+* ℂ) (hτ : τ (A.H.rt : D.host.E) ≠ A.H.rt0) (a : Fin (S.Dw.mult τ))
    (hi : S.Dw.p + S.Dw.q - 1 - a < N) :
    ∑ y : DV.Rt D.what₂.Tau N, μ y.2 * rootEx S.Dw (DV.tauEmb D y.1) y.2 ⟨τ, a⟩ =
      ∑ t, if conjEmb (DV.tauEmb D t) = τ then -μ ⟨S.Dw.p + S.Dw.q - 1 - a, hi⟩ else 0 := by
  have hq : (a : ℕ) < S.Dw.q := by
    have := a.isLt
    simp only [Datum.mult, if_neg hτ] at this
    exact this
  have hN := S.rank_eq
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single ⟨S.Dw.p + S.Dw.q - 1 - a, hi⟩]
  · have e : S.Dw.p + S.Dw.q - 1 - (S.Dw.p + S.Dw.q - 1 - (a : ℕ)) = a := by omega
    rw [rootEx_apply]
    dsimp only
    rw [if_neg (by omega)]
    by_cases h : conjEmb (DV.tauEmb D t) = τ <;> simp [h, e]
  · intro i _ hne
    rw [rootEx_apply]
    dsimp only
    split_ifs with h1 h2 h3
    · exact absurd (h2.1 ▸ A.cm t) hτ
    · simp
    · exact absurd (Fin.ext (by have := i.isLt; simp only; omega)) hne
    · simp
  · simp

end Coeff

end GlobalTheory.FlagAmple.BorelWeil

namespace GlobalTheory.FlagAmple.BorelWeil

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O

theorem lmu_div_eq (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp)
    (μ : Fin N → ℤ) (hμ : StrictAnti μ) :
    ∃ (w : GlobalTheory.FlagAmple.Step S.Dw → ℕ) (c : (D.host.E →+* ℂ) → ℤ), (∀ x, 0 < w x) ∧
      -∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootEx S.Dw (DV.tauEmb D x.1) x.2) =
        ∑ x : GlobalTheory.FlagAmple.Step S.Dw, (w x : ℤ) • -GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ) +
          ∑ τ : D.host.E →+* ℂ, c τ • GlobalTheory.FlagAmple.detDiv (Φ.C k) τ (S.Dw.mult τ) := by
  classical
  set f : Letter S.Dw → ℤ :=
    fun x => -∑ y : DV.Rt D.what₂.Tau N, μ y.2 * rootEx S.Dw (DV.tauEmb D y.1) y.2 x with hf
  have hL : -∑ x : DV.Rt D.what₂.Tau N, μ x.2 • divOf (Φ.C k) (rootEx S.Dw (DV.tauEmb D x.1) x.2) =
      divOf (Φ.C k) f := by
    simp only [divOf, hf, Finset.smul_sum, smul_smul, neg_smul, Finset.sum_smul, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have hmono : ∀ τ (a b : Fin (S.Dw.mult τ)), a < b → f ⟨τ, a⟩ < f ⟨τ, b⟩ := by
    intro τ a b hab
    have hab' : (a : ℕ) < b := hab
    have hN := S.rank_eq
    by_cases hτ : τ (A.H.rt : D.host.E) = A.H.rt0
    · have hm : S.Dw.mult τ = S.Dw.p := if_pos hτ
      have ha : (a : ℕ) < N := by have := a.isLt; omega
      have hb : (b : ℕ) < N := by have := b.isLt; omega
      have hμab : μ ⟨b, hb⟩ < μ ⟨a, ha⟩ := hμ (Fin.mk_lt_mk.2 hab')
      simp only [hf, coeff_cm S μ τ hτ a ha, coeff_cm S μ τ hτ b hb, neg_lt_neg_iff]
      obtain ⟨t0, ht0⟩ := exists_tauEmb A τ hτ
      apply Finset.sum_lt_sum
      · intro t _
        split_ifs
        · exact hμab.le
        · exact le_rfl
      · exact ⟨t0, Finset.mem_univ _, by simp only [ht0, if_true]; exact hμab⟩
    · have hm : S.Dw.mult τ = S.Dw.q := if_neg hτ
      have ha : S.Dw.p + S.Dw.q - 1 - (a : ℕ) < N := by have := a.isLt; omega
      have hb : S.Dw.p + S.Dw.q - 1 - (b : ℕ) < N := by have := b.isLt; omega
      have hμab : μ ⟨_, ha⟩ < μ ⟨_, hb⟩ := hμ (Fin.mk_lt_mk.2 (by have := b.isLt; omega))
      simp only [hf, coeff_conj S μ τ hτ a ha, coeff_conj S μ τ hτ b hb, neg_lt_neg_iff]
      obtain ⟨t0, ht0⟩ := exists_conjEmb A τ hτ
      apply Finset.sum_lt_sum
      · intro t _
        split_ifs
        · exact neg_le_neg hμab.le
        · exact le_rfl
      · exact ⟨t0, Finset.mem_univ _, by simp only [ht0, if_true]; exact neg_lt_neg hμab⟩
  obtain ⟨w, c, hw, h⟩ := exists_steps (Φ.C k) f hmono
  exact ⟨w, c, hw, hL.trans h⟩

end GlobalTheory.FlagAmple.BorelWeil
