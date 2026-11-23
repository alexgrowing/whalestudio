import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualMapCompStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootTowerUniformHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareThirdStatement
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrRef

section Chart

open GlobalTheory.CompanionTheory.Ar.Cmp

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω] {J : Type}

theorem one_mem_left (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (e₁ : J ≃ ι₁ k₁) (e₂ : J ≃ ι₂ k₂) (h : ∀ a, y₁ ⟨k₁, e₁ a⟩ = y₂ ⟨k₂, e₂ a⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = 1) (hd₂ : d (Sum.inr k₂) = -1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0) :
    (1 : Ω) ∈ chartLatNm (joinVec y₁ y₂) d 1 := by
  classical
  intro c _
  have key : ∀ x : ι₂ k₂, y₂ ⟨k₂, x⟩ = y₁ ⟨k₁, e₁ (e₂.symm x)⟩ := fun x => by
    rw [h, Equiv.apply_symm_apply]
  have hmem : 1 * ∏ k, joinVec y₁ y₂ ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * d k)) ∈ chartRingZ (joinVec y₁ y₂) c := by
    rw [one_mul, Finset.prod_eq_mul (Sum.inl k₁) (Sum.inr k₂) (by simp)
      (fun k _ hk => by simp [hd k hk.1 hk.2]) (by simp) (by simp), hd₁, hd₂]
    have hg : y₁ ⟨k₁, e₁ (e₂.symm (c (Sum.inr k₂)))⟩ / joinVec y₁ y₂ ⟨Sum.inl k₁, c (Sum.inl k₁)⟩ ∈
        chartRingZ (joinVec y₁ y₂) c :=
      Algebra.subset_adjoin ⟨joinInl ι₁ ι₂ ⟨k₁, e₁ (e₂.symm (c (Sum.inr k₂)))⟩, rfl⟩
    have e : joinVec y₁ y₂ ⟨Sum.inr k₂, c (Sum.inr k₂)⟩ = y₁ ⟨k₁, e₁ (e₂.symm (c (Sum.inr k₂)))⟩ :=
      key (c (Sum.inr k₂))
    rw [e]
    convert hg using 1
    simp [div_eq_mul_inv, mul_comm]
  exact isIntegral_algebraMap (R := chartRingZ (joinVec y₁ y₂) c) (x := ⟨_, hmem⟩)

theorem one_mem_right (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (e₁ : J ≃ ι₁ k₁) (e₂ : J ≃ ι₂ k₂) (h : ∀ a, y₁ ⟨k₁, e₁ a⟩ = y₂ ⟨k₂, e₂ a⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = -1) (hd₂ : d (Sum.inr k₂) = 1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0) :
    (1 : Ω) ∈ chartLatNm (joinVec y₁ y₂) d 1 := by
  classical
  intro c _
  have key : ∀ x : ι₁ k₁, y₁ ⟨k₁, x⟩ = y₂ ⟨k₂, e₂ (e₁.symm x)⟩ := fun x => by
    rw [← h, Equiv.apply_symm_apply]
  have hmem : 1 * ∏ k, joinVec y₁ y₂ ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * d k)) ∈ chartRingZ (joinVec y₁ y₂) c := by
    rw [one_mul, Finset.prod_eq_mul (Sum.inl k₁) (Sum.inr k₂) (by simp)
      (fun k _ hk => by simp [hd k hk.1 hk.2]) (by simp) (by simp), hd₁, hd₂]
    have hg : y₂ ⟨k₂, e₂ (e₁.symm (c (Sum.inl k₁)))⟩ / joinVec y₁ y₂ ⟨Sum.inr k₂, c (Sum.inr k₂)⟩ ∈
        chartRingZ (joinVec y₁ y₂) c :=
      Algebra.subset_adjoin ⟨joinInr ι₁ ι₂ ⟨k₂, e₂ (e₁.symm (c (Sum.inl k₁)))⟩, rfl⟩
    have e : joinVec y₁ y₂ ⟨Sum.inl k₁, c (Sum.inl k₁)⟩ = y₂ ⟨k₂, e₂ (e₁.symm (c (Sum.inl k₁)))⟩ :=
      key (c (Sum.inl k₁))
    rw [e]
    convert hg using 1
    simp [div_eq_mul_inv]
  exact isIntegral_algebraMap (R := chartRingZ (joinVec y₁ y₂) c) (x := ⟨_, hmem⟩)

end Chart

theorem vertBound_mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {c c' : ℝ} (h : Ht.VertBound y a u c) (hc : c ≤ c') :
    Ht.VertBound y a u c' := by
  obtain ⟨hu, q, m, hq, hm, hl, h₁, h₂⟩ := h
  refine ⟨hu, q, m, hq, hm, hl.trans ?_, h₁, h₂⟩
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q)

theorem archBetween_mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {M R : Top.RootModel Ψ N} {i : R.Ω →+* M.Ω}
    {u : Option (Ψ × Fin N) → M.Ω} {t : ℝ} {lam : Top.Wt Ψ N} {s lo hi lo' hi' : ℝ}
    (h : Ht.ArchBetween M R i u t lam s lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') :
    Ht.ArchBetween M R i u t lam s lo' hi' :=
  fun z hz val hv => Set.Icc_subset_Icc hl hh (h z hz val hv)

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}
  {S S₀ : Finset ℕ} {M R : Top.RootModel (CMType H) (D.p + D.q)}

theorem vertBound_none (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω)
    (hi : i.comp o₀.g = o.g) {b : ℝ} (hb : 0 ≤ b) :
    Ht.VertBound (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 b := by
  classical
  have hy : ∀ a, M.y ⟨o.k₀, o.ix a⟩ = i (R.y ⟨o₀.k₀, o₀.ix a⟩) := fun a => by
    rw [o.y_eq, o₀.y_eq, ← hi]; rfl
  have hd₁ : Ht.joinDeg M R none (Sum.inl o.k₀) = 1 := o.A_deg.1
  have hd₂ : Ht.joinDeg M R none (Sum.inr o₀.k₀) = -1 := by
    show -(R.A.a o₀.k₀) = -1
    rw [o₀.A_deg.1]
  have hd : ∀ k, k ≠ Sum.inl o.k₀ → k ≠ Sum.inr o₀.k₀ → Ht.joinDeg M R none k = 0 := by
    rintro (k | k) h₁ h₂
    · exact o.A_deg.2 k fun e => h₁ (congrArg _ e)
    · show -(R.A.a k) = 0
      rw [o₀.A_deg.2 k fun e => h₂ (congrArg _ e), neg_zero]
  refine ⟨one_ne_zero, 1, 1, one_pos, one_pos, by simpa using hb, ?_, ?_⟩
  · have h₁ : (1 : M.Ω) ∈ chartLatNm (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 :=
      one_mem_left M.y (fun p => i (R.y p)) o.ix o₀.ix hy _ hd₁ hd₂ hd
    simpa using h₁
  · have h₂ : (1 : M.Ω) ∈ chartLatNm (Ht.joinOf M R i) (-Ht.joinDeg M R none) 1 :=
      one_mem_right M.y (fun p => i (R.y p)) o.ix o₀.ix hy (-Ht.joinDeg M R none)
        (by simp [hd₁]) (by simp [hd₂]) (fun k h₁ h₂ => by simp [hd k h₁ h₂])
    simpa using h₂

theorem exists_comparison (o₀ : RootOrigin Y S₀ R Fx) (h₀ : o₀.Fl.deg = 1) (o : RootOrigin Y S M Fx) :
    ∃ i : R.Ω →+* M.Ω, i.comp o₀.g = o.g := by
  have hb : Function.Bijective o₀.g := by
    refine ⟨o₀.g.injective, fun x => ?_⟩
    letI := o₀.g.toAlgebra
    have h1 : Module.finrank Fx.Ωf R.Ω = 1 := o₀.g_deg.trans h₀
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : R.Ω) one_ne_zero).mp h1 x
    refine ⟨a, ?_⟩
    rw [← ha, Algebra.smul_def, mul_one]
    rfl
  refine ⟨o.g.comp (RingEquiv.ofBijective o₀.g hb).symm.toRingHom, ?_⟩
  ext x
  have : (RingEquiv.ofBijective o₀.g hb).symm (o₀.g x) = x :=
    (RingEquiv.ofBijective o₀.g hb).symm_apply_apply x
  simp [this]

theorem genUnit_some (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω)
    (hi : i.comp o₀.g = o.g) (r : RootIx D) :
    Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) := by
  refine GlobalTheory.T.root_model_flag_compare E H D l Xo c Y S S₀ M R o.𝔐 o₀.𝔐 o.Fl o₀.Fl i o.e o₀.e ?_ ?_ o.lines o₀.lines r
  · rw [o.g_over, o₀.g_over, ← hi, spMap_comp, Category.assoc]
  · intro s k
    rw [o.g_flag, o₀.g_flag, ← hi, dualMap_comp, spMap_comp, Category.assoc]

open GroundTheory.Heights₂.Heights.Model in

theorem sum_bound {T : Top.RootTower (CMType H) (D.p + D.q)} [DecidableEq (CMType H)] (o : TowerOrigin Y T) :
    ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∑ p ∈ o.S B, ((if p = 2 then 2 else 1 / ((p : ℝ) - 1)) +
      2 * padicValInt p (discr E)) * Real.log p ≤ C * Real.log B := by
  have hE : discr E ≠ 0 := discr_ne_zero E
  have hM : ((l.M' : ℕ) : ℤ) ≠ 0 := by
    have h₁ : l.M ≠ 0 := by have := l.three_le; omega
    have h₂ : l.A ≠ 0 := l.A_pos.ne'
    exact_mod_cast Nat.lcm_ne_zero h₁ h₂
  have h2M : (2 * (l.M' : ℤ)) ≠ 0 := mul_ne_zero two_ne_zero hM
  obtain ⟨C, hC⟩ := SumCp.full (discr E * (2 * (l.M' : ℤ))) (mul_ne_zero hE h2M)
  refine ⟨C, fun B hB => ?_⟩
  have hS : ∀ p ∈ o.S B, p.Prime ∧ ((p : ℝ) ≤ (B : ℝ) ∨ (p : ℤ) ∣ discr E * (2 * (l.M' : ℤ))) := by
    intro p hp
    obtain ⟨hpp, h | h⟩ := (o.S_iff B p).mp hp
    · exact ⟨hpp, Or.inl (by exact_mod_cast h)⟩
    · refine ⟨hpp, Or.inr ?_⟩
      have := ((o.bad_iff p).mp h).2
      convert this using 1
      ring
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) (hC B (by exact_mod_cast hB) _ hS)
  have hpp := (hS p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  refine mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le))
  rw [padicValInt.mul hE h2M]
  simp only [primeWeight]
  push_cast
  nlinarith [(Nat.cast_nonneg (padicValInt p (2 * (l.M' : ℤ))) : (0 : ℝ) ≤ _)]

theorem has_ref : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (g : Top.GoodOrigin Y T), (∀ B a, ∀ p ∈ g.S B, ∃ κ, HT.IsCp p κ ∧ HT.Sandwich (g.Or B a).𝔐 p κ) → Ht.HasRef T g.R := by
  intro E _ _ _ H D l Xo c Y _ T g hS
  have hC₀ := fun a => GlobalTheory.T.exists_uniform_height_constant_alt E H D l Xo c Y (g.Sys a) (g.Fx a) (g.R a) (g.refOr a)
  choose C₀ hC₀ using hC₀
  obtain ⟨C₂, s₀, hs₀, hA⟩ := GlobalTheory.T.root_tower_uniform_height_bound E H D l Xo c Y T g
  obtain ⟨C₃, hC₃⟩ := sum_bound g.toTowerOrigin
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₁ : ℝ := ∑ a, |C₀ a| with hC₁
  have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₁a : ∀ a, C₀ a ≤ C₁ := fun a => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun a => |C₀ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
  set C : ℝ := C₁ / Real.log 2 + |C₃| + |C₂| + 1 with hC
  have hCC₂ : C₂ ≤ C := by
    have := le_abs_self C₂
    have : 0 ≤ C₁ / Real.log 2 := div_nonneg hC₁0 hl2.le
    have := abs_nonneg C₃
    linarith
  have hC0 : 0 ≤ C := by
    have : 0 ≤ C₁ / Real.log 2 := div_nonneg hC₁0 hl2.le
    have := abs_nonneg C₃
    have := abs_nonneg C₂
    linarith
  refine ⟨C, min s₀ 1, lt_min hs₀ one_pos, fun B hB a => ?_⟩
  have hlB : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have hlB0 : 0 < Real.log B := hl2.trans_le hlB
  obtain ⟨i, hi⟩ := exists_comparison (g.refOr a) (g.ref_deg a) (g.Or B a)
  refine ⟨i, fun j => j.elim 1 fun r => i ((g.refOr a).e r) / (g.Or B a).e r, ?_, ?_⟩
  · refine ⟨by rw [(g.Or B a).kA_eq, (g.refOr a).kA_eq], ?_, ?_⟩
    · rintro (_ | r)
      · exact (GlobalTheory.T.root_origin_compare_third E H D l Xo c Y (g.S B) ∅ (T.M B a) (g.R a) (g.Sys a) (g.Fx a) (g.Or B a)
          (g.refOr a) i hi).1
      · exact genUnit_some (g.Or B a) (g.refOr a) i hi r
    · rintro (_ | r)
      · exact vertBound_none (g.Or B a) (g.refOr a) i hi (mul_nonneg hC0 hlB0.le)
      · have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ g.S B := by
          intro p hp hd
          refine (g.S_iff B p).mpr ⟨hp, Or.inr ((g.bad_iff p).mpr ⟨hp, ?_⟩)⟩
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _
        refine vertBound_mono (hC₀ a (g.S B) (T.M B a) (g.Or B a) i hi hdisc (hS B a) r) ?_
        have h₃ := hC₃ B hB
        have h₄ : C₁ ≤ C₁ / Real.log 2 * Real.log B := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
          exact mul_le_mul_of_nonneg_left hlB hC₁0
        have h₅ : C₃ * Real.log B ≤ |C₃| * Real.log B :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hlB0.le
        have h₆ : 0 ≤ (|C₂| + 1) * Real.log B := mul_nonneg (by positivity) hlB0.le
        have h₇ := hC₁a a
        rw [hC]
        nlinarith
  · intro mu s hmu hn hs hs'
    have hs₁ : s ≤ s₀ := hs'.trans (min_le_left _ _)
    have hs₂ : s ≤ 1 := hs'.trans (min_le_right _ _)
    have hlog : 0 ≤ Real.log (1 / s) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
    refine archBetween_mono (hA B a i hi mu s hmu hn hs hs₁) ?_ hCC₂
    have := mul_le_mul_of_nonneg_right hCC₂ hlog
    linarith

end GlobalTheory.CompanionTheory.Ar.OrRef
