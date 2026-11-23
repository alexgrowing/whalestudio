import Development.WeilBound.CoreStatements.ProjectiveValuations.FrequentlyNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsEvenSecEvRNeZero

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology

def Tw (V : Unf Xo c σ r) (e : Ix D → ℤ) (k : V.Comp) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r) : Prop :=
  ∀ y : FrPt Xo c (CAt σ), ∃ (a a₀ : (E →+* ℂ) × ℕ → ℕ) (n n₀ : ℕ) (g : Rul Xo c), Dom a n ∧ NV Xo c σ a n ∧ Dom a₀ n₀ ∧
    g ∈ sec Xo c a₀ n₀ ∧ (fun i => (ex D a n i : ℤ)) = e + (fun i => (ex D a₀ n₀ i : ℤ)) ∧
    laU V a n k = la + laU V a₀ n₀ k ∧ evR Xo c g y ≠ 0

theorem isSec_mul {X : Data E r} {la la' : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · have hdiag : ∀ τ i, b τ i i ≠ 0 := fun τ i => by
      have hdet := (hb τ).1
      rw [Matrix.det_of_isUpperTriangular (M := mat b τ) (fun a c hac => (hb τ).2 a c hac)] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
    have hadd : bchar (la + la') b = bchar la b * bchar la' b := by
      simp only [bchar, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_
      rw [Pi.add_apply, Pi.add_apply, zpow_add₀ (hdiag τ i)]
    show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, hadd]
    ring
  · show P _ * Q _ = _ * (P x * Q x)
    rw [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem sec_frBorZ {V : Unf Xo c σ r} (hU : IsUnf V) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {x x' : (V.X k).dom} {t : Ix D → (CAt σ)ˣ} (ht : FrBor t (V.un k x) (V.un k x')) :
    P x'.1 = chr e t * P x.1 := by
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT (V.un k x)
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  have h1 : P x'.1 * rdU V g k x'.1 = chr (fun i => (ex D a n i : ℤ)) t * (P x.1 * rdU V g k x.1) :=
    sec_frBor hU hD hN hPg ht
  rw [rdU_eq, rdU_eq, DifferentiableLines.evR_frBor hg ht, he, chr_add] at h1
  refine mul_right_cancel₀ (mul_ne_zero (chr_ne_zero (fun i => (ex D a₀ n₀ i : ℤ)) t)
    (show toC (evR Xo c g (V.un k x)) ≠ 0 from hg0)) ?_
  rw [h1]
  ring

theorem open_secZ {V : Unf Xo c σ r} (hU : IsUnf V) (T : TorFlag Xo c) {e : Ix D → ℤ} {k : V.Comp}
    {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la) {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) :
    ∃ h ∈ GlobalTheory.CxPts.fibSec (flagStr T.X) σ (T.X.LL e), Reads V T e k P h ∧ OffZero V T k h := by
  classical
  obtain ⟨-, g1, g2, g3⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  have hex : ∀ (i : T.X.F.J) (z : Sp (CAt σ) ⟶ T.X.YY), ∃ v : ℂ,
      (∀ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q → FrBor t Q (V.un k x) → P x.1 = chr e t * v) ∧
      ((¬ ⊤ ≤ z ⁻¹ᵁ T.X.F.U i ∨ ∀ x : (V.X k).dom, T.X.ptY (V.un k x) ≠ z) → v = 0) := by
    intro i z
    by_cases h : ∃ (x : (V.X k).dom) (hz : ⊤ ≤ z ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
        T.X.F.ChartFr i z hz Q ∧ FrBor t Q (V.un k x)
    · obtain ⟨x₀, hz₀, Q₀, t₀, hQ₀, ht₀⟩ := h
      refine ⟨(chr e t₀)⁻¹ * P x₀.1, fun x hz Q t hQ ht => ?_, fun h => ?_⟩
      · obtain rfl : Q₀ = Q := hQ₀.unique hQ
        have h1 := sec_frBorZ hU hT hP (g1 _ _ _ _ _ (g2 _ _ _ ht₀) ht)
        have h2 : chr e t = chr e t₀ * chr e (t₀⁻¹ * t) := by rw [← chr_mul, mul_inv_cancel_left]
        rw [h1, h2]
        have := chr_ne_zero e t₀
        field_simp
        try exact mul_comm _ _
      · exact (h.elim (fun h => h hz₀) fun h =>
          h x₀ (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ₀.lies.frBor ht₀)).symm).elim
    · exact ⟨0, fun x hz Q t hQ ht => (h ⟨x, hz, Q, t, hQ, ht⟩).elim, fun _ => rfl⟩
  choose v hv hv0 using hex
  refine ⟨fun i y => v i y.1, ⟨fun i j y hi hj => ?_, fun i y hi => hv0 i y.1 (Or.inl hi)⟩,
    fun x hx i y hz Q t _ hQ ht => hv i y.1 ⟨x, hx⟩ hz Q t hQ ht,
    fun i y h => hv0 i y.1 (Or.inr fun x => h x.1 x.2)⟩
  by_cases h : ∃ x : (V.X k).dom, T.X.ptY (V.un k x) = y.1
  · obtain ⟨x, hx⟩ := h
    obtain ⟨Q, t, hQ, ht⟩ := exists_chart_frBor T (V.un k x) i hx hi
    obtain ⟨Q', t', hQ', ht'⟩ := exists_chart_frBor T (V.un k x) j hx hj
    have hh : ⊤ ≤ (y.1 : Sp (CAt σ) ⟶ T.X.YY) ⁻¹ᵁ (T.X.F.U i ⊓ T.X.F.U j) := GlobalTheory.FlagMod.le_preimage_inf hi hj
    have h1 := g3 _ _ _ _ ht (g1 _ _ _ _ _ (hQ.frBor hQ' hh) ht')
    have h2 := (hv i y.1 x hi Q t hQ ht).symm.trans (hv j y.1 x hj Q' t' hQ' ht')
    have h3 : GlobalTheory.CxPts.gv (flagStr T.X) σ (T.X.LL e) i j y = chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) :=
      (GlobalTheory.CxPts.ev_eq (p := flagStr T.X) (σ := σ) (y := y) (U := T.X.F.U i ⊓ T.X.F.U j) hh _).trans
        (T.X.F.ev_LL_g (S := CAt σ) e i j y.1 hh)
    have h4 : chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh) * chr e (T.X.F.TAt (S := CAt σ) i j y.1 hh) = 1 := by
      rw [← chr_add, neg_add_cancel, chr_zero]
    rw [h1, chr_mul] at h2
    show v i y.1 = _ * v j y.1
    rw [h3]
    refine mul_left_cancel₀ (chr_ne_zero e t') ?_
    linear_combination (chr (-e) (T.X.F.TAt (S := CAt σ) i j y.1 hh)) * h2 - chr e t' * v i y.1 * h4
  · push Not at h
    show v i y.1 = _ * v j y.1
    rw [hv0 i y.1 (Or.inr h), hv0 j y.1 (Or.inr h), mul_zero]

theorem differentiableAt_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) (i : T.X.F.J) {m : ℕ}
    {B : Set (Fin m → ℂ)} (s : (Fin m → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ)
    (ho : ∀ W, IsOpen (B ∩ s ⁻¹' ptsIn _ σ W))
    (hd : ∀ W (u : Γ(T.X.YY, W)), DifferentiableOn ℂ (fun b => ev _ σ W u (s b)) (B ∩ s ⁻¹' ptsIn _ σ W))
    {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) (hi : s b₀ ∈ ptsIn _ σ (flagOpen T.X ⊓ T.X.F.U i)) :
    DifferentiableAt ℂ (fun b => h i (s b)) b₀ := by
  obtain ⟨hO, hz⟩ := mem_ptsIn_inf.1 hi
  obtain ⟨Q₀, hQ₀⟩ := exists_chartFr_alg T (S := CAt σ) (zOf (s b₀)) hO (s b₀).2 i hz
  obtain ⟨a, a₀, n, n₀, g, hD, hN, hD₀, hg, he, hl, hg0⟩ := hT Q₀
  have hPg := isSec_mul hP (hU.2.2.2.2.1 a₀ n₀ hD₀ g hg k)
  rw [← hl] at hPg
  choose u hu using fun j => exists_fun_chart (σ := σ) T hg j
  let h' : T.X.F.J → GlobalTheory.CxPts (flagStr T.X) σ → ℂ := fun j y => h j y * ev _ σ _ (u j) y
  have hR' : Reads V T (fun i => (ex D a n i : ℤ)) k (fun x => P x * rdU V g k x) h' := by
    intro x hx j y hy Q t hxy hQ ht
    have e₁ : P x = chr e t * h j y := hR x hx j y hy Q t hxy hQ ht
    have e₂ : rdU V g k x = _ := (rdU_eq V g k ⟨x, hx⟩).trans (DifferentiableLines.evR_frBor hg ht)
    rw [hu j y hy Q (mem_open_of_ptY T _ _ hxy) hQ] at e₂
    show P x * rdU V g k x = chr (fun i => (ex D a n i : ℤ)) t * (h j y * ev _ σ _ (u j) y)
    rw [e₁, e₂, he, chr_add]
    ring
  have hZ' : OffZero (e := fun i => (ex D a n i : ℤ)) V T k h' := fun j y hy => by
    show h j y * _ = 0
    rw [hZ j y hy, zero_mul]
  have d₁ : DifferentiableAt ℂ (fun b => h' i (s b)) b₀ :=
    differentiableAt_reads hσ hU T hD hN hPg hR' hZ' i s ho hd hb₀ hi
  have d₂ : DifferentiableAt ℂ (fun b => ev _ σ _ (u i) (s b)) b₀ :=
    (hd _ (u i)).differentiableAt ((ho _).mem_nhds ⟨hb₀, hi⟩)
  have n₂ : ev _ σ _ (u i) (s b₀) ≠ 0 := by
    rw [← hu i _ hz Q₀ hO hQ₀]
    exact hg0
  refine (d₁.mul (d₂.inv n₂)).congr_of_eventuallyEq ?_
  filter_upwards [d₂.continuousAt.eventually_ne n₂] with b hb
  exact (mul_inv_cancel_right₀ hb _).symm

theorem open_holoZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {e : Ix D → ℤ} {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r} (hT : Tw V e k la)
    {P : Frame (V.X k).Ψ r → ℂ} (hP : (V.X k).IsSec la P) {d : ℕ} (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T e k P h) (hZ : OffZero V T k h) :
    ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL e).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i) := by
  intro i j v hv
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  have key := differentiableAt_readsZ hσ hU T hT hP hR hZ i (B := L.symm ⁻¹' C.e.target)
    (fun b => C.e.symm (L.symm b))
    (fun W => (GlobalTheory.ChartGlue.isOpen_over C.e (isOpen_ptsIn W)).preimage L.symm.continuous)
    (fun W u => (C.holo W u).comp L.symm.differentiableOn fun b hb => hb) (b₀ := L v)
    (by simpa using hv.1) (by
      simp only [ContinuousLinearEquiv.symm_apply_apply]
      exact mem_ptsIn_inf.2 ⟨hv.2.2, hv.2.1⟩)
  refine DifferentiableAt.differentiableWithinAt ?_
  have := key.comp v L.differentiableAt
  refine this.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem evR_mul' (f g : Rul Xo c) (y : FrPt Xo c (CAt σ)) : evR Xo c (f * g) y = evR Xo c f y * evR Xo c g y :=
  evalAt_mul _ _ _ _ _

theorem evR_pow_ne {f : Rul Xo c} {y : FrPt Xo c (CAt σ)} (h : toC (evR Xo c f y) ≠ 0) (N : ℕ) :
    toC (evR Xo c (f ^ (N + 1)) y) ≠ 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [pow_succ, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) ih h

open GlobalTheory.AllWt GlobalTheory.ShFam in

theorem tw_of_dec {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (κ : KeySec Xo c)
    (hNV : ∀ a n, Dom a n → NV Xo c σ a n) (G : WTZ E) (hG : G.2 = 0)
    (hdec : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < D.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) (k : V.Comp) :
    Tw V (exZ D G) k (modelWt V G k) := by
  intro y
  set M : ℕ := ∑ τ : E →+* ℂ, ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs with hM
  have hMb : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → -G.1 (τ, i) ≤ M := fun τ i hi => by
    have h1 : (G.1 (τ, i)).natAbs ≤ ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs :=
      Finset.single_le_sum (f := fun i => (G.1 (τ, i)).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.2 hi)
    have h2 : ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs ≤ M :=
      Finset.single_le_sum (f := fun τ => ∑ i ∈ Finset.range (D.mult τ), (G.1 (τ, i)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ)
    have h3 : -G.1 (τ, i) ≤ ((G.1 (τ, i)).natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact neg_le_abs _
    omega
  obtain ⟨n₁, hn0, ⟨m', hm'⟩, h, hh, h0⟩ := GlobalTheory.Reg.exists_even_sec_evR_ne_zero E H D l Xo c σ y
  obtain ⟨m, rfl⟩ : ∃ m, n₁ = 2 * (m + 1) := ⟨m' - 1, by omega⟩
  set g : Rul Xo c := h ^ (M + 1) * (κ.ρ : Rul Xo c) ^ (M + 1) with hgdef
  have hh' : h ∈ secZ Xo c (fun i => (ex D 0 (2 * (m + 1)) i : ℤ)) := by
    rw [secZ_nat]; exact hh
  have hg0 := mul_mem_secZ (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ hh' M) (GlobalTheory.FlatTw.Hol.pow_succ_mem_secZ κ.mem M)
  have hg : g ∈ sec Xo c (fun _ => M + 1) (2 * ((M + 1) * m)) := by
    rw [← secZ_nat]
    convert hg0 using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, keyEx]
      ring
    · simp [ex, keyEx]
  set a : (E →+* ℂ) × ℕ → ℕ := fun x => if x.2 < D.mult x.1 then (G.1 x + (M + 1)).toNat else 0 with ha
  have haZ : ∀ (τ : E →+* ℂ) (i : ℕ), i < D.mult τ → (a (τ, i) : ℤ) = G.1 (τ, i) + (M + 1) := fun τ i hi => by
    show ((if i < D.mult τ then (G.1 (τ, i) + (M + 1)).toNat else 0 : ℕ) : ℤ) = _
    rw [if_pos hi, Int.toNat_of_nonneg (by linarith [hMb τ i hi])]
  have hDa : Dom a (2 * ((M + 1) * m)) := by
    refine ⟨fun τ i j hij => ?_, even_two_mul _⟩
    simp only [ha]
    split_ifs with h1 h2 h2
    · exact Int.toNat_le_toNat (by linarith [hdec τ i j hij h1])
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have hEx : exZ D (wtZ a (2 * ((M + 1) * m))) = exZ D (G + wtZ (fun _ => M + 1) (2 * ((M + 1) * m))) := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp only [exZ, wtZ, Prod.snd_add, hG, zero_add]
    · simp [exZ, wtZ]
      exact haZ τ i i.2
  have hκ : toC (evR Xo c (κ.ρ : Rul Xo c) y) ≠ 0 := fun hz => by
    have e₁ : evR Xo c (κ.ρ : Rul Xo c) y * evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y = 1 := by
      rw [← evR_mul', Units.mul_inv]
      exact evalAt_one _ _ _ ((GlobalTheory.Reg.evLaws_genFr_atlas E H D l Xo c).1.test _ _)
    have e₂ : toC (evR Xo c (κ.ρ : Rul Xo c) y) * toC (evR Xo c ((κ.ρ⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) y) = 1 := e₁
    rw [hz, zero_mul] at e₂
    exact zero_ne_one e₂
  refine ⟨a, fun _ => M + 1, _, _, g, hDa, hNV _ _ hDa, ⟨fun _ => antitone_const, even_two_mul _⟩, hg, ?_, ?_, ?_⟩
  · rw [← GlobalTheory.AllWt.exZ_wtZ, ← GlobalTheory.AllWt.exZ_wtZ, hEx]
    exact funext fun i => by first | exact Formalism.L2.Pj.exZ_add _ _ i | exact GlobalTheory.AllWt.exZ_add _ _ i | (cases i <;> rfl)
  · rw [← modelWt_wtZ, modelWt_congr V hσ hU hEx, modelWt_add V (hG ▸ Even.zero)
      ⟨(((M + 1) * m : ℕ) : ℤ), by simp [wtZ]; ring⟩, modelWt_wtZ]
  · rw [hgdef, evR_mul']
    exact mul_ne_zero (M₀ := ℂ) (evR_pow_ne h0 M) (evR_pow_ne hκ M)

end PositivityTheory.UnitarySelfGeneration.VuOnto
