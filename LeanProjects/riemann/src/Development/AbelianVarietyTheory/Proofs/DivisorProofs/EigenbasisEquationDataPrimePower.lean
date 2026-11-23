import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalizationNearDistinctEigenvaluesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetResidueLogBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstLatRel

variable {F : Type} [Field F] [NumberField F]

theorem w_natCast_le_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (m : ℕ) : e.w (m : AlgebraicClosure F) ≤ 1 := by
  have h := e.w_alg (m : F)
  rw [map_natCast] at h
  rw [h]
  exact NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v m

theorem w_lt_one {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {p : ℕ} (hv : resP v = p) :
    e.w (p : AlgebraicClosure F) < 1 := by
  have hpv : ((p : 𝓞 F)) ∈ v.asIdeal := by
    have h0 : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ p).2 (by rw [← hv]; rfl)
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)] at h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have h := e.w_alg (p : F)
  rw [map_natCast] at h
  rw [h, ← map_natCast (algebraMap (𝓞 F) F) p, ← FinitePlace.norm_embedding]
  exact (FinitePlace.norm_lt_one_iff_mem F v _).2 hpv

theorem w_pow_le_w_natCast {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {p : ℕ} (hp : p.Prime) (hv : resP v = p)
    {n : ℕ} (hn : n ≠ 0) : e.w (p : AlgebraicClosure F) ^ n ≤ e.w (n : AlgebraicClosure F) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hm1 : e.w (m : AlgebraicClosure F) = 1 := by
    have h := e.w_alg (m : F)
    rw [map_natCast] at h
    rw [h]
    by_contra h'
    have hmem := (GlobalTheory.PlaceSum.adicAbv_natCast_ne_one_iff v m).1 h'
    apply hm
    have hc : ((m : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    rw [← hv]
    exact ringChar.dvd hc
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow, hm1, mul_one]
  have hk : k ≤ p ^ k * m := by
    have h1 : k < p ^ k := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ k ≤ p ^ k * m := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _)))
    omega
  exact pow_le_pow_of_le_one (e.w.nonneg _) (w_natCast_le_one e p) hk

theorem w_le_one_of_isIntegral {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {x : F} (hx : IsIntegral ℤ x) :
    e.w (algebraMap F (AlgebraicClosure F) x) ≤ 1 := by
  have h1 : IsIntegral ℤ (algebraMap F (AlgebraicClosure F) x) := hx.algebraMap
  have h2 : IsIntegral e.O (algebraMap F (AlgebraicClosure F) x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact (e.mem_O _).1 y.2

section Val

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}

theorem regAt_sum {x : Z} {ι : Type} (s : Finset ι) (f : ι → Z.functionField) (h : ∀ i ∈ s, RegAt x (f i)) :
    RegAt x (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using regAt_zero x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem valAt_add {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f + g) = valAt y f + valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_add, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_add]

theorem valAt_sum {ι : Type} (s : Finset ι) (f : ι → Z.functionField) (h : ∀ i ∈ s, RegAt (below y) (f i)) :
    valAt y (∑ i ∈ s, f i) = ∑ i ∈ s, valAt y (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ← map_zero (algebraMap (Z.presheaf.stalk (below y)) Z.functionField),
      SmallSec.valAt_algebraMap, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      valAt_add (h a (Finset.mem_insert_self a s)) (regAt_sum s f fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

end Val

section Chart

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {g : ℕ}

theorem isoAgree_mono {V : Cover Y} {W : Y.X.Opens} {ι : Type} {U : ι → V.X.Opens}
    {H : ι → Matrix (Fin (g + g)) (Fin g) V.G.functionField} {T : Y.X → Matrix (Fin g) (Fin g) Y.Fn}
    {J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ} {p k k' : ℕ} (hk : k ≤ k') (h : IsoAgree V W U H T J p k') :
    IsoAgree V W U H T J p k := by
  intro v hv e y hy z yt hz hyt a ha
  have hle : e.w (p : AlgebraicClosure F) ^ k' ≤ e.w (p : AlgebraicClosure F) ^ k :=
    pow_le_pow_of_le_one (e.w.nonneg _) (w_natCast_le_one e p) hk
  obtain ⟨h1, h2⟩ := h v hv e y hy z yt hz hyt a ha
  exact ⟨fun u u' hu hu' => (h1 u u' hu hu').trans hle, fun b hb u hu => (h2 b hb u hu).trans hle⟩

theorem chartReg_const_mul {V : Cover Y} {U : V.X.Opens} {H : Matrix (Fin (g + g)) (Fin g) V.G.functionField}
    {T : Y.X → Matrix (Fin g) (Fin g) Y.Fn} (P : Matrix (Fin (g + g)) (Fin (g + g)) F) (h : ChartReg V U H T) :
    ChartReg V U (P.map (V.φ.comp (algebraMap F Y.Fn)) * H) T := by
  intro z hz k l
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  exact regAt_sum _ _ fun j _ => (V.regAt_φ (Var.regAt_algebraMap Y _ _)).mul (h z hz j l)

theorem valMat_const_mul (V : Cover Y) (H : Matrix (Fin (g + g)) (Fin g) V.G.functionField)
    (Tm : Matrix (Fin g) (Fin g) Y.Fn) (P : Matrix (Fin (g + g)) (Fin (g + g)) F) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (hz : (z ≫ V.π) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)))
    (hr : ∀ k l, RegAt (below z) ((H * (Tm.map V.φ)⁻¹) k l)) :
    valMat V (P.map (V.φ.comp (algebraMap F Y.Fn)) * H) Tm z =
      P.map (algebraMap F (AlgebraicClosure F)) * valMat V H Tm z := by
  have hc : ∀ c : F, valAt z (V.φ (algebraMap F Y.Fn c)) = algebraMap F (AlgebraicClosure F) c := fun c => by
    rw [V.valAt_φ z (Var.regAt_algebraMap Y _ c)]
    exact OfLattice.valAt_const (z ≫ V.π) hz c
  ext k l
  have e1 : valMat V (P.map (V.φ.comp (algebraMap F Y.Fn)) * H) Tm z =
      (P.map (V.φ.comp (algebraMap F Y.Fn)) * (H * (Tm.map V.φ)⁻¹)).map (valAt z) := by
    rw [valMat, Matrix.mul_assoc]
  rw [e1, Matrix.map_apply, Matrix.mul_apply (M := P.map (V.φ.comp (algebraMap F Y.Fn))),
    Matrix.mul_apply (M := P.map (algebraMap F (AlgebraicClosure F)))]
  refine (valAt_sum Finset.univ (fun j => P.map (V.φ.comp (algebraMap F Y.Fn)) k j * (H * (Tm.map V.φ)⁻¹) j l)
    fun j _ => (V.regAt_φ (Var.regAt_algebraMap Y _ (P k j))).mul (hr j l)).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [SmallSec.valAt_mul (f := P.map (V.φ.comp (algebraMap F Y.Fn)) k j) (V.regAt_φ (Var.regAt_algebraMap Y _ (P k j)))
    (hr j l)]
  show valAt z (V.φ (algebraMap F Y.Fn (P k j))) * _ = algebraMap F _ (P k j) * valAt z ((H * (Tm.map V.φ)⁻¹) j l)
  rw [hc]

end Chart

section Main

theorem relData_of_eqData : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {g : ℕ} {E : Type} [Field E] [NumberField E]
    (A A' : Fin g → Adl C Y) (β : Fin g → (E →+* F)) (sh : (E →+* F) → ℝ)
    (ρ : 𝓞 E →+* Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (J : Matrix (Fin (g + g)) (Fin (g + g)) ℤ) (p n : ℕ)
    (P Q : Matrix (Fin (g + g)) (Fin (g + g)) F), p.Prime → n ≠ 0 → IsUnit J.det → EigBasis ρ J sh p n P Q →
    (∀ k, EqData A A' β sh ρ J p k) → ∀ k, RelData A A' p n k := by
  intro F _ _ Y C g E _ _ A A' β sh ρ J p n P Q hp hn hJ hEig hEq k
  obtain ⟨hSL, b, α, hdiag, hsep, hnorm⟩ := hEig
  obtain ⟨V, W, ι, U, H, d, T, hgen, hcov, hT, hLA, hLA', hchart, hiso, heq⟩ := hEq (k + 3 * n + 1)
  refine ⟨V, W, ι, U, H, d, T, J, P, Q, hJ, hSL, hgen, hcov, hT, hLA, hLA', fun a => ⟨(hchart a).1, (hchart a).2.1,
    chartReg_const_mul P (hchart a).1, ?_⟩, isoAgree_mono (by omega) hiso⟩
  intro v hv e y hy z yt hz hyt hU
  have mn := (hchart a).2.1 v hv e y hy z yt hz hyt hU
  have bn := (hchart a).2.2 v hv e y hy z yt hz hyt hU
  have eqv := heq v hv e y hy z yt hz hyt a hU α
  have hPin : V.j (below z) ∈ U a := by
    have e2 : V.j (below z) = yt ((spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F))) := by
      change (z ≫ V.j) _ = _
      rw [← hyt]; rfl
    rw [e2]; exact hU trivial
  have hπ : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have hr : ∀ k l, RegAt (below z) ((H a * ((T (below y.1)).map V.φ)⁻¹) k l) := by
    intro k l
    have h := (hchart a).1 (below z) hPin k l
    rwa [hπ] at h
  have hz' : (z ≫ V.π) ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) := by rw [hz]; exact y.2
  rw [valMat_const_mul V (H a) (T (below y.1)) P z hz' hr]

  set w := e.w with hw
  have hp0 : 0 < w (p : AlgebraicClosure F) := w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
  have hp1 : w (p : AlgebraicClosure F) < 1 := w_lt_one e hv
  have hη0 : 0 < w (n : AlgebraicClosure F) := w.pos (Nat.cast_ne_zero.2 hn)
  have hη1 : w (n : AlgebraicClosure F) ≤ 1 := w_natCast_le_one e n
  have hpn : w (p : AlgebraicClosure F) ^ n ≤ w (n : AlgebraicClosure F) := w_pow_le_w_natCast e hp hv hn
  have hε : w (p : AlgebraicClosure F) ^ (k + 3 * n + 1) < w (n : AlgebraicClosure F) ^ 3 := by
    have h1 : w (p : AlgebraicClosure F) ^ (k + 3 * n + 1) ≤ w (p : AlgebraicClosure F) ^ (3 * n + 1) :=
      pow_le_pow_of_le_one hp0.le hp1.le (by omega)
    have h2 : w (p : AlgebraicClosure F) ^ (3 * n + 1) < w (p : AlgebraicClosure F) ^ (3 * n) := by
      rw [pow_succ]
      exact mul_lt_of_lt_one_right (pow_pos hp0 _) hp1
    have h3 : w (p : AlgebraicClosure F) ^ (3 * n) ≤ w (n : AlgebraicClosure F) ^ 3 := by
      rw [mul_comm, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hp0.le _) hpn 3
    linarith
  have hinv : ∀ x : F, IsIntegral ℤ ((n : F) * x) → w (algebraMap F (AlgebraicClosure F) x) ≤ (w (n : AlgebraicClosure F))⁻¹ := by
    intro x hx
    have h := w_le_one_of_isIntegral e hx
    rw [map_mul, map_natCast, map_mul] at h
    have h' : w (algebraMap F (AlgebraicClosure F) x) ≤ 1 / w (n : AlgebraicClosure F) :=
      (le_div_iff₀ hη0).2 (by rwa [mul_comm])
    simpa [one_div] using h'
  have hPQ : P.map (algebraMap F (AlgebraicClosure F)) * Q.map (algebraMap F (AlgebraicClosure F)) = 1 := by
    rw [← Matrix.map_mul, hSL.1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQb : ∀ i j, w (P.map (algebraMap F (AlgebraicClosure F)) i j) ≤ (w (n : AlgebraicClosure F))⁻¹ ∧
      w (Q.map (algebraMap F (AlgebraicClosure F)) i j) ≤ (w (n : AlgebraicClosure F))⁻¹ :=
    fun i j => ⟨hinv _ (hSL.2.1 i j).1, hinv _ (hSL.2.1 i j).2⟩
  have hdiag' : P.map (algebraMap F (AlgebraicClosure F)) * (ρ α).map (Int.castRingHom (AlgebraicClosure F)) *
      Q.map (algebraMap F (AlgebraicClosure F)) =
      Matrix.diagonal (fun r => (fun τ : E →+* F => algebraMap F (AlgebraicClosure F) (τ (α : E))) (b r)) := by
    have h := congrArg (fun M => M.map (algebraMap F (AlgebraicClosure F))) hdiag
    simp only [Matrix.map_mul, Matrix.map_map, Matrix.diagonal_map (map_zero _)] at h
    convert h using 3
    ext i j
    simp
  have hsep' : ∀ σ τ : E →+* F, σ ≠ τ → w (n : AlgebraicClosure F) ≤
      w (algebraMap F (AlgebraicClosure F) (σ (α : E)) - algebraMap F (AlgebraicClosure F) (τ (α : E))) := by
    intro σ τ hστ
    obtain ⟨hne, hint⟩ := hsep σ τ hστ
    have h := w_le_one_of_isIntegral e hint
    have hd : algebraMap F (AlgebraicClosure F) (σ (α : E) - τ (α : E)) ≠ 0 :=
      (map_ne_zero _).2 (sub_ne_zero.2 hne)
    rw [map_div₀, map_natCast, map_div₀, div_le_one (w.pos hd), map_sub] at h
    exact h
  have key := GlobalTheory.T.log_colMinor_mul_Iic_sub_Iio_eq_block_add_log w (isNonarchimedean_w e) (valMat V (H a) (T (below y.1)) z)
    (P.map (algebraMap F (AlgebraicClosure F))) (Q.map (algebraMap F (AlgebraicClosure F)))
    ((ρ α).map (Int.castRingHom (AlgebraicClosure F))) b β (fun τ => algebraMap F (AlgebraicClosure F) (τ (α : E)))
    (fun τ => w (p : AlgebraicClosure F) ^ sh τ) (w (n : AlgebraicClosure F)) (w (p : AlgebraicClosure F) ^ (k + 3 * n + 1))
    hη0 hη1 hε hPQ hPQb hdiag' hsep' (fun τ y' hy' => hnorm v hv e τ y' hy') eqv mn.1
  refine ⟨key.1, fun i => ?_⟩
  rw [bn i]
  have h2 := (key.2 i).2
  have h3 : Real.log (w (p : AlgebraicClosure F) ^ sh (β i)) = sh (β i) * Real.log (w (p : AlgebraicClosure F)) :=
    Real.log_rpow hp0 _
  rw [h3] at h2
  linarith

end Main

end GlobalTheory.ConstLatRel
