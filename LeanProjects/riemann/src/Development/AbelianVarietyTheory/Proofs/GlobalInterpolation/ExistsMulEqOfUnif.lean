import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocPDelAtrEqLocPNabAtr
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
import Formalism.LocalToGlobal.Columns.BtExistsSmulLeOfFg
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open scoped Matrix

noncomputable section

namespace GlobalTheory.KerT.PStd

open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis admitted InClosure extLat ptTable detFac)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (InIntClosure Induces adj suppP StdAtT)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (UnramOver StdOver)

section Place

variable {p : ℕ} [Fact p.Prime]

theorem val_le_iff (x y : ℂ_[p]) :
    NormedField.valuation (K := ℂ_[p]) x ≤ NormedField.valuation (K := ℂ_[p]) y ↔ ‖x‖ ≤ ‖y‖ := by
  change ‖x‖₊ ≤ ‖y‖₊ ↔ _
  exact Iff.rfl

theorem val_le_one_iff (x : ℂ_[p]) : NormedField.valuation (K := ℂ_[p]) x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  change ‖x‖₊ ≤ 1 ↔ _
  exact Iff.rfl

theorem norm_le_one_iff {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) :
    NormedField.valuation (K := ℂ_[p]) (ι x) ≤ 1 ↔ w.valuation K x ≤ 1 := by
  rw [val_le_one_iff]
  refine ⟨fun h => ?_, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw x⟩
  by_contra hx
  have hx1 : 1 < w.valuation K x := not_le.1 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx1
  have h1 : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hx1
  obtain ⟨r, t, e⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ h1.le
  have h2 : r ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K r) < 1
    rw [← e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (w.valuation_le_one _)) h1
  have h3 : 1 ≤ ‖ι ((t : 𝓞 K) : K)‖ := not_lt.1 fun hlt => t.2 ((hw _).2 hlt)
  have h4 := (hw r).1 h2
  have h5 : ‖ι ((t : 𝓞 K) : K)‖ = ‖ι x‖ * ‖ι (r : K)‖ := by
    rw [← norm_mul, ← map_mul]
    congr 2
    change _ = x * algebraMap (𝓞 K) K r
    rw [← e, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (r : K))]

theorem finite_inDeg {I : Type} [Fintype I] {a b : ℕ} (lam : I → DomWeight a) (s' : I → ℤ) :
    {m : DVar I a b →₀ ℕ | InDeg lam s' m}.Finite := by
  refine (Finsupp.finite_of_degree_le (∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ)).toNat).subset fun m hm => ?_
  have h4 : (m.degree : ℤ) = ∑ τ, ∑ i : Fin a, ((lam τ).w i + s' τ) := by
    rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [← hm τ, Fintype.sum_prod_type]
  change m.degree ≤ _
  omega

theorem inClosure_of {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ_[p]) {I : Type} [Fintype I] {a b : ℕ}
    (lam : I → DomWeight a) (s' : I → ℤ) (M : I → Submodule (𝓞 K) (Fin a → K)) (MW : I → Submodule (𝓞 K) (Fin b → K))
    (κ : K) (J : (DVar I a b →₀ ℕ) → K) {H : Type} {Sup : Set H} (ap : H → I → Matrix (Fin a) (Fin b) ℂ_[p])
    {Ms : Set (DVar I a b →₀ ℕ)} (hM : ∀ m, InDeg lam s' m → m ∈ Ms)
    (hadm : ∀ x ∈ Sup, admitted (NormedField.valuation (K := ℂ_[p])) ι M MW (ap x))
    (h : InIntClosure Sup (fun x m => ι κ * ptTable (ap x) m) Ms fun m => ι (J m)) :
    InClosure (NormedField.valuation (K := ℂ_[p])) ι lam s' M MW κ J := by
  intro ε hε
  obtain ⟨c, hc, hc1, hc2⟩ := h (finite_inDeg (b := b) lam s').toFinset (fun m hm => hM m (by simpa using hm)) ‖ι ε‖
    (norm_pos_iff.2 ((map_ne_zero ι).2 hε))
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun i => c (e i), fun i => ap (e i), fun i => (val_le_one_iff _).2 (hc1 _),
    fun i => hadm _ (hc (e i).2), fun m hm => (val_le_iff _ _).2 ?_⟩
  have h1 := hc2 m (by simpa using hm)
  have h2 : (c.sum fun x r => r * (ι κ * ptTable (ap x) m)) = ι κ * ∑ i, c (e i) * ptTable (ap (e i)) m := by
    rw [Finsupp.sum, ← Finset.sum_coe_sort, ← e.sum_comp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  rw [← h2]
  exact h1.le

end Place

section Lat

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {I : Type} [Fintype I] (emb : I → E →+* K) {n : ℕ}

theorem localization_tauLat_le (w : HeightOneSpectrum (𝓞 K)) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal)
    {L L' : Submodule (𝓞 E) (Fin n → E)} (h : L ≤ localization₂ P.asIdeal L') :
    localization₂ w.asIdeal (tauLat emb τ L) ≤ localization₂ w.asIdeal (tauLat emb τ L') :=
  localization_le_of_le_localization w (tauLat_le_locP emb w τ fun x hx => by
    obtain ⟨s, hs, hsx⟩ := h hx
    exact ⟨s, fun h' => hs (hP s h'), hsx⟩)

omit [Fintype I] in
theorem tauLat_colLat (τ : I) (B : GL (Fin n) E) :
    tauLat emb τ (colLat B) = colLat (Matrix.GeneralLinearGroup.map (emb τ) B) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero =>
      simp only [Pi.zero_apply, map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      simp only [Pi.add_apply, map_add]
      exact add_mem hy hz
    | smul r y _ hy =>
      have e : (fun a => emb τ ((r • y) a)) = RingOfIntegers.mapRingHom (emb τ) r • fun a => emb τ (y a) := by
        funext a
        rw [Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl
      change (fun a => emb τ ((r • y) a)) ∈ _
      rw [e]
      exact Submodule.smul_mem _ _ hy
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem isBasisAt_tauLat (w : HeightOneSpectrum (𝓞 K)) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal)
    {L : Submodule (𝓞 E) (Fin n → E)} {B : GL (Fin n) E} (h : IsBasisAt P L B) :
    IsBasisAt w (tauLat emb τ L) (Matrix.GeneralLinearGroup.map (emb τ) B) := by
  unfold IsBasisAt at h ⊢
  rw [← tauLat_colLat]
  exact le_antisymm (localization_tauLat_le emb w τ P hP (fun x hx => h ▸ GlobalTheory.TestLat.WeylLocal.le_locP P L hx))
    (localization_tauLat_le emb w τ P hP (fun x hx => h ▸ GlobalTheory.TestLat.WeylLocal.le_locP P (colLat B) hx))

theorem admissible_of_integral_conj_le {Ω Γ : Type} [Field Ω] [LinearOrderedCommGroupWithZero Γ] (v : Valuation Ω Γ) (σ : K →+* Ω)
    (w : HeightOneSpectrum (𝓞 K)) (hσ : ∀ x : K, v (σ x) ≤ 1 ↔ w.valuation K x ≤ 1) (τ : I) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ s : 𝓞 E, RingOfIntegers.mapRingHom (emb τ) s ∈ w.asIdeal → s ∈ P.asIdeal) {a b : ℕ}
    {L : Submodule (𝓞 E) (Fin a → E)} {L' : Submodule (𝓞 E) (Fin b → E)} (A : Matrix (Fin a) (Fin b) E)
    (hA : ∀ y ∈ L', A *ᵥ y ∈ localization₂ P.asIdeal L) (c : Ω) (hc : v c ≤ 1) :
    ∀ y ∈ extLat v σ (tauLat emb τ L'), (Matrix.of fun α β => c * σ (emb τ (A α β))) *ᵥ y ∈ extLat v σ (tauLat emb τ L) := by
  have h1 : ∀ z ∈ tauLat emb τ L', A.map (emb τ) *ᵥ z ∈ localization₂ w.asIdeal (tauLat emb τ L) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have e : A.map (emb τ) *ᵥ (fun a => emb τ (x a)) = fun a => emb τ ((A *ᵥ x) a) := by
        funext α
        simp [Matrix.mulVec, dotProduct]
      rw [e]
      exact localization_tauLat_le emb w τ P hP (L := localization₂ P.asIdeal L) le_rfl
        (GlobalTheory.TestLat.WeylLocal.le_locP w _ (Submodule.subset_span ⟨_, hA x hx, rfl⟩))
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    have h2 := (GlobalTheory.ExtLatMatrix.extLat_matrix_integral K w Ω Γ v σ hσ).1 a _ _ (h1 z hz)
    have e : (Matrix.of fun α β => c * σ (emb τ (A α β))) *ᵥ (fun i => σ (z i)) =
        (⟨c, hc⟩ : v.integer) • fun i => σ ((A.map (emb τ) *ᵥ z) i) := by
      funext α
      simp [Matrix.mulVec, dotProduct, Subring.smul_def, Finset.mul_sum, mul_assoc]
    rw [e]
    exact Submodule.smul_mem _ _ h2
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul r x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx

end Lat

section Ker

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem exists_mul_eq_of_unif {P : HeightOneSpectrum (𝓞 E)} {T r : 𝓞 E} (hT : T ∈ P.asIdeal) (hT2 : T ∉ P.asIdeal ^ 2)
    (hr : r ∈ P.asIdeal) : ∃ s ∉ P.asIdeal, ∃ b : 𝓞 E, s * r = T * b := by
  obtain ⟨J, hJ⟩ : P.asIdeal ∣ Ideal.span {T} := Ideal.dvd_span_singleton.2 hT
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply hT2
    have : Ideal.span {T} ≤ P.asIdeal ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨s, hsJ, hs⟩ := Set.not_subset.1 hJP
  have hm : r * s ∈ Ideal.span {T} := hJ ▸ Ideal.mul_mem_mul hr hsJ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨s, hs, b, by rw [mul_comm s, ← hb, mul_comm]⟩

theorem isBasisAt_one {P : HeightOneSpectrum (𝓞 E)} {L : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal L = stdAt E n P) :
    IsBasisAt P L 1 := by
  unfold IsBasisAt
  rw [h, stdAt, stdLat_eq_span, colLat]
  congr 3
  funext j a
  simp [Matrix.one_apply, Pi.single_apply]

theorem exists_basis_ker {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hs : d.at P.1 = stdAt E n P.1) {T : 𝓞 E}
    (hT : T ∈ P.1.asIdeal) (hT2 : T ∉ P.1.asIdeal ^ 2) :
    ∃ B : GL (Fin n) E, (B : Matrix (Fin n) (Fin n) E).det = algebraMap (𝓞 E) E T ∧ IsBasisAt P.1 d.L B := by
  classical
  have hle : stdLat E n ≤ d.at P.1 := hs ▸ Formalism.L2.Col.le_locP P.1 _
  have hvec : ∀ r : Fin n → 𝓞 E, (fun a => algebraMap (𝓞 E) E (r a) : Sp E n) ∈ stdLat E n := fun r =>
    (mem_stdLat _).2 fun a => ⟨r a, rfl⟩
  let g : (Fin n → 𝓞 E) →ₗ[𝓞 E] (𝓞 E ⧸ P.1.asIdeal) := (hd.fLin P _ hle) ∘ₗ
    LinearMap.codRestrict (stdLat E n) ((Algebra.linearMap (𝓞 E) E).compLeft (Fin n)) hvec
  have hg : ∀ r, g r = d.f P fun a => algebraMap (𝓞 E) E (r a) := fun _ => rfl
  have hgs : ∀ r, g r = ∑ j, Ideal.Quotient.mk P.1.asIdeal (r j) * g (Pi.single j 1) := fun r => by
    conv_lhs => rw [← Finset.univ_sum_single r, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← quot_smul_def, ← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
  have hred : ∀ x ∈ d.at P.1, ∃ s ∉ P.1.asIdeal, ∃ r : Fin n → 𝓞 E, s • x = (fun a => algebraMap (𝓞 E) E (r a)) ∧
      g r = Ideal.Quotient.mk P.1.asIdeal s * d.f P x := by
    intro x hx
    obtain ⟨s, hs1, hs2⟩ := (Formalism.L2.Col.mem_locP P.1 (stdLat E n) x).1 (show x ∈ stdAt E n P.1 from hs ▸ hx)
    choose r hr using (mem_stdLat _).1 hs2
    have e : s • x = fun a => algebraMap (𝓞 E) E (r a) := funext fun a => (hr a).symm
    exact ⟨s, hs1, r, e, by rw [hg, ← e, hd.f_smul P s x hx]⟩
  obtain ⟨i, hi⟩ : ∃ i, g (Pi.single i 1) ≠ 0 := by
    by_contra h0
    push Not at h0
    obtain ⟨x, hx, hne⟩ := hd.f_ne P
    obtain ⟨s, hs1, r, -, e⟩ := hred x (Formalism.L2.Col.le_locP P.1 _ hx)
    rw [hgs] at e
    simp only [h0, mul_zero, Finset.sum_const_zero] at e
    exact mul_ne_zero (mk_ne_zero hs1) hne e.symm
  have hmax := P.1.isMaximal
  obtain ⟨z, hz⟩ := Ideal.Quotient.exists_inv hi
  choose c hc using fun j => Ideal.Quotient.mk_surjective (g (Pi.single j 1) * z)
  have hc' : ∀ j, g (Pi.single j 1) = Ideal.Quotient.mk P.1.asIdeal (c j) * g (Pi.single i 1) := fun j => by
    rw [hc, mul_assoc, mul_comm z, hz, mul_one]
  let t : Fin n → 𝓞 E := Function.update (fun j => -c j) i T
  let B₀ : Matrix (Fin n) (Fin n) (𝓞 E) := (1 : Matrix (Fin n) (Fin n) (𝓞 E)).updateRow i t
  have hdet : B₀.det = T := by
    have h1 := Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) (𝓞 E)) i t
    have h2 : (∑ k, t k • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) k) = t := by
      funext j
      simp [Finset.sum_apply, Matrix.one_apply]
    rw [h2] at h1
    simp [B₀, h1, t]
  have hT0 : algebraMap (𝓞 E) E T ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hT2 (zero_mem _)
  have hdet' : (B₀.map (algebraMap (𝓞 E) E)).det = algebraMap (𝓞 E) E T := by
    rw [← hdet, RingHom.map_det]
    rfl
  have hcol : ∀ j, (fun a => B₀ a j) = if j = i then T • Pi.single i 1 else Pi.single j 1 - c j • Pi.single i 1 := by
    intro j
    funext a
    by_cases ha : a = i <;> by_cases hj : j = i <;>
      simp [B₀, t, ha, hj, Matrix.updateRow_apply, Matrix.one_apply, Pi.single_apply, Function.update_apply, eq_comm]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet' ▸ hT0), hdet', le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (hd.mem_locP_L P x).1 hx
    obtain ⟨s, hs1, r, e, e'⟩ := hred x hx1
    have h1 : r i + ∑ j ∈ Finset.univ.erase i, r j * c j ∈ P.1.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      refine (mul_eq_zero.1 ?_).resolve_right hi
      rw [hx2, mul_zero, hgs, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at e'
      rw [← e', map_add, map_sum, add_mul, Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul, mul_assoc, ← hc']
    obtain ⟨s', hs', b, hb⟩ := exists_mul_eq_of_unif hT hT2 h1
    refine (Formalism.L2.Col.mem_locP P.1 _ x).2 ⟨s' * s, fun hm => (P.1.isPrime.mem_or_mem hm).elim hs' hs1, ?_⟩
    have h2 : s' • r = ∑ j, (Function.update (s' • r) i b) j • fun a => B₀ a j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hcol, if_pos rfl, Function.update_self,
        Finset.sum_congr rfl fun j hj => by rw [hcol, if_neg (Finset.ne_of_mem_erase hj),
          Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
      funext a
      by_cases ha : a = i
      · subst ha
        simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        rw [Finset.sum_congr rfl fun j hj => by rw [Pi.single_eq_of_ne' (Finset.ne_of_mem_erase hj)]]
        rw [mul_add, Finset.mul_sum] at hb
        rw [mul_comm b, ← hb, add_assoc, ← Finset.sum_add_distrib, Finset.sum_eq_zero fun j _ => by ring, add_zero]
      · simp [Finset.sum_apply, Pi.single_apply, ha]
    have h3 : (s' * s) • x = ∑ j, (Function.update (s' • r) i b) j • fun a => algebraMap (𝓞 E) E (B₀ a j) := by
      funext a
      have h4 := congrArg (fun y => algebraMap (𝓞 E) E (y a)) h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul] at h4
      rw [mul_smul, e]
      simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
      exact h4
    rw [h3]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · refine localization_le_of_le_localization P.1 (Submodule.span_le.2 ?_)
    rintro _ ⟨j, rfl⟩
    refine (hd.mem_locP_L P _).2 ⟨hle (hvec fun a => B₀ a j), (hg fun a => B₀ a j).symm.trans ?_⟩
    rw [hcol]
    split_ifs with hj
    · rw [map_smul, quot_smul_def, Ideal.Quotient.eq_zero_iff_mem.2 hT, zero_mul]
    · rw [map_sub, map_smul, quot_smul_def, ← hc', sub_self]

end Ker

section Data

theorem unramOver_of_mem {X : Fields} {S : Set ℕ} (mu : Tup X.F X.E X.K S) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) :
    UnramOver (mu : Chr X.F X.E X.K) p := by
  intro v hv hq
  have h1 : GoodPl X.E S v := by
    by_contra hg
    exact hq (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 mu.2).2 v) hg)
  have h2 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ p := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hv
  haveI := v.isPrime
  have h3 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p := ((Nat.dvd_prime hp).1 h2).resolve_left CharP.ringChar_ne_one
  exact h1.2.2 (show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S from h3 ▸ hS)

theorem stdOver_of_stdAtT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {n : ℕ}
    {SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n (Pr.vT u) SG) (h : StdAtT d.1) : StdOver (Pr.T u) d.1.N := by
  intro Q hQ
  rw [← hPr.piT_norm u] at hQ
  rcases Q.isPrime.mem_or_mem hQ with h1 | h1
  · exact h ⟨Q, (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) Q).2 h1⟩
  · have h2 := h ⟨conjPrime₂ Q, (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).2 h1⟩
    have h3 := GlobalTheory.StdReps.localization_conj_le_of_le d.2.lat.fg d.2.uni stdLat_unimodular h2.le
    have h4 := GlobalTheory.StdReps.localization_conj_le_of_le stdLat_lattice.fg stdLat_unimodular d.2.uni h2.ge
    rw [GlobalTheory.CharVal.conjP_conjP'] at h3 h4
    exact le_antisymm h4 h3

end Data

theorem pTerm_std : GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.JetMoments → GlobalTheory.Published.InducedSimpleLowestAlcove → ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → JetsAll Z.W sel mu cst (ambOf s B χ cD) u i (i + 1) → AlcoveAt Z.W u (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), seenC Z.Pr u w → ∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L := by
  intro hJ hKnown Z H s cc δ B χ cD sel S mu cst u i hi hyp hjets halc w hw SG SG' d fr d' fr' Ξ₀ hstd hfr hfr' hbox hint y hy
  classical
  have hZ := hyp.ok
  have hPr := hZ.primes
  have hTp := hPr.T_prime u
  haveI : Fact (Z.Pr.T u).Prime := ⟨hTp⟩
  obtain ⟨τ₀⟩ : Nonempty Z.X.Tau := Fintype.card_pos_iff.1 hZ.fields.f_pos
  have hP : ∀ τ, pullW τ w ∈ Z.Pr.vT u := (seenC_iff hPr u w).1 hw
  have hTw : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.K) ∈ w.asIdeal := by
    have h1 := (mem_pullW τ₀ w _).1 (T_mem hPr u ⟨_, hP τ₀⟩)
    rwa [map_natCast] at h1
  have hT0 : (Z.Pr.T u : Z.X.K) ≠ 0 := Nat.cast_ne_zero.2 hTp.ne_zero
  obtain ⟨ι, hι⟩ := GlobalTheory.DatumJets.Place.exists_embedding (p := Z.Pr.T u) w hTw
  have hind : Induces ι w := fun y => by rw [hι]; rfl
  have hσ := norm_le_one_iff ι w hind
  have hTS : Z.Pr.T u ∈ S := hyp.host (Or.inr ⟨u, rfl⟩)
  have hgS : ∀ k, Z.Pr.g k ∈ S := fun k => hyp.host (Or.inl (by fin_cases k <;> simp))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩

  obtain ⟨m0, eta, htied, hmu⟩ := hyp.tied
  have hscal := ((((GlobalTheory.CharVal.charValAtT Z H s χ u hZ hyp.ana.1 hyp.ana.2.1 hyp.ana.2.2.2.2.1 hyp.chiK).2.2 m0 eta htied sel
    hyp.isSel S mu (unramOver_of_mem mu hTp hTS) (fun k => unramOver_of_mem mu (hPr.g_prime k) (hgS k)) cst hmu ⟨i, hi⟩).1
    w hTw).1).2 _ _ d.1.N fr d'.1.N fr' hsd hsd' (stdOver_of_stdAtT hPr u d hstd.1) (stdOver_of_stdAtT hPr u d' hstd.2) hfr hfr'

  have hcopT : Nat.Coprime (Ideal.absNorm cc) (Z.Pr.T u) := by
    have h1 := hyp.cop _ (Finset.mem_union_left _ (hP τ₀))
    rwa [hPr.vT_norm u _ (hP τ₀)] at h1
  obtain ⟨un, hun, hmom⟩ := hJ Z hZ H s cc δ B χ cD hyp.ana u hcopT w ι hind
  have hclo := (hmom sel S mu cst hyp.isSel hyp.host (fun P hP => hyp.cop P (Finset.mem_union_right _ hP)) i _ hi rfl SG SG' d d'
    hstd.1 hstd.2 Ξ₀ (fun x _ => ⟨hint x, hbox.2 x⟩)).2 hw

  obtain ⟨s₀, s', hwt, -⟩ := GlobalTheory.ColPeriod.chainWeights Z.X Z.Pr Z.R Z.W u i hi
  have hloc : ∀ τ, localization₂ (pullW τ w).asIdeal d.1.Lsh = d.1.at (pullW τ w) := fun τ =>
    d.2.locP_Lsh (sepElt_of_ok hPr u) ⟨_, hP τ⟩
  have hM : LatWithBasis w (fun τ => tauLat Z.X.emb τ d.1.Lsh) 1 := fun τ =>
    ⟨(tauLatLattice _ _ _ _ Z.X.emb τ _ d.2.Lsh_lattice).fg, by
      have h1 := isBasisAt_tauLat Z.X.emb w τ (pullW τ w) (fun _ h => h) (isBasisAt_one ((hloc τ).trans (hstd.1 ⟨_, hP τ⟩)))
      rwa [map_one] at h1⟩
  choose BE hBE hBE' using fun τ => exists_basis_ker d'.2 ⟨_, hP τ⟩ (hstd.2 ⟨_, hP τ⟩) (T_unif hZ.fields hPr u ⟨_, hP τ⟩).1
    (T_unif hZ.fields hPr u ⟨_, hP τ⟩).2
  have hMW : LatWithBasis w (fun τ => tauLat Z.X.emb τ d'.1.L) fun τ => Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ) := fun τ =>
    ⟨(tauLatLattice _ _ _ _ Z.X.emb τ _ d'.2.L_lattice).fg, isBasisAt_tauLat Z.X.emb w τ (pullW τ w) (fun _ h => h) (hBE' τ)⟩
  have hfac : detFac s₀ s' (1 : Z.X.Tau → GL (Fin (Z.R.N i)) Z.X.K)
      (fun τ => Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ)) =
      (Z.Pr.T u : Z.X.K) ^ ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift := by
    have h1 : ∀ τ, ((Matrix.GeneralLinearGroup.map (Z.X.emb τ) (BE τ)).val).det = Z.Pr.T u := fun τ => by
      have h2 := congrArg (Z.X.emb τ) (hBE τ)
      rw [RingHom.map_det, map_natCast, map_natCast] at h2
      exact h2
    simp only [detFac, h1, Pi.one_apply, Units.val_one, Matrix.det_one, one_zpow, one_mul, GlobalTheory.JetPoint.detShift_eq hwt]
    induction (Finset.univ : Finset Z.X.Tau) using Finset.induction_on with
    | empty => simp
    | insert τ t h ih => rw [Finset.prod_insert h, Finset.sum_insert h, zpow_add₀ hT0, ih]
  have hin := inClosure_of ι (Z.W.lamTrue u i) s' (fun τ => tauLat Z.X.emb τ d.1.Lsh) (fun τ => tauLat Z.X.emb τ d'.1.L)
    ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * Z.R.N i))⁻¹
    (GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.jetSum (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x)
    (Ms := GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable.RatIdx (ambOf s B χ cD) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) d.1.N d'.1.N
      fun x => phiT Z.X.K d.1 d'.1 x * Ξ₀ x) (Sup := suppP d.1 d'.1)
    (fun x τ => Matrix.of fun α β => un τ * ι (Z.X.emb τ (LinearMap.toMatrix' (adj x) α β)))
    (fun m hm x hx _ => hjets _ _ hsd hsd' x hx m fun τ => by
      refine (hm τ).trans (Finset.sum_congr rfl fun a _ => ?_)
      rw [hwt.2.2 τ]
      ring)
    (fun x hx τ => admissible_of_integral_conj_le Z.X.emb _ ι w hσ τ (pullW τ w) (fun _ h => h) _ (fun y hy => by
      have h1 := (d'.2.mem_locP_L ⟨_, hP τ⟩ y).1 (Formalism.L2.Col.le_locP _ _ hy)
      rw [LinearMap.toMatrix'_mulVec, hloc]
      exact hx ⟨_, hP τ⟩ y h1.1 h1.2) _ ((val_le_one_iff _).2 (hun τ).le))
    (by
      rw [map_inv₀, map_pow, map_natCast]
      exact hclo)
  have hy' : y ∈ HAt w (Z.W.lamTrue u i) fun τ => tauLat Z.X.emb τ d.1.Lsh := by
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨t, ht, delLeNab _ _ _ _ _ hty⟩
  obtain ⟨G, hG, hG'⟩ := GlobalTheory.JetPoint.closureIntegral Z.X.K w _ _ _ ι hσ _ _ _ _ _ _ s₀ s' _ hwt _ _ _ _ hM hMW _ _ hin y hy'
  rw [term, ker, stepT, GlobalTheory.ColPeriod.kerOf_thDistC _ _ _ (GlobalTheory.ColPeriod.cAof_pos sel mu cst)
    (GlobalTheory.ColPeriod.cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat, LinearMap.smul_apply, smul_comm, hG', hfac, smul_smul (_ ^ _),
    zpow_sub₀ hT0, zpow_natCast]
  refine GlobalTheory.ColPeriod.smul_mem_localizationAt_of_le w _ (le_of_eq hscal) ?_
  rw [div_mul_eq_mul_div, mul_inv_cancel_left₀ (pow_ne_zero _ hT0), div_self (zpow_ne_zero _ hT0), one_smul]
  rw [GlobalTheory.KerT.localization_delAtr_eq_localization_nabAtr hKnown Z.X _ (Z.Pr.T u) _ hTp halc w hTw _ d'.2.L_lattice]
  exact hG

end GlobalTheory.KerT.PStd
