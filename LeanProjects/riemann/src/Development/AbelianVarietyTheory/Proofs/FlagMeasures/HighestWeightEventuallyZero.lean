import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDerivPhiConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivExpEntry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.SchmidIntegral

variable {n : ℕ}

local notation "Mt" => Matrix (Fin n) (Fin n) ℂ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma continuous_inv_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => (toMK k)⁻¹) := by
  have e : (fun k : KG ε => (toMK k)⁻¹) =
      fun k : KG ε => ((((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) := by
    funext k
    exact (Matrix.coe_units_inv _).symm
  rw [e]
  exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)

private lemma one_mem_Omega : (1 : Mt) ∈ Omega n := by
  simp only [GlobalTheory.Dec.Omega, Set.mem_setOf_eq]
  intro i
  simp only [Formalism.MainNotions.S.leadMinor, Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  exact one_ne_zero

lemma eventually_mem_kConjNonzeroMinorsSet (ε : Fin n → Bool) : ∀ᶠ z : Mt in nhds 1, z ∈ U1 ε := by
  have hK : IsCompact (Kset ε) := (Formalism.REAL.kFacts n ε).2.1
  have hc : Continuous (fun p : Mt × Mt => p.2ᴴ * p.1 * p.2) :=
    (continuous_snd.matrix_conjTranspose.matrix_mul continuous_fst).matrix_mul continuous_snd
  have hev : ∀ᶠ z : Mt in nhds 1, ∀ k ∈ Kset ε, kᴴ * z * k ∈ Omega n := by
    refine hK.eventually_forall_of_forall_eventually fun k hk => ?_
    have h1 : kᴴ * (1 : Mt) * k ∈ Omega n := by
      have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk.1
      rw [Matrix.mul_one, ← Matrix.star_eq_conjTranspose, hu]
      exact one_mem_Omega
    exact hc.continuousAt.preimage_mem_nhds (GlobalTheory.Dec.PsiEig.isOpen_Omega.mem_nhds h1)
  filter_upwards [hev] with z hz
  intro k hk
  have hu : kᴴ * k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hk.1
  rw [Matrix.inv_eq_left_inv hu]
  exact hz k hk

private lemma toMK_mem_Kset {ε : Fin n → Bool} (k : KG ε) : toMK k ∈ Kset ε :=
  (Formalism.REAL.mem_KG ε k).mp k.2

private lemma continuous_toMK_inv_mul_mul_toMK' (ε : Fin n → Bool) (Y : Mt) :
    Continuous (fun k : KG ε => (toMK k)⁻¹ * Y * toMK k) :=
  ((continuous_inv_toMK ε).matrix_mul continuous_const).matrix_mul (GlobalTheory.Dec.PsiEig.continuous_toMK ε)

def dInt {ε : Fin n → Bool} (l : Fin n → Fin n → Mt → ℂ) (X z : Mt) (k : KG ε) : ℂ :=
  ∑ c, ∑ d, ((toMK k)⁻¹ * X * toMK k) c d * l c d ((toMK k)⁻¹ * z * toMK k)

lemma continuousOn_dInt {ε : Fin n → Bool} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n)) (X : Mt) :
    ContinuousOn (fun x : Mt × KG ε => dInt l X x.1 x.2) (U1 ε ×ˢ Set.univ) := by
  show ContinuousOn (fun x : Mt × KG ε => ∑ c, ∑ d, ((toMK x.2)⁻¹ * X * toMK x.2) c d *
    l c d ((toMK x.2)⁻¹ * x.1 * toMK x.2)) _
  have hc : Continuous (fun x : Mt × KG ε => (toMK x.2)⁻¹ * x.1 * toMK x.2) :=
    (((continuous_inv_toMK ε).comp continuous_snd).matrix_mul continuous_fst).matrix_mul
      ((GlobalTheory.Dec.PsiEig.continuous_toMK ε).comp continuous_snd)
  have hX : Continuous (fun x : Mt × KG ε => (toMK x.2)⁻¹ * X * toMK x.2) :=
    (continuous_toMK_inv_mul_mul_toMK' ε X).comp continuous_snd
  have hmaps : Set.MapsTo (fun x : Mt × KG ε => (toMK x.2)⁻¹ * x.1 * toMK x.2) (U1 ε ×ˢ Set.univ) (Omega n) :=
    fun x hx => hx.1 _ (toMK_mem_Kset x.2)
  refine continuousOn_finset_sum _ fun c _ => continuousOn_finset_sum _ fun d _ => ?_
  exact (hX.matrix_elem c d).continuousOn.mul ((hl c d).comp hc.continuousOn hmaps)

lemma integrable_dInt {ε : Fin n → Bool} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n)) (X : Mt) {z : Mt} (hz : z ∈ U1 ε) {w : KG ε → ℂ}
    (hw : Continuous w) : Integrable (fun k => dInt l X z k * w k) (muK ε) := by
  have hcont : Continuous (fun k => dInt l X z k * w k) :=
    ((continuousOn_dInt hl X).comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hz, Set.mem_univ _⟩).mul hw
  exact integrableOn_univ.mp (hcont.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ)

private lemma leadMinor_map_star (M : Mt) (m : ℕ) (hm : m ≤ n) :
    Formalism.MainNotions.S.leadMinor (M.map star) m hm = star (Formalism.MainNotions.S.leadMinor M m hm) := by
  simp only [Formalism.MainNotions.S.leadMinor]
  have e : (M.map star).submatrix (Fin.castLE hm) (Fin.castLE hm) =
      ((M.submatrix (Fin.castLE hm) (Fin.castLE hm))ᴴ)ᵀ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  rw [e, Matrix.det_transpose, Matrix.det_conjTranspose]

private lemma map_star_mem_Omega {M : Mt} (h : M ∈ Omega n) : M.map star ∈ Omega n := by
  simp only [GlobalTheory.Dec.Omega, Set.mem_setOf_eq] at h ⊢
  intro i
  rw [leadMinor_map_star]
  exact star_ne_zero.mpr (h i)

private lemma mul_mem_UJset_flag_measures {ε : Fin n → Bool} {a b : Mt} (ha : inUJ ε a) (hb : inUJ ε b) :
    a * b ∈ UJset ε := by
  have ha' : aᴴ * Jm ε * a = Jm ε := ha
  have hb' : bᴴ * Jm ε * b = Jm ε := hb
  show (a * b)ᴴ * Jm ε * (a * b) = Jm ε
  have e : (a * b)ᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, ha', hb']

lemma rd_integral {ε : Fin n → Bool} {lam : Fin n → ℝ} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n))
    (hd : ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Mt, inG ε X →
      HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star))
        (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0)
    {w : KG ε → ℂ} (hw : Continuous w) {z X : Mt} (hz : inUJ ε z) (hX : inG ε X)
    (h : ∀ᶠ y in nhds z, y ∈ U1 ε) :
    Rd X (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * w k ∂(muK ε)) z =
      ∫ k, dInt l X z k * w k ∂(muK ε) := by
  have hcurve : Continuous (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • X)) :=
    continuous_iff_continuousAt.mpr fun t => (GlobalTheory.Dec.PsiEig.hasDerivAt_curveR z X t).continuousAt
  have hS0 : ∀ᶠ s : ℝ in nhds 0, z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε := by
    have ht : Filter.Tendsto (fun s : ℝ => z * NormedSpace.exp ((s : ℂ) • X)) (nhds 0) (nhds z) := by
      simpa using hcurve.tendsto 0
    exact ht.eventually h
  have hF : ∀ t ∈ {s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε}, Continuous (fun k : KG ε =>
      Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star) * w k) := by
    intro t ht
    have hmem : ∀ k : KG ε,
        ((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star ∈ Omega n :=
      fun k => map_star_mem_Omega (ht _ (toMK_mem_Kset k))
    have hcm : Continuous (fun k : KG ε =>
        ((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k).map star) :=
      (continuous_toMK_inv_mul_mul_toMK' ε _).matrix_map continuous_star
    refine Continuous.mul ?_ hw
    exact continuous_iff_continuousAt.mpr fun k =>
      ContinuousAt.comp (g := Phi lam) (GlobalTheory.PhiConjDeriv.analyticAt_Phi lam (hmem k)).continuousAt
        hcm.continuousAt
  have hF' : ContinuousOn (fun x : ℝ × KG ε => dInt l X (z * NormedSpace.exp ((x.1 : ℂ) • X)) x.2 * w x.2)
      ({s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε} ×ˢ Set.univ) := by
    have h1 : ContinuousOn (fun x : ℝ × KG ε => dInt l X (z * NormedSpace.exp ((x.1 : ℂ) • X)) x.2)
        ({s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε} ×ˢ Set.univ) :=
      (continuousOn_dInt hl X).comp
        (f := fun x : ℝ × KG ε => (z * NormedSpace.exp ((x.1 : ℂ) • X), x.2))
        ((hcurve.comp continuous_fst).prodMk continuous_snd).continuousOn
        fun x hx => Set.mk_mem_prod (hx.1 : z * NormedSpace.exp ((x.1 : ℂ) • X) ∈ U1 ε) (Set.mem_univ _)
    exact h1.mul (hw.comp continuous_snd).continuousOn
  have hD : ∀ k : KG ε, ∀ t ∈ {s : ℝ | z * NormedSpace.exp ((s : ℂ) • X) ∈ U1 ε},
      HasDerivAt (fun s : ℝ =>
        Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((s : ℂ) • X)) * toMK k).map star) * w k)
        (dInt l X (z * NormedSpace.exp ((t : ℂ) • X)) k * w k) t := by
    intro k t ht
    have hk := toMK_mem_Kset k
    have hgU : z * NormedSpace.exp ((t : ℂ) • X) ∈ UJset ε :=
      mul_mem_UJset_flag_measures hz (Formalism.REAL.expUJ n ε X hX t)
    have hgO : (toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X)) * toMK k ∈ Omega n := ht _ hk
    have H := hd (toMK k) hk _ hgU hgO X hX
    have H2 := (HasDerivAt.comp_sub_const (f := fun u : ℝ => Phi lam (((toMK k)⁻¹ *
      (z * NormedSpace.exp ((t : ℂ) • X) * NormedSpace.exp ((u : ℂ) • X)) * toMK k).map star)) t t
      (by rw [sub_self]; exact H)).mul_const (w k)
    have hfun : (fun s : ℝ =>
        Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((s : ℂ) • X)) * toMK k).map star) * w k) =
        fun s : ℝ => Phi lam (((toMK k)⁻¹ * (z * NormedSpace.exp ((t : ℂ) • X) *
          NormedSpace.exp (((s - t : ℝ) : ℂ) • X)) * toMK k).map star) * w k := by
      funext s
      have e : t + (s - t) = s := by ring
      rw [Matrix.mul_assoc z, ← Formalism.REAL.oneParam n X t (s - t), e]
    rw [hfun]
    exact H2
  have key := GlobalTheory.Dec.PsiEig.hasDerivAt_integral_compact (muK ε) hS0 hF hF' hD
  have e0 : z * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = z := by simp
  simp only [e0] at key
  exact key.deriv

private lemma dInt_add_smul {ε : Fin n → Bool} (l : Fin n → Fin n → Mt → ℂ) (X Y z : Mt) (k : KG ε)
    (c : ℂ) : dInt l (X + c • Y) z k = dInt l X z k + c * dInt l Y z k := by
  simp only [dInt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma eab_integral {ε : Fin n → Bool} {lam : Fin n → ℝ} {l : Fin n → Fin n → Mt → ℂ}
    (hl : ∀ c d, ContinuousOn (l c d) (Omega n))
    (hd : ∀ k ∈ Kset ε, ∀ g ∈ UJset ε, k⁻¹ * g * k ∈ Omega n → ∀ X : Mt, inG ε X →
      HasDerivAt (fun t : ℝ => Phi lam ((k⁻¹ * (g * NormedSpace.exp ((t : ℂ) • X)) * k).map star))
        (∑ c, ∑ d, (k⁻¹ * X * k) c d * l c d (k⁻¹ * g * k)) 0)
    {w : KG ε → ℂ} (hw : Continuous w) {z : Mt} (hz : inUJ ε z) (h : ∀ᶠ y in nhds z, y ∈ U1 ε)
    (a b : Fin n) :
    Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * w k ∂(muK ε)) z =
      ∫ k, dInt l (Matrix.single a b 1) z k * w k ∂(muK ε) := by
  have hc := Formalism.REAL.cpartMem n ε (Matrix.single a b 1)
  have hz1 : z ∈ U1 ε := h.self_of_nhds
  have i1 := integrable_dInt hl (cpart1 ε (Matrix.single a b 1)) hz1 hw
  have i2 := integrable_dInt hl (cpart2 ε (Matrix.single a b 1)) hz1 hw
  show Rd (cpart1 ε (Matrix.single a b 1)) _ z + Complex.I * Rd (cpart2 ε (Matrix.single a b 1)) _ z = _
  rw [rd_integral hl hd hw hz hc.1 h, rd_integral hl hd hw hz hc.2.1 h, ← integral_const_mul,
    ← integral_add i1 (i2.const_mul _)]
  conv_rhs => rw [hc.2.2.1]
  congr 1
  funext k
  rw [dInt_add_smul]
  ring

lemma conj_single_apply (A B : Mt) (a b c d : Fin n) :
    (A * Matrix.single a b (1 : ℂ) * B) c d = A c a * B b d := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_single_apply_same, mul_one]
  · intro j _ hj
    simp [hj]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

lemma sum_comm_four (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem eab_integral_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsURepOn (UJset ε) σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∀ y : H, ∀ᶠ g : UJ ε in nhds 1, ∑ a, ∑ b, Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) * (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g) = 0 := by
  intro n ε H _ _ _ σ V E lam u hσ hD hK hfin G hG y
  obtain ⟨l, hl0, hlc, hd⟩ := GlobalTheory.PhiConjDeriv.exists_deriv_Phi_conj n ε lam
  have hσc : Continuous (fun k : KG ε => σ (toMK k) (u : H)) :=
    (hσ.2.2 (u : H)).comp_continuous (GlobalTheory.Dec.PsiEig.continuous_toMK ε) fun k => (k : UJ ε).2
  have hw : ∀ a b : Fin n, Continuous (fun k : KG ε =>
      ⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) :=
    fun a b => (continuous_const.inner hσc).mul (hσc.inner continuous_const)
  have hU : ∀ᶠ g : UJ ε in nhds 1, ∀ᶠ x in nhds (umat g), x ∈ U1 ε := by
    have h1 : ∀ᶠ x : Matrix (Fin n) (Fin n) ℂ in nhds 1, ∀ᶠ x' in nhds x, x' ∈ U1 ε :=
      (eventually_mem_kConjNonzeroMinorsSet ε).eventually_nhds
    have hc : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
    exact (hc.tendsto 1).eventually h1
  have hpt : ∀ k : KG ε, ∀ z : Matrix (Fin n) (Fin n) ℂ, ∑ a, ∑ b, dInt l (Matrix.single a b 1) z k *
      (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) = 0 := by
    intro k z
    have hk := toMK_mem_Kset k
    simp only [dInt, conj_single_apply, Finset.sum_mul]
    rw [sum_comm_four]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hdc : d < c
    · simp [hl0 c d _ hdc]
    · have hv := GlobalTheory.Jet.VminusK.vminus_K n ε H σ V E (LamOf ε lam) u hσ hD hK hfin G hG (toMK k) hk c d hdc
      rw [← mul_zero (l c d ((toMK k)⁻¹ * z * toMK k) * ⟪y, σ (toMK k) (u : H)⟫_ℂ), ← hv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
  filter_upwards [hU] with g hg
  have hz : inUJ ε (umat g) := g.2
  have hz1 : umat g ∈ U1 ε := hg.self_of_nhds
  calc _ = ∑ a, ∑ b, ∫ k, dInt l (Matrix.single a b 1) (umat g) k *
        (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        exact eab_integral hlc hd (hw a b) hz hg a b
    _ = ∫ k, ∑ a, ∑ b, dInt l (Matrix.single a b 1) (umat g) k *
        (⟪y, σ (toMK k) (u : H)⟫_ℂ * ⟪σ (toMK k) (u : H), (at1 G a b : V)⟫_ℂ) ∂(muK ε) := by
        rw [integral_finset_sum _ fun a _ =>
          integrable_finset_sum _ fun b _ => integrable_dInt hlc _ hz1 (hw a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ fun b _ => integrable_dInt hlc _ hz1 (hw a b)]
    _ = 0 := by simp only [hpt, integral_zero]

end GlobalTheory.Jet.SchmidIntegral
