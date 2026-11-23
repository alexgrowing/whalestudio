import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLetterOfLocalEmbedding
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.HostJumpWin

open Formalism.MainNotions.AdmissibleParameterJ

variable {D : D7}

theorem refl_refl (q : ℚ) : AdmissibleParameterJ.refl D (AdmissibleParameterJ.refl D q) = q := by unfold AdmissibleParameterJ.refl; ring

theorem refl_injective : Function.Injective (AdmissibleParameterJ.refl D) := fun a b h => by
  have := congrArg (AdmissibleParameterJ.refl D) h
  rwa [refl_refl, refl_refl] at this

theorem ncard_reflS (S : Set ℚ) : (reflS D S).ncard = S.ncard :=
  Set.ncard_preimage_of_injective_subset_range refl_injective (fun q _ => ⟨AdmissibleParameterJ.refl D q, refl_refl q⟩)

theorem finite_reflS {S : Set ℚ} (h : S.Finite) : (reflS D S).Finite :=
  Set.Finite.preimage (refl_injective.injOn) h

theorem int_reflS {S : Set ℚ} (hS : ∀ q ∈ S, ∃ z : ℤ, q = z) : ∀ q ∈ reflS D S, ∃ z : ℤ, q = z := by
  intro q hq
  obtain ⟨z, hz⟩ := hS _ hq
  refine ⟨(D.R.t : ℤ) - 1 - z, ?_⟩
  have e : AdmissibleParameterJ.refl D q = (D.R.t : ℚ) - 1 - q := rfl
  push_cast
  linarith

def intPart (S : Set ℚ) (h : S.Finite) : Finset ℤ :=
  (Set.Finite.preimage (Int.cast_injective.injOn) h : ((Int.cast : ℤ → ℚ) ⁻¹' S).Finite).toFinset

theorem mem_intPart {S : Set ℚ} (h : S.Finite) (a : ℤ) : a ∈ intPart S h ↔ (a : ℚ) ∈ S := by
  simp [intPart]

theorem card_intPart {S : Set ℚ} (h : S.Finite) (hS : ∀ q ∈ S, ∃ z : ℤ, q = z) :
    (intPart S h).card = S.ncard := by
  unfold intPart
  refine (Set.ncard_eq_toFinset_card _ _).symm.trans ?_
  exact Set.ncard_preimage_of_injective_subset_range Int.cast_injective
    (fun q hq => let ⟨z, hz⟩ := hS q hq; ⟨z, hz.symm⟩)

theorem exists_int_eq_jumpBlockCentreOffset : ∃ k : ℤ, c0 D = k := by
  obtain ⟨n, hn⟩ := D.R.t_odd
  refine ⟨n, ?_⟩
  unfold c0
  rw [hn]
  push_cast
  ring

theorem sz_int (j : ℕ) (ρ : D.what₂.Tau) : ∃ z : ℤ, sz D j ρ = z := by
  unfold sz
  split_ifs with h
  · exact (D.hc ρ).e_int _
  · exact ⟨0, by simp⟩

theorem cloudJ_finite (j : ℕ) (ρ : D.what₂.Tau) : (cloudJ D j ρ).Finite :=
  (Set.finite_range (fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D)).subset
    (fun _ ⟨a, ha⟩ => ⟨a, ha.symm⟩)

theorem lowJ_finite (j : ℕ) (ρ : D.what₂.Tau) : (lowJ D j ρ).Finite :=
  (Set.finite_range (fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)).subset
    (fun _ ⟨a, ha⟩ => ⟨a, ha.symm⟩)

theorem cloudJ_int (j : ℕ) (ρ : D.what₂.Tau) : ∀ q ∈ cloudJ D j ρ, ∃ z : ℤ, q = z := by
  rintro q ⟨a, rfl⟩
  obtain ⟨z1, h1⟩ := sz_int (D := D) j ρ
  obtain ⟨z2, h2⟩ := (D.hc ρ).v_int a
  obtain ⟨z3, h3⟩ := exists_int_eq_jumpBlockCentreOffset (D := D)
  exact ⟨z1 + z2 + z3, by rw [h1, h2, h3]; push_cast; ring⟩

theorem lowJ_int (j : ℕ) (ρ : D.what₂.Tau) : ∀ q ∈ lowJ D j ρ, ∃ z : ℤ, q = z := by
  rintro q ⟨a, rfl⟩
  obtain ⟨z1, h1⟩ := sz_int (D := D) j ρ
  obtain ⟨z2, h2⟩ := (D.hc ρ).b_int a
  obtain ⟨z3, h3⟩ := exists_int_eq_jumpBlockCentreOffset (D := D)
  exact ⟨z1 - z2 + z3, by rw [h1, h2, h3]; push_cast; ring⟩

theorem mem_blockJ (a : ℤ) : (a : ℚ) ∈ blockJ D ↔ 0 ≤ a ∧ a < D.R.t := by
  constructor
  · rintro ⟨c, hc, h⟩
    have e : a = (c : ℤ) := by exact_mod_cast h
    subst e
    exact ⟨by positivity, by exact_mod_cast hc⟩
  · rintro ⟨h0, h1⟩
    refine ⟨a.toNat, by omega, ?_⟩
    have := Int.toNat_of_nonneg h0
    exact_mod_cast this.symm

theorem mem_reflS_blockJ (a : ℤ) : (a : ℚ) ∈ reflS D (blockJ D) ↔ 0 ≤ a ∧ a < D.R.t := by
  show AdmissibleParameterJ.refl D (a : ℚ) ∈ blockJ D ↔ _
  have e : AdmissibleParameterJ.refl D (a : ℚ) = (((D.R.t : ℤ) - 1 - a : ℤ) : ℚ) := by unfold AdmissibleParameterJ.refl; push_cast; ring
  rw [e, mem_blockJ]
  omega

theorem mem_JJ (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (a : ℤ) : (a : ℚ) ∈ JJ D up j ρ ↔
    (a : ℚ) ∈ cloudT D up j ρ ∨ (a : ℚ) ∈ lowT D up j ρ ∨ (0 ≤ a ∧ a < D.R.t) := by
  cases up
  · rw [← mem_reflS_blockJ]
    simp only [JJ, cloudT, lowT, Bool.false_eq_true, if_false, Jm, Jp, reflS, Set.mem_setOf_eq, Set.mem_union]
    tauto
  · rw [← mem_blockJ]
    simp only [JJ, cloudT, lowT, if_true, Jp, Set.mem_union]
    tauto

theorem sz_bounds (L : SizeData₂ D) (P : ParameterChoice' D L) (hP : AdmPar L) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) :
    L.etaSz + D.R.t + 1 + ((D.R.t : ℝ) - 1) / 2 < (sz D j ρ : ℝ) ∧
      (sz D j ρ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  have hw : Formalism.BasicNotions.wj D j ρ = (sz D j ρ : ℝ) := by
    unfold Formalism.BasicNotions.wj sz
    split_ifs <;> simp
  rw [← hw]
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    positivity
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hn : (1 : ℝ) ≤ (D.R.n : ℝ) := by
    exact_mod_cast D.R.ord_pos
  have hw''0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    exact div_nonneg hb'.le (by positivity)
  have hw''b' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    unfold Scale.w''
    exact div_le_self hb'.le (by nlinarith)
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hte : (D.R.t : ℝ) ≤ L.etaSz := hP.2.2.2
  have hmt := P.mteta
  have h2 : 2 * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have := mul_le_mul_of_nonneg_right hm (mul_nonneg (by positivity) L.etaSz_pos.le : (0 : ℝ) ≤ ((D.R.t : ℝ) + 1) * L.etaSz)
    nlinarith
  have hbig : L.etaSz + D.R.t + 1 + ((D.R.t : ℝ) - 1) / 2 < L.sc.w'' D.R.n := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * D.R.t + 1) (by linarith : (0 : ℝ) ≤ L.etaSz - D.R.t)]
  have hw3 := hP.2.1
  have hbx : 0 ≤ L.sc.b' / L.sc.x := by positivity
  by_cases htop : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', he⟩ := Finset.mem_image.1 htop
    obtain ⟨h1, h2⟩ := L.win_top j hj1 hj2 ρ ⟨t, ht'⟩ he.symm
    have hbt := L.bT_ge ⟨t, ht'⟩
    have hbt2 := hP.2.2.1 ⟨t, ht'⟩
    constructor <;> linarith
  · by_cases hth : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨h1, h2⟩ := L.win_thick j hj1 hj2 ρ hth
      constructor <;> linarith
    · obtain ⟨h1, h2⟩ := L.win_thin j hj1 hj2 ρ ⟨(D.eTau ρ).2, htop, hth⟩
      constructor <;> linarith

theorem iotaQ_eq (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (z : FractionRing (D.nd.O i)) :
    D.naut.iotaQ i z = ((Br.toLLK (D.nbr i w hw) z : ↥(D.nbr i w hw).LL.1) : Qbar (D.nd.l i)) := by
  have h := (D.loc_tie i w hw).1
  have e : D.naut.iotaQ i = ((D.nbr i w hw).LL.1.val.toRingHom).comp (Br.toLLK (D.nbr i w hw)) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (D.nd.O i))
    ext x
    simp only [RingHom.comp_apply]
    rw [Br.toLLK_alg]
    exact h x
  exact DFunLike.congr_fun e z

theorem typeU_of_emb (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) (g : D.R.GG) (ρ : D.what₂.Tau)
    (hR : ReadAt D i (gEmb C τ) g ρ) (e : Bool)
    (τ₀ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw)
    (h0 : EmbeddingTypeJumps.EmbTypeUe e τ₀) (hτ : ∀ x, τ x = C.inc (τ₀ x)) : TypeU D e g := by
  obtain ⟨g', key, hU⟩ := GlobalTheory.HTW.exists_letter_of_local_embedding D i w hw τ₀
  have hemb : ∀ x, D.host.emb g x = D.host.emb g' x := by
    intro x
    have h1 := DFunLike.congr_fun hR.1 x
    rw [← h1]
    show D.naut.iotaQC i ((C.LL.1.val.toRingHom) (τ (Br.cEw D.nbr i w hw x))) = _
    rw [hτ, key]
    have e1 : (C.LL.1.val.toRingHom) (C.inc (Br.toLLK (D.nbr i w hw)
        (D.nd.embK i (D.embE (D.host.sigmaOf g' x))))) =
        ((Br.toLLK (D.nbr i w hw) (D.nd.embK i (D.embE (D.host.sigmaOf g' x))) :
          ↥(D.nbr i w hw).LL.1) : Qbar (D.nd.l i)) := rfl
    rw [e1, ← iotaQ_eq i w hw, D.naut.iota_LL]
    exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf g' x)
  have hgg : g = g' := (factEmb D.R D.host).1.1 (RingHom.ext hemb)
  subst hgg
  cases e
  · simp only [EmbeddingTypeJumps.EmbTypeUe, Bool.false_eq_true, if_false] at h0
    obtain ⟨-, φ, hφ, hφr⟩ := h0
    show (g ∈ D.R.Psi ↔ false = true)
    simp only [Bool.false_eq_true, iff_false]
    intro hgP
    have hm := ((factEmb D.R D.host).2 g).2 hgP
    have hv := hφr (D.host.sqd)
      (D.embE (D.host.sigmaOf g (D.host.sqd))) (key _).symm
    have he2 : D.what₂.embLL (D.embE (D.host.sigmaOf g (D.host.sqd))) =
        D.host.emb g (D.host.sqd) :=
      DFunLike.congr_fun D.embE_φ₀ _
    rw [he2] at hv
    have hd : (0 : ℝ) < Real.sqrt (D.host.d : ℝ) := by
      have := D.host.qd_big.2
      exact Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < D.host.d))
    simp only [Formalism.HC.HostRaw.cmType, Set.mem_ofPred_eq, Set.mem_setOf_eq] at hm hφ
    rw [hm, hφ] at hv
    have him := congrArg Complex.im hv
    simp at him
    linarith
  · simp only [EmbeddingTypeJumps.EmbTypeUe, if_true] at h0
    show (g ∈ D.R.Psi ↔ true = true)
    simp only [iff_true]
    exact hU.1 h0

theorem jumpBlockCentreOffset_coe_real : ((c0 D : ℚ) : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
  unfold c0
  push_cast
  ring

theorem key_sets (L : SizeData₂ D) (hJb : CloudCentreDistance L) (hJc : jcCondition L) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool)
    (hlo : L.etaSz + D.R.t + 1 + ((D.R.t : ℝ) - 1) / 2 < (sz D j ρ : ℝ))
    (hhi : (sz D j ρ : ℝ) ≤ L.sc.b + L.etaSz + 1) :
    ∃ (s : ℤ) (Jc Jl : Finset ℤ),
      L.etaSz + D.R.t + 1 < (s : ℝ) ∧ (s : ℝ) ≤ L.sc.b + L.etaSz + D.R.t + 1 ∧
      Jc.card = D.R.k - 1 ∧ Jl.card = D.R.m ∧
      (∀ a ∈ Jl,
          ((-L.etaSz + ((D.R.t : ℝ) - 1) / 2 ≤ (a : ℝ) ∧ a ≤ -2) ∨
            ((D.R.t : ℤ) + 1 ≤ a ∧ (a : ℝ) ≤ L.etaSz + ((D.R.t : ℝ) - 1) / 2)) ∧
          ¬ (0 ≤ a ∧ a < D.R.t) ∧ a ≠ -1 ∧ a ≠ D.R.t) ∧
      (up = true → ∀ a ∈ Jc, s ≤ a ∧ (a : ℝ) ≤ s + L.Sc) ∧
      (up = false → ∀ a ∈ Jc, -((s : ℝ) + L.Sc) ≤ a ∧ a ≤ -s) ∧
      ∀ a : ℤ, (a : ℚ) ∈ JJ D up j ρ ↔ a ∈ Jc ∨ a ∈ Jl ∨ (0 ≤ a ∧ a < D.R.t) := by
  obtain ⟨hcl, -, -, hcard1, hcard2, -⟩ := hJb j hj1 hj2 ρ
  obtain ⟨hlows, -, -, -⟩ := hJc j hj1 hj2 ρ
  obtain ⟨zs, hzs⟩ := sz_int (D := D) j ρ
  obtain ⟨kc, hkc⟩ := exists_int_eq_jumpBlockCentreOffset (D := D)
  have hkR : (kc : ℝ) = ((D.R.t : ℝ) - 1) / 2 := by
    rw [← jumpBlockCentreOffset_coe_real, hkc]
    push_cast
    rfl
  have hzR : ((sz D j ρ : ℚ) : ℝ) = (zs : ℝ) := by
    rw [hzs]
    push_cast
    rfl
  have ht1 : (1 : ℝ) ≤ D.R.t := L.t_win.1
  have hS0 : 0 < L.Sc := L.Sc_pos
  have hη : 0 < L.etaSz := L.etaSz_pos
  have hkc0 : (0 : ℝ) ≤ kc := by rw [hkR]; linarith
  have hc0 := jumpBlockCentreOffset_coe_real (D := D)
  rw [hzR] at hlo hhi
  cases up
  ·
    refine ⟨zs - kc, intPart _ (finite_reflS (D := D) (cloudJ_finite j ρ)), intPart _ (finite_reflS (D := D) (lowJ_finite j ρ)),
      ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by simp), ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith
    · rw [card_intPart _ (int_reflS (D := D) (cloudJ_int j ρ)), ncard_reflS (D := D), hcard1]
    · rw [card_intPart _ (int_reflS (D := D) (lowJ_int j ρ)), ncard_reflS (D := D), hcard2]
    · intro a ha
      rw [mem_intPart] at ha
      have hq := hlows _ ha
      have e : AdmissibleParameterJ.refl D (a : ℚ) = (D.R.t : ℚ) - 1 - a := rfl
      rw [e] at hq
      have hcast : (((D.R.t : ℚ) - 1 - a : ℚ) : ℝ) = (D.R.t : ℝ) - 1 - a := by push_cast; ring
      rw [hcast, hc0] at hq
      have key : a ≤ -2 ∨ (D.R.t : ℤ) + 1 ≤ a := by
        rcases hq with ⟨-, h⟩ | ⟨h, -⟩
        · right
          have : ((D.R.t : ℤ) - 1 - a : ℚ) ≤ -2 := by push_cast; linarith
          have : (D.R.t : ℤ) - 1 - a ≤ -2 := by exact_mod_cast this
          omega
        · left
          have : ((D.R.t : ℤ) + 1 : ℚ) ≤ ((D.R.t : ℤ) - 1 - a : ℤ) := by push_cast; linarith
          have : (D.R.t : ℤ) + 1 ≤ (D.R.t : ℤ) - 1 - a := by exact_mod_cast this
          omega
      refine ⟨?_, by omega, by omega, by omega⟩
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        refine ⟨?_, by linarith⟩
        have : ((D.R.t : ℤ) - 1 - a : ℚ) ≤ -2 := by push_cast; linarith
        have : (D.R.t : ℤ) - 1 - a ≤ -2 := by exact_mod_cast this
        omega
      · left
        refine ⟨by linarith, ?_⟩
        have : ((D.R.t : ℤ) + 1 : ℚ) ≤ ((D.R.t : ℤ) - 1 - a : ℤ) := by push_cast; linarith
        have : (D.R.t : ℤ) + 1 ≤ (D.R.t : ℤ) - 1 - a := by exact_mod_cast this
        omega
    · intro _ a ha
      rw [mem_intPart] at ha
      have hq := hcl _ ha
      have e : AdmissibleParameterJ.refl D (a : ℚ) = (D.R.t : ℚ) - 1 - a := rfl
      rw [e] at hq
      have hcast : ((((D.R.t : ℚ) - 1 - a) - c0 D : ℚ) : ℝ) = (D.R.t : ℝ) - 1 - a - ((D.R.t : ℝ) - 1) / 2 := by
        push_cast [hc0]; ring
      rw [hcast, hzR] at hq
      refine ⟨by push_cast; linarith, ?_⟩
      have h2 : (a : ℝ) ≤ ((-(zs - kc) : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast h2
    · intro a
      rw [mem_JJ, mem_intPart, mem_intPart]
      rfl
  · refine ⟨zs + kc, intPart _ (cloudJ_finite j ρ), intPart _ (lowJ_finite j ρ),
      ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd h (by simp), ?_⟩
    · push_cast; linarith
    · push_cast; linarith
    · rw [card_intPart _ (cloudJ_int j ρ), hcard1]
    · rw [card_intPart _ (lowJ_int j ρ), hcard2]
    · intro a ha
      rw [mem_intPart] at ha
      have hq := hlows _ ha
      have hcast : (((a : ℚ)) : ℝ) = (a : ℝ) := by push_cast; rfl
      rw [hcast, hc0] at hq
      have key : a ≤ -2 ∨ (D.R.t : ℤ) + 1 ≤ a := by
        rcases hq with ⟨-, h⟩ | ⟨h, -⟩
        · left; exact_mod_cast h
        · right; exact_mod_cast h
      refine ⟨?_, by omega, by omega, by omega⟩
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, by exact_mod_cast h2⟩
      · right; exact ⟨by exact_mod_cast h1, h2⟩
    · intro _ a ha
      rw [mem_intPart] at ha
      have hq := hcl _ ha
      have hcast : ((((a : ℚ)) - c0 D : ℚ) : ℝ) = (a : ℝ) - ((D.R.t : ℝ) - 1) / 2 := by
        push_cast [hc0]; ring
      rw [hcast, hzR] at hq
      have h1 : ((zs + kc : ℤ) : ℝ) ≤ (a : ℝ) := by push_cast; linarith
      refine ⟨by exact_mod_cast h1, ?_⟩
      push_cast
      linarith
    · intro a
      rw [mem_JJ, mem_intPart, mem_intPart]
      rfl

open Classical in

theorem main : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), Setup L nch HW X C₂ → ∀ ep, AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes X.r ep L := by
  intro _ D L P nch HW F Cm X C₂ S ep hJa
  obtain ⟨-, hJb, hJc, -⟩ := GlobalTheory.JumpStatement.holds_all D L (S.facts.admJ L S.par)
  intro i _ w hw C τ
  obtain ⟨g, ρ, hR, hjx, -⟩ := hJa i (X.r i) (S.canon.fam.good i) w hw C τ
  obtain ⟨hj1, hj2⟩ := D.nd.j_range i
  obtain ⟨hlo, hhi⟩ := sz_bounds L P S.par (D.nd.j i) hj1 hj2 ρ
  have hUp : EmbeddingTypeJumps.UpAt ep C τ → AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ =>
    typeU_of_emb i C τ g ρ hR ep τ₀ h0 e0
  have hDn : EmbeddingTypeJumps.DownAt ep C τ → ¬ AdmissibleParameterJ.TypeU D ep g := fun ⟨τ₀, h0, e0⟩ h => by
    have h' := typeU_of_emb i C τ g ρ hR (!ep) τ₀ h0 e0
    unfold AdmissibleParameterJ.TypeU at h h'
    cases ep <;> simp_all
  obtain ⟨s, Jc, Jl, h1, h2, h3, h4, h5, hpos, hneg, hJJ⟩ :=
    key_sets L hJb hJc (D.nd.j i) hj1 hj2 ρ (decide (AdmissibleParameterJ.TypeU D ep g)) hlo hhi
  refine ⟨s, Jc, Jl, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_⟩
  · by_cases ht : AdmissibleParameterJ.TypeU D ep g
    · left; exact hpos (by simp [ht])
    · right; exact hneg (by simp [ht])
  · intro hu; exact hpos (by simp [hUp hu])
  · intro hd; exact hneg (by simp [hDn hd])
  · intro x a
    exact ((hjx x a).1).trans (hJJ a)

end GlobalTheory.HostJumpWin
