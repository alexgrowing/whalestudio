import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfComponentZeroUnderPrime
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.Columns.RecLevelLocP
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

open scoped TensorProduct
open Filter Topology

theorem tendsto_fact_loc (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : v.adicCompletion F)) atTop (𝓝 0) := by
  have hle : ∀ m : ℕ, ‖(m : v.adicCompletion F)‖ ≤ 1 := fun m => by
    have := FinitePlace.norm_le_one F v (m : 𝓞 F)
    simpa using this
  set M := Ideal.absNorm v.asIdeal with hM
  have hlt : ‖(M : v.adicCompletion F)‖ < 1 := by
    have := (FinitePlace.norm_lt_one_iff_mem F v (M : 𝓞 F)).2 (Ideal.absNorm_mem _)
    simpa using this
  have hM0 : 0 < M := lt_trans one_pos (NumberField.HeightOneSpectrum.one_lt_absNorm v)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hlt
  refine ⟨M ^ k, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := Nat.dvd_factorial (pow_pos hM0 k) hn
  rw [dist_zero_right, hc, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (hle c)) hk

theorem tendsto_fact (F : Type) [Field F] [NumberField F] :
    Tendsto (fun n : ℕ => ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => fun v : HeightOneSpectrum (𝓞 F) =>
      ((n.factorial : ℕ) : v.adicCompletionIntegers F)) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun v => ?_
    rw [tendsto_subtype_rng]
    simpa using tendsto_fact_loc F v
  have h2 := ((RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := cofinite)).continuous.tendsto _).comp h1
  exact h2

theorem val_inv_le {K Γ : Type} [CommRing K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) K) (h : (1 + X) * (1 + Y) = 1) (ε : Γ) (hε : ε < 1) (hY : ∀ a b, w (Y a b) ≤ ε) (a b : Fin n) :
    w (X a b) ≤ ε := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n)) (fun p => w (X p.1 p.2)) ⟨(a, b), Finset.mem_univ _⟩
  refine (hp (a, b) (Finset.mem_univ _)).trans ?_
  have e : X = -Y - X * Y := by
    have : X = (1 + X) * (1 + Y) - 1 - Y - X * Y := by noncomm_ring
    rw [h] at this
    exact this.trans (by noncomm_ring)
  have e2 : X p.1 p.2 = -Y p.1 p.2 - ∑ l, X p.1 l * Y l p.2 := by
    conv_lhs => rw [e]
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply]
  by_contra hlt
  rw [not_le] at hlt
  have hm0 : 0 < w (X p.1 p.2) := lt_of_le_of_lt zero_le hlt
  have h1 : w (∑ l, X p.1 l * Y l p.2) < w (X p.1 p.2) := by
    refine w.map_sum_lt hm0.ne' fun l _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (hp (p.1, l) (Finset.mem_univ _)) (hY l p.2)) (mul_lt_of_lt_one_right hm0 hε)
  have h2 : w (-Y p.1 p.2) < w (X p.1 p.2) := by rw [Valuation.map_neg]; exact lt_of_le_of_lt (hY _ _) hlt
  have h3 := w.map_sub_lt h2 h1
  rw [← e2] at h3
  exact lt_irrefl _ h3

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem inv_eq_cT (σ : E →ₐ[F] E) {n : ℕ} {u : GL (Fin n) 𝒜} (hu : u ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸) :
    ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) =
      1 + cT (sigR σ 𝔸) ((u : Matrix (Fin n) (Fin n) 𝒜) - 1) := by
  have h : cT (sigR σ 𝔸) (u : Matrix (Fin n) (Fin n) 𝒜) *
      ((1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) 𝔸)) * (u : Matrix (Fin n) (Fin n) 𝒜) =
      (1 : Matrix (Fin n) (Fin n) E).map (inclE (F := F) 𝔸) := hu
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h
  have e : 1 + cT (sigR σ 𝔸) ((u : Matrix (Fin n) (Fin n) 𝒜) - 1) = cT (sigR σ 𝔸) (u : Matrix (Fin n) (Fin n) 𝒜) := by
    unfold cT
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_sub, Matrix.transpose_one,
      add_sub_cancel]
  rw [e]
  calc ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜)
      = (cT (sigR σ 𝔸) (u : Matrix (Fin n) (Fin n) 𝒜) * (u : Matrix (Fin n) (Fin n) 𝒜)) *
          ((u⁻¹ : GL (Fin n) 𝒜) : Matrix (Fin n) (Fin n) 𝒜) := by rw [h, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra rlt_top rlt_isModTop rlt_topRing

theorem exists_princ (σ : E →ₐ[F] E) {n : ℕ} (U : Subgroup (GL (Fin n) 𝒜))
    (hU : IsOpen {x : UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸 | (x : GL (Fin n) 𝒜) ∈ U}) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ z ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸,
      (∀ a b, iA F E (M : E)⁻¹ * ((z : Matrix (Fin n) (Fin n) 𝒜) - 1) a b ∈ Formalism.L2.Herm.intAf F E) → z ∈ U := by
  obtain ⟨T, hT, hTU⟩ := isOpen_induced_iff.1 hU
  obtain ⟨T', hT', rfl⟩ := isOpen_induced_iff.1 hT
  have h1 : Units.embedProduct _ (1 : GL (Fin n) 𝒜) ∈ T' := by
    have : (1 : UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸) ∈ {x : UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸 | (x : GL (Fin n) 𝒜) ∈ U} :=
      U.one_mem
    rw [← hTU] at this
    exact this
  let g : 𝒜 × Matrix (Fin n) (Fin n) 𝒜 → Matrix (Fin n) (Fin n) 𝒜 × (Matrix (Fin n) (Fin n) 𝒜)ᵐᵒᵖ :=
    fun p => (1 + p.1 • p.2, MulOpposite.op (1 + cT (sigR σ 𝔸) (p.1 • p.2)))
  have hs : Continuous fun p : 𝒜 × Matrix (Fin n) (Fin n) 𝒜 => p.1 • p.2 := continuous_fst.smul continuous_snd
  have hg : Continuous g := by
    refine (continuous_const.add hs).prodMk (MulOpposite.continuous_op.comp (continuous_const.add ?_))
    unfold cT
    exact (hs.matrix_map (rlt_continuous_sig σ)).matrix_transpose
  have hK : IsCompact {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} := by
    have h : {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E} =
        Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => (Formalism.L2.Herm.intAf F E : Set 𝒜) := by
      ext A
      exact ⟨fun hA i _ j _ => hA i j, fun hA i j => hA i (Set.mem_univ _) j (Set.mem_univ _)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => rlt_isCompact_intAf
  have hev : ∀ᶠ c in 𝓝 (0 : 𝒜), ∀ A ∈ {A : Matrix (Fin n) (Fin n) 𝒜 | ∀ i j, A i j ∈ Formalism.L2.Herm.intAf F E}, g (c, A) ∈ T' := by
    refine hK.eventually_forall_of_forall_eventually (P := fun c A => g (c, A) ∈ T') fun A _ => ?_
    refine (hT'.preimage hg).mem_nhds ?_
    show g (0, A) ∈ T'
    have : g (0, A) = Units.embedProduct _ (1 : GL (Fin n) 𝒜) := by
      simp [g, cT]
    rw [this]; exact h1
  have ht : Tendsto (fun k : ℕ => ((k.factorial : ℕ) : 𝒜)) atTop (𝓝 0) := by
    have := ((continuous_algebraMap 𝔸 𝒜).tendsto 0).comp (tendsto_fact F)
    rw [map_zero] at this
    refine this.congr fun k => ?_
    simp only [Function.comp_apply, map_natCast]
  obtain ⟨k, hk⟩ := (ht.eventually hev).exists
  refine ⟨k.factorial, k.factorial_ne_zero, fun z hz hint => ?_⟩
  have h2 := hk (iA F E (k.factorial : E)⁻¹ • ((z : Matrix (Fin n) (Fin n) 𝒜) - 1)) hint
  have e : ((k.factorial : ℕ) : 𝒜) • iA F E (k.factorial : E)⁻¹ • ((z : Matrix (Fin n) (Fin n) 𝒜) - 1) =
      (z : Matrix (Fin n) (Fin n) 𝒜) - 1 := by
    rw [smul_smul, ← map_natCast (iA F E), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 k.factorial_ne_zero), map_one, one_smul]
  have h3 : Units.embedProduct _ z ∈ T' := by
    have e2 : Units.embedProduct _ z = g (((k.factorial : ℕ) : 𝒜), iA F E (k.factorial : E)⁻¹ • ((z : Matrix (Fin n) (Fin n) 𝒜) - 1)) := by
      simp only [g, e, Units.embedProduct_apply, inv_eq_cT σ hz, add_sub_cancel]
    rw [e2]; exact h2
  have h4 : (⟨z, hz⟩ : UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸) ∈
      {x : UPts σ (1 : Matrix (Fin n) (Fin n) E) 𝔸 | (x : GL (Fin n) 𝒜) ∈ U} := by
    rw [← hTU]; exact h3
  exact h4

def cp (ι : 𝒜 ≃+* FiniteAdeleRing (𝓞 E) E) (Q : HeightOneSpectrum (𝓞 E)) : 𝒜 →+* Q.adicCompletion E where
  toFun z := ι z Q
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by rw [map_mul]; rfl
  map_zero' := by rw [map_zero]; rfl
  map_add' x y := by rw [map_add]; rfl

theorem val_cp_mul {ι : 𝒜 ≃+* FiniteAdeleRing (𝓞 E) E} (hι : GlobalTheory.TwU.IsAdIso ι) (Q : HeightOneSpectrum (𝓞 E)) (c : E) (x : 𝒜) :
    Valued.v (ι (iA F E c⁻¹ * x) Q) ≤ 1 ↔ Valued.v (cp ι Q x) * (Q.valuation E c)⁻¹ ≤ 1 := by
  have e : cp ι Q (iA F E c⁻¹) = ((c⁻¹ : E) : Q.adicCompletion E) := by
    show ι (c⁻¹ ⊗ₜ[F] 1) Q = _
    rw [hι.1]
    rfl
  show Valued.v (cp ι Q (iA F E c⁻¹ * x)) ≤ 1 ↔ _
  rw [map_mul, map_mul, e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀, mul_comm]

variable [StarRing E]

theorem intAtA_sig (hc : CMData F E) (P : HeightOneSpectrum (𝓞 E)) {x : 𝒜} (hx : IntAtA (F := F) P x) :
    IntAtA (F := F) (conjPrime₂ P) (sigR hc.sig 𝔸 x) := by
  obtain ⟨s, hs, hm⟩ := hx
  refine ⟨cO E s, fun h => hs (by rwa [mem_conjP, cO_cO] at h), ?_⟩
  have h2 := Formalism.UG.P.csScale_sigR_mem hc.sig hm
  rw [map_mul] at h2
  have e : sigR hc.sig 𝔸 (iA F E (algebraMap (𝓞 E) E s)) = iA F E (algebraMap (𝓞 E) E (cO E s)) := by
    rw [algebraMap_cO]; rfl
  rwa [e] at h2

theorem exists_depth (hc : CMData F E) {n : ℕ} (U : Subgroup (GL (Fin n) 𝒜))
    (hU : IsOpen {x : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) 𝔸 | (x : GL (Fin n) 𝒜) ∈ U})
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : IsOver v P) :
    ∃ N : ℕ, ∀ z ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) 𝔸, (∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) →
      GlobalTheory.TwU.CongAt P N z → z ∈ U := by
  obtain ⟨M, hM, hMU⟩ := exists_princ hc.sig U hU
  obtain ⟨ι, hι⟩ := GlobalTheory.TwU.exists_isAdIso F E
  set q : E := ((qOf P : ℕ) : E) with hq
  have hq0 : q ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact Nat.cast_ne_zero.2 this
  have hlt : ∀ Q : HeightOneSpectrum (𝓞 E), ((qOf P : ℕ) : 𝓞 E) ∈ Q.asIdeal → Q.valuation E q < 1 := fun Q hQ => by
    have e : q = algebraMap (𝓞 E) E (qOf P : 𝓞 E) := by rw [map_natCast]
    rw [e, HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hQ
  have hP := hlt P (Ideal.absNorm_mem _)
  have hP' := hlt (conjPrime₂ P) (by rw [mem_conjP, map_natCast]; exact Ideal.absNorm_mem _)
  have hMv : ∀ Q : HeightOneSpectrum (𝓞 E), 0 < Q.valuation E (M : E) := fun Q =>
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hM))
  have hqv : ∀ (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ), 0 < Q.valuation E (q ^ k) := fun Q k =>
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq0))
  obtain ⟨N₁, hN₁⟩ := exists_pow_lt₀ hP (Units.mk0 _ (hMv P).ne')
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt₀ hP' (Units.mk0 _ (hMv (conjPrime₂ P)).ne')
  have hb : P.valuation E (q ^ (N₁ + N₂ + 1)) ≤ P.valuation E (M : E) := by
    rw [map_pow]
    exact (pow_le_pow_right_of_le_one' hP.le (by omega)).trans hN₁.le
  have hb' : (conjPrime₂ P).valuation E (q ^ (N₁ + N₂ + 1)) ≤ (conjPrime₂ P).valuation E (M : E) := by
    rw [map_pow]
    exact (pow_le_pow_right_of_le_one' hP'.le (by omega)).trans hN₂.le
  refine ⟨N₁ + N₂ + 1, fun z hz hsup hcg => hMU z hz fun a b => (hι.2 _).2 fun Q => ?_⟩
  by_cases hQ : IsOver v Q
  · rw [val_cp_mul hι, mul_inv_le_iff₀ (hMv Q), one_mul]
    rcases rll_over_cases hc hv hQ with rfl | rfl
    · have h1 := hι.val_le (hcg a b)
      rw [val_cp_mul hι, mul_inv_le_iff₀ (hqv _ _), one_mul] at h1
      exact h1.trans hb
    · refine le_trans ?_ hb'
      have hprod : (1 + ((z : Matrix (Fin n) (Fin n) 𝒜) - 1)) * (1 + cT (sigR hc.sig 𝔸) ((z : Matrix (Fin n) (Fin n) 𝒜) - 1)) = 1 := by
        rw [← inv_eq_cT hc.sig hz, add_sub_cancel, Units.mul_inv]
      have hprod' := congrArg (cp ι (conjPrime₂ P)).mapMatrix hprod
      rw [map_mul, map_add, map_add, map_one] at hprod'
      refine val_inv_le Valued.v _ _ hprod' _ ?_ (fun i j => ?_) a b
      · rw [map_pow]; exact pow_lt_one₀ zero_le hP' (by omega)
      · have h1 := intAtA_sig hc P (hcg j i)
        have e : sigR hc.sig 𝔸 (iA F E (q ^ (N₁ + N₂ + 1))⁻¹) = iA F E (q ^ (N₁ + N₂ + 1))⁻¹ := by
          show hc.sig (q ^ (N₁ + N₂ + 1))⁻¹ ⊗ₜ[F] (1 : 𝔸) = (q ^ (N₁ + N₂ + 1))⁻¹ ⊗ₜ[F] (1 : 𝔸)
          rw [map_inv₀, map_pow, hq, map_natCast]
        rw [map_mul, e] at h1
        have h2 := hι.val_le h1
        rw [val_cp_mul hι, mul_inv_le_iff₀ (hqv _ _), one_mul] at h2
        exact h2
  · refine hι.val_le (GlobalTheory.VanishAwayInt.intAtA_of_prV_eq_zero Q _ fun w hw => ?_)
    have hne : w ≠ v := fun e => hQ (e ▸ hw)
    have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] w.adicCompletion F) => (g : Matrix (Fin n) (Fin n) (E ⊗[F] w.adicCompletion F)) a b)
      (hsup w hne)
    simp only [Units.val_one] at h2
    change prV (E := E) w ((z : Matrix (Fin n) (Fin n) 𝒜) a b) = (1 : Matrix (Fin n) (Fin n) _) a b at h2
    rw [map_mul, Matrix.sub_apply, map_sub, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem exists_depth_step (hc : CMData F E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad)
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : IsOver v P) :
    ∃ N : ℕ, ∀ z ∈ UPts hc.sig J 𝔸, (∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) →
      GlobalTheory.TwU.CongAt P N z → z ∈ S.U := by
  subst hJ
  exact exists_depth hc S.U S.U_open P v hv

end Gen

theorem level_contains_deep : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad) (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∃ N : ℕ, ∀ z ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z = 1) → GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z → z ∈ S.U := by
  intro B X I hI hP l Z a T i hi bad S P v hv
  have hg : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  exact exists_depth_step (I.rec7 l Z).sp.cm hg S _ v hv

end GlobalTheory.Mem.Col2.AdT.Opn

end
