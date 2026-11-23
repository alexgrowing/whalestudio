import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev.GlueApprox

section Local

variable {k Γ : Type} [Field k] [LinearOrderedCommGroupWithZero Γ] {v : Valuation k Γ} {n : ℕ}

theorem sm_inv_sub_one {γ : Γ} (hγ : γ < 1) {A B : Matrix (Fin n) (Fin n) k} (h : ColAd.Sm v γ (A - 1))
    (hAB : A * B = 1) : ColAd.Sm v γ (B - 1) := by
  have hB : ColAd.Sm v 1 B := fun i j => by
    refine ColAd.int_of_mulVec h hγ (x := fun l => B l j) (fun l => ?_) i
    have e : (A *ᵥ fun l => B l j) l = (A * B) l j := rfl
    rw [e, hAB, Matrix.one_apply]
    split_ifs <;> simp
  have hBA : B * A = 1 := mul_eq_one_comm.1 hAB
  have e : B - 1 = -(B * (A - 1)) := by rw [Matrix.mul_sub, hBA, Matrix.mul_one]; abel
  intro i j
  rw [e, Matrix.neg_apply, Valuation.map_neg]
  have := hB.mul h i j
  rwa [one_mul] at this

end Local

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ne_zero_of_sm {P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (hγ : γ < 1) {a : E}
    (ha0 : a ≠ 0) (ha : P.valuation E a < 1) (Zi : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (C : Matrix (Fin n) (Fin n) E) (h : ColAd.Sm Valued.v γ (Zi * C.map (algebraMap E _) - 1)) : C.det ≠ 0 := by
  intro hd
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw0
  replace hi : w i ≠ 0 := hi
  set c : E := (a * w i)⁻¹ with hc
  let x : Fin n → P.adicCompletion E := fun l => algebraMap E _ ((c • w) l)
  have hx0 : C.map (algebraMap E (P.adicCompletion E)) *ᵥ x = 0 := by
    funext l
    rw [Pi.zero_apply, show x = (algebraMap E (P.adicCompletion E)) ∘ (c • w) from rfl, ← RingHom.map_mulVec,
      Matrix.mulVec_smul, hw, smul_zero, Pi.zero_apply, map_zero]
  have h4 := ColAd.int_of_mulVec h hγ (x := x) (fun l => by
    rw [← Matrix.mulVec_mulVec, hx0, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
    exact zero_le_one) i
  have e : (c • w) i = a⁻¹ := by
    rw [Pi.smul_apply, smul_eq_mul, hc]
    field_simp
  have ha0' : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha0
  simp only [x] at h4
  rw [e, valued_algebraMap, map_inv₀, inv_le_one₀ (zero_lt_iff.2 ha0')] at h4
  exact absurd ha (not_lt.2 h4)

theorem exists_near_entry (x : AfE F E) (P : HeightOneSpectrum (𝓞 E)) {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0) :
    ∃ y : E, Valued.v (adAt F P x - algebraMap E _ y) < γ := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small x {P} hγ
  refine ⟨y, ?_⟩
  rw [e, map_add, adAt_inclE, add_sub_cancel_left]
  exact valued_nat_mul_lt hr (hN P (by simp))

theorem locM_sub_one_apply (w : HeightOneSpectrum (𝓞 E)) (x : GL (Fin n) (AfE F E)) (i j : Fin n) :
    (ColAd.locM w x - 1) i j =
      adAt F w ((x : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  rw [map_sub, ← ColAd.locM_one (F := F) (P := w)]
  rfl

variable [StarRing E] (hc : CMData F E)

local notation "ι" => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F)
local notation "σ" => Formalism.UG.sigR (CMData.sig hc) (FiniteAdeleRing (𝓞 F) F)

theorem inv_sub_one_apply {u : GL (Fin n) (AfE F E)} (hu : u ∈ UAd hc n) (i j : Fin n) :
    ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j =
      σ ((u : Matrix (Fin n) (Fin n) (AfE F E)) j i - (1 : Matrix (Fin n) (Fin n) (AfE F E)) j i) := by
  rw [PtExist.inv_apply hu, map_sub]
  congr 1
  rcases eq_or_ne i j with rfl | h
  · rw [Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h.symm, map_zero]

include hc in

theorem valued_nat_conj (w : HeightOneSpectrum (𝓞 E)) (m : ℕ) :
    Valued.v (algebraMap E (w.adicCompletion E) (m : E)) =
      Valued.v (algebraMap E ((conjPrime₂ w).adicCompletion E) (m : E)) := by
  have := valued_sigR hc w (ι (m : E))
  rwa [sigR_inclE, star_natCast, adAt_inclE, adAt_inclE] at this

theorem glue_approx {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q) (m : ℕ) (hm : 0 < m)
    (hmQ : ∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) {z : GL (Fin n) (AfE F E)} (hz : z ∈ UAd hc n)
    (hzS : ∀ w i j, Valued.v (adAt F w (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j)) ≤ 1) :
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  classical
  set vm : HeightOneSpectrum (𝓞 E) → WithZero (Multiplicative ℤ) :=
    fun w => Valued.v (algebraMap E (w.adicCompletion E) (m : E)) with hvm
  have hmE : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hm0 : ∀ w, vm w ≠ 0 := fun w => by
    simp only [hvm, valued_algebraMap]
    exact (Valuation.ne_zero_iff _).2 hmE
  have hmv : ∀ P ∈ Q, P.valuation E (m : E) < 1 := fun P hP => by
    have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) P _).2 (hmQ P hP)
    exact_mod_cast this
  have hm1 : ∀ P ∈ Q, vm P < 1 := fun P hP => by
    simp only [hvm, valued_algebraMap]
    exact hmv P hP
  choose C hC using fun (P : HeightOneSpectrum (𝓞 E)) (i j : Fin n) =>
    exists_near_entry ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) P (hm0 P)
  obtain ⟨CM, hCM⟩ : ∃ CM : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P i j,
      Valued.v (adAt F P ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) - algebraMap E _ (CM P i j)) < vm P :=
    ⟨fun P => Matrix.of (C P), hC⟩
  have hA : ∀ P, ColAd.Sm Valued.v (vm P) (ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1) := by
    intro P
    have hZ : ColAd.locM P z⁻¹ * ColAd.locM P z = 1 := by
      rw [← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]
    have e : ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) - 1 =
        ColAd.locM P z⁻¹ * ((CM P).map (algebraMap E _) - ColAd.locM P z) := by
      rw [Matrix.mul_sub, hZ]
    rw [e]
    have h1 : ColAd.Sm Valued.v 1 (ColAd.locM P z⁻¹) := fun i j => hzS P i j
    have h2 : ColAd.Sm Valued.v (vm P) ((CM P).map (algebraMap E _) - ColAd.locM P z) := fun i j => by
      rw [Matrix.sub_apply, Matrix.map_apply, Valuation.map_sub_swap]
      exact (hCM P i j).le
    have := h1.mul h2
    rwa [one_mul] at this
  have hdet : ∀ P ∈ Q, IsUnit (CM P).det := fun P hP =>
    isUnit_iff_ne_zero.2 (det_ne_zero_of_sm (hm1 P hP) hmE (hmv P hP) _ _ (hA P))
  obtain ⟨Ci, hCi⟩ : ∃ Ci : HeightOneSpectrum (𝓞 E) → Matrix (Fin n) (Fin n) E, ∀ P ∈ Q, Ci P * CM P = 1 :=
    ⟨fun P => (CM P)⁻¹, fun P hP => Matrix.nonsing_inv_mul _ (hdet P hP)⟩
  let G : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    PtExist.glue hc Q ((z : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => CM P i j) fun P => Ci P j i
  let G' : Matrix (Fin n) (Fin n) (AfE F E) := Matrix.of fun i j =>
    PtExist.glue hc Q (((z⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) (fun P => Ci P i j)
      fun P => CM P j i
  have hG : ∀ w i j, adAt F w (G i j) = _ := fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w
  have hG' : ∀ w i j, adAt F w (G' i j) = _ := fun w i j => PtExist.adAt_glue hc Q hQ _ _ _ w
  have hone : ∀ w i j, adAt F w ((1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((1 : Matrix (Fin n) (Fin n) E) i j) := fun w i j => by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : G' * G = 1 := by
    ext i j
    refine PtExist.ad_ext fun w => ?_
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul, hG, hG']
    split_ifs with h h'
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, hCi w h, hone]
    · simp only [← map_mul, ← map_sum, ← star_mul, ← star_sum]
      rw [← Matrix.mul_apply, hCi _ h', hone, Matrix.one_apply, Matrix.one_apply]
      by_cases e : i = j <;> simp [e, eq_comm]
    · simp only [← map_mul, ← map_sum]
      rw [← Matrix.mul_apply, Units.inv_mul]
  let g : GL (Fin n) (AfE F E) := ⟨G, G', mul_eq_one_comm.1 h1, h1⟩
  have hg : g ∈ UAd hc n := by
    rw [PtExist.mem_uad_iff, ← h1]
    congr 1
    ext i j
    show σ (G j i) = G' i j
    exact (PtExist.sig_glue hc Q _ _ _).trans (by rw [← PtExist.inv_apply hz]; rfl)
  have hgQ : g ∈ RatAt Q := fun P i j => ⟨CM P.1 i j, (hG P.1 i j).trans (if_pos P.2)⟩
  have hgP : ∀ P ∈ Q, ColAd.locM P g = (CM P).map (algebraMap E _) := fun P hP =>
    Matrix.ext fun i j => (hG P i j).trans (if_pos hP)
  have hgw : ∀ w, w ∉ Q → conjPrime₂ w ∉ Q → ColAd.locM w g = ColAd.locM w z := fun w h h' =>
    Matrix.ext fun i j => (hG w i j).trans (by rw [if_neg h, if_neg h']; rfl)
  have hu : z⁻¹ * g ∈ UAd hc n := mul_mem (inv_mem hz) hg
  have key : ∀ P ∈ Q, ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g) - 1) ∧
      ColAd.Sm Valued.v (vm P) (ColAd.locM P (z⁻¹ * g)⁻¹ - 1) := by
    intro P hP
    have e : ColAd.locM P (z⁻¹ * g) = ColAd.locM P z⁻¹ * (CM P).map (algebraMap E _) := by
      rw [ColAd.locM_mul, hgP P hP]
    refine ⟨e ▸ hA P, sm_inv_sub_one (hm1 P hP) (e ▸ hA P) ?_⟩
    rw [← ColAd.locM_mul, mul_inv_cancel, ColAd.locM_one]
  have all : ∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g) - 1) ∧
      ColAd.Sm Valued.v (vm w) (ColAd.locM w (z⁻¹ * g)⁻¹ - 1) := by
    intro w
    by_cases hw : w ∈ Q
    · exact key w hw
    by_cases hw' : conjPrime₂ w ∈ Q
    · obtain ⟨k1, k2⟩ := key _ hw'
      have ev : vm w = vm (conjPrime₂ w) := valued_nat_conj hc w m
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have e := inv_sub_one_apply hc (inv_mem hu) i j
        rw [inv_inv] at e
        rw [locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]
        exact k2 j i
      · have e := inv_sub_one_apply hc hu i j
        rw [locM_sub_one_apply, e, valued_sigR, ev, ← locM_sub_one_apply]
        exact k1 j i
    · have e1 : ColAd.locM w (z⁻¹ * g) = 1 := by
        rw [ColAd.locM_mul, hgw w hw hw', ← ColAd.locM_mul, inv_mul_cancel, ColAd.locM_one]
      have e2 : ColAd.locM w (z⁻¹ * g)⁻¹ = 1 := by
        have := ColAd.locM_mul (F := F) (P := w) (z⁻¹ * g)⁻¹ (z⁻¹ * g)
        rw [inv_mul_cancel, ColAd.locM_one, e1, Matrix.mul_one] at this
        exact this.symm
      rw [e1, e2, sub_self]
      exact ⟨fun i j => by simp, fun i j => by simp⟩
  have cong : ∀ x : GL (Fin n) (AfE F E), (∀ w, ColAd.Sm Valued.v (vm w) (ColAd.locM w x - 1)) →
      ColAd.CongOne ((m : ℕ) : 𝓞 E) x := by
    intro x hx i j
    refine (mem_rInt_iff F E _).2 fun w => ?_
    rw [← adAt_apply, map_mul, adAt_inclE, map_natCast, map_inv₀, map_mul, map_inv₀, ← locM_sub_one_apply]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 (hm0 w))).2 (hx w i j)
  exact ⟨g, hg, hgQ, cong _ fun w => (all w).1, cong _ fun w => (all w).2⟩

end Main

open GlobalTheory.SeeSaw.TwLev.GlueApprox in

theorem exists_ratAt_congOne : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 E))}, (∀ P ∈ Q, conjPrime₂ P ∉ Q) →
    ∀ (m : ℕ), 0 < m → (∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) → ∀ (z : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    z ∈ St (1 : GL (Fin n) (AfE F E)) →
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  intro F E _ _ _ _ _ _ hc n _ Q hQ m hm hmQ z hz hzS
  obtain ⟨y, hy, -⟩ := St_one_int (inv_mem hzS)
  refine glue_approx hc hQ m hm hmQ hz fun w i j => ?_
  rw [hy]
  exact (mem_rInt_iff F E _).1 (y i j).2 w

end GlobalTheory.SeeSaw.TwLev.GlueApprox
