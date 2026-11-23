import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryOfFiniteSupportStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemAdelicSpanOfLatticeIffForallPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLevelCharacterMatchAtTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeFrameConditionCharacterLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepLevelTLat

noncomputable section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.LvlZero

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem not_both_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (p : 𝓞 F) ∈ v.asIdeal) (h2 : (q : 𝓞 F) ∈ v.asIdeal) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have e : (1 : 𝓞 F) = (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this
    exact this.symm
  have h1' : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [e]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ h1) (v.asIdeal.mul_mem_left _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

theorem finite_mem {p : ℕ} (hp : p ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(p : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in

theorem prVec_sub_one_mulVec (v : HeightOneSpectrum (𝓞 F)) (y : GL (Fin n) (E ⊗[F] Ad F))
    (x : Fin n → E ⊗[F] Ad F) :
    prVec v ((y.1 - 1) *ᵥ x) = ((bc (prV (E := E) v) y).1 - 1) *ᵥ prVec v x := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    ← GlobalTheory.St.G.Carry.prVec_mulVec]
  funext i
  simp only [prVec, Pi.sub_apply, map_sub]

theorem mem_hat_of_loc {L : Submodule (𝓞 E) (Fin n → E)} (hL : IsLat L) (v : HeightOneSpectrum (𝓞 F))
    (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x ∈ loc v L) :
    (fun i => Formalism.UG.P.afsplitIE v (x i)) ∈ hat F L := by
  rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n L hL]
  intro w
  by_cases hw : w = v
  · subst hw; rw [GlobalTheory.St.G.Carry.prVec_single_self]; exact hx
  · rw [GlobalTheory.St.G.Carry.prVec_single_ne v w hw]; exact Submodule.zero_mem _

end SlopeTestRemainingChoices

set_option maxHeartbeats 2000000 in

theorem level_conj_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k), ∃ κ : UPts cm.sig J (Ad F), κ.1 ∈ stabGL (hat F S.Lb) ∧ ∀ y : UPts cm.sig J (Ad F), (Fr.InK y.1 ↔ ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U) ∧ ∀ hy : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL _ _) ∈ S.U, Fr.chi y.1 = ((S.chi ⟨_, hy⟩ : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hsplit hsplitT hdeg Fr
  classical
  have hL : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  have hTL : TLat cm.sig J T f S.Lb := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hD := GlobalTheory.T.dual_lattice_local_characterization F E cm n J hJ hdet S.Lb hL
  have hLD : IsLat (dualL cm.sig J S.Lb) := hD.1
  have hsd : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal →
      ∀ x, x ∈ loc v (dualL cm.sig J S.Lb) ↔ x ∈ loc v S.Lb := by
    intro v hv x
    rw [hD.2.1 v x]
    exact (GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f S.Lb hTL v hv x).symm
  have hlevI : ∀ v (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ levelVL cm.sig J v S.Lb ↔
      g ∈ UPts cm.sig J (v.adicCompletion F) ∧ g ∈ stabGL (loc v S.Lb) := fun v g => Iff.rfl
  have hQauto : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal →
      ∀ g : GL (Fin n) (E ⊗[F] v.adicCompletion F), g ∈ stabGL (loc v S.Lb) →
      ∀ x ∈ loc v (dualL cm.sig J S.Lb), (g.1 - 1) *ᵥ x ∈ loc v S.Lb := by
    intro v hv g hg x hx
    rw [hsd v hv] at hx
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Submodule.sub_mem _ ((hg x).mp hx) hx

  have gm := fun (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal) =>
    GlobalTheory.T.local_level_character_match_at_type_prime F E cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hsplit Fr i v hv
  choose κl hκl hκs using gm
  let hf : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F) := fun v =>
    if h0 : (gp 0 : 𝓞 F) ∈ v.asIdeal then κl 0 v h0
    else if h1 : (gp 1 : 𝓞 F) ∈ v.asIdeal then κl 1 v h1 else 1
  have hf_g : ∀ i v (h : (gp i : 𝓞 F) ∈ v.asIdeal), hf v = κl i v h := by
    intro i v h
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · simp only [hf, dif_pos h]
    · have h0 : (gp 0 : 𝓞 F) ∉ v.asIdeal := fun h0 => not_both_mem (hgp 0) (hgp 1) hne v h0 h
      simp only [hf, dif_neg h0, dif_pos h]
  have hf_one : ∀ v, (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → hf v = 1 := by
    intro v h0 h1
    simp only [hf, dif_neg h0, dif_neg h1]
  have hf_lev : ∀ v, hf v ∈ levelVL cm.sig J v S.Lb := by
    intro v
    by_cases h0 : (gp 0 : 𝓞 F) ∈ v.asIdeal
    · rw [hf_g 0 v h0]; exact hκl 0 v h0
    by_cases h1 : (gp 1 : 𝓞 F) ∈ v.asIdeal
    · rw [hf_g 1 v h1]; exact hκl 1 v h1
    rw [hf_one v h0 h1]; exact Subgroup.one_mem _
  have hfin : {v | hf v ≠ 1}.Finite := by
    refine ((finite_mem (hgp 0).ne_zero).union (finite_mem (hgp 1).ne_zero)).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hc
    exact hv (hf_one v hc.1 hc.2)
  obtain ⟨x0, hx0, hx0v⟩ := GlobalTheory.T.exists_adelic_unitary_of_finite_support F E n cm.sig J hf (fun v => ((hlevI v _).mp (hf_lev v)).1) hfin
  let κ : UPts cm.sig J (Ad F) := ⟨x0, hx0⟩
  have hκv : ∀ v, bc (prV (E := E) v) (κ : GL (Fin n) (E ⊗[F] Ad F)) = hf v := hx0v
  refine ⟨κ, ?_, ?_⟩
  · exact (GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n S.Lb S.Lb hL hL x0).mpr (fun v x => by
      rw [hx0v v]; exact ((hlevI v _).mp (hf_lev v)).2 x)
  intro y
  have hbcUP : ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ UPts cm.sig J (v.adicCompletion F) :=
    fun v => Formalism.UG.P.afsplit_bc_mem cm.sig J v _ y.2
  have hwv : ∀ v, bc (prV (E := E) v) ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) =
      (hf v)⁻¹ * bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) * hf v := by
    intro v
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hκv]
  have hconj : ∀ v, (hf v)⁻¹ * bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) * hf v ∈ levelVL cm.sig J v S.Lb →
      bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb := by
    intro v h
    have := (levelVL cm.sig J v S.Lb).mul_mem ((levelVL cm.sig J v S.Lb).mul_mem (hf_lev v) h)
      ((levelVL cm.sig J v S.Lb).inv_mem (hf_lev v))
    simpa [mul_assoc] using this

  have hA : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb) ↔
      ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) :=
    GlobalTheory.T.adelicLattice_carry_iff_forall_place F E n S.Lb S.Lb hL hL y
  have hB : (∀ x, (∀ z ∈ hat F S.Lb, hR cm.sig J (Ad F) z x ∈ OAd F E) → (y.1.1 - 1) *ᵥ x ∈ hat F S.Lb) ↔
      ∀ v, ∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb := by
    constructor
    · intro h v x hx
      have hx' := mem_hat_of_loc hLD v x hx
      have h1 := h _ ((hD.2.2 _).mp hx')
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n S.Lb hL] at h1
      have h2 := h1 v
      rwa [prVec_sub_one_mulVec, GlobalTheory.St.G.Carry.prVec_single_self] at h2
    · intro h x hx
      have hx' := (hD.2.2 x).mpr hx
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n _ hLD] at hx'
      rw [GlobalTheory.T.mem_adelicSpanOfLattice_iff_forall_place F E n S.Lb hL]
      intro v
      rw [prVec_sub_one_mulVec]
      exact h v _ (hx' v)
  have hIL := fun (hs : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb)) =>
    GlobalTheory.T.adelicLatticeFrame_condition_character_local F E cm n J hJ hdet k gp S.Lb Fr hgp hne hL S.Lb_int y.1 hs
  have hK : Fr.InK y.1 ↔ ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)))) := by
    unfold AdFrame.InK
    constructor
    · rintro ⟨hs, hq, hc⟩
      have hs' := hA.mp hs
      have hq' := hB.mp hq
      have hc' := (hIL hs).1.mp hc
      intro v
      refine ⟨hs' v, hq' v, ?_⟩
      rintro (h | h)
      · exact hc' 0 v h
      · exact hc' 1 v h
    · intro h
      have hs := hA.mpr (fun v => (h v).1)
      refine ⟨hs, hB.mpr (fun v => (h v).2.1), (hIL hs).1.mpr ?_⟩
      intro i v hv
      refine (h v).2.2 ?_
      obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
      · exact Or.inl hv
      · exact Or.inr hv
  have hloc : ∀ v, bc (prV (E := E) v) ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) ∈ S.Uloc v ↔
      (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))))) := by
    intro v
    rw [hwv v]
    by_cases hb : (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal
    · obtain ⟨i, hi⟩ : ∃ i, (gp i : 𝓞 F) ∈ v.asIdeal := hb.elim (fun h => ⟨0, h⟩) (fun h => ⟨1, h⟩)
      have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun hT' => not_both_mem hT (hgp i) (hTg i) v hT' hi
      have sp := hκs i v hi
      rw [← hf_g i v hi] at sp
      constructor
      · intro hu
        have hl := hconj v (S.Uloc_lev v hu)
        have hl' := (hlevI v _).mp hl
        exact ⟨hl'.2, hQauto v hTv _ hl'.2, fun _ => ((sp _ hl).1).mpr hu⟩
      · rintro ⟨hs, -, hkk⟩
        have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
          (hlevI v _).mpr ⟨hbcUP v, hs⟩
        exact ((sp _ hl).1).mp (hkk hb)
    · have h0 : (gp 0 : 𝓞 F) ∉ v.asIdeal := fun h => hb (Or.inl h)
      have h1 : (gp 1 : 𝓞 F) ∉ v.asIdeal := fun h => hb (Or.inr h)
      rw [hf_one v h0 h1, inv_one, one_mul, mul_one]
      by_cases hTv : (T : 𝓞 F) ∈ v.asIdeal
      · have fu := GlobalTheory.T.trivial_on_dual_quotient_iff_mem_localUnitary F E cm n J hJ hdet T f _ S hT hsplitT hdeg v hTv
        constructor
        · intro hu
          have hl := S.Uloc_lev v hu
          exact ⟨((hlevI v _).mp hl).2, (fu _ hl).mpr hu, fun h => absurd h hb⟩
        · rintro ⟨hs, hq, -⟩
          have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
            (hlevI v _).mpr ⟨hbcUP v, hs⟩
          exact (fu _ hl).mp hq
      · rw [S.Uloc_hyp v hb hTv]
        constructor
        · intro hl
          have hl' := (hlevI v _).mp hl
          exact ⟨hl'.2, hQauto v hTv _ hl'.2, fun h => absurd h hb⟩
        · rintro ⟨hs, -, -⟩
          exact (hlevI v _).mpr ⟨hbcUP v, hs⟩
  have hU : ((κ⁻¹ * y * κ : UPts cm.sig J (Ad F)) : GL (Fin n) (E ⊗[F] Ad F)) ∈ S.U ↔
      ∀ v, bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (loc v S.Lb) ∧
      (∀ x ∈ loc v (dualL cm.sig J S.Lb),
        ((bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F))).1 - 1) *ᵥ x ∈ loc v S.Lb) ∧
      ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal →
        Fr.LocK S.Lb v (bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)))) := by
    rw [S.U_eq]
    constructor
    · rintro ⟨-, h⟩ v
      exact (hloc v).mp (h v)
    · intro h
      exact ⟨(κ⁻¹ * y * κ).2, fun v => (hloc v).mpr (h v)⟩
  refine ⟨hK.trans hU.symm, ?_⟩
  intro hy
  have hall := hU.mp hy
  have hs : (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ stabGL (hat F S.Lb) := hA.mpr (fun v => (hall v).1)
  rw [(hIL hs).2, Gl.chi_eq ⟨_, hy⟩]
  refine Finset.prod_congr rfl (fun i _ => finprod_congr (fun v => finprod_congr (fun h => ?_)))
  have hb : (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · exact Or.inl h
    · exact Or.inr h
  have hl : bc (prV (E := E) v) (y : GL (Fin n) (E ⊗[F] Ad F)) ∈ levelVL cm.sig J v S.Lb :=
    (hlevI v _).mpr ⟨hbcUP v, (hall v).1⟩
  rw [(hκs i v h _ hl).2 ((hall v).2.2 hb)]
  dsimp only
  rw [hwv v, hf_g i v h]

end GlobalTheory.St.G.LvlZero
