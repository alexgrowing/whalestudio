import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftQuasiLogarithmAlongPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedQuasiLogBasisPDivGroupLieDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreePDThickeningFrameValuationIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameReflTransGenCyclicChain
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReduceBasis

section Ring

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q) :=
  fun _ => ⟨0, trivial, by simp⟩

theorem in_neg {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (-f) := by
  simpa using KLift.in_sub in_zero hf

theorem in_smul (r : B) {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal B) (algebraMap B Q r • f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨r * b, trivial, by rw [coeff_smul, hb, map_mul]⟩

theorem in_sum {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i, In (⊤ : Ideal B) (f i)) : In (⊤ : Ideal B) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (in_zero : In (⊤ : Ideal B) (0 : MvPowerSeries σ Q))
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact KLift.in_add (hf a) ih

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem comb_sub (x y : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb x e - comb y e = comb (x - y) e := by
  simp only [comb, ← Finset.sum_sub_distrib, Pi.sub_apply, map_sub, sub_smul]

theorem comb_single [DecidableEq ι] (l : ι) (e : ι → MvPowerSeries σ Q) :
    comb (Pi.single l (1 : B)) e = e l := by
  rw [comb, Finset.sum_eq_single l (fun j _ hj => by simp [Pi.single_apply, hj])
    (fun h => absurd (Finset.mem_univ l) h)]
  simp

theorem comb_comb (M : κ → B) (N : κ → ι → B) (e : ι → MvPowerSeries σ Q) :
    ∑ m, algebraMap B Q (M m) • comb (N m) e = comb (fun l => ∑ m, M m * N m l) e := by
  simp only [comb, Finset.smul_sum, smul_smul, ← map_mul, map_sum, Finset.sum_smul]
  exact Finset.sum_comm

theorem mul_eq_single [DecidableEq ι] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {e : ι → MvPowerSeries (Fin d) Q} {f : κ → MvPowerSeries (Fin d) Q} (he : IsBasis μ e)
    (M : ι → κ → B) (N : κ → ι → B) (hM : ∀ l, In (⊤ : Ideal B) (e l - comb (M l) f))
    (hN : ∀ m, In (⊤ : Ideal B) (f m - comb (N m) e)) (l : ι) :
    (fun l' => ∑ m, M l m * N m l') = Pi.single l 1 := by
  refine (he.2 (e l) (he.1 l)).unique ?_ ?_
  · have hs : e l - comb (fun l' => ∑ m, M l m * N m l') e =
        (e l - comb (M l) f) + ∑ m, algebraMap B Q (M l m) • (f m - comb (N m) e) := by
      simp only [smul_sub, Finset.sum_sub_distrib, comb_comb]
      simp only [comb]; abel
    rw [hs]
    exact KLift.in_add (hM l) (in_sum _ _ fun m => in_smul _ (hN m))
  · rw [comb_single, sub_self]; exact in_zero

end Ring

section Map

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {σ : Type} {θ : B →+* O} {Θ : Q →+* C}
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))

include hΘ in
theorem in_map {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, hb⟩ := hf α
  exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem map_smul_series (c : Q) (f : MvPowerSeries σ Q) : map Θ (c • f) = Θ c • map Θ f := by
  ext α
  simp [coeff_map, coeff_smul]

include hΘ in
theorem map_comb {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  simp only [comb, map_sum, map_smul_series, hΘ]

end Map

end GlobalTheory.ReduceBasis

namespace GlobalTheory.ReduceBasis

theorem isBasis_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → ∀ Θ : F.Q →+* C, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O C (F.θ b)) → IsBasis c.μ (fun l => map Θ (e l)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hL hμ k e he Θ hΘ
  classical
  have hC : IsFrame p C (RingHom.id O) := GlobalTheory.FrameIntegers.isFrame_integers p C v O hv
  have hcμ : (fun i => map F.θ (μ' i)) = c.μ := funext hμ
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := KLift.const_map _ μ' hL.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := KLift.const_map _ _ c.isLaw.const
  have hΘμ : (fun i => map Θ (up F.Q μ' i)) = up C c.μ := by
    have hc : Θ.comp (algebraMap F.B F.Q) = (algebraMap O C).comp F.θ := RingHom.ext hΘ
    funext i
    unfold up
    rw [← hμ i, ← RingHom.comp_apply (map Θ), ← map_comp,
      ← RingHom.comp_apply (map (algebraMap O C)), ← map_comp, hc]
  have hQL : ∀ f, QL μ' ⊤ f → QL c.μ ⊤ (map Θ f) := by
    rintro f ⟨h0, h1, h2⟩
    refine ⟨?_, fun i => ?_, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
        map_zero]
    · obtain ⟨b, -, hb⟩ := h1 i
      refine ⟨F.θ b, trivial, ?_⟩
      simp only [lin, coeff_map] at hb ⊢
      rw [hb, hΘ]
    · rw [← hΘμ, ← KLift.map_formalGroupLawCoboundaryOne_eq Θ _ hμQ]
      exact in_map hΘ h2

  have hlift : ∀ g, QL c.μ ⊤ g → ∃ f, QL μ' ⊤ f ∧ map Θ f = g := by
    intro g hg
    choose o _ ho using hg.2.1
    choose w hw using fun i => F.frame.surj (o i)
    obtain ⟨f, hf, hfg, -⟩ := KLift.lift_quasiLog p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ g w
      (by rw [hcμ]; exact hg) (fun i => by rw [ho, hw])
    exact ⟨f, hf, hfg⟩
  have key : ∀ x : Fin d ⊕ Fin k → O, In (⊤ : Ideal O) (comb x fun l => map Θ (e l)) → x = 0 := by
    intro x hx
    obtain ⟨k0, e0, -, he0, -⟩ := GlobalTheory.T.exists_adapted_quasiLog_basis_pDivGroup_lieDual p C v O hv G d c C hC
    choose f hf hfe using fun m => hlift (e0 m) (he0.1 m)
    have hfB : IsBasis μ' f := GlobalTheory.basis_lift p F.B O F.Q F.θ F.frame d μ' hL C hC Θ hΘ _ f hf
      (by rw [hcμ]; simpa only [hfe] using he0) (GlobalTheory.BChain.reflTransGen_isStep p C v O hv ε hε F)
    choose M hM _ using fun l => hfB.2 (e l) (he.1 l)
    choose N hN _ using fun m => he.2 (f m) (hf m)
    have hMN := mul_eq_single he M N hM hN
    set y : Fin d ⊕ Fin k0 → O := fun m => ∑ l, x l * F.θ (M l m) with hydef
    have hy : In (⊤ : Ideal O) (comb y e0) := by
      have hs : comb y e0 = comb x (fun l => map Θ (e l)) -
          ∑ l, algebraMap O C (x l) • map Θ (e l - comb (M l) f) := by
        simp only [map_sub, map_comb hΘ, hfe, smul_sub, Finset.sum_sub_distrib, comb_comb, hydef]
        simp only [comb]
        abel
      rw [hs]
      exact KLift.in_sub hx (in_sum _ _ fun l => in_smul _ (in_map hΘ (hM l)))
    have h0 : QL c.μ ⊤ (0 : MvPowerSeries (Fin d) C) := by
      refine ⟨by simp, fun i => ⟨0, trivial, by simp [lin]⟩, ?_⟩
      have : cob1 (up C c.μ) (0 : MvPowerSeries (Fin d) C) = 0 := by
        simpa using formalCoboundary_smul hμC (0 : C) (0 : MvPowerSeries (Fin d) C)
      rw [this]
      exact in_zero
    have hy0 : y = 0 := by
      refine (he0.2 0 h0).unique ?_ ?_
      · simpa using in_neg hy
      · have : comb (0 : Fin d ⊕ Fin k0 → O) e0 = 0 := by simp [comb]
        rw [this, sub_zero]
        exact in_zero
    funext l'
    have e1 : ∀ l, F.θ (∑ m, M l m * N m l') = if l' = l then 1 else 0 := fun l => by
      have h1 := congrFun (hMN l) l'
      rw [h1, Pi.single_apply]
      split_ifs <;> simp
    have s1 : x l' = ∑ l, x l * F.θ (∑ m, M l m * N m l') := by
      simp only [e1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have s2 : ∑ l, x l * F.θ (∑ m, M l m * N m l') = ∑ m, y m * F.θ (N m l') := by
      simp only [hydef, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
    rw [s1, s2, hy0]
    simp
  refine ⟨fun l => hQL _ (he.1 l), fun g hg => ?_⟩
  obtain ⟨f, hf, hfg⟩ := hlift g hg
  obtain ⟨b, hb, -⟩ := he.2 f hf
  have hx0 : In (⊤ : Ideal O) (g - comb (fun l => F.θ (b l)) fun l => map Θ (e l)) := by
    have := in_map hΘ hb
    rwa [map_sub, hfg, map_comb hΘ] at this
  refine ⟨fun l => F.θ (b l), hx0, fun y hy => ?_⟩
  have h := key ((fun l => F.θ (b l)) - y) (by
    rw [← comb_sub]
    convert KLift.in_sub hy hx0 using 1
    abel)
  exact (sub_eq_zero.1 h).symm

end GlobalTheory.ReduceBasis
