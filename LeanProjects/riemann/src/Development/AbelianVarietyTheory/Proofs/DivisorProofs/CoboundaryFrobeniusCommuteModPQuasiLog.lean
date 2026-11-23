import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobCongr

variable {Q : Type} [CommRing Q]

theorem frob_eq_expand {σ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem subst_frob {σ τ : Type} (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    subst a (frob p s g) = subst (fun i => a i ^ p) (map s g) := by
  rw [frob, subst_comp_subst_apply (HasSubst.X_pow hp) ha]
  congr 1
  funext i
  rw [subst_pow ha, subst_X ha]

theorem frob_subst {σ τ : Type} [Finite σ] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q) {a : σ → MvPowerSeries τ Q}
    (ha : HasSubst a) (g : MvPowerSeries σ Q) :
    frob p s (subst a g) = subst (fun i => expand p hp (map s (a i))) (map s g) := by
  have ha' : HasSubst fun i => map s (a i) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by
      rw [constantCoeff_map]; exact (ha.const_coeff i).map s
  rw [frob_eq_expand p hp, map_subst ha, expand_subst p hp ha']

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem coeff_pow_sub_expand_mem {B τ : Type} [CommRing B] (p : ℕ) [hp : Fact p.Prime]
    (hnu : ¬IsUnit (p : B)) (σ : B →+* B) (hσ : ∀ b, (p : B) ∣ σ b - b ^ p)
    (g : MvPowerSeries τ B) (α : τ →₀ ℕ) :
    coeff α (g ^ p - expand p hp.out.ne_zero (map σ g)) ∈ Ideal.span {(p : B)} := by
  haveI : CharP (B ⧸ Ideal.span {(p : B)}) p := CharP.quotient B p hnu
  set π := Ideal.Quotient.mk (Ideal.span {(p : B)})
  have hπσ : π.comp σ = (frobenius (B ⧸ Ideal.span {(p : B)}) p).comp π := by
    ext b
    simp only [RingHom.comp_apply, frobenius_def]
    rw [← map_pow, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.2 (hσ b)
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map]
  change coeff α (map π (g ^ p - expand p hp.out.ne_zero (map σ g))) = 0
  rw [map_sub, map_pow, map_expand, map_map, hπσ, ← map_map, ← map_expand,
    map_frobenius_expand, sub_self, map_zero]

end GlobalTheory.FrobCongr

namespace GlobalTheory.FrobCongr

theorem dIn_comb {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι]
    (b : ι → B) (e : ι → MvPowerSeries σ Q) (he : ∀ i, DIn (⊤ : Ideal B) (e i)) :
    DIn (⊤ : Ideal B) (comb b e) := by
  intro α j
  choose c _ hc using fun i => he i α j
  refine ⟨∑ i, b i * c i, trivial, ?_⟩
  simp only [comb, map_sum, coeff_smul, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc i]; ring

theorem dIn_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (φ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (φ b)) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) (map s f) := by
  intro α j
  obtain ⟨c, -, hc⟩ := hf α j
  refine ⟨φ c, trivial, ?_⟩
  rw [coeff_map, ← hs, ← hc, map_mul, map_natCast]

theorem frob_cong : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ b : ι → F.B, In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb b e)) - frob p F.s (cob1 (up F.Q μ') (comb b e))) := by
  intro p hp O _ hO _ ε F d μ' hμ ι _ e he b
  have hp0 : p ≠ 0 := hp.out.ne_zero
  set f := comb b e with hfdef
  set M := up F.Q μ' with hM
  have hM0 : ∀ i, constantCoeff (M i) = 0 := fun i => by
    rw [hM, up, constantCoeff_map, hμ.const i, map_zero]
  have hsM : HasSubst M := hasSubst_of_constantCoeff_zero hM0
  have hsL : HasSubst fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) F.Q) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

  have hX : ∀ (a : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.Q), (∀ i, ∃ j, a i = X j) → HasSubst a →
      subst a (frob p F.s f) = frob p F.s (subst a f) := by
    intro a ha has
    rw [subst_frob p hp0 F.s has, frob_subst p hp0 F.s has]
    congr 1
    funext i
    obtain ⟨j, hj⟩ := ha i
    rw [hj, map_X, expand_X]
  have hL := hX _ (fun i => ⟨_, rfl⟩) hsL
  have hR := hX _ (fun i => ⟨_, rfl⟩) hsR

  set u : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => μ' i ^ p with hu
  set v : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B := fun i => expand p hp0 (map F.σ (μ' i)) with hv
  have hsalg : F.s.comp (algebraMap F.B F.Q) = (algebraMap F.B F.Q).comp F.σ :=
    RingHom.ext fun x => F.s_alg x
  have hup_u : up F.Q u = fun i => M i ^ p := by
    funext i; rw [up, hu, hM, up, map_pow]
  have hup_v : up F.Q v = fun i => expand p hp0 (map F.s (M i)) := by
    funext i; rw [up, hv, hM, up, map_expand, map_map, map_map, hsalg]
  have key : cob1 M (frob p F.s f) - frob p F.s (cob1 M f) =
      subst (up F.Q u) (map F.s f) - subst (up F.Q v) (map F.s f) := by
    rw [hup_u, hup_v, ← subst_frob p hp0 F.s hsM, ← frob_subst p hp0 F.s hsM]
    have hfs : ∀ a c : MvPowerSeries (Fin d ⊕ Fin d) F.Q,
        frob p F.s (a - c) = frob p F.s a - frob p F.s c := fun a c => by
      simp only [frob_eq_expand p hp0, map_sub]
    unfold cob1 inL inR
    rw [hfs, hfs, hL, hR]
    abel
  rw [key, ← Ideal.mul_top (Ideal.span {(p : F.B)})]
  have hnu : ¬IsUnit (p : F.B) := fun h => hO.out (by simpa using h.map F.θ)
  refine GlobalTheory.KatzCongr.subst_sub_in p F.B O F.Q F.θ F.frame _ ?_ (Fin d) (Fin d ⊕ Fin d) ⊤
    (map F.s f) u v ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨z ^ p * (p : F.B) ^ (p - 1),
      Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.sub_pos_of_lt hp.out.one_lt)), ?_⟩
    rw [mul_pow, mul_left_comm, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  · exact dIn_map F.σ F.s F.s_alg f
      (dIn_comb b e fun i => GlobalTheory.QLogDiff.dIn_of_QL p F.B O F.Q F.θ F.frame d μ' hμ ⊤ (e i) (he i))
  · intro i; rw [hu, map_pow, hμ.const i, zero_pow hp0]
  · intro i; rw [hv, constantCoeff_expand, constantCoeff_map, hμ.const i, map_zero]
  · intro i α
    exact coeff_pow_sub_expand_mem p hnu F.σ F.σ_pow (μ' i) α

end GlobalTheory.FrobCongr
