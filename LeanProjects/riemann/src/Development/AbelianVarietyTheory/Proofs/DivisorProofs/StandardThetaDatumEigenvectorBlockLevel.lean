import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPrincipalCongruenceLevelSubgroupIffIntegralCoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBlockCongruenceLevelSubgroupIffStabilizerEntrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelMovesCosetVectorIntegralPointStatement

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

theorem sum_mul_right_eq {G M : Type} [Group G] [AddCommMonoid M] (H K : Subgroup G)
    (hn : ∀ g ∈ H, ∀ κ ∈ K, g⁻¹ * κ * g ∈ K) (R : Finset G) (hR : ∀ r ∈ R, r ∈ H)
    (hR2 : ∀ x ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * x ∈ K) (f : G → M) (hf : ∀ x, ∀ κ ∈ K, f (x * κ) = f x)
    (g : G) (hg : g ∈ H) : ∑ r ∈ R, f (r * g) = ∑ r ∈ R, f r := by
  classical
  choose! σ hσ hσu using hR2
  have hmem : ∀ r ∈ R, r * g ∈ H := fun r hr => mul_mem (hR r hr) hg
  refine Finset.sum_nbij (fun r => σ (r * g)) (fun r hr => (hσ _ (hmem r hr)).1) ?_ ?_ ?_
  · intro r1 h1 r2 h2 e
    simp only at e
    have a1 := (hσ _ (hmem r1 h1)).2
    have a2 := (hσ _ (hmem r2 h2)).2
    rw [e] at a1
    have h3 : g⁻¹ * (r1⁻¹ * r2) * g ∈ K := by
      have := mul_mem (inv_mem a1) a2
      simpa [mul_assoc] using this
    have h4 : r1⁻¹ * r2 ∈ K := by
      have := hn g⁻¹ (inv_mem hg) _ h3
      simpa [mul_assoc] using this
    have u1 := hσu r1 (hR r1 h1) r1 ⟨h1, by simpa using K.one_mem⟩
    have u2 := hσu r1 (hR r1 h1) r2 ⟨h2, by simpa using inv_mem h4⟩
    exact u1.trans u2.symm
  · intro r' hr'
    have hx : r' * g⁻¹ ∈ H := mul_mem (hR r' hr') (inv_mem hg)
    obtain ⟨hr, hk⟩ := hσ _ hx
    refine ⟨σ (r' * g⁻¹), hr, ?_⟩
    have h5 : g⁻¹ * (g * r'⁻¹ * σ (r' * g⁻¹)) * g ∈ K := by
      refine hn g hg _ ?_
      have := inv_mem hk
      simpa [mul_assoc] using this
    exact (hσu _ (hmem _ hr) r' ⟨hr', by simpa [mul_assoc] using h5⟩).symm
  · intro r hr
    have := (hσ _ (hmem r hr)).2
    rw [← hf (σ (r * g)) _ this]
    simp

variable {D : D7}

theorem mul_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {x y : AE D} (hx : x ∈ OhE D) (hy : y ∈ hatId D 𝔪) :
    x * y ∈ hatId D 𝔪 := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg y _ h => rw [mul_neg]; exact neg_mem h

theorem congOne_conj {𝔪 : Ideal (𝓞 D.host.E)} {N : ℕ} {g κ : GA D N} (hg : g ∈ intG D N) (hκ : CongOne D 𝔪 κ) :
    CongOne D 𝔪 (g⁻¹ * κ * g) := by
  intro i j
  have e : (((g⁻¹ * κ * g : GA D N) : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) - 1 =
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((((κ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) - 1) *
          ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := by
    have h1 : (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) *
        ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    simp [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  have hgi := (mem_intG g).1 hg
  rw [e, Matrix.mul_apply]
  refine sum_mem fun l _ => ?_
  rw [mul_comm]
  refine mul_mem_hatId (hgi l j).1 ?_
  rw [Matrix.mul_apply]
  exact sum_mem fun m _ => mul_mem_hatId (hgi i m).2 (hκ m l)

theorem om_finsum {δ : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ} (W : WeilO D ⊤ δ a d e0) (g : GA D a) (g' : GA D d) {ι : Type}
    (s : Finset ι) (F : ι → VC D a d → ℂ) (hF : ∀ i ∈ s, F i ∈ TT D (tor0 D ⊤ δ) a d) :
    W.Om g g' (∑ i ∈ s, F i) = ∑ i ∈ s, W.Om g g' (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 : (0 : VC D a d → ℂ) ∈ TT D (tor0 D ⊤ δ) a d := (GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).zero_mem
    have := W.smul g g' 0 0 h0
    simpa using this
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx,
      W.add g g' _ (hF x (Finset.mem_insert_self _ _)) _
        ((GlobalTheory.FinWeil.TTs D (tor0 D ⊤ δ) a d).sum_mem fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hF i (Finset.mem_insert_of_mem hi)]

theorem stdSum_eig : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → a ≤ d → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ R : Finset (GA D a), (∀ r ∈ R, r ∈ intG D a) → (∀ k ∈ intG D a, ∃! r, r ∈ R ∧ CongOne D 𝔪 (r⁻¹ * k)) → (∀ k ∈ intG D a, W.Om k 1 (stdSum W 𝔪 0 R) = stdSum W 𝔪 0 R) → ∀ h ∈ blockLev D 𝔪 d a, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om 1 h (stdSum W 𝔪 0 R) = c • stdSum W 𝔪 0 R := by
  intro D δ t0 hc a d e0 vac had W 𝔪 hm hcop hnu R hR1 hR2 _hfix h hh
  obtain ⟨hhi, hb⟩ := (GlobalTheory.T.mem_blockCongruenceLevelSubgroup_iff_stabilizer_entries D 𝔪 d a h).1 hh
  obtain ⟨c, hc1, k, hk, hk'⟩ := GlobalTheory.T.blockLevel_moves_cosetVector_integral_point D δ t0 hc e0 vac had W 𝔪 hm hcop hnu h hhi hb
  refine ⟨c, hc1, ?_⟩
  have hcv := GlobalTheory.T.unitBlockCosetThetaVector_mem_thetaFunctions D δ hc 𝔪 hm 0 a d e0 vac.1
  have hcong : ∀ x, x ∈ congLev D 𝔪 a ↔ x ∈ intG D a ∧ CongOne D 𝔪 x := GlobalTheory.T.mem_principalCongruenceLevelSubgroup_iff_integral_congruent D 𝔪 a
  unfold stdSum
  rw [om_finsum W 1 h R _ (fun r _ => W.maps _ _ _ hcv), Finset.smul_sum]
  have e1 : ∀ r, W.Om 1 h (W.Om r 1 (cosetV D δ 𝔪 0 a d e0)) = c • W.Om (r * k) 1 (cosetV D δ 𝔪 0 a d e0) := by
    intro r
    have m1 := W.mul 1 r h 1 _ hcv
    have m2 := W.mul r 1 1 h _ hcv
    have m3 := W.mul r k 1 1 _ hcv
    simp only [one_mul, mul_one] at m1 m2 m3
    rw [← m1, m2, hk', W.smul _ _ _ _ (W.maps _ _ _ hcv), ← m3]
  simp_rw [e1]
  refine sum_mul_right_eq (intG D a) (congLev D 𝔪 a) (fun g hg κ hκ => ?_) R hR1 (fun x hx => ?_)
    (fun x => c • W.Om x 1 (cosetV D δ 𝔪 0 a d e0)) (fun x κ hκ => ?_) k hk
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    exact (hcong _).2 ⟨mul_mem (mul_mem (inv_mem hg) h1) hg, congOne_conj hg h2⟩
  · obtain ⟨r, ⟨hr, hrx⟩, hu⟩ := hR2 x hx
    exact ⟨r, ⟨hr, (hcong _).2 ⟨mul_mem (inv_mem (hR1 r hr)) hx, hrx⟩⟩,
      fun r' ⟨hr', h'⟩ => hu r' ⟨hr', ((hcong _).1 h').2⟩⟩
  · obtain ⟨h1, h2⟩ := (hcong κ).1 hκ
    have m4 := W.mul x κ 1 1 _ hcv
    rw [mul_one] at m4
    rw [m4, GlobalTheory.T.weil_fixes_cosetVector_congruent_one_mod_ideal D δ t0 hc e0 vac W 𝔪 hm hcop hnu 0 (by omega) κ h1 h2]

end GlobalTheory.FunObj.StdDatum.CapelliMinorMembership

end
