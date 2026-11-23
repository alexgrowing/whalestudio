import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVectorStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMulStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SplitMatch

open Formalism.L2.NTheta

variable {D : D7}

theorem exists_isIdemAt {P : Pl D.host.E} (hP : conjPl P ≠ P) : ∃ e : AE D, IsIdemAt e P := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨e, f, h⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  rcases h with ⟨h, -⟩ | ⟨-, ⟨v, ε, -, rfl⟩, ht⟩
  · exact ⟨e, h⟩
  · refine absurd (GlobalTheory.IdemSupport.eq_of_le (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)) hP
    have h2 := GlobalTheory.IdemSupport.Comparison₂.conj (P := P) ht
    rw [GlobalTheory.IdemSupport.cA_algebraMap] at h2
    by_cases h0 : x = 0
    · rw [h0]; exact zero_mem _
    · exact (h2 x h0).2 ((ht x h0).1 hx)

theorem idem_unique {P : Pl D.host.E} {e e' f' : AE D} (he : IsIdemAt e P) (h : IsPrimeIdem P e' f') :
    e' = e ∧ f' = e + cA D e := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨hd, ε, hε, h1⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (f := e + cA D e) (Or.inl ⟨he, rfl⟩)
  obtain ⟨hd', ε', hε', h1'⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  exact ⟨GlobalTheory.IdemSupport.delta_unique hΦ hd' hd, by rw [h1, h1', GlobalTheory.IdemSupport.placeIdem_unique hε' hε]⟩

theorem mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {V : HSp D} {k : GA D V} (hk : k ∈ hyp V P) :
    k ∈ locPart V (KsphC V ∅) e := by
  obtain ⟨h1, e', f', h2, h3⟩ := hk
  rw [(idem_unique he h2).2] at h3
  exact ⟨h1, h3⟩

theorem one_mem_hyp {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) (V : HSp D) : (1 : GA D V) ∈ hyp V P := by
  refine ⟨⟨one_mem _, fun y => ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, e + cA D e,
    Or.inl ⟨he, rfl⟩, GlobalTheory.SplitHecke.suppAt_one V⟩
  rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]

theorem unr {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {χ : (AE D)ˣ →* Circle} (hχ : UnrPl P χ)
    (y : (AE D)ˣ) (h : (1 - e) * (y : AE D) = 1 - e) (h1 : finPart D (e * (y : AE D)) ∈ intAE D)
    (h2 : finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have h' : (1 - e) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
    conv_lhs => rw [← h, mul_assoc, Units.mul_inv, mul_one]
  have e0 : finPart D e ∈ intAE D := by
    by_contra hc
    have := (he.2 1 one_ne_zero).2 (by
      rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have key : ∀ z : AE D, (1 - e) * z = 1 - e → finPart D (e * z) ∈ intAE D → finPart D z ∈ intAE D := fun z a b => by
    have : z = e * z + 1 - e := by linear_combination a
    rw [this, RingHom.map_sub, RingHom.map_add, RingHom.map_one]
    exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) e0
  refine hχ e _ (Or.inl ⟨he, rfl⟩) y ?_ (key _ h h1) (key _ h' h2)
  linear_combination (cA D e - 1) * h + ((y : AE D) - 1) * he.1.2.1

theorem sphOp_of {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) {V : HSp D} {d : List ℤ} (hd : d.Pairwise fun a b => b ≤ a) {α : GA D V}
    (hα : SuppAt e V α) (hD : DivAt V e (ϖ : D.host.E) d α) {R : Finset (GA D V)} (hR : ∀ γ ∈ R, SuppAt e V γ)
    (hc : IsCosetRep V (locPart V (KsphC V ∅) e) α R) : SphOp V P d R :=
  ⟨e, e + cA D e, ϖ, α, fun v hv => absurd hv (Finset.notMem_empty v), Or.inl ⟨he, rfl⟩, h1, h2, hd,
    fun _ _ => Iff.rfl, fun _ _ _ => rfl, hα, hD, hR, hc⟩

theorem splitLab_pairwise (n k : ℕ) : (splitLab n k).Pairwise fun a b => b ≤ a := by
  simp [splitLab, List.pairwise_append, List.pairwise_replicate]

theorem dual_splitLab_pairwise (n k : ℕ) : (dualLab (splitLab n k)).Pairwise fun a b => b ≤ a := by
  simp [dualLab, splitLab, List.pairwise_append, List.pairwise_replicate]

theorem exists_data {P : Pl D.host.E} {e : AE D} (he : IsIdemAt e P) {ϖ : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal)
    (h2 : ϖ ∉ P.asIdeal ^ 2) (V : HSp D) : ∃ (α : ℕ → GA D V) (R R' : ℕ → Finset (GA D V)),
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j) (R j)) ∧
      (∀ j, j ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) j (α j) ∧ (∀ γ ∈ R' j, SuppAt e V γ) ∧
        IsCosetRep V (locPart V (KsphC V ∅) e) (α j)⁻¹ (R' j)) ∧
      (∀ j, j ≤ V.rank → SphOp V P (dualLab (splitLab V.rank j)) (R j)) ∧
      ∀ j, j ≤ V.rank → SphOp V P (splitLab V.rank j) (R' j) := by
  obtain ⟨-, hrep, hH⟩ := GlobalTheory.SplitPlace.split_local V P e he
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  choose! α hα using (hH ϖ h1 h2).1
  choose! ρ hρ using hrep
  have hD := fun j hj => GlobalTheory.SplitDivisors.divAt_inv_of_isHeckeElt V P e ϖ j (α j) he h1 h2 hj (hα j hj)
  have s := fun j hj => (hα j hj).2.1
  have s' := fun j hj => GlobalTheory.SplitHecke.suppAt_inv (s j hj)
  refine ⟨α, fun j => ρ (α j), fun j => ρ (α j)⁻¹, fun j hj => ⟨hα j hj, hρ _ (s j hj)⟩,
    fun j hj => ⟨hα j hj, hρ _ (s' j hj)⟩, fun j hj => ?_, fun j hj => ?_⟩
  · refine sphOp_of he h1 h2 (dual_splitLab_pairwise _ _) (s j hj) ?_ (hρ _ (s j hj)).1 (hρ _ (s j hj)).2
    have := (GlobalTheory.T.divisorsAt_inv_dualLabel_and_stabilizer_mul V e _ _ _ he.1.1 h0 (hD j hj)).1
    rwa [inv_inv] at this
  · exact sphOp_of he h1 h2 (splitLab_pairwise _ _) (s' j hj) (hD j hj) (hρ _ (s' j hj)).1 (hρ _ (s' j hj)).2

section

variable {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (P : Pl D.host.E)

theorem opOf_single (d : List ℤ) (z : ℂ) : opOf π P (Finsupp.single d z) = z • ∑ γ ∈ rep V P d, π γ := by
  unfold opOf
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_sum (s : Finset ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) :
    opOf π P (∑ j ∈ s, Finsupp.single (d j) (z j)) = ∑ j ∈ s, z j • opOf π P (Finsupp.single (d j) 1) := by
  simp only [opOf_single, one_smul]
  unfold opOf
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  exact Finset.sum_congr rfl fun j _ => Finsupp.sum_single_index (zero_smul _ _)

theorem opOf_trunc (n k : ℕ) (d : ℕ → List ℤ) (z : ℕ → ℂ) (u : M) :
    opOf π P (∑ j ∈ Finset.range (n + 1), Finsupp.single (d j) (if j ≤ k then z j else 0)) u =
      ∑ j ∈ Finset.range (min k n + 1), z j • opOf π P (Finsupp.single (d j) 1) u := by
  rw [opOf_sum, LinearMap.sum_apply]
  symm
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega), LinearMap.smul_apply]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul, LinearMap.zero_apply]

end

theorem dualC_splitC (n : ℕ) (z : ℕ → ℂ) :
    dualC (splitC n z) = ∑ j ∈ Finset.range (n + 1), Finsupp.single (dualLab (splitLab n j)) (z j) := by
  unfold dualC splitC
  rw [Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single]

set_option maxHeartbeats 1000000 in

theorem match_split : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → conjPl P ≠ P → UnrPl P χS → UnrPl P χT → VacFix ψ om P ∧ ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → (T.rank = S.rank + t → ∀ k, k ≤ T.rank → Match ψ om P (dualC (splitC S.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank)⁻¹ ^ k * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank) ^ j else 0)) (Finsupp.single (splitLab T.rank k) 1)) ∧ (S.rank = T.rank + t → ∀ k, k ≤ S.rank → Match ψ om P (dualC (Finsupp.single (splitLab S.rank k) 1)) (splitC T.rank fun j => if j ≤ k then (Ideal.absNorm P.asIdeal : ℂ) ^ ((T.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - j) : ℂ) * ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ T.rank)⁻¹ ^ k * ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ S.rank) ^ j else 0)) := by
  intro D ψ S T χS χT om P hW hP hS hT
  have main : ∀ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ) (t : ℕ) (he : IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal)
      (h2 : ϖ ∉ P.asIdeal ^ 2) (hx : (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e)) f (hf : IsVacAt ψ S T P f)
      αS αT RS RT a b, _ := fun e ϖ x t he h1 h2 hx f hf αS αT RS RT a b =>
    GlobalTheory.SplitHecke.hecke_identity_split ψ S T χS χT om P e ϖ x f αS αT RS RT t hW he h1 h2 hx
      (fun y a b c => ⟨unr he hS y a b c, unr he hT y a b c⟩) hf.1 (hf.2 e _ (Or.inl ⟨he, rfl⟩)) a b
  have fix : VacFix ψ om P := by
    intro f hf k hk k' hk'
    obtain ⟨e, he⟩ := exists_isIdemAt hP
    obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt
      (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
    have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
      rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
    have hi : incA D (ϖ : D.host.E) * incA D (ϖ : D.host.E)⁻¹ = 1 := by
      rw [← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one]
    obtain ⟨αS, RS, -, a, -, -, -⟩ := exists_data he h1 h2 S
    obtain ⟨αT, -, RT, -, b, -, -⟩ := exists_data he h1 h2 T
    exact (main e ϖ (Units.mkOfMulEqOne _ _ (GlobalTheory.SplitHecke.idem_mul_inv he.1.1 hi)) 0 he h1 h2 rfl f hf
      αS αT RS RT a b).1 k (mem_hyp he hk) k' (mem_hyp he hk')
  refine ⟨fix, fun e ϖ x t he h1 h2 hx => ?_⟩
  obtain ⟨αS, RS, -, a, -, a', -⟩ := exists_data he h1 h2 S
  obtain ⟨αT, -, RT, -, b, -, b'⟩ := exists_data he h1 h2 T
  have eS : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ S.rank → ∑ γ ∈ RS j, om (γ, 1) f =
      opOf (om.comp (MonoidHom.inl _ _)) P (Finsupp.single (dualLab (splitLab S.rank j)) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors S P).1 _ _ (a' j hj)).2 _ (om.comp (MonoidHom.inl _ _)) f
      fun k hk => fix f hf k hk 1 (one_mem_hyp he T)
  have eT : ∀ f, IsVacAt ψ S T P f → ∀ j, j ≤ T.rank → ∑ γ ∈ RT j, om (1, γ) f =
      opOf (om.comp (MonoidHom.inr _ _)) P (Finsupp.single (splitLab T.rank j) 1) f := fun f hf j hj =>
    ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors T P).1 _ _ (b' j hj)).2 _ (om.comp (MonoidHom.inr _ _)) f
      fun k hk => fix f hf 1 (one_mem_hyp he S) k hk
  refine ⟨fun hr k hk f hf => ?_, fun hr k hk f hf => ?_⟩
  · rw [dualC_splitC, opOf_trunc, ← eT f hf k hk, (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.1 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eS f hf j (by rw [Finset.mem_range] at hj; omega)]
  · rw [splitC, opOf_trunc, dualC, Finsupp.mapDomain_single, ← eS f hf k hk,
      (main e ϖ x t he h1 h2 hx f hf αS αT RS RT a b).2.2 hr k hk]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [eT f hf j (by rw [Finset.mem_range] at hj; omega)]

end GlobalTheory.Hk3.SplitMatch

end
