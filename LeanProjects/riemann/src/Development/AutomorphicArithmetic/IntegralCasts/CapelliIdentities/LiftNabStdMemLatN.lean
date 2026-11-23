import Mathlib
import Formalism.LocalRingCardinality.DataCoeff
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.PieriBlockIdeals.BlockIdealBound5Derived
import Formalism.GradedWeylDivisibility.StatementA
import Formalism.PieriBlockIdeals.BranchingBoundLastGradedOneRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
import Formalism.HermitianLattices.StatementLat
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormIntegersLeOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightedHomogeneousMap
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SemilinearLatticeMem

open MvPolynomial in
private theorem mem_dw_iff {R : Type} [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν ↔ IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) f ν ∧
      ∀ l j : Fin n, l < j → Formalism.GradedWeylDivisibility.colAddGen R l j f = rename some f := by
  simp [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_iInf, sub_eq_zero]

open MvPolynomial in
private theorem map_mem_dw_iff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : Function.Injective φ)
    (r n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl S r n ν ↔ f ∈ Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [mem_dw_iff, mem_dw_iff]
  obtain ⟨h1, h2⟩ := UpperTheory.aeval_map_eq_rename_map_iff R S φ hφ _ _ (Formalism.GradedWeylDivisibility.colW r n) ν f
  refine and_congr h1 (forall_congr' fun l => forall_congr' fun j => forall_congr' fun _ => ?_)
  refine h2 _ _ _ some fun v => ?_
  split_ifs <;> simp

private theorem smul_mem_latN {l : ℕ} [Fact l.Prime] {ι : Type} {n : ℕ} (F : GlobalTheory.ExpFrame.Frame l ι n) (lamW : ι → ℕ → ℕ)
    (a : F.O) (y : Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW) (hy : y ∈ F.latN lamW) : F.emb a • y ∈ F.latN lamW := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, x, hx, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, x, hx, by rw [map_mul, mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

private theorem map_detPol {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) :
    MvPolynomial.map φ (GlobalTheory.FrameRead.detPol R n) = GlobalTheory.FrameRead.detPol S n := by
  unfold GlobalTheory.FrameRead.detPol
  rw [RingHom.map_det]
  congr 1
  ext a s : 2
  simp

theorem UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN :
    ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K] (l : ℕ)
    [inst_2 : Fact (Nat.Prime l)] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (e0 : K →+* PadicAlgCl l) (ι : Type) [inst_3 : Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → Formalism.BasicNotions.DomWeight n)
    (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : GlobalTheory.ExpFrame.Frame l ι n)
    (Φ : ↥(Formalism.L2.DIV.VV K lam) →ₛₗ[e0] Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW),
    GlobalTheory.FrameRead.AtPlace w e0 →
      Function.Injective (⇑F.emb : F.O → PadicAlgCl l) →
        (∀ (x : K),
            ‖(e0 : K → PadicAlgCl l) x‖ ≤ (1 : ℝ) → (e0 : K → PadicAlgCl l) x ∈ Set.range (⇑F.emb : F.O → PadicAlgCl l)) →
          GlobalTheory.FrameRead.Shift lam lamW c →
            GlobalTheory.FrameRead.IsPhi e0 lam lamW Φ →
              ∀ (v : ↥(Formalism.L2.DIV.VV K lam)),
                (↑v : Formalism.L2.DIV.Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.L2.DIV.nabStd K lam) →
                  (Φ : ↥(Formalism.L2.DIV.VV K lam) → Formalism.CohomologicalDescent.DepthNonnegative.NablaT (PadicAlgCl l) n lamW) v ∈
                    F.latN
                      lamW := by
  intro K _ _ l _ w e0 ι _ _ n lam lamW c F Φ hw hinj hrange _ hΦ v hv
  obtain ⟨s, hs, hv⟩ := hv
  have hint : ∀ r : NumberField.RingOfIntegers K, e0 (algebraMap _ K r) ∈ Set.range F.emb :=
    fun r => hrange _ (UpperTheory.norm_integers_le_one K l e0 r)
  have hs1 : 1 ≤ ‖e0 (algebraMap _ K s)‖ := not_lt.1 fun h => hs ((hw s).2 h)
  have hs0 : algebraMap _ K s ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hs1
    exact absurd hs1 (by norm_num)
  refine UpperTheory.semilinear_lattice_mem _ K _ _ _ e0 _ Φ (Set.range F.emb) (F.latN lamW) _ ?_ hint ?_ s hs0 ?_ v hv
  · rintro _ ⟨a, rfl⟩ y hy
    exact smul_mem_latN F lamW a y hy
  · rintro _ ⟨x, hx, rfl⟩
    choose x0 hx0 hxe using hx
    have hxe' : ∀ τ, MvPolynomial.map (algebraMap (NumberField.RingOfIntegers K) K) (x0 τ) = x τ := hxe
    have hxK : ∀ τ, x τ ∈ Formalism.BasicNotions.nablaSq K n (lam τ) := fun τ => by
      rw [← hxe' τ]
      exact (map_mem_dw_iff _ (IsFractionRing.injective _ K) _ _ _ _).2 (hx0 τ)
    have hU : Formalism.L2.DIV.ten x ∈ Formalism.L2.DIV.VV K lam := Submodule.subset_span ⟨x, hxK, rfl⟩
    refine ⟨hU, ?_⟩
    obtain ⟨y, hy, hΦv⟩ := hΦ x ⟨_, hU⟩ hxK rfl
    let φ : NumberField.RingOfIntegers K →+* F.O :=
      ((RingEquiv.ofBijective F.emb.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), F.emb.rangeRestrict_surjective⟩).symm.toRingHom).comp
        ((e0.comp (algebraMap _ K)).codRestrict F.emb.range hint)
    have hφ : F.emb.comp φ = e0.comp (algebraMap _ K) := by
      ext r
      exact congrArg Subtype.val ((RingEquiv.ofBijective F.emb.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h), F.emb.rangeRestrict_surjective⟩).apply_symm_apply _)
    refine AddSubgroup.subset_closure ⟨1, y, fun τ => ?_, ?_⟩
    · have he : MvPolynomial.map F.emb (GlobalTheory.FrameRead.liftPol φ (lamW τ (n - 1)) (x0 τ)) = y τ := by
        rw [hy τ, ← hxe' τ]
        simp only [GlobalTheory.FrameRead.liftPol, map_mul, map_pow, map_detPol, MvPolynomial.map_map, hφ]
      refine ⟨_, (map_mem_dw_iff F.emb hinj _ _ _ _).1 ?_, he⟩
      rw [he]
      exact (y τ).2
    · rw [map_one, one_smul]
      exact hΦv
  · refine hrange _ ?_
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ hs1
