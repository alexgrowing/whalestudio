import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedModuleSystemRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsUniformCokernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingOperatorsKernelLiftStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

open TowerAx

section

variable {ι : Type} [LinearOrder ι] {R : Type} [CommRing R] {g : ℕ} {ρ : Fin g → R}
  {T : ℕ → ℤ → Finset ι → Type} [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)]
  {res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S'}
  {p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S}
  {mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S}
  (H : TowerAx ρ res p mm)
  (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S)

theorem resTot_self
    (h1 : ∀ e t S (h : S ⊆ S) a, res e t S S h a = a) (S : Finset ι) (h : S ⊆ S) (a : H.Tot hc S) :
    H.resTot hc S S h a = a := by
  induction a using (H.ops hc S).induction with
  | h0 => exact map_zero _
  | hof e t a =>
    rw [resTot_of]
    exact congrArg _ (Subtype.ext (h1 _ _ _ _ _))
  | hadd a b ha hb => rw [map_add, ha, hb]

theorem resTot_resTot
    (h2 : ∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a,
      res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a)
    (S S' S'' : Finset ι) (h : S ⊆ S') (h' : S' ⊆ S'') (a : H.Tot hc S) :
    H.resTot hc S' S'' h' (H.resTot hc S S' h a) = H.resTot hc S S'' (h.trans h') a := by
  induction a using (H.ops hc S).induction with
  | h0 => simp only [map_zero]
  | hof e t a =>
    rw [resTot_of, resTot_of, resTot_of]
    exact congrArg _ (Subtype.ext (h2 _ _ _ _ _ _ _ _))
  | hadd a b ha hb => simp only [map_add, ha, hb]

theorem X_smul_bijective_tot
    (h9 : ∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    Function.Bijective fun m : H.Tot hc S =>
      (MvPolynomial.X i : MvPolynomial ι (MvPolynomial (Fin g) R)) • m := by
  have hS : S.Nonempty := ⟨i, hi⟩
  refine (H.ops hc S).X_smul_bijective i fun e t => ⟨fun a b h => ?_, fun b => ?_⟩
  · exact Subtype.ext ((h9 i (e + 1) t S hi).1 (congrArg Subtype.val h))
  · obtain ⟨a, ha⟩ := (h9 i (e + 1) t S hi).2 (b : T (e + 1) (t + 1) S)
    refine ⟨⟨a, (mem_Ks hS).2 ((h9 i e t S hi).1 ?_)⟩, Subtype.ext ha⟩
    rw [← H.p_mm i e t S a hS, ha, (mem_Ks hS).1 b.2, map_zero]

end

theorem exists_uniform_h1_kernels : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] [IsNoetherianRing R] (g : ℕ) (ρ : Fin g → R) (T : ℕ → ℤ → Finset ι → Type) [∀ e t S, AddCommGroup (T e t S)] [∀ e t S, Module R (T e t S)] (res : ∀ e t (S S' : Finset ι), S ⊆ S' → T e t S →ₗ[R] T e t S') (p : ∀ e t S, T (e + 1) t S →ₗ[R] T e t S) (mm : ι → ∀ e t S, T e t S →ₗ[R] T e (t + 1) S) (one : ∀ e (i : ι), T e 0 {i}) (hc : ∀ e S, OperatorsCommute (ι := ι) (R := R) (A := fun t => T e t S) fun j t => mm j e t S), (∀ e t S (h : S ⊆ S) a, res e t S S h a = a) → (∀ e t S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res e t S' S'' h' (res e t S S' h a) = res e t S S'' (h.trans h') a) → (∀ e t S S' (h : S ⊆ S') a, S.Nonempty → p e t S' (res (e + 1) t S S' h a) = res e t S S' h (p e t S a)) → (∀ j e t S a, S.Nonempty → p e (t + 1) S (mm j (e + 1) t S a) = mm j e t S (p e t S a)) → (∀ j e t S S' (h : S ⊆ S') a, S.Nonempty → res e (t + 1) S S' h (mm j e t S a) - mm j e t S' (res e t S S' h a) ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e (t + 1) S'))) → (∀ e t S, S.Nonempty → Function.Surjective (p e t S)) → (∀ e t S, S.Nonempty → LinearMap.ker (p e t S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤) → (∀ e t S, S.Nonempty → Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (T e t S)) = ⊥) → (∀ i e t S, i ∈ S → Function.Bijective (mm i e t S)) → (∀ e S j t (a : T e t S), S.Nonempty → res e t S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e S) t a = 0) → (∀ e S j t (b : T e t (insert j S)), S.Nonempty → ∃ (k : ℕ) (t' : ℤ) (a : T e t' S), GrSum.of (hc e (insert j S)) t' (res e t' S (insert j S) (Finset.subset_insert j S) a) = (MvPolynomial.X j : MvPolynomial ι R) ^ k • GrSum.of (hc e (insert j S)) t b) → (∀ e i, p e 0 {i} (one (e + 1) i) = one e i) → (∀ e i t (a : T e t {i}), ∃ (k : ℕ) (q : MvPolynomial ι R) (t' : ℤ) (w : T e t' {i}), w ∈ Ideal.span (Set.range ρ) • (⊤ : Submodule R (T e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (one e i) + GrSum.of (hc e {i}) t' w) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ e (c : ∀ i j : ι, T (e + 1) t {i, j}), (∀ i j, p e t {i, j} (c i j) = 0) → (∀ i j k, res (e + 1) t {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res (e + 1) t {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res (e + 1) t {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, T (e + 1) t {i}, (∀ i, p e t {i} (b i) = 0) ∧ ∀ i j, c i j = res (e + 1) t {i} {i, j} (sub_pair_left i j) (b i) - res (e + 1) t {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ R _ _ g ρ T _ _ res p mm one hc h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have H : TowerAx ρ res p mm := ⟨h3, h4, h5, h6, h7, h8⟩
  obtain ⟨t₀, ht⟩ := GlobalTheory.T.graded_module_system_restriction ι (MvPolynomial (Fin g) R) (H.Tot hc)
    (fun S => (H.ops hc S).grading) (H.resTot hc) (fun S S' h => H.isGradedMap_resTot hc h)
    (resTot_self H hc h1) (resTot_resTot H hc h2)
    (fun i S hi => X_smul_bijective_tot H hc h9 i S hi)
    (GlobalTheory.T.commuting_operators_uniform_kernel ι R g ρ T res p mm hc H h10) (GlobalTheory.T.commuting_operators_uniform_cokernel ι R g ρ T res p mm hc H h11)
    (GlobalTheory.T.commuting_operators_kernel_lift ι R g ρ T res p mm hc H one h12 h13)
  refine ⟨t₀, fun t htt e c hp hcoc => ?_⟩
  have hne (i j : ι) : ({i, j} : Finset ι).Nonempty := ⟨i, Finset.mem_insert_self _ _⟩
  let c' : ∀ i j : ι, H.Tot hc {i, j} := fun i j =>
    (H.ops hc {i, j}).of e t ⟨c i j, (mem_Ks (hne i j)).2 (hp i j)⟩
  obtain ⟨b', -, hcob⟩ := ht t htt c' (fun i j => (H.ops hc {i, j}).of_mem_grading e t _) (by
    intro i j k
    simp only [c', resTot_of, ← map_add]
    exact congrArg _ (Subtype.ext (hcoc i j k)))
  refine ⟨fun i => ((H.ops hc {i}).comp e t (b' i) : T (e + 1) t {i}), fun i =>
    (mem_Ks (Finset.singleton_nonempty i)).1 ((H.ops hc {i}).comp e t (b' i)).2, fun i j => ?_⟩
  have h := congrArg (fun m => (((H.ops hc {i, j}).comp e t m : Ks p e t {i, j}) : T (e + 1) t {i, j}))
    (hcob i j)
  simpa [c', comp_resTot] using h

end GlobalTheory.CompanionTheory.FormalAlg.Lift
