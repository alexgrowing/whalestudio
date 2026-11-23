import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPullHomExtAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.Cris GlobalTheory.CurveRootGeometry GlobalTheory.AbDatum GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymmPoincare

universe u

section Linear

variable {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V]
  {ψ : Module.Dual K V →ₗ[K] Module.Dual K V →ₗ[K] K} {β : V →ₗ[K] Module.Dual K V}

theorem bijective_of_eval [Module.Finite K V] (h : ∀ s y, ψ (β s) y = y s) : Function.Bijective β := by
  have inj : Function.Injective β := (injective_iff_map_eq_zero _).2 fun s hs ↦
    (Module.forall_dual_apply_eq_zero_iff K s).1 fun y ↦ by rw [← h, hs, map_zero, LinearMap.zero_apply]
  exact ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := K) (V := V)).symm).1 inj⟩

theorem mem_iff_of_isotropic [Module.Finite K V] (h : ∀ s y, ψ (β s) y = y s) (F : Submodule K V)
    (hF : Module.finrank K V = 2 * Module.finrank K F)
    (iso : ∀ x ∈ F.dualAnnihilator, ∀ y ∈ F.dualAnnihilator, ψ x y = 0) (s : V) :
    s ∈ F ↔ ∀ w ∈ F, β s w = 0 := by
  let e := LinearEquiv.ofBijective β (bijective_of_eval h)
  have le : F.dualAnnihilator.map e.symm.toLinearMap ≤ F := by
    rintro _ ⟨x, hx, rfl⟩
    refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff F _).1 fun y hy ↦ ?_
    rw [← h]
    exact (congrArg (fun z ↦ ψ z y) (e.apply_symm_apply x)).trans (iso x hx y hy)
  have eq : F.dualAnnihilator.map e.symm.toLinearMap = F := by
    refine Submodule.eq_of_le_of_finrank_eq le ?_
    rw [LinearEquiv.finrank_map_eq]
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq F
    omega
  rw [← Submodule.mem_dualAnnihilator]
  conv_lhs => rw [← eq]
  rw [Submodule.mem_map_equiv]
  rfl

end Linear

section Swap

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A B : Over S} [GrpObj A] [GrpObj B]

theorem isCorrForm_swap {P : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) : IsCorrForm κ t B A (swap P) (-φ.flip) := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  have m : IsMor κ ((A ⊗ B).hom ≫ t) κ ((B ⊗ A).hom ≫ t) (RingHom.id R) (lift (snd B A) (fst B A)).left :=
    (homMor κ t (lift (snd B A) (fst B A))).isMor
  have k := isChern_pull m hc
  rw [crystallinePull2_sum_cup] at k
  refine ⟨n, fun i ↦ -b i, a, ?_, fun x y ↦ ?_⟩
  · convert k using 2 with i
    rw [pullOver_pullOver, pullOver_pullOver, lift_fst, lift_snd, Submodule.coe_neg, map_neg, map_neg,
      LinearMap.neg_apply, neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)]
  · simp only [LinearMap.neg_apply, LinearMap.flip_apply, hφ, map_neg, ← Finset.sum_neg_distrib, neg_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]

theorem isCorrForm_of_iso {P Q : LB (A ⊗ B).left} {φ : Crys κ t A →ₗ[R] Crys κ t B →ₗ[R] R}
    (H : IsCorrForm κ t A B P φ) (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : IsCorrForm κ t A B Q φ := by
  obtain ⟨n, a, b, hc, hφ⟩ := H
  exact ⟨n, a, b, (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ hP hQ e _ hc, hφ⟩

theorem skew_of_symm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB) (hs : LBIso (swap P) P)
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x :=
  LinearMap.congr_fun₂ (H.unique C hP (isCorrForm_of_iso (isCorrForm_swap H) (pull_isLB hP _) hP hs)) x y

theorem isPerfect_of_symm {P : LB (A ⊗ A).left} (hd : IsDual A A P) (hs : LBIso (swap P) P) :
    IsPerfect A A P := by
  have hP := hd.isLB
  have hs' : (swap P).IsLB := pull_isLB hP _
  have sym {Y : Over S} (x y : Y ⟶ A) : evc hP x y = evc hP y x := by
    rw [← evc_swap hP hs', evc, (CechPic.cls_eq_iff hs' hP).2 hs, evc]
  refine ⟨hP, (triv_ev_iff hP _ _).2 (hd.additive.evc_one hP _), hd.zero, fun Y x hx ↦ hd.eq_one x ?_,
    fun _ ↦ hd.eq_one⟩
  have k := congrArg (CechPic.pull (lift (snd A Y) (fst A Y)).left) ((triv_ev_iff hP _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at k
  rw [triv_ev_iff hP, sym, k]

end Swap

theorem finrank_eq_of_rankAtStalk {K : Type} [Field K] {V : Type u} [AddCommGroup V] [Module K V] {n : ℕ}
    (h : ∀ q : PrimeSpectrum K, Module.rankAtStalk V q = n) : Module.finrank K V = n := by
  have e := h ⊥
  rwa [Module.rankAtStalk_eq_finrank_of_free] at e

theorem skew_lagrangian : GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.ConjugateFiltration → ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (hK : (p : K) = 0) (A : Over (Sp K)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A), SmoothOfRelativeDimension g A.hom → ∀ P : LB (A ⊗ A).left, IsDual A A P → LBIso (swap P) P → ∀ (ψ : HdR A →ₗ[K] HdR A →ₗ[K] K) (β : primDR A →ₗ[K] HdR A), IsCorrForm (dp0 K) (𝟙 _) A A P ψ → (∀ s y, ψ (β s) y = y s) → Module.Finite K (primDR A) ∧ Function.Bijective β ∧ (∀ s w, β s w = - β w s) ∧ (∀ s, s ∈ PrimitiveSubmodule A ↔ ∀ w ∈ PrimitiveSubmodule A, β s w = 0) ∧ ∀ s, s ∈ conjDR p K hK A ↔ ∀ w ∈ conjDR p K hK A, β s w = 0 := by
  intro hD hC p _ K _ hK A _ g hA hg P hd hs ψ β hψ hβ
  obtain ⟨hfin, -, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hD.1 hA hg
  have hV := finrank_eq_of_rankAtStalk hrk
  have sk := skew_of_symm (cupSquare_of_free hD.1 (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) (smooth_prod hg hg))
    hd.isLB hs hψ
  obtain ⟨-, h₁, -⟩ := hψ.perfect hD hA hg hA hg (isPerfect_of_symm hd hs)
  obtain ⟨-, -, -, -, hF⟩ := hD.2.1 K A g hA hg
  obtain ⟨-, -, hG, h₂⟩ := hC p K hK A g hA hg (cast_left p K hK A) (frobMor p K hK A (cast_left p K hK A))
  refine ⟨hfin, bijective_of_eval hβ, fun s w ↦ by rw [← hβ w, sk, hβ],
    mem_iff_of_isotropic hβ _ (by rw [hV, finrank_eq_of_rankAtStalk hF]) fun x hx ↦ (h₁ x).1 hx,
    mem_iff_of_isotropic hβ _ (hV.trans (congrArg (2 * ·) (finrank_eq_of_rankAtStalk hG).symm))
      fun x hx y hy ↦ ?_⟩
  exact h₂ A hA hg _ (frobMor p K hK A (cast_left p K hK A)) P hd ψ hψ x y
    (fun c ↦ (Submodule.mem_dualAnnihilator x).1 hx _ (Submodule.subset_span ⟨c, rfl⟩))
    fun c ↦ (Submodule.mem_dualAnnihilator y).1 hy _ (Submodule.subset_span ⟨c, rfl⟩)

end GlobalTheory.SymmPoincare
