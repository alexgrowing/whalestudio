import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyExhaustion.PropsExh
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfJacquetMin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrreducibleSmoothQuotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivPiExteriorTensorBlockLevi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMapLaw
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRest
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.JacquetLeft

open GlobalTheory.SmGL.CuspMax GlobalTheory.JacMinCusp Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tmul_ne_zero' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] {x : X} {y : Y}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DYha2.main hx hy

theorem isCuspidal_of_jacquet_min_left {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] [Nontrivial W']
    (π : Representation ℂ (GL (Fin n) k) V) (h : a + b = n)
    (hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < a →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))))
    (σ : Representation ℂ (GL (Fin a) k) W) (ρ : Representation ℂ (GL (Fin b) k) W') (hσ : IsSmooth σ)
    (φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor σ ρ)) (hφ : Function.Surjective φ) :
    IsCuspidal σ := by
  refine (isCuspidal_iff_maximal k a W σ).2 ⟨hσ, fun r t h' hr ht => ?_⟩
  have hcd : r + (t + b) = n := by omega
  have hJ : twKer π (unipRad k (two (stdSum hcd))) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 (hmin r (t + b) hcd hr (by omega))
  set K' := twKer σ (unipRad k (two (stdSum h'))) 1 with hK'
  set Kab := twKer π (unipRad k (two (stdSum h))) 1 with hKab
  let T : W ⊗[ℂ] W' →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := LinearMap.rTensor W' K'.mkQ
  let Φ : V →ₗ[ℂ] (W ⧸ K') ⊗[ℂ] W' := T ∘ₗ φ.toLinearMap ∘ₗ Kab.mkQ
  have hΦ : ∀ v, Φ v = T (φ (Submodule.Quotient.mk v)) := fun v => rfl

  have hA : ∀ u' ∈ unipRad k (two (stdSum h')), ∀ y : W ⊗[ℂ] W',
      T (extTensor σ ρ (u', 1) y) = T y := by
    intro u' hu' y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w w' =>
      rw [extTensor_tmul]
      simp only [T, LinearMap.rTensor_tmul, map_one, Module.End.one_apply, Submodule.mkQ_apply]
      congr 1
      exact (Submodule.Quotient.eq K').2 (Submodule.subset_span ⟨⟨u', hu'⟩, w, by simp⟩)
    | add x y hx hy => simp only [map_add, hx, hy]

  have hB : ∀ g : GL (Fin a) k × GL (Fin b) k, GeneralLinearGroup.det g.1 = 1 → g.2 = 1 → ∀ v : V,
      jac₂ (stdSum h) π g (Submodule.Quotient.mk v) =
        Submodule.Quotient.mk (π (leviEmb k (two (stdSum h)) (leviTwo k _ _ g)) v) := by
    intro g h1 h2 v
    have hd : deltaHalf k (Two (Fin a) (Fin b)) (leviTwo k _ _ g) = 1 := by
      rw [deltaHalf_two, h1, h2]; simp
    show jac (two (stdSum h)) π (leviTwo k _ _ g) _ = _
    rw [jac_mk, hd]; simp
  have hN : ∀ u ∈ unipRad k (two (stdSum h)), ∀ v : V,
      (Submodule.Quotient.mk (π u v) : V ⧸ Kab) = Submodule.Quotient.mk v := by
    intro u hu v
    exact (Submodule.Quotient.eq Kab).2 (Submodule.subset_span ⟨⟨u, hu⟩, v, by simp⟩)
  have hC : ∀ u ∈ unipRad k (two (stdSum hcd)), ∀ v : V, Φ (π u v) = Φ v := by
    intro u hu v
    have hu' := (mem_unipRad_two_iff hcd).1 hu
    have hp : u ∈ parab k (two (stdSum h)) := by
      rw [mem_parab]
      intro i j hij
      rw [blk_two_stdSum_lt] at hij
      rw [hu' i j (by omega), Matrix.one_apply_ne]
      intro hij'; subst hij'; omega
    obtain ⟨n', hn', hun⟩ := exists_levi_mul_unip k (two (stdSum h)) ⟨u, hp⟩
    set g := (leviTwo k (Fin a) (Fin b)).symm (leviProj k (two (stdSum h)) ⟨u, hp⟩) with hg
    have hlg : leviTwo k _ _ g = leviProj k (two (stdSum h)) ⟨u, hp⟩ := by simp [g]
    have hg2 : g.2 = 1 := by
      ext i j
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ true : Matrix (Fin b) (Fin b) k) i j = _
      rw [leviProj_apply, two_true, two_true]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hg1 : g.1 ∈ unipRad k (two (stdSum h')) := by
      rw [mem_unipRad_two_iff]
      intro i j hij
      show (leviProj k (two (stdSum h)) ⟨u, hp⟩ false : Matrix (Fin a) (Fin a) k) i j = _
      rw [leviProj_apply, two_false, two_false]
      rw [hu' _ _ (by simp; omega)]
      simp [Matrix.one_apply, stdSum]
    have hdet : GeneralLinearGroup.det g.1 = 1 := det_eq_one_of_mem_unipRad k hg1
    have hu_eq : u = leviEmb k (two (stdSum h)) (leviTwo k _ _ g) * n' := by rw [hlg]; exact hun
    rw [hu_eq, map_mul, Module.End.mul_apply, hΦ, ← hB g hdet hg2, φ.isIntertwining,
      show g = (g.1, 1) from Prod.ext rfl hg2, hA _ hg1, hN _ hn', ← hΦ]

  have hΦ0 : ∀ v, Φ v = 0 := by
    intro v
    have hv : v ∈ twKer π (unipRad k (two (stdSum hcd))) 1 := hJ ▸ Submodule.mem_top
    have : twKer π (unipRad k (two (stdSum hcd))) 1 ≤ LinearMap.ker Φ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      simp [hC u u.2 w]
    exact this hv
  have hsurj : Function.Surjective Φ :=
    (LinearMap.rTensor_surjective W' (Submodule.mkQ_surjective K')).comp
      (hφ.comp (Submodule.mkQ_surjective Kab))

  show Subsingleton (W ⧸ K')
  refine ⟨fun x y => ?_⟩
  rw [← sub_eq_zero]
  by_contra hq
  obtain ⟨w, hw⟩ := exists_ne (0 : W')
  obtain ⟨v, hv⟩ := hsurj ((x - y) ⊗ₜ w)
  exact tmul_ne_zero' hq hw (hv.symm.trans (hΦ0 v))

theorem nontrivial_jacquet_top {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hπ : π.IsIrreducible) (h : n + 0 = n) :
    Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = false := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · rfl
    · exact Fin.elim0 y
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  haveI : Nontrivial V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible hπ
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

theorem bernsteinZelevinsky (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness := fun k _ _ _ _ =>
  ⟨GlobalTheory.BZBridge.irreducibleAdmissible hA k, GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k, GlobalTheory.SmGL.IndDual.inductionContragredient k⟩

theorem exists_quotient_jac₂ (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hn : 0 < n) :
    ∃ (a b : ℕ) (h : a + b = n) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k)),
      0 < a ∧ IsCuspidal s.ρ ∧
        ∃ φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor s.ρ t.ρ), Function.Surjective φ := by
  classical
  let P : ℕ → Prop := fun d => 0 < d ∧ ∃ (t : ℕ) (h : d + t = n),
    Nontrivial (Jacquet π (unipRad k (two (stdSum h))))
  have hP : ∃ d, P d := ⟨n, hn, 0, rfl, nontrivial_jacquet_top π hi _⟩
  obtain ⟨ha, b, h, hJ⟩ := Nat.find_spec hP
  have hmin : ∀ (c d : ℕ) (h' : c + d = n), 0 < c → c < Nat.find hP →
      Subsingleton (Jacquet π (unipRad k (two (stdSum h')))) := fun c d h' hc hca => by
    by_contra hns
    exact Nat.find_min hP hca ⟨hc, d, h', not_subsingleton_iff_nontrivial.1 hns⟩
  generalize Nat.find hP = a at ha h hJ hmin
  have hBZ := bernsteinZelevinsky hA
  have hfl : HasFiniteLength (jac (two (stdSum h)) π) :=
    (hBZ k).2.1 _ _ _ (two (stdSum h)) V π hs (hasFiniteLength_of_isIrreducible hi)
  obtain ⟨Y, _, _, τ, hτs, hτi, q, hq⟩ :=
    IrrQuot.exists_irreducible_smooth_quotient _ (isSmooth_jac (two (stdSum h)) hs) hfl hJ
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hBZ k Bool (Two (Fin a) (Fin b))
    (⟨Y, τ, hτs, hτi⟩ : IrrRep _)
  let F : ∀ j : Bool, Representation ℂ (GL (Two (Fin a) (Fin b) j) k) (s j).V := fun j => (s j).ρ
  let B := GlobalTheory.JacFactor.piTensorBoolEquiv F
  let φ : (jac₂ (stdSum h) π).IntertwiningMap (extTensor (F false) (F true)) :=
    ⟨B.toLinearEquiv.toLinearMap ∘ₗ E.toLinearEquiv.toLinearMap ∘ₗ q.toLinearMap, fun g =>
      LinearMap.ext fun v => by
        show B (E (q (jac (two (stdSum h)) π (leviTwo k _ _ g) v))) =
          extTensor (F false) (F true) g (B (E (q v)))
        have e1 : E (τ (leviTwo k _ _ g) (q v)) = piTensor F (leviTwo k _ _ g) (E (q v)) :=
          E.toIntertwiningMap.isIntertwining _ _ _ _
        have e2 := B.toIntertwiningMap.isIntertwining _ _ g (E (q v))
        rw [q.isIntertwining]
        exact (congrArg B e1).trans e2⟩
  have hφ : Function.Surjective φ :=
    B.toLinearEquiv.surjective.comp (E.toLinearEquiv.surjective.comp hq)
  haveI : Nontrivial (s true).V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible (s true).irr
  exact ⟨a, b, h, s false, s true, ha,
    isCuspidal_of_jacquet_min_left π h hmin (s false).ρ (s true).ρ (s false).smooth φ hφ, φ, hφ⟩

theorem exists_injective_comp {G A B C : Type} [Group G] [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
    [AddCommMonoid C] [Module ℂ C] {ρ₁ : Representation ℂ G A} {ρ₂ : Representation ℂ G B}
    {ρ₃ : Representation ℂ G C} (ψ : ρ₁.IntertwiningMap ρ₂) (hψ : Function.Injective ψ) (E : ρ₂.Equiv ρ₃) :
    ∃ f : ρ₁.IntertwiningMap ρ₃, Function.Injective f :=
  ⟨E.toIntertwiningMap.comp ψ, E.toLinearEquiv.injective.comp hψ⟩

set_option maxHeartbeats 4000000 in

theorem exists_embedding_of_prod₂ {a b : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (a + b)) k) V) (s : IrrRep (GL (Fin a) k)) (t : IrrRep (GL (Fin b) k))
    (ha : 0 < a) (hc : IsCuspidal s.ρ) (ψ : π.IntertwiningMap (prod₂ s.ρ t.ρ)) (hψ : Function.Injective ψ) :
    ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = a + b), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  have hd : ∑ i, (![IrrGL.of s.ρ s.smooth s.irr, IrrGL.of t.ρ t.smooth t.irr] i).1 = a + b :=
    Fin.sum_univ_two _
  obtain ⟨E⟩ := nonempty_prod₂_equiv_prodIrr s.ρ s.smooth s.irr t.ρ t.smooth t.irr hd
  obtain ⟨f, hf⟩ := exists_injective_comp ψ hψ E
  exact ⟨_, hd, IrrGL.isCusp_of.2 ⟨ha, hc⟩, f, hf⟩

theorem exists_embedding {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π)
    (hi : π.IsIrreducible) (hn : 0 < n) :
    ∃ (y : Fin 2 → IrrGL k) (hd : ∑ a, (y a).1 = n), (y 0).IsCusp ∧
      ∃ f : π.IntertwiningMap (prodIrr y hd), Function.Injective f := by
  obtain ⟨a, b, rfl, s, t, ha, hc, φ, hφ⟩ := exists_quotient_jac₂ hA π hs hi hn
  haveI : Nontrivial s.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible s.irr
  haveI : Nontrivial t.V := GlobalTheory.JacFactor.nontrivial_of_isIrreducible t.irr
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    obtain ⟨w, hw⟩ := exists_ne (0 : s.V)
    obtain ⟨w', hw'⟩ := exists_ne (0 : t.V)
    obtain ⟨v, hv⟩ := hφ (w ⊗ₜ w')
    exact tmul_ne_zero' hw hw' hv.symm
  exact (GlobalTheory.CompanionTheory.Frob.exists_injective_of_jac₂ k a b V s.V t.V π s.ρ t.ρ hs hi φ hφ0).elim fun ψ hψ =>
    exists_embedding_of_prod₂ π s t ha hc ψ hψ

theorem jacquetSubLeft : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k :=
  fun hA x hx => exists_embedding hA x.rep x.2.rep.smooth x.2.rep.irr hx

end GlobalTheory.CompanionTheory.JacquetLeft

end
