import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType GlobalTheory.StepData GlobalTheory.ProdSupport Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LevelType

theorem exists_parVec_of_map : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (α n : Type) [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (s : ∀ a, Representation ℂ (GL (m a) F) (X a)) (a : α) (θ : (ZMod p)ˣ →* ℂˣ) (χ : Fˣ →* ℂˣ) (U : Type) [AddCommGroup U] [Module ℂ U] (ρ : Representation ℂ (GL n (ZMod p)) U) (φ : U →ₗ[ℂ] IndSp e (piTensor s)), resCard F = p → CharLift θ χ → (∀ g ∈ KO F (m a), ∀ v, s a g v = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • v) → φ ≠ 0 → (∀ (g : GL n (ZMod p)) (h : GL n F), IsLift g h → ∀ w, multiProd e s h (φ w) = φ (ρ g w)) → ∃ v : U, v ≠ 0 ∧ ParVec ρ e a θ v := by
  intro F _ _ _ _ p _ α n _ _ _ _ m _ _ e X _ _ s a θ χ U _ _ ρ φ hp hθ hs hφ hint
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  let Λ : U →ₗ[ℂ] (⨂[ℂ] b, X b) :=
    { toFun := fun w => (φ w).1.1 1
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hΛ : ∀ w, Λ w = (φ w).1.1 1 := fun _ => rfl
  have hΛ0 : Λ ≠ 0 := by
    obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
      by_contra! h
      exact hφ (LinearMap.ext h)
    obtain ⟨x, hx⟩ : ∃ x, (φ w).1.1 x ≠ 0 := by
      by_contra! h
      exact hw (Subtype.ext (Subtype.ext (funext h)))
    obtain ⟨q, κ, hκ, rfl⟩ := MultiIrr.exists_parab_mul e x
    obtain ⟨g, hg⟩ := exists_isLift_of_mem_KO hp hκ
    intro h0
    apply hx
    have h1 : (φ w).1.1 κ = 0 := by
      have h2 : Λ (ρ g w) = 0 := by rw [h0]; rfl
      rw [hΛ, ← hint g κ hg w] at h2
      have h3 : (multiProd e s κ (φ w)).1.1 1 = (φ w).1.1 (1 * κ) := rfl
      rwa [h3, one_mul] at h2
    rw [parInd_law, h1, map_zero, smul_zero]
  let H : Subgroup (GL n (ZMod p)) := Subgroup.map (parab (ZMod p) e).subtype
    (⨅ b : {b // b ≠ a}, ((Pi.evalMonoidHom (fun c => GL (m c) (ZMod p)) b.1).comp (leviProj (ZMod p) e)).ker)
  have hH : ∀ x : parab (ZMod p) e, (∀ b, b ≠ a → leviProj (ZMod p) e x b = 1) → (x : GL n (ZMod p)) ∈ H := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf]
    intro b
    exact MonoidHom.mem_ker.2 (hx b.1 b.2)
  have hH' : ∀ y ∈ H, ∃ x : parab (ZMod p) e, (x : GL n (ZMod p)) = y ∧
      ∀ b, b ≠ a → leviProj (ZMod p) e x b = 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_iInf] at hx
    exact ⟨x, rfl, fun b hb => MonoidHom.mem_ker.1 (hx ⟨b, hb⟩)⟩
  have key : ∀ y ∈ H, ∀ w, Λ (ρ y w) = ((θ.comp GeneralLinearGroup.det y : ℂˣ) : ℂ) • Λ w := by
    intro y hy w
    obtain ⟨x, rfl, hx⟩ := hH' y hy
    obtain ⟨h, hh, hl⟩ := exists_canon_lift hp (x : GL n (ZMod p))
    have hP : h ∈ parab F e := mem_parab.2 fun i j hij => by
      have h0 := mem_parab.1 x.2 i j hij
      change h.val i j = 0
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) i j).val : F) = 0
      rw [h0]
      simp
    let q : parab F e := ⟨h, hP⟩
    have hq : ∀ b, b ≠ a → leviProj F e q b = 1 := by
      intro b hb
      have h2 := hx b hb
      refine Units.ext (Matrix.ext fun i j => ?_)
      have h3 := congrArg (fun g : GL (m b) (ZMod p) => (g : Matrix (m b) (m b) (ZMod p)) i j) h2
      simp only [leviProj_apply] at h3
      rw [leviProj_apply]
      change h.val _ _ = _
      rw [hh]
      change ((((x : GL n (ZMod p)) : Matrix n n (ZMod p)) _ _).val : F) = _
      rw [h3]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, ZMod.val_one]
    have hqa : leviProj F e q = Pi.mulSingle a (leviProj F e q a) := by
      funext b
      by_cases hb : b = a
      · subst hb; simp
      · rw [Pi.mulSingle_eq_of_ne hb, hq b hb]
    have hKa : leviProj F e q a ∈ KO F (m a) := by
      refine IsLift.mem_KO hp (g := leviProj (ZMod p) e x a) fun i j => ?_
      change valuation F (h.val _ _ - _) < 1
      rw [hh]
      simp
    have hδ : deltaHalf F m (leviProj F e q) = 1 := by
      rw [deltaHalf_apply]
      refine Finset.prod_eq_one fun b _ => isUnram_absPow F _ _ ?_
      by_cases hb : b = a
      · subst hb; exact valuation_det_of_mem_KO hKa
      · rw [hq b hb, map_one]; simp
    have hdet : χ (GeneralLinearGroup.det (leviProj F e q a)) = θ (GeneralLinearGroup.det (x : GL n (ZMod p))) := by
      rw [← CharLift.det hp hθ hl]
      congr 1
      change _ = GeneralLinearGroup.det (q : GL n F)
      rw [det_parab F e q, Finset.prod_eq_single a]
      · intro b _ hb; rw [hq b hb, map_one]
      · simp
    have hv := hint _ h hl w
    rw [hΛ, hΛ, ← hv]
    change (φ w).1.1 (1 * h) = _
    rw [one_mul]
    have hlaw := parInd_law e (piTensor s) (φ w) q 1
    rw [mul_one] at hlaw
    change (φ w).1.1 (q : GL n F) = _
    rw [hlaw, hδ, Units.val_one, one_smul, hqa, piTensor_mulSingle s a _ _ (hs _ hKa), MonoidHom.comp_apply, hdet]
  obtain ⟨v, hv0, hv⟩ := exists_eigen_of_map ρ H (θ.comp GeneralLinearGroup.det) Λ hΛ0 key
  exact ⟨v, hv0, fun x hx => hv _ (hH x hx)⟩

end GlobalTheory.LevelType

end
