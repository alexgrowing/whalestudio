import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.RowSurjZ
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeDegenerationNaturalStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.AffineOpenCaps.GlobTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackCoverStarCompatStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob

namespace CrystallineSemistableComparison.Om.GlobPf2

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (U : Cov q) (a : ℕ)
  (t : ∀ n (i : Fin (n + 1) → U.ι), HU (Fk q U a) (capT (Vk q U a) i) a ≃ₗ[K] OmU q (capO U.U i) a)

def tH (ht : ∀ m n (i : Fin (n + 1) → U.ι) (θ : Fin (m + 1) → Fin (n + 1)) (x : HU (Fk q U a) (capT (Vk q U a) (i ∘ θ)) a),
      t n i ((resU (Fk q U a) (U := capT (Vk q U a) (i ∘ θ)) (V := capT (Vk q U a) i) fun T hT k => hT (θ k)).pull a x) =
        formRes q (capO_comp U.U i θ) a (t m (i ∘ θ) x)) :
    Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) where
  f n := LinearMap.pi fun i => (t n i).toLinearMap.comp (LinearMap.proj i)
  comm n x := by
    funext i
    have key : ∀ k : Fin (n + 2), (formCos q U.U a).δ n k (fun i' => t n i' (x i')) i =
        t (n + 1) i ((cechH (Fk q U a) (Vk q U a) a).δ n k x i) := fun k =>
      (ht n (n + 1) i k.succAbove (x (i ∘ k.succAbove))).symm
    change (formCos q U.U a).d n (fun i' => t n i' (x i')) i = t (n + 1) i ((cechH (Fk q U a) (Vk q U a) a).d n x i)
    rw [Cos.d_apply, Cos.d_apply, Finset.sum_apply, Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, Pi.smul_apply, map_zsmul, key k]

theorem tH_bij (ht) (n : ℕ) : Function.Bijective ((tH q U a t ht).f n) := by
  refine ⟨fun x y h => funext fun i => (t n i).injective (congrFun h i), fun y => ⟨fun i => (t n i).symm (y i), ?_⟩⟩
  funext i
  exact (t n i).apply_symm_apply (y i)

end

theorem cls_congr0 {R : Type} [CommRing R] (L : Cx.{0} R) (n : ℕ) (x y : L.X n) (hx : L.d n x = 0) (hy : L.d n y = 0)
    (h : x = y) : L.cls x hx = L.cls y hy := by
  subst h; rfl

theorem glob_iso : ∀ (K : Type) [Field K] [CharZero K],
    ∃ e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a j : ℕ),
      HT.Hdg q a (a + j) ≃ₗ[K] (formCos q U.U a).cx.H j,
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [Smooth q] [Smooth p]
      (u : X ⟶ Y) (hu : u ≫ p = q) (U : Cov q) (W : Cov p) (τ : U.ι → W.ι)
      (hτ : ∀ n (i : Fin (n + 1) → U.ι), capO U.U i ≤ u ⁻¹ᵁ capO W.U (τ ∘ i)) (a j : ℕ) (c : (formCos p W.U a).X j)
      (h0 : (formCos p W.U a).cx.d j c = 0)
      (h1 : (formCos q U.U a).cx.d j (fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i)))) = 0),
      HT.pullH u hu a (a + j) ((e p W a j).symm ((formCos p W.U a).cx.cls c h0)) =
        (e q U a j).symm ((formCos q U.U a).cx.cls _ h1) := by
  intro K _ _
  obtain ⟨e1, he1⟩ := GlobalTheory.T.cech_hodge_degeneration_natural K
  obtain ⟨t, htr, htp⟩ := GlobalTheory.CompanionTheory.OmGlobTerm.AssemblyHe1.term K
  let φ : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (U : Cov q) (a : ℕ),
      Cx.Hom (cechH (Fk q U a) (Vk q U a) a).cx (formCos q U.U a).cx (RingHom.id K) := fun q _ U a =>
    tH q U a (t q U a) fun m n i θ x => htr q U a m n i θ x
  refine ⟨fun q _ U a j => (e1 q U a j).trans
    (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)), ?_⟩
  intro X Y q p _ _ u hu U W τ hτ a j c h0 h1
  obtain ⟨hG, hτ'⟩ := GlobalTheory.T.pullback_cover_star_compat q p u hu U W τ hτ a

  let c₀ : (cechH (Fk p W a) (Vk p W a) a).X j := fun i => (t p W a j i).symm (c i)
  have hc₀ : (φ p W a).f j c₀ = c := funext fun i => (t p W a j i).apply_symm_apply (c i)
  have h0' : (cechH (Fk p W a) (Vk p W a) a).cx.d j c₀ = 0 := by
    refine (tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ p W a).comm, hc₀, h0]

  let c₁ : (cechH (Fk q U a) (Vk q U a) a).X j := fun i =>
    (morU (morU (pullM u hu a) (U := KC p W a) (U' := KC q U a) hG) (U := capT (Vk p W a) (τ ∘ i))
      (U' := capT (Vk q U a) i) fun T hT k => hτ' (i k) T (hT k)).pull a (c₀ (τ ∘ i))
  have hc₁ : (φ q U a).f j c₁ = fun i => formRes q (hτ j i) a (formPull hu (capO W.U (τ ∘ i)) a (c (τ ∘ i))) := by
    funext i
    refine (htp q p u hu U W τ hτ a hG j i (fun T hT k => hτ' (i k) T (hT k)) (c₀ (τ ∘ i))).trans ?_
    exact congrArg _ (congrArg _ ((t p W a j (τ ∘ i)).apply_symm_apply (c (τ ∘ i))))
  have h1' : (cechH (Fk q U a) (Vk q U a) a).cx.d j c₁ = 0 := by
    refine (tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) (j + 1)).1 ?_
    rw [map_zero, ← (φ q U a).comm, hc₁, h1]
  have key := he1 q p u hu U W τ a hG hτ' j c₀ h0' h1'
  have eY : (LinearEquiv.ofBijective ((φ p W a).mapH j) (P.mapH_bij (φ p W a) (fun n => tH_bij p W a (t p W a) (fun m n i θ x => htr p W a m n i θ x) n) j)).symm
      ((formCos p W.U a).cx.cls c h0) = (cechH (Fk p W a) (Vk p W a) a).cx.cls c₀ h0' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ p W a) j c₀ h0' (by rw [hc₀]; exact h0)]
    exact cls_congr0 _ j _ _ _ _ hc₀.symm
  have eX : (LinearEquiv.ofBijective ((φ q U a).mapH j) (P.mapH_bij (φ q U a) (fun n => tH_bij q U a (t q U a) (fun m n i θ x => htr q U a m n i θ x) n) j)).symm
      ((formCos q U.U a).cx.cls _ h1) = (cechH (Fk q U a) (Vk q U a) a).cx.cls c₁ h1' := by
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, P.mapH_cls (φ q U a) j c₁ h1' (by rw [hc₁]; exact h1)]
    exact cls_congr0 _ j _ _ _ _ hc₁.symm
  rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_trans_apply, eY, eX]
  exact key

end CrystallineSemistableComparison.Om.GlobPf2
