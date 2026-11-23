import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

private theorem rs_rs' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (z : ↑(X.presheaf.obj (Opposite.op U))) : rs X h₂ (rs X h₁ z) = rs X (h₂.trans h₁) z := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem congr_secMulOn {X X' : Scheme.{0}} {π : X ⟶ X'} {N : LB X} {N' : LB X'}
    (v : LB.Iso N (N'.pull π)) (hN : N.IsLB) (hN' : N'.IsLB) (hv : v.IsGen) {a b c : ℤ}
    (h : a + b = c) {V : X.Opens} {V' : X'.Opens} (e : V ≤ π ⁻¹ᵁ V')
    (x : SecOn (pw N' a) V') (y : SecOn (pw N' b) V') (s : SecOn (pw N a) V)
    (t : SecOn (pw N b) V)
    (hs : SecOn.congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) V s = SecOn.pullLE (pw N' a) π V' V e x)
    (ht : SecOn.congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) V t = SecOn.pullLE (pw N' b) π V' V e y) :
    SecOn.congr (isLB_pw hN c) (LB.isLB_pull (isLB_pw hN' c) π) (pullPow v c)
      (pullPow_isGen v c hv) V (secMulOn h s t) =
      SecOn.pullLE (pw N' c) π V' V e (secMulOn h x y) := by
  subst h
  classical
  have hMc : ((pw N' (a + b)).pull π).IsLB := LB.isLB_pull (isLB_pw hN' (a + b)) π
  have key : ∀ (p : ((pw N' (a + b)).pull π).ι) (q : N.ι) {O : X.Opens}
      (hp : O ≤ V ⊓ ((pw N' (a + b)).pull π).U p)
      (hq : O ≤ V ⊓ (pw N (a + b)).U q) (hpq : O ≤ ((pw N' (a + b)).pull π).U p ⊓ (pw N (a + b)).U q),
      rs X hp (GlobalTheory.LB.coord (SecOn.congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π)
        (pullPow v (a + b)) (pullPow_isGen v (a + b) hv) V (secMulOn rfl s t)) p) =
      rs X hp (GlobalTheory.LB.coord (SecOn.pullLE (pw N' (a + b)) π V' V e (secMulOn rfl x y)) p) := by
    intro p q O hp hq hpq
    have ha := SecOn.coord_congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) s p q hp hq hpq
    have hb := SecOn.coord_congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) t p q hp hq hpq
    rw [hs, SecOn.coord_pullLE π e x p] at ha
    rw [ht, SecOn.coord_pullLE π e y p] at hb
    rw [SecOn.coord_congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π) (pullPow v (a + b))
      (pullPow_isGen v (a + b) hv) _ p q hp hq hpq, SecOn.coord_pullLE π e (secMulOn rfl x y) p,
      coord_secMulOn, coord_secMulOn rfl x y (p PUnit.unit)]
    erw [map_mul, map_mul, map_mul, ha, hb]
    dsimp only [pullPow]
    erw [zpow_add, Units.val_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hcov : V ≤ ⨆ a' : ((pw N' (a + b)).pull π).ι × N.ι, V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2 := by
    intro z hz
    have h1 : z ∈ (⨆ i, ((pw N' (a + b)).pull π).U i) := by rw [hMc.cover]; trivial
    have h2 : z ∈ (⨆ i, N.U i) := by rw [hN.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h1 h2 ⊢
    obtain ⟨p, hp⟩ := h1
    obtain ⟨q, hq⟩ := h2
    exact ⟨(p, q), ⟨⟨hz, hp⟩, hq⟩⟩
  refine SecOn.ext_of_cover
    (fun a' : ((pw N' (a + b)).pull π).ι × N.ι => V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2)
    (fun a' => inf_le_left.trans inf_le_left) hcov ?_
  intro a'
  apply (SecOn.chart hMc a'.1 (inf_le_left.trans inf_le_right)).injective
  rw [SecOn.chart_apply, SecOn.chart_apply, SecOn.coord_restrict, SecOn.coord_restrict, rs_rs', rs_rs']
  exact key a'.1 a'.2 _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)

private theorem secOnR_linEquiv_symm_of {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {L M : LB X} {V : X.Opens} (φ : SecOn L V ≃ₗ[↑(X.presheaf.obj (Opposite.op V))] SecOn M V) (m : SecOn M V) :
    (SecOnR.linEquiv f φ).symm (SecOnR.of f M V m) = SecOnR.of f L V (φ.symm m) := by
  rw [LinearEquiv.symm_apply_eq, SecOnR.linEquiv_of, LinearEquiv.apply_symm_apply]

theorem red_secMulOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  intro R _ I Y β hβ N v hN ι D hDβ a b c h e S x y
  simp only [red, redL, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, SecOnR.pull_of,
    secOnR_linEquiv_symm_of, LinearEquiv.symm_apply_apply]
  refine congrArg (SecOnR.of _ _ _) ?_
  rw [LinearEquiv.symm_apply_eq]
  exact (congr_secMulOn (v e) (hN e).1 (hN (e + 1)).1 (hN e).2 h (hDβ e S) x y _ _
    (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
