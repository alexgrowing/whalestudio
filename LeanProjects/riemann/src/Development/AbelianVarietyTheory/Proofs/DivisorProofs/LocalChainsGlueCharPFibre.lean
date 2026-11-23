import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveMapsGlueAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc.SheafPsi

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} [Fact p.Prime] {B : GlobalTheory.Vert.Model O}
  {Λ : Type} [CommRing Λ] {h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)}
  {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {E : ℕ → B.X.Modules} {ι : ∀ n, E n ⟶ freeModule B.X (Fin h)}
  {n : ℕ} {Q Q' : AM B Λ} {t : E n ⟶ Q.V} {t' : E (n + 1) ⟶ Q'.V}

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

theorem exists_psi [Mono (ι n)] [Mono (ι (n + 1))] (hn : n < o) (k : IsQuot M (ι n) (baseOn h π) Q t)
    (k' : IsQuot M (ι (n + 1)) (baseOn h π) Q' t') {W : B.X.Opens} (hW : IsAffineOpen W)
    (D : ChainOn p h o Lie Om π γ W) (hD : Fits ι D) :
    ∃ ψ : Γ(Q'.V, W) →+ Γ(Q.V, W), IsFrobLin Γ(B.X, W) p (p ^ (0 + 1)) ψ ∧
      ∀ (s' : Γ(E (n + 1), W)) (s : Γ(E n, W)) (x' : D.L (n + 1)) (x : D.L n), x'.1 = crd (ι (n + 1)) W s' →
        x.1 = crd (ι n) W s → D.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk x →
          ψ (t'.app W s') = t.app W s := by
  obtain ⟨e, he⟩ := k.exists_equiv hW (hD n hn.le) rfl
  obtain ⟨e', he'⟩ := k'.exists_equiv hW (hD (n + 1) hn) rfl
  refine ⟨e.toLinearMap.toAddMonoidHom.comp ((D.ψ n).comp e'.symm.toLinearMap.toAddMonoidHom), ?_, ?_⟩
  · rw [zero_add, pow_one]
    have a := (GlobalTheory.RingChain.FrobLin.main Γ(B.X, W) p Γ(Q'.V, W) (Qt (D.L (n + 1)) (baseOn h π W))
      (Qt (D.L n) (baseOn h π W))).2.2.2.1 p e'.symm (D.ψ n) (D.ψ_lin n hn)
    exact (GlobalTheory.RingChain.FrobLin.main Γ(B.X, W) p Γ(Q'.V, W) (Qt (D.L n) (baseOn h π W)) Γ(Q.V, W)).2.2.2.2 p _ e a
  · intro s' s x' x hx' hx hψ
    change e (D.ψ n (e'.symm (t'.app W s'))) = _
    rw [← he' s' x' hx', LinearEquiv.symm_apply_apply, hψ, he s x hx]

theorem exists_rep (hn : n < o) (k' : IsQuot M (ι (n + 1)) (baseOn h π) Q' t') {W : B.X.Opens} (hW : IsAffineOpen W)
    (D : ChainOn p h o Lie Om π γ W) (hD : Fits ι D) (u : Γ(Q'.V, W)) :
    ∃ (s' : Γ(E (n + 1), W)) (s : Γ(E n, W)) (x' : D.L (n + 1)) (x : D.L n), x'.1 = crd (ι (n + 1)) W s' ∧
      x.1 = crd (ι n) W s ∧ D.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk x ∧ t'.app W s' = u := by
  obtain ⟨s', rfl⟩ := (k'.2 W hW).1 u
  let x' : D.L (n + 1) := ⟨crd (ι (n + 1)) W s', by rw [hD (n + 1) hn]; exact ⟨s', rfl⟩⟩
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (D.ψ n (Submodule.Quotient.mk x'))
  obtain ⟨s, hs⟩ : x.1 ∈ latOf (ι n) W := hD n hn.le ▸ x.2
  exact ⟨s', s, x', x, rfl, hs.symm, hx.symm, rfl⟩

theorem psi_res (hn : n < o) (k' : IsQuot M (ι (n + 1)) (baseOn h π) Q' t') {W W' : B.X.Opens} (hW : IsAffineOpen W)
    (hle : W' ≤ W) (D : ChainOn p h o Lie Om π γ W) (hD : Fits ι D) (D' : ChainOn p h o Lie Om π γ W')
    (hr : ResMap hle D D') (ψ : Γ(Q'.V, W) →+ Γ(Q.V, W)) (χ : Γ(Q'.V, W') →+ Γ(Q.V, W'))
    (hψ : ∀ (s' : Γ(E (n + 1), W)) (s : Γ(E n, W)) (x' : D.L (n + 1)) (x : D.L n), x'.1 = crd (ι (n + 1)) W s' →
      x.1 = crd (ι n) W s → D.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk x → ψ (t'.app W s') = t.app W s)
    (hχ : ∀ (s' : Γ(E (n + 1), W')) (s : Γ(E n, W')) (x' : D'.L (n + 1)) (x : D'.L n), x'.1 = crd (ι (n + 1)) W' s' →
      x.1 = crd (ι n) W' s → D'.ψ n (Submodule.Quotient.mk x') = Submodule.Quotient.mk x → χ (t'.app W' s') = t.app W' s)
    (u : Γ(Q'.V, W)) : χ (resM Q'.V hle u) = resM Q.V hle (ψ u) := by
  obtain ⟨s', s, x', x, hx', hx, e, rfl⟩ := exists_rep hn k' hW D hD u
  rw [hψ s' s x' x hx' hx e, ← GlobalTheory.Twist.app_resM, ← GlobalTheory.Twist.app_resM]
  refine hχ _ _ ⟨_, hr.mem _ _ x'.2⟩ ⟨_, hr.mem _ _ x.2⟩ ?_ ?_ (hr.ψ n hn x' _ x _ rfl rfl e)
  · rw [crd_resM, ← hx']; exact mv_one _ _
  · rw [crd_resM, ← hx]; exact mv_one _ _

end SlopeTestRemainingChoices

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)) (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0), IsLoc M ι V D → ∀ n < o, ∀ (Q Q' : AM B Λ) (t : E n ⟶ Q.V) (t' : E (n + 1) ⟶ Q'.V), IsQuot M (ι n) (baseOn h π) Q t → IsQuot M (ι (n + 1)) (baseOn h π) Q' t' → Nonempty (Q ≅ frobA p hp Q') := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D hp hL n hn Q Q' t t' k k'
  obtain ⟨hV, hc, hVV, hE, hF, hO, hA⟩ := hL
  haveI := (hE n).2
  haveI := (hE (n + 1)).2
  haveI := k.1
  haveI := k'.1
  choose ψ hψ1 hψ2 using fun i => exists_psi hn k k' (hV i) (D i) (hF i)
  obtain ⟨e⟩ := GlobalTheory.T.additive_maps_glue_affine_cover O p B Λ hp Q' Q I V 0 ψ hV hc hVV hψ1 (fun i i' => by
      obtain ⟨D', hD', r1, r2⟩ := hO i i'
      obtain ⟨χ, hχ1, hχ2⟩ := exists_psi hn k k' (hVV i i') D' hD'
      exact ⟨χ, hχ1, psi_res hn k' (hV i) _ (D i) (hF i) D' r1 _ _ (hψ2 i) hχ2,
        psi_res hn k' (hV i') _ (D i') (hF i') D' r2 _ _ (hψ2 i') hχ2⟩) (fun i a u => by
      obtain ⟨s', s, x', x, hx', hx, e, rfl⟩ := exists_rep hn k' (hV i) (D i) (hF i) u
      have m' := (hA i a).mem _ _ x'.2
      have m := (hA i a).mem _ _ x.2
      obtain ⟨z', hz'⟩ : mv (RingHom.id _) (M a) x'.1 ∈ latOf (ι (n + 1)) (V i) := hF i (n + 1) hn ▸ m'
      obtain ⟨z, hz⟩ : mv (RingHom.id _) (M a) x.1 ∈ latOf (ι n) (V i) := hF i n hn.le ▸ m
      rw [hψ2 i s' s x' x hx' hx e, (k'.2 _ (hV i)).2.2 a s' z' (by rw [hz', hx']),
        (k.2 _ (hV i)).2.2 a s z (by rw [hz, hx])]
      exact hψ2 i z' z ⟨_, m'⟩ ⟨_, m⟩ hz'.symm hz.symm ((hA i a).ψ n hn x' _ x _ rfl rfl e))
  exact ⟨e.symm⟩

end GlobalTheory.ChainDesc.SheafPsi

end
