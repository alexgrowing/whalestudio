import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBasis

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

namespace GlobalTheory.ChainDesc.SheafJ

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {p h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} {M : Λ →+* Matrix (Fin h) (Fin h) ℤ}
  {E : ℕ → B.X.Modules} {ι : ∀ n, E n ⟶ freeModule B.X (Fin h)} {Q : AM B Λ} {t : E 0 ⟶ Q.V}

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A') (x : Fin h → A) : mv g 1 x = piMap g _ x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

def IsJ (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (t : E 0 ⟶ Q.V) {W : B.X.Opens} (D : ChainOn p h o Lie Om π γ W)
    (φ : Γ(Lie.V, W) →ₗ[Γ(B.X, W)] Γ(Q.V, W)) : Prop :=
  ∀ (s : Γ(Lie.V, W)) (x : Γ(E 0, W)) (y : D.L 0), y.1 = crd (ι 0) W x → D.j s = Submodule.Quotient.mk y →
    φ s = t.app W x

theorem exists_rep {W : B.X.Opens} {D : ChainOn p h o Lie Om π γ W} (hD : Fits ι D) (s : Γ(Lie.V, W)) :
    ∃ (x : Γ(E 0, W)) (y : D.L 0), y.1 = crd (ι 0) W x ∧ D.j s = Submodule.Quotient.mk y := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (D.j s)
  obtain ⟨x, hx⟩ : y.1 ∈ latOf (ι 0) W := hD 0 (Nat.zero_le _) ▸ y.2
  exact ⟨x, y, hx.symm, hy.symm⟩

theorem exists_isJ [Mono (ι 0)] (k : IsQuot M (ι 0) (baseOn h π) Q t) {W : B.X.Opens} (hW : IsAffineOpen W)
    {D : ChainOn p h o Lie Om π γ W} (hD : Fits ι D) : ∃ φ, IsJ ι t D φ := by
  obtain ⟨e, he⟩ := k.exists_equiv hW (hD 0 (Nat.zero_le _)) rfl
  refine ⟨e.toLinearMap ∘ₗ D.j, fun s x y hy hs => ?_⟩
  change e (D.j s) = _
  rw [hs, he x y hy]

theorem IsJ.res {W W' : B.X.Opens} (hle : W' ≤ W) {D : ChainOn p h o Lie Om π γ W} {D' : ChainOn p h o Lie Om π γ W'}
    (hD : Fits ι D) (r : ResMap hle D D') {φ : Γ(Lie.V, W) →ₗ[Γ(B.X, W)] Γ(Q.V, W)}
    {φ' : Γ(Lie.V, W') →ₗ[Γ(B.X, W')] Γ(Q.V, W')} (hφ : IsJ ι t D φ) (hφ' : IsJ ι t D' φ') (s : Γ(Lie.V, W)) :
    φ' (resM Lie.V hle s) = resM Q.V hle (φ s) := by
  obtain ⟨x, y, hy, hs⟩ := exists_rep hD s
  rw [hφ s x y hy hs, ← GlobalTheory.Twist.app_resM]
  refine hφ' _ _ ⟨_, r.mem 0 _ y.2⟩ ?_ (r.j s y _ rfl hs)
  rw [crd_resM, ← hy]
  exact mv_one _ _

theorem IsJ.smul_eq_zero (k : IsQuot M (ι 0) (baseOn h π) Q t) {W : B.X.Opens} (hW : IsAffineOpen W)
    {D : ChainOn p h o Lie Om π γ W} (hD : Fits ι D) {φ : Γ(Lie.V, W) →ₗ[Γ(B.X, W)] Γ(Q.V, W)} (hφ : IsJ ι t D φ)
    (s : Γ(Lie.V, W)) : φ (resG B.X (le_top : W ≤ ⊤) π • s) = 0 := by
  obtain ⟨x, y, hy, hs⟩ := exists_rep hD s
  have e : t.app W (resG B.X (le_top : W ≤ ⊤) π • x) = 0 := ((k.2 W hW).2.1 _).2 (by
    rw [map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ trivial)
  rw [map_smul, hφ s x y hy hs, ← e]
  exact (Scheme.Modules.Hom.app_smul t _ x).symm

theorem exists_sheaf_j : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), Lie.V.IsQuasicoherent → IsLoc M ι V D → ∀ (Q : AM B Λ) (t : E 0 ⟶ Q.V), IsQuot M (ι 0) (baseOn h π) Q t → ∃ j : Lie ⟶ Q, smulA Lie π ≫ j = 0 ∧ (∀ i, JOn (ι 0) (D i) t j.hom) ∧ ∀ (i : I) (W : B.X.Opens) (hle : W ≤ V i) (D' : ChainOn p h o Lie Om π γ W), IsAffineOpen W → Fits ι D' → ResMap hle (D i) D' → JOn (ι 0) D' t j.hom := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D hq hL Q t k
  obtain ⟨hV, hc, hVV, hE, hD, hov, hact⟩ := hL
  haveI := (hE 0).2
  haveI := k.1
  have hc' : iSup V = ⊤ := top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  obtain ⟨-, hext, -⟩ := GlobalTheory.CoverHom.hom_on_affineCover B.X Lie.V Q.V I V hV hc'
  choose φ hφ using fun i => exists_isJ k (hV i) (hD i)
  obtain ⟨u, hu⟩ := GlobalTheory.CoverHom.exists_hom_of_cover V hV hc' hVV φ fun i l => by
    obtain ⟨D', h1, h2, h3⟩ := hov i l
    obtain ⟨ψ, hψ⟩ := exists_isJ k (hVV i l) h1
    exact ⟨ψ, IsJ.res _ (hD i) h2 (hφ i) hψ, IsJ.res _ (hD l) h3 (hφ l) hψ⟩
  refine ⟨⟨u, fun a => hext _ _ fun i s => ?_⟩, Action.Hom.ext (hext _ _ fun i s => ?_),
    fun i s x y hy hs => (hu i s).trans (hφ i s x y hy hs), fun i W hle D' hW hD' r s x y hy hs => ?_⟩
  · change u.app _ ((Lie.ρ a : Lie.V ⟶ Lie.V).app _ s) = (Q.ρ a : Q.V ⟶ Q.V).app _ (u.app _ s)
    obtain ⟨x, y, hy, hs⟩ := exists_rep (hD i) s
    have hm := (hact i a).mem 0 _ y.2
    obtain ⟨x', hx'⟩ : mv (RingHom.id _) (M a) y.1 ∈ latOf (ι 0) (V i) := hD i 0 (Nat.zero_le _) ▸ hm
    rw [hu, hu, hφ i s x y hy hs, (k.2 _ (hV i)).2.2 a x x' (by rw [hx', hy])]
    exact hφ i _ x' ⟨_, hm⟩ hx'.symm ((hact i a).j s y _ rfl hs)
  · exact (hu i _).trans ((hφ i).smul_eq_zero k (hV i) (hD i) s)
  · obtain ⟨ψ, hψ⟩ := exists_isJ k hW hD'
    rw [← hψ s x y hy hs]
    change appLinear u W s = ψ s
    refine GlobalTheory.CoverHom.induction_res (hV i) hW hle (fun s => appLinear u W s = ψ s) (fun s => ?_)
      (fun a s e => ?_) (fun s s' e e' => ?_) s
    · rw [IsJ.res hle (hD i) r (hφ i) hψ, ← hu]
      exact GlobalTheory.Twist.app_resM _ _ _
    · rw [map_smul, map_smul, e]
    · rw [map_add, map_add, e, e']

end GlobalTheory.ChainDesc.SheafJ

end
