import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveMapsGlueAffineCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrob

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
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

noncomputable section

namespace GlobalTheory.ChainDesc.Kap

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : GlobalTheory.Vert.Model O} {Λ : Type} [CommRing Λ]

theorem qcoh_cok (p : ℕ) (Lie : AM B Λ) [Lie.V.IsQuasicoherent] :
    (cokernel (smulA Lie (p : Γ(B.X, ⊤)))).V.IsQuasicoherent :=
  isQuasicoherent_of_iso (Examples₂.cokV (smulA Lie (p : Γ(B.X, ⊤)))).symm

theorem exists_cok (p : ℕ) (Lie : AM B Λ) [Lie.V.IsQuasicoherent] {W : B.X.Opens} (hW : IsAffineOpen W) :
    ∃ c : (Γ(Lie.V, W) ⧸ (p : Γ(B.X, W)) • (⊤ : Submodule Γ(B.X, W) Γ(Lie.V, W))) ≃ₗ[Γ(B.X, W)]
      Γ((cokernel (smulA Lie (p : Γ(B.X, ⊤)))).V, W),
      ∀ y, c (Submodule.Quotient.mk y) = (cokernel.π (smulA Lie (p : Γ(B.X, ⊤)))).hom.app W y := by
  let f := smulA Lie (p : Γ(B.X, ⊤))
  haveI : Epi (cokernel.π f).hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π f)))
  have hS : (ShortComplex.mk f.hom (cokernel.π f).hom (congrArg Action.Hom.hom (cokernel.condition f))).Exact :=
    (ShortComplex.exact_cokernel f).map (Action.forget B.X.Modules Λ)
  obtain ⟨h1, h2⟩ := exact_and_surjective_app_of_exact_of_epi hS hW
  have hf : ∀ y : Γ(Lie.V, W), f.hom.app W y = (p : Γ(B.X, W)) • y := fun y => by
    change (B.X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (p : Γ(B.X, ⊤)) • y = _
    rw [map_natCast]
  have hk : (p : Γ(B.X, W)) • (⊤ : Submodule Γ(B.X, W) Γ(Lie.V, W)) =
      LinearMap.ker (appLinear (cokernel.π f).hom W) := by
    ext y
    rw [Submodule.mem_smul_pointwise_iff_exists, LinearMap.mem_ker]
    refine Iff.trans ?_ (h1 y).symm
    exact ⟨fun ⟨z, _, e⟩ => ⟨z, (hf z).trans e⟩, fun ⟨z, e⟩ => ⟨z, trivial, (hf z).symm.trans e⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hk).trans (LinearMap.quotKerEquivOfSurjective _ h2), fun _ => rfl⟩

variable {p h o : ℕ} [Fact p.Prime] {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)}
  {M : Λ →+* Matrix (Fin h) (Fin h) ℤ} {E : ℕ → B.X.Modules} {ι : ∀ n, E n ⟶ freeModule B.X (Fin h)}

theorem exists_map [Lie.V.IsQuasicoherent] {n : ℕ} (hn : n < o) [Mono (ι n)] {Q : AM B Λ} {t : E n ⟶ Q.V}
    (k : IsQuot M (ι n) (latOf (ι (n + 1))) Q t) {W : B.X.Opens} (hW : IsAffineOpen W)
    (D : ChainOn p h o Lie Om π γ W) (hD : Fits ι D) :
    ∃ ψ : Γ(Q.V, W) →+ Γ((cokernel (smulA Lie (p : Γ(B.X, ⊤)))).V, W), IsFrobLin Γ(B.X, W) p (p ^ (n + 1)) ψ ∧
      ∀ (s : Γ(E n, W)) (x : D.L n) (y : Γ(Lie.V, W)), x.1 = crd (ι n) W s →
        D.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
          ψ (t.app W s) = (cokernel.π (smulA Lie (p : Γ(B.X, ⊤)))).hom.app W y := by
  obtain ⟨c, hc⟩ := exists_cok p Lie hW
  obtain ⟨e, he⟩ := k.exists_equiv hW (hD n hn.le) (hD (n + 1) hn)
  refine ⟨c.toLinearMap.toAddMonoidHom.comp ((D.κ n).comp e.symm.toLinearMap.toAddMonoidHom), ?_, fun s x y hx hy => ?_⟩
  · exact (GlobalTheory.RingChain.FrobLin.main _ p _ _ _).2.2.2.2 _ _ c
      ((GlobalTheory.RingChain.FrobLin.main _ p _ _ _).2.2.2.1 _ e.symm _ (D.κ_lin n hn))
  · change c (D.κ n (e.symm (t.app W s))) = _
    rw [← he s x hx, e.symm_apply_apply, hy, hc]

theorem exists_rep {n : ℕ} (hn : n < o) {Q : AM B Λ} {t : E n ⟶ Q.V}
    (k : IsQuot M (ι n) (latOf (ι (n + 1))) Q t) {W : B.X.Opens} (hW : IsAffineOpen W)
    (D : ChainOn p h o Lie Om π γ W) (hD : Fits ι D) (z : Γ(Q.V, W)) :
    ∃ (s : Γ(E n, W)) (x : D.L n) (y : Γ(Lie.V, W)), z = t.app W s ∧ x.1 = crd (ι n) W s ∧
      D.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  obtain ⟨s, rfl⟩ := (k.2 W hW).1 z
  have hx : crd (ι n) W s ∈ D.L n := by rw [hD n hn.le]; exact ⟨s, rfl⟩
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (D.κ n (Submodule.Quotient.mk ⟨_, hx⟩))
  exact ⟨s, ⟨_, hx⟩, y, rfl, rfl, hy.symm⟩

theorem map_res {n : ℕ} (hn : n < o) {Q : AM B Λ} {t : E n ⟶ Q.V}
    (k : IsQuot M (ι n) (latOf (ι (n + 1))) Q t) {W W' : B.X.Opens} (hW : IsAffineOpen W) (hle : W' ≤ W)
    {D : ChainOn p h o Lie Om π γ W} (hD : Fits ι D) {D' : ChainOn p h o Lie Om π γ W'} (r : ResMap hle D D')
    {G : B.X.Modules} {q : Lie.V ⟶ G} {ψ : Γ(Q.V, W) →+ Γ(G, W)} {χ : Γ(Q.V, W') →+ Γ(G, W')}
    (hψ : ∀ (s : Γ(E n, W)) (x : D.L n) (y : Γ(Lie.V, W)), x.1 = crd (ι n) W s →
      D.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → ψ (t.app W s) = q.app W y)
    (hχ : ∀ (s : Γ(E n, W')) (x : D'.L n) (y : Γ(Lie.V, W')), x.1 = crd (ι n) W' s →
      D'.κ n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y → χ (t.app W' s) = q.app W' y)
    (z : Γ(Q.V, W)) : χ (resM Q.V hle z) = resM G hle (ψ z) := by
  obtain ⟨s, x, y, rfl, hx, hy⟩ := exists_rep hn k hW D hD z
  have e : mv (resG B.X hle) 1 x.1 = crd (ι n) W' (resM (E n) hle s) := by
    rw [crd_resM, mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec, hx]; rfl
  rw [hψ s x y hx hy, ← GlobalTheory.Twist.app_resM, ← GlobalTheory.Twist.app_resM]
  exact hχ _ ⟨_, r.mem n x.1 x.2⟩ _ e (r.κ n hn x _ y rfl hy)

end GlobalTheory.ChainDesc.Kap

open GlobalTheory.ChainDesc.Kap in

theorem GlobalTheory.ChainDesc.Kap.main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)) (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0), Lie.V.IsQuasicoherent → IsLoc M ι V D → ∀ n < o, ∀ (Q : AM B Λ) (t : E n ⟶ Q.V), IsQuot M (ι n) (latOf (ι (n + 1))) Q t → Nonempty ((frobA p hp)^[n + 1] Q ≅ cokernel (smulA Lie (p : Γ(B.X, ⊤)))) := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D hp hq hL n hn Q t k
  obtain ⟨ha, hc, ha2, hv, hF, ho, hact⟩ := hL
  haveI := (hv n).2
  haveI := k.1
  haveI := qcoh_cok p Lie
  choose ψ hψ hψ' using fun i => exists_map hn k (ha i) (D i) (hF i)
  refine GlobalTheory.T.additive_maps_glue_affine_cover O p B Λ hp Q _ I V n ψ ha hc ha2 hψ (fun i i' => ?_) fun i a z => ?_
  · obtain ⟨D', hD', r, r'⟩ := ho i i'
    obtain ⟨χ, hχ, hχ'⟩ := exists_map hn k (ha2 i i') D' hD'
    exact ⟨χ, hχ, map_res hn k (ha i) _ (hF i) r (hψ' i) hχ', map_res hn k (ha i') _ (hF i') r' (hψ' i') hχ'⟩
  · obtain ⟨s, x, y, rfl, hx, hy⟩ := exists_rep hn k (ha i) (D i) (hF i) z
    have hm := (hact i a).mem n x.1 x.2
    obtain ⟨s', hs'⟩ : mv (RingHom.id _) (M a) x.1 ∈ latOf (ι n) (V i) := hF i n hn.le ▸ hm
    rw [(k.2 _ (ha i)).2.2 a s s' (by rw [hs', hx]), hψ' i s x y hx hy,
      hψ' i s' ⟨_, hm⟩ _ hs'.symm ((hact i a).κ n hn x _ y rfl hy), app_app, app_app]
    exact congrArg (fun u => Scheme.Modules.Hom.app u (V i) y) ((cokernel.π (smulA Lie (p : Γ(B.X, ⊤)))).comm a)

end
