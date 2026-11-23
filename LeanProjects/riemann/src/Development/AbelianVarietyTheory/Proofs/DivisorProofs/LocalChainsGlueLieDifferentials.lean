import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBasis

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

namespace GlobalTheory.ChainDesc.SheafRho

theorem mv_one {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') {h : ℕ} (x : Fin h → A) :
    mv φ 1 x = piMap φ (Fin h) x := by
  rw [mv, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.one_mulVec]; rfl

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  {p h o : ℕ} {Lie Om : AM B Λ} {π : Γ(B.X, ⊤)} {γ : ℕ → Γ(B.X, ⊤)} {M : Λ →+* Matrix (Fin h) (Fin h) ℤ}
  {E : B.X.Modules} {ι : E ⟶ freeModule B.X (Fin h)} {Q : AM B Λ} {t : E ⟶ Q.V}

theorem exists_rep {W : B.X.Opens} (D : ChainOn p h o Lie Om π γ W) (hD : D.L 0 = latOf ι W) (s : Γ(Om.V, W)) :
    ∃ (x : Γ(E, W)) (y : D.L 0), y.1 = crd ι W x ∧ D.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y) := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (D.ρ s)
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, hx⟩ := hD.le y.2
  exact ⟨x, y, hx.symm, hz.symm⟩

theorem isQuasicoherent_cok [Lie.V.IsQuasicoherent] [Q.V.IsQuasicoherent] (j : Lie ⟶ Q) :
    (cokernel j).V.IsQuasicoherent :=
  isQuasicoherent_of_iso (Examples₂.cokV j).symm

theorem exists_local [Mono ι] [Lie.V.IsQuasicoherent] (k : IsQuot M ι (baseOn h π) Q t) (j : Lie ⟶ Q) {W : B.X.Opens}
    (hW : IsAffineOpen W) (D : ChainOn p h o Lie Om π γ W) (hD : D.L 0 = latOf ι W) (hj : JOn ι D t j.hom) :
    ∃ r : Γ(Om.V, W) →ₗ[Γ(B.X, W)] Γ((cokernel j).V, W), Function.Surjective r ∧
      ∀ (s : Γ(Om.V, W)) (x : Γ(E, W)) (y : D.L 0), y.1 = crd ι W x →
        D.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y) → r s = (cokernel.π j).hom.app W (t.app W x) := by
  haveI := k.1
  haveI := isQuasicoherent_cok j
  haveI : Epi (cokernel.π j).hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π j)))
  obtain ⟨e, he⟩ := k.exists_equiv hW hD rfl
  let u := appLinear (cokernel.π j).hom W ∘ₗ e.toLinearMap
  have hu : LinearMap.range D.j ≤ LinearMap.ker u := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (D.j s)
    obtain ⟨x, hx⟩ := hD.le y.2
    change (cokernel.π j).hom.app W (e (D.j s)) = 0
    rw [← hy, he x y hx.symm, ← hj s x y hx.symm hy.symm]
    change (j ≫ cokernel.π j).hom.app W s = 0
    rw [cokernel.condition]
    rfl
  refine ⟨(LinearMap.range D.j).liftQ u hu ∘ₗ D.ρ, fun z => ?_, fun s x y hy hs => ?_⟩
  · obtain ⟨z, rfl⟩ := surjective_app_of_epi (cokernel.π j).hom hW z
    obtain ⟨z, rfl⟩ := e.surjective z
    obtain ⟨s, hs⟩ := D.ρ_surj (Submodule.Quotient.mk z)
    exact ⟨s, (congrArg ((LinearMap.range D.j).liftQ u hu) hs).trans (Submodule.liftQ_apply _ u z)⟩
  · exact ((congrArg ((LinearMap.range D.j).liftQ u hu) hs).trans (Submodule.liftQ_apply _ u _)).trans
      (congrArg ((cokernel.π j).hom.app W) (he x y hy))

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (M : Λ →+* Matrix (Fin h) (Fin h) ℤ) (E : ℕ → B.X.Modules) (ι : ∀ n, E n ⟶ freeModule B.X (Fin h)) (I : Type) (V : I → B.X.Opens) (D : ∀ i, ChainOn p h o Lie Om π γ (V i)), Lie.V.IsQuasicoherent → Om.V.IsQuasicoherent → IsLoc M ι V D → ∀ (Q : AM B Λ) (t : E 0 ⟶ Q.V), IsQuot M (ι 0) (baseOn h π) Q t → ∀ j : Lie ⟶ Q, (∀ i, JOn (ι 0) (D i) t j.hom) → (∀ (i : I) (W : B.X.Opens) (hle : W ≤ V i) (D' : ChainOn p h o Lie Om π γ W), IsAffineOpen W → Fits ι D' → ResMap hle (D i) D' → JOn (ι 0) D' t j.hom) → ∃ ρ : Om ⟶ cokernel j, Epi ρ ∧ ∀ i, ROn (ι 0) (D i) (t ≫ (cokernel.π j).hom) ρ.hom := by
  intro O _ _ _ p _ B Λ _ h o Lie Om π γ M E ι I V D _ _ ⟨hV, hc, hVV, hι, hF, hR, hA⟩ Q t k j hj hj'
  haveI := (hι 0).2
  haveI := k.1
  haveI := isQuasicoherent_cok j
  have hcov : iSup V = ⊤ := eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 (hc x)
  obtain ⟨g1, g2, g3, -⟩ := GlobalTheory.CoverHom.hom_on_affineCover B.X Om.V (cokernel j).V I V hV hcov
  choose r hr hr' using fun i => exists_local k j (hV i) (D i) (hF i 0 o.zero_le) (hj i)
  have key : ∀ (i : I) (W : B.X.Opens) (hle : W ≤ V i) (D' : ChainOn p h o Lie Om π γ W), Fits ι D' →
      ResMap hle (D i) D' → ∀ ψ : Γ(Om.V, W) →ₗ[Γ(B.X, W)] Γ((cokernel j).V, W),
      (∀ (s : Γ(Om.V, W)) (x : Γ(E 0, W)) (y : D'.L 0), y.1 = crd (ι 0) W x →
        D'.ρ s = Submodule.Quotient.mk (Submodule.Quotient.mk y) → ψ s = (cokernel.π j).hom.app W (t.app W x)) →
      ∀ s, ψ (resM Om.V hle s) = resM (cokernel j).V hle (r i s) := by
    intro i W hle D' hF' hR' ψ hψ s
    obtain ⟨x, y, hy, hs⟩ := exists_rep (D i) (hF i 0 o.zero_le) s
    have e : crd (ι 0) W (resM _ hle x) = mv (resG B.X hle) 1 y.1 := by rw [mv_one, hy, crd_resM]
    rw [hr' i s x y hy hs, hψ _ (resM _ hle x) ⟨_, hR'.mem 0 _ y.2⟩ e.symm (hR'.ρ s y _ rfl hs),
      GlobalTheory.Twist.app_resM, GlobalTheory.Twist.app_resM]
  obtain ⟨u, hu⟩ := g1 hVV r fun i l => by
    obtain ⟨D', hF', h1, h2⟩ := hR i l
    obtain ⟨ψ, -, hψ⟩ := exists_local k j (hVV i l) D' (hF' 0 o.zero_le) (hj' i _ _ D' (hVV i l) hF' h1)
    exact ⟨ψ, key i _ _ D' hF' h1 ψ hψ, key l _ _ D' hF' h2 ψ hψ⟩
  have hcomm : ∀ a : Λ, (Om.ρ a : Om.V ⟶ Om.V) ≫ u = u ≫ ((cokernel j).ρ a : (cokernel j).V ⟶ (cokernel j).V) := by
    intro a
    refine g2 _ _ fun i s => ?_
    obtain ⟨x, y, hy, hs⟩ := exists_rep (D i) (hF i 0 o.zero_le) s
    obtain ⟨x', hx'⟩ := (hF i 0 o.zero_le).le ((hA i a).mem 0 _ y.2)
    have hπ : (Q.ρ a : Q.V ⟶ Q.V) ≫ (cokernel.π j).hom =
        (cokernel.π j).hom ≫ ((cokernel j).ρ a : (cokernel j).V ⟶ (cokernel j).V) := (cokernel.π j).comm a
    rw [← app_app, ← app_app, hu, hu, hr' i s x y hy hs,
      hr' i _ x' ⟨_, (hA i a).mem 0 _ y.2⟩ hx'.symm ((hA i a).ρ s y _ rfl hs),
      ← (k.2 _ (hV i)).2.2 a x x' (by rw [hx', hy]), app_app _ (cokernel.π j).hom, hπ, app_app (cokernel.π j).hom]
  refine ⟨⟨u, hcomm⟩, (Action.forget B.X.Modules Λ).epi_of_epi_map (g3 u fun i z => ?_), fun i s x y hy hs => ?_⟩
  · obtain ⟨s, rfl⟩ := hr i z
    exact ⟨s, hu i s⟩
  · exact (hu i s).trans (hr' i s x y hy hs)

end GlobalTheory.ChainDesc.SheafRho

end
