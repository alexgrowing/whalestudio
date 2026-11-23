import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmaDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem gdet_eq_ofRep {n : ℕ} {A G E S : Type} [CommRing A] [Group G] [Ring E] [Algebra A E] [CommRing S]
    [Algebra A S] (D : GDet n A G) (DE : Det n A E) (ι : MonoidAlgebra A G →ₐ[A] E) (hp : DE.pull ι = D.toDet)
    (hch : DE.IsCH) (ep : Fin n → E) (he : CompleteOrthogonalIdempotents ep)
    (h1 : ∀ i, DE.D A[X] (1 + X ⊗ₜ ep i) = 1 + X) (φ : E →ₐ[A] Matrix (Fin n) (Fin n) S)
    (hφ : ∀ i, φ (ep i) = single i i 1) (vr : G →* Matrix (Fin n) (Fin n) S)
    (hvr : ∀ γ, vr γ = φ (ι (MonoidAlgebra.single γ 1))) :
    D.map (algebraMap A S) = GDet.ofRep vr := by
  refine GDet.ext fun T _ _ y => ?_
  letI : Algebra A T := ((algebraMap S T).comp (algebraMap A S)).toAlgebra
  haveI : IsScalarTower A S T := .of_algebraMap_eq fun _ => rfl
  let ψ : T ⊗[A] E →ₐ[T] Matrix (Fin n) (Fin n) T :=
    Algebra.TensorProduct.lift (Algebra.ofId T _) ((IsScalarTower.toAlgHom A S T).mapMatrix.comp φ)
      fun s _ => Algebra.commute_algebraMap_left s _
  have hψ : ∀ (t : T) (z : E), ψ (t ⊗ₜ z) = t • (φ z).map (algebraMap S T) := fun t z =>
    (Algebra.TensorProduct.lift_tmul _ _ _ t z).trans (Algebra.smul_def _ _).symm
  have hD : ∀ w : T ⊗[A] E, DE.D T w = (ψ w).det := by
    intro w
    obtain ⟨k, t, z, rfl⟩ := TensorProduct.exists_sum_tmul_eq w
    rw [d_gma_det DE ep hch he h1 S φ hφ T t z, map_sum]
    simp only [hψ]
  have h2 : D.D T y = DE.D T (Algebra.TensorProduct.map (AlgHom.id T T) ι (toT A G T y)) := by
    have h3 : D.D T y = D.toDet.D T (toT A G T y) := (congrArg (D.D T) (ofT_toT (A := A) y)).symm
    rw [h3, ← hp]
    rfl
  change D.D T y = (GDet.repAlg vr T y).det
  rw [h2, hD]
  clear h2
  congr 1
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g s =>
    rw [toT_single, Algebra.TensorProduct.map_tmul, hψ, ← hvr]
    simp [GDet.repAlg]

theorem UpperTheory.V.Pa.gr_det :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] {e : G.G₀ →* Bˣ} (H : Hat h x D I Bh e) {ep : Fin n → H.E} (g : GrAlg H.T n x.a H.r ep), CompleteOrthogonalIdempotents ep → (∀ i, H.DE.D Bh[X] (1 + X ⊗ₜ ep i) = 1 + X) → ∀ vr : G.G₀ →* Matrix (Fin n) (Fin n) g.AA, (∀ γ, vr γ = g.φ (H.ι (MonoidAlgebra.single γ 1))) → D.map ((algebraMap Bh g.AA).comp (algebraMap B Bh)) = GDet.ofRep vr := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ _ e H ep g he h1 vr hvr
  rw [← (d_gmap D).2.1]
  exact gdet_eq_ofRep _ H.DE H.ι H.pull H.ch ep he h1 g.φ g.φ_ep vr hvr
