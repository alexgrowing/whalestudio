import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem characteristic_polynomial_compatibility {n : ℕ} {G B A Bh F E : Type} [Group G] [CommRing B] [CommRing A] [CommRing Bh] [CommRing F]
    [Ring E] [Algebra Bh E] [Algebra Bh F] (D : GDet n B G) (f : B →+* A) (g : B →+* Bh) (a : A →+* F)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (hD : D.map f = GDet.ofRep ρ)
    (hc : ∀ b, algebraMap Bh F (g b) = a (f b)) (ι : MonoidAlgebra Bh G →ₐ[Bh] E) (DE : Det n Bh E)
    (hp : DE.pull ι = (D.map g).toDet) (r : E →ₐ[Bh] Matrix (Fin n) (Fin n) F)
    (hr : ∀ s, r (ι (MonoidAlgebra.single s 1)) = (ρ s).map a) (z : MonoidAlgebra Bh G) :
    (DE.chi (ι z)).map (algebraMap Bh F) = (r (ι z)).charpoly := by
  have hc' : (algebraMap Bh F).comp g = a.comp f := RingHom.ext hc
  rw [← (d_pull DE ι).1 z, hp, (d_toDet _ z).1, ← ((d_gmap (D.map g)).2.2.1 (algebraMap Bh F) z).1,
    (d_gmap D).2.1, hc', ← (d_gmap D).2.1, hD, (d_gmap (GDet.ofRep ρ)).2.2.2, ← (d_toDet _ _).1,
    d_toDet_ofRep.1, (d_ofRep _ _ _).1]
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single s b =>
    have : (MonoidAlgebra.single s b : MonoidAlgebra Bh G) = b • MonoidAlgebra.single s 1 := by simp
    rw [MonoidAlgebra.mapRingHom_single]
    conv_rhs => rw [this, map_smul, map_smul, hr]
    ext i j
    simp [GDet.repAlg, Algebra.smul_def]

theorem UpperTheory.V.Pa.hat_chi :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)], (∀ b, algebraMap Bh (FractionRing x.A) (algebraMap B Bh b) = algebraMap x.A (FractionRing x.A) (P.f b)) → ∀ H : Hat h x u.D P.ker Bh (G.frame.eps O B), ∀ y, (H.DE.chi y).map (algebraMap Bh (FractionRing x.A)) = (H.r y).charpoly := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ _ hc H y
  obtain ⟨z, rfl⟩ := H.surj y
  exact characteristic_polynomial_compatibility u.D P.f.toRingHom (algebraMap B Bh) (algebraMap x.A (FractionRing x.A)) (mat (x.ρ.comp h.p₀))
    P.maps.1 hc H.ι H.DE H.pull H.r H.r_ι z
