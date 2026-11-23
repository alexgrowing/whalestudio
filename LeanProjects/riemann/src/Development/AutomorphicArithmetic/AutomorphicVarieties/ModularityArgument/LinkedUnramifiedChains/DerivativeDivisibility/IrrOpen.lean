import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrIffSpan

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N

namespace UpperTheory.V.J

section Abstract

private theorem tr_comap' {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).tr (MonoidAlgebra.single g 1) = D.tr (MonoidAlgebra.single (φ g) 1) := by
  have hc : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1))) = _
    congr 1
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.tr, GDet.lam, hc]

private theorem tr_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : H) :
    f (D.tr (MonoidAlgebra.single (φ g) 1)) = (ρ g).trace := by
  have h1 : f (D.tr (MonoidAlgebra.single (φ g) 1)) = (D.map f).tr (MonoidAlgebra.single (φ g) 1) := by
    have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single (φ g) 1)).2 1
    simpa [GDet.tr, MonoidAlgebra.mapRingHom_apply] using this.symm
  rw [h1, ← tr_comap', h, ← (UpperTheory.V.CA.d_toDet _ _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
    (UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
  congr 1

private theorem gram_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
    f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
      Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [tr_at hn D f φ ρ h, map_mul]

private theorem isIrr_iff_span {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (r : Γ →* GL (Fin n) k) : IsIrr r ↔ Submodule.span k (Set.range (mat r)) = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
  constructor
  · intro h N hN
    obtain ⟨-, -, h3⟩ := h
    exact h3 N le_top fun g v hv => hN g v hv
  · intro h
    refine ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun W _ hW => h W fun g v hv => hW g v hv⟩

end Abstract

end UpperTheory.V.J

end
