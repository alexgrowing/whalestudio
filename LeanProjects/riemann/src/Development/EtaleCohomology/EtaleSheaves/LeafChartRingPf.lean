import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section

namespace LateralTheory.E.LeafChartRingPf

open MvPolynomial

def coordMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (g : B)
    (y : Fin e → B) (t : Fin d → B) : MvPolynomial (Fin d) (MvPolynomial (Fin e) A) →+* Localization.Away g :=
  MvPolynomial.eval₂Hom (MvPolynomial.aeval (fun k => algebraMap B (Localization.Away g) (y k))).toRingHom
    (fun j => algebraMap B (Localization.Away g) (t j))

def LeafCoords : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ g ∉ P, ∃ (t : Fin d → B) (y : Fin e → B),
    I.map (algebraMap B (Localization.Away g)) = Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) ∧
    LinearIndependent (Localization.Away g) (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) ∧
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤

def LeafJacobian : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ),
  Algebra.IsStandardSmoothOfRelativeDimension n A B → ∀ (g : B) (t : Fin d → B) (y : Fin e → B),
    LinearIndependent (Localization.Away g) (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j)))) →
    Submodule.span (Localization.Away g) (Set.range (Sum.elim
      (fun k => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (y k)))
      (fun j => KaehlerDifferential.D A (Localization.Away g) (algebraMap B _ (t j))))) = ⊤ →
    (coordMap (A := A) g y t).Etale

theorem varIdeal_coordMap {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d e : ℕ} (g : B)
    (y : Fin e → B) (t : Fin d → B) :
    LateralTheory.E.t_E6Cut.varIdeal (coordMap (A := A) g y t) =
      Ideal.span (Set.range fun j => algebraMap B (Localization.Away g) (t j)) := by
  unfold LateralTheory.E.t_E6Cut.varIdeal coordMap
  simp

theorem LeafChartRing_of (hC : LeafCoords) (hJ : LeafJacobian) : LateralTheory.E.t_E6Cut.LeafChartRing := by
  intro d e A B _ _ _ I hB hBI P hP hIP
  obtain ⟨g, hg, t, y, hI, hli, hsp⟩ := hC d e A B I hB hBI P hP hIP
  refine ⟨g, hg, MvPolynomial (Fin e) A, inferInstance, coordMap (A := A) g y t,
    hJ d e A B (e + d) hB g t y hli hsp, ?_⟩
  rw [varIdeal_coordMap, hI]

end LateralTheory.E.LeafChartRingPf
