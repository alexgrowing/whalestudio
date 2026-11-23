import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
