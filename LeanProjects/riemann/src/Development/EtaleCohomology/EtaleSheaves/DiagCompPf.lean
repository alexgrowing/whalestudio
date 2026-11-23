import Development.EtaleCohomology.EtaleSheaves.PartDiagCut

noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.DiagCompPf

theorem block_unique {A : Type} [CommRing A] (P R : PartDiagCut.Part A) (e : A) (he : e ∈ R.1) (a b : P.1)
    (ha : e * a.1 = e) (hb : e * b.1 = e) : a = b := by
  by_contra hne
  have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
  have h0 : a.1 * b.1 = 0 := P.orth a.1 a.2 b.1 b.2 hne'
  have : e = 0 := by
    calc e = e * a.1 * b.1 := by rw [ha, hb]
      _ = e * (a.1 * b.1) := by ring
      _ = 0 := by rw [h0, mul_zero]
  exact (R.idem e he).2 this

theorem par_trans {B : Type} [CommRing B] (I : Ideal B) {P Q R : PartDiagCut.Part (B ⧸ I)} (h1 : P ≤ Q) (h2 : Q ≤ R) (e : R.1) :
    par (h1.trans h2) e = par h1 (par h2 e) := by
  apply block_unique P R e.1 e.2
  · exact par_spec _ e
  · calc e.1 * (par h1 (par h2 e)).1 = e.1 * (par h2 e).1 * (par h1 (par h2 e)).1 := by rw [par_spec h2 e]
      _ = e.1 * ((par h2 e).1 * (par h1 (par h2 e)).1) := by ring
      _ = e.1 := by rw [par_spec h1 (par h2 e), par_spec h2 e]

theorem DiagComp_of : DiagComp := by
  intro B _ I P Q R h1 h2
  ext x e
  have key : ∀ (g g' : B →+* B), g = g' → ∀ (a b : P.1), a = b →
      ∀ (hA : S I a.1 ≤ (S I e.1).comap g) (hD : S I b.1 ≤ (S I e.1).comap g'),
      IsLocalization.map (M := S I a.1) (T := S I e.1) (Localization (S I e.1)) g hA (x a)
      = IsLocalization.map (M := S I b.1) (T := S I e.1) (Localization (S I e.1)) g' hD (x b) := by
    rintro g _ rfl a _ rfl hA hD; rfl
  simp only [stageMap, RingHom.comp_apply, RingHom.pi_apply, Pi.evalRingHom_apply]
  erw [IsLocalization.map_map]
  exact key _ _ (RingHom.id_comp _).symm _ _ (par_trans I h1 h2 e) _ _

end LateralTheory.E.DiagCompPf
