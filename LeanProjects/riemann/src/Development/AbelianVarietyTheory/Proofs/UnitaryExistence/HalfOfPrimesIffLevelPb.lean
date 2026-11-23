import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients

noncomputable section

namespace GlobalTheory.ParAtCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke

theorem isHalf_of_level (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.IsHalf D l.Mb :=
  ⟨l.fromK, hl.1 ▸ l.prod, l.coprime⟩

theorem levelAt_Mb (D : D7) (l : Level (hostOfRecord D)) (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    HalfLevelCoefficients.levelAt D l.Mb (isHalf_of_level D l hl) = l := by
  obtain ⟨M, h3, hodd, Mb, hK, hp, hc, A, hA⟩ := l
  obtain ⟨h1, h2⟩ := hl
  dsimp only at h1 h2
  subst h1 h2
  rfl

theorem levelAt_spec (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : HalfLevelCoefficients.IsHalf D Mb) :
    (HalfLevelCoefficients.levelAt D Mb h).M = D.host.g 0 * D.host.g 1 ∧ (HalfLevelCoefficients.levelAt D Mb h).A = 1 :=
  ⟨rfl, rfl⟩

def levelEquivHalf (D : D7) :
    {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1} ≃
      {Mb : Ideal (𝓞 D.host.E) // HalfLevelCoefficients.IsHalf D Mb} where
  toFun l := ⟨l.1.Mb, isHalf_of_level D l.1 l.2⟩
  invFun Mb := ⟨HalfLevelCoefficients.levelAt D Mb.1 Mb.2, levelAt_spec D Mb.1 Mb.2⟩
  left_inv l := Subtype.ext (levelAt_Mb D l.1 l.2)
  right_inv _ := rfl

theorem datAt_eq (D : D7) : HalfLevelCoefficients.datAt D = datumAtLift D _ (datHolds D) := rfl

theorem parAt_levelAt (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : Ideal (𝓞 D.host.E))
    (h : HalfLevelCoefficients.IsHalf D Mb) :
    Formalism.L2.Pj.parAt D hF hz hN (HalfLevelCoefficients.levelAt D Mb h) (levelAt_spec D Mb h) = HalfLevelCoefficients.parAt D hF hz hN Mb h :=
  rfl

theorem parAt_eq (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
    (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) :
    Formalism.L2.Pj.parAt D hF hz hN l hl = HalfLevelCoefficients.parAt D hF hz hN l.Mb (isHalf_of_level D l hl) := by
  rw [← parAt_levelAt]
  congr 1
  exact (levelAt_Mb D l hl).symm

theorem levelPb_iff (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) :
    LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb) := by
  constructor
  · rintro ⟨l, hl, hb⟩
    have h := isHalf_of_level D l hl
    rw [hb] at h
    exact h
  · intro h
    exact ⟨HalfLevelCoefficients.levelAt D _ h, levelAt_spec D _ h, rfl⟩

theorem halfOfPrimes_iff_levelPb (D : D7) :
    HalfLevelCoefficients.HalfOfPrimes D ↔ ∀ pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K),
      (∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) → LevelPb D pb :=
  forall₂_congr fun pb _ => (levelPb_iff D pb).symm

theorem typings_agree (D : D7) :
    (∀ l : {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1}, (levelEquivHalf D l).1 = l.1.Mb) ∧
    (∀ (hF : OFull D) (hz : OZeta D) (hN : N1ab)
      (l : {l : Level (hostOfRecord D) // l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1}),
      Formalism.L2.Pj.parAt D hF hz hN l.1 l.2 =
        HalfLevelCoefficients.parAt D hF hz hN (levelEquivHalf D l).1 (levelEquivHalf D l).2) ∧
    (∀ (hF : OFull D) (hz : OZeta D) (hN : N1ab) (Mb : {Mb : Ideal (𝓞 D.host.E) // HalfLevelCoefficients.IsHalf D Mb}),
      Formalism.L2.Pj.parAt D hF hz hN ((levelEquivHalf D).symm Mb).1 ((levelEquivHalf D).symm Mb).2 =
        HalfLevelCoefficients.parAt D hF hz hN Mb.1 Mb.2) ∧
    (∀ pb, LevelPb D pb ↔ HalfLevelCoefficients.IsHalf D (HalfLevelCoefficients.halfOf D pb)) ∧
    (HalfLevelCoefficients.HalfOfPrimes D ↔ ∀ pb, HalfLevelCoefficients.PrimesOver D pb → LevelPb D pb) :=
  ⟨fun _ => rfl, fun hF hz hN l => parAt_eq D hF hz hN l.1 l.2,
    fun hF hz hN Mb => parAt_levelAt D hF hz hN Mb.1 Mb.2, levelPb_iff D, halfOfPrimes_iff_levelPb D⟩

end GlobalTheory.ParAtCompare
