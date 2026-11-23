import Development.EtaleCohomology.WeilConjectures.GysinSeqCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.Gys.LV
open LateralTheory.EWeil LateralTheory.EWeil.Gys

def LowVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), n < 2 * r →
  ∀ x : HZ (l ^ c) i P.j n, x = 0

def PointVan : Prop := Base → ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ), 2 * r < n →
  ∀ (x : HZ (l ^ c) i P.j n) (t : P.X), ∃ (P' : SPair l r) (f : P'.Hom P),
    t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def Glue : Prop := ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (P : SPair l r) (c : ℕ) (i n : ℤ) (x : HZ (l ^ c) i P.j n),
  (∀ t : P.X, ∃ (P' : SPair l r) (f : P'.Hom P), t ∈ Set.range f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0) →
  ∃ (P' : SPair l r) (f : P'.Hom P), Surjective f.fX ∧ pullZ _ i f.fX f.fU f.sqU n x = 0

def SPair.idHom {l r : ℕ} (P : SPair l r) : P.Hom P where
  fX := 𝟙 _
  fZ := 𝟙 _
  fU := 𝟙 _
  etale := inferInstance
  sqZ := IsPullback.of_horiz_isIso ⟨by simp⟩
  sqU := by simp

theorem goal_of (hL : LowVan) (hP : PointVan) (hG : Glue) : Gys.LocalVan := by
  intro hB l _ r P c i n hn x
  rcases lt_or_gt_of_ne hn with h | h
  · refine ⟨P, SPair.idHom P, show Surjective (𝟙 P.X) from inferInstance, ?_⟩
    rw [hL hB l r P c i n h x, map_zero]
  · exact hG l r P c i n x (fun t => hP hB l r P c i n h x t)

end LateralTheory.EWeil.Gys.LV
