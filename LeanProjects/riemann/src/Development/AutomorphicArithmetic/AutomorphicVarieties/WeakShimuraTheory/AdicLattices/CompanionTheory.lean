import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws.Lat

def TConj {ι Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (t : Kˣ × Kˣ) (P P' : PD ι Γ R) : Prop :=
  (∀ g, (P'.r g).map f = tconj t ((P.r g).map f)) ∧ ∀ v, (P'.n v).map f = tconj t ((P.n v).map f)

def nCo {R : Type} [CommRing R] (X : M4 R) (w : ℤ × ℤ) : R :=
  if w = -wAl then X 1 0 else if w = -wBe then X 2 1 else if w = -wPs then X 2 0 else if w = -wTh then X 3 0 else 0

def Tight {ι Γ R : Type} [Group Γ] [CommRing R] (P : PD ι Γ R) : Set (ℤ × ℤ) :=
  {w | w ∈ roots ∧ (Ent P.r w ∨ ∃ v, nCo (P.n v) w ≠ 0)}

def CompanionTheory (Si : Set (ℤ × ℤ)) : Prop :=
  (wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP) ∨ (-wAl ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ qQ) ∨ (-wTh ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ {-wTh, -wPs}) ∨
    (-wAl ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ nM) ∨ (-wTh ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe}) ∨
    (-wTh ∈ Si ∧ wAl ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe, wAl})

variable {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) {R : Type} [CommRing R] (a : O →+* R)

structure PreRes [TopologicalSpace Γ] (P : PD Φ.ι Γ R) : Prop where
  pair : Φ.IsPair a P
  diag : ∀ g i, P.r g i i = a (Φ.χ i g)
  char : ∀ v, ∀ s ∈ Φ.Gv v, ∀ i, P.ψ v i s = a (Φ.χ i s)
  cont : P.Cont ⊥

def OddVan [TopologicalSpace Γ] : Prop :=
  ∀ w ∈ oddRoots, ∀ z ∈ Φ.Zgl a w, ∀ m : Φ.ι → R, Φ.LocTriv a w z m → z = 0 ∧ m = 0

def EntVan (P : PD Φ.ι Γ R) : Prop :=
  ∀ i j, wt i j ∈ oddRoots → (∀ g h x, x ≠ i → x ≠ j → P.r g i x * P.r h x j = 0) → ∀ m : Φ.ι → R,
    (∀ v, ∀ s ∈ Φ.Gv v, P.r s i j = m v * (a (Φ.χ j s) - a (Φ.χ i s))) → (∀ g, P.r g i j = 0) ∧ m = 0

theorem TConj.refl {ι Γ R K : Type} [Group Γ] [CommRing R] [CommRing K] (f : R →+* K) (P : PD ι Γ R) : TConj f 1 P P := by
  constructor <;> intro _ <;> ext i j <;> simp [tconj, wv]

example : CompanionTheory {wBe, -wPs} := .inl ⟨by simp, by simp, by rintro w (rfl | rfl) <;> simp [nP]⟩

end UpperTheory.V.Ws.Lat

end
