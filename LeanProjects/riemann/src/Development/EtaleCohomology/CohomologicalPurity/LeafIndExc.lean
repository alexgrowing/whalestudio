import Development.EtaleCohomology.CohomologicalPurity.InrFold

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

def Hyp : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ DivisorNaturality ∧ DivisorRingCompatibility ∧ A9 ∧ A11 ∧ B1 ∧ C4 ∧ D1 ∧ E1

def Gysin (d : ℕ) : Prop :=
  ∃ (gys : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.Z) n i →+ Ht q (sch.obj P.X) (n + 2 * d) (i + d))
    (rs : ∀ (q : ℕ) (P : SP d) (n i : ℤ), Ht q (sch.obj P.U) (n + 2 * d - 1) (i + d) →+ Ht q (sch.obj P.Z) n i),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  (∀ n i : ℤ, Function.Exact (pull _ (sch.map P.U.ι) (tw q (i + d)) (n + 2 * d - 1)) (rs q P n i) ∧
    Function.Exact (rs q P n i) (gys q P n i) ∧
    Function.Exact (gys q P n i) (pull _ (sch.map P.U.ι) (tw q (i + d)) (n + 2 * d))) ∧
  (∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ),
    (∀ a, pull _ (sch.map φ.f) _ _ (gys q P n i a) = gys q P' n i (pull _ (sch.map φ.g) _ _ a)) ∧
    ∀ u, pull _ (sch.map φ.g) _ _ (rs q P n i u) = rs q P' n i (pull _ (sch.map (φ.f.resLE P.U P'.U φ.le)) _ _ u)) ∧
  (∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    gys q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b) = (cup q a (gys q P m j b)).cast (by ring) (by ring)) ∧
  ∀ r : ℕ, r ∣ q → ∀ n i : ℤ, (∀ a, gys r P n i (red q r _ _ _ a) = red q r _ _ _ (gys q P n i a)) ∧
    ∀ u, rs r P n i (red q r _ _ _ u) = red q r _ _ _ (rs q P n i u)

def Goal : Prop := Hyp → (∀ d, Gysin d) ∧ E6

def LeafAW : Prop := ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧
  ∀ (E : Spc) (n m : ℤ) (α : Cocycle ((chains _).obj E) (res _ (tw q i)) n) (β : Cocycle ((chains _).obj E) (res _ (tw q j)) m),
    ∃ γ : Cocycle ((chains _).obj E) (res _ (tw q (i + j))) (n + m), (twPair q i j).IsAW rfl α.1 β.1 γ.1 ∧
      cup q (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def LeafBd : Prop := ∃ δ, IsBd δ

def LeafExc : Prop := A1 → ∀ (q : ℕ) {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U' : X'.Opens) (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ h : U' = f ⁻¹ᵁ U, Exc q (opnMap f U' U h.le)

def LeafHens : Prop := Nonempty Hens

def LeafIndExc : Prop := A1 → A4 → B1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A), I.FG →
  IndNbhd φ I → IsUnit (q : A) → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B (I.map φ)) (off A I) h)

def LeafThom : Prop := Hyp → ∀ d, ∃ th, IsThom d th

def LeafChart : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X) (W : P.X.Opens), x ∈ W →
  ∃ V : P.X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W ∧ (P.ι.ker.ideal V).FG ∧ Chart d Γ(P.X, V.1) (P.ι.ker.ideal V)

def LeafCl : Prop := Hyp → ∀ d, ∃ c, IsCl d c

def LeafTube : Prop := Hyp → ∀ d, ∃ T : ∀ P : SP d, Tube P, ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

def LeafGysin : Prop := Hyp → ∀ d, Gysin d

def LeafSemi : Prop := A9 → (∀ d, Gysin d) → E6

end LateralTheory.CohomologicalPurity
