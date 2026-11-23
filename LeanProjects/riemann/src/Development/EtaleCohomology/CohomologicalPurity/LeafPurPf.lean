import Development.EtaleCohomology.CohomologicalPurity.LeafGysinPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

namespace PurPf

def actH (q : ℕ) {P : Arrow Spc} (n : ℤ) {m i j : ℤ} (b : Hs q P m j) :
    Ht q P.right n i →+ Hs q P (n + m) (i + j) where
  toFun a := Hs.act q a b
  map_zero' := by
    apply Subtype.ext
    simp [Hs.act, Hs.proj]
  map_add' x y := by
    apply Subtype.ext
    simp only [Hs.act, Hs.proj, map_add, AddMonoidHom.add_apply, AddSubgroup.coe_add]
    abel

theorem bij_comp {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C] {f : B →+ C} {g : A →+ B}
    (hf : Function.Bijective f) (hg : Function.Bijective g) : Function.Bijective (f.comp g) := by
  rw [AddMonoidHom.coe_comp]; exact hf.comp hg

def purT {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) (P : SP d) (n i : ℤ) :
    Ht q (sch.obj P.Z) n i →+ Hs q (opn P.U) (n + 2 * d) (i + d) := by
  classical
  exact if h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) then
    haveI : NeZero q := ⟨h.1⟩
    ((AddEquiv.ofBijective _ (((T P).ok q h.2).2.2.1 (n + 2 * d) (i + d))).symm.toAddMonoidHom.comp
      (actH q (P := abv P.U (T P).π) n (i := i) (Hs.pull q (abvMap P.U (T P).π) _ _ (fcl d q P)))).comp
      ((AddEquiv.ofBijective _ (((T P).ok q h.2).1 i n)).symm.toAddMonoidHom.comp
        (pull _ (pullback.snd (T P).π (sch.map P.ι)) (tw q i) n))
  else 0

theorem purT_bij {d : ℕ} (T : ∀ P : SP d, Tube P) (q : ℕ) [NeZero q] (P : SP d) (hq : IsUnit (q : Γ(P.X, ⊤)))
    (n i : ℤ) : Function.Bijective (purT T q P n i) := by
  classical
  have h : q ≠ 0 ∧ IsUnit (q : Γ(P.X, ⊤)) := ⟨NeZero.ne q, hq⟩
  unfold purT
  rw [dif_pos h]
  refine bij_comp (bij_comp (AddEquiv.bijective _) ?_) (bij_comp (AddEquiv.bijective _) (((T P).ok q hq).2.1 i n))
  exact ((T P).ok q hq).2.2.2 n i

def TubeRef {d : ℕ} (T : ∀ P : SP d, Tube P) : Prop := ∀ (P' P : SP d) (φ : P'.Hom P),
  ∃ (T' : Tube P') (a : T'.E ⟶ (T P').E) (b : T'.E ⟶ (T P).E), a ≫ (T P').π = T'.π ∧ b ≫ (T P).π = T'.π ≫ sch.map φ.f

end PurPf

open PurPf

def EtalePurityNaturality : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P), TubeRef T →
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (P' : SP d) (φ : P'.Hom P) (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    Hs.pull q (opnMap φ.f _ _ φ.le) _ _ (purT T q P n i a) = purT T q P' n i (pull _ (sch.map φ.g) _ _ a)

def EtalePurityProjection : Prop := Hyp → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ (n m i j : ℤ) (a : Ht q (sch.obj P.X) n i) (b : Ht q (sch.obj P.Z) m j),
    (Hs.fgt q (opn P.U) (n + m + 2 * d) (i + j + d) (purT T q P (n + m) (i + j) (cup q (pull _ (sch.map P.ι) _ _ a) b)) :
      Ht q (sch.obj P.X) (n + m + 2 * d) (i + j + d)) =
      (cup q a (Hs.fgt q (opn P.U) (m + 2 * d) (j + d) (purT T q P m j b) : Ht q (sch.obj P.X) (m + 2 * d) (j + d))).cast
        (by ring) (by ring)

def EtalePurityReduction : Prop := Hyp → LeafCl → ∀ d (T : ∀ P : SP d, Tube P),
  ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) →
  ∀ r : ℕ, r ∣ q → ∀ (n i : ℤ) (a : Ht q (sch.obj P.Z) n i),
    (purT T r P n i (red q r _ _ _ a)).1 = red q r _ _ _ (purT T q P n i a).1

theorem EtalePurity_of_parts (hCl : LeafCl) (hTube : LeafTube) (hN : EtalePurityNaturality) (hP : EtalePurityProjection) (hR : EtalePurityReduction) :
    LeafPur := by
  intro hH d
  obtain ⟨T, hT⟩ := hTube hH d
  exact ⟨purT T, fun q _ P hq =>
    ⟨purT_bij T q P hq, hN hH hCl d T hT q P hq, hP hH d T q P hq, hR hH hCl d T q P hq⟩⟩

end LateralTheory.CohomologicalPurity
