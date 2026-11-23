import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.FibPf

def FibClosed : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z S : Scheme.{0}}
  (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  Eqv _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)

theorem total (H : Hyp) (h0 : HZero) (hA : AICAcyc) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {Z S : Scheme.{0}} (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c]
    [QuasiSeparated c] (hZ : AICSch Z) (hS : AICSch S) : Eqv _ (sch.map c) (tw q i) := by
  obtain ⟨_, _⟩ := qcqs_of p
  obtain ⟨_, _⟩ := qcqs_of (c ≫ p)
  have : IsIntegral Z := hZ.1
  have : ConnectedSpace Z := inferInstance
  exact eqv_of H.a9 _ (h0 H q c hS this (unit_of hq p) i)
    (fun n hn => hA H q Z hZ (unit_of hq (c ≫ p)) n i hn) (fun n hn => hA H q S hS (unit_of hq p) n i hn)

theorem Fib_of (hF0 : FibClosed) (h0 : HZero) (hA : AICAcyc) : Fib := by
  intro H q i A _ _ hq Z S c p _ _ _ _ _ hZ hS hB
  have ec := total H h0 hA q i A hq c p hZ hS
  have em := hF0 H q i A hq c p hZ hS hB
  have sq : pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst p (cpt A)
      = pullback.fst (c ≫ p) (cpt A) ≫ c := pullback.lift_fst _ _ _
  have key : ∀ n x, pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n (pull _ (sch.map c) (tw q i) n x)
      = pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n x) := by
    intro n x
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, sq]
  have fe : ∀ n, (pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)
      = (pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
          (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n) := fun n => funext (key n)
  constructor
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.fst (c ≫ p) (cpt A))) (tw q i) n) ∘ (pull _ (sch.map c) (tw q i) n)) :=
      (h n).comp (ec n)
    rw [fe n] at h1
    exact (Function.Bijective.of_comp_iff' (em n) _).1 h1
  · intro h n
    have h1 : Function.Bijective ((pull _ (sch.map (pullback.map (c ≫ p) (cpt A) p (cpt A) c (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) n) ∘
        (pull _ (sch.map (pullback.fst p (cpt A))) (tw q i) n)) := (em n).comp (h n)
    rw [← fe n] at h1
    exact (Function.Bijective.of_comp_iff _ (ec n)).1 h1

end LateralTheory.E.FibPf
