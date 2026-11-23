import Development.EtaleCohomology.WeilConjectures.ArtinCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut

namespace LateralTheory.EWeil.LerayCut

universe u v w

abbrev gam {C : Type u} [Category.{v} C] [Preadditive C] (U : C) : C ⥤ AddCommGrpCat.{v} :=
  preadditiveCoyoneda.obj (op U)

abbrev gamCx {C : Type u} [Category.{v} C] [Preadditive C] (U : C) (K : CochainComplex C ℕ) :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((gam U).mapHomologicalComplex _).obj K

abbrev unitSh (A : CommRingCat.{0}) : Sm A :=
  (constantSheaf (Spec A).smallEtaleTopology AddCommGrpCat.{1}).obj (AddCommGrpCat.of (ULift ℤ))

def Hyper : Prop := ∀ (C : Type u) [Category.{v} C] [Abelian C] [HasExt.{w} C] (U : C) (K : CochainComplex C ℕ) (d : ℕ),
  (∀ s n : ℕ, 0 < n → Subsingleton (Abelian.Ext U (K.X s) n)) →
  (∀ j m : ℕ, d < j + m → Subsingleton (Abelian.Ext U (K.homology m) j)) →
  ∀ n : ℕ, d < n → Subsingleton ((gamCx U K).homology n)

def ZeroSheaf : Prop := ∀ (A : CommRingCat.{0}) (F : Sm A), (∀ p : PrimeSpectrum A, StalkZero F p) →
  ∀ n : ℕ, Subsingleton (Sheaf.H.{1} F n)

def Push : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) → ∀ i : ℤ,
  ∃ K : CochainComplex (Sm A) ℕ,
    (∀ s n : ℕ, 0 < n → Subsingleton (Sheaf.H.{1} (K.X s) n)) ∧
    (∀ (m : ℕ) (V : (Spec A).Etale) (x : (K.homology m).obj.obj (op V)), q • x = 0) ∧
    (∀ (p : PrimeSpectrum A) (m : ℕ), (∀ (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D),
        IsStalk f p → IsPushout β f u v → Van q D m) → StalkZero (K.homology m) p) ∧
    ∀ n : ℕ, Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) K).homology n)

example (A : CommRingCat.{0}) (F : Sm A) (n : ℕ) : Sheaf.H.{1} F n = Abelian.Ext (unitSh A) F n := rfl

lemma enat_lt_add_of_sub_lt (d m : ℕ) (x : ℕ∞) (hm : m ≤ d) (h : ((d - m : ℕ) : ℕ∞) < x) : (d : ℕ∞) < (m : ℕ∞) + x := by
  induction x using ENat.recTopCoe with
  | top => simp
  | coe x =>
    have : d - m < x := by exact_mod_cast h
    exact_mod_cast (by omega : d < m + x)

lemma enat_lt_add_of_lt (d m : ℕ) (x : ℕ∞) (hm : d < m) : (d : ℕ∞) < (m : ℕ∞) + x :=
  lt_of_lt_of_le (by exact_mod_cast hm) le_self_add

theorem goal_of (hH : Hyper.{2, 1, 1}) (hZ : ZeroSheaf) (hP : Push) : LateralTheory.EWeil.ArtinCut.Leray := by
  intro base q _ A B β hq δ d hsm hst n hn i
  obtain ⟨K, hacy, htor, hstalk, hiso⟩ := hP base q β hq i
  have hn0 : (0 : ℤ) ≤ n := by omega
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  have hdN : d < N := by omega
  obtain ⟨e⟩ := hiso N
  have key : Subsingleton ((gamCx (unitSh A) K).homology N) := by
    refine hH (Sm A) (unitSh A) K d (fun s k hk => hacy s k hk) ?_ N hdN
    intro j m hjm
    by_cases hm : m ≤ d
    · refine hsm (K.homology m) (htor m) (d - m) ?_ j (by omega)
      intro p hp
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_sub_lt d m _ hm hp))
    · refine hZ A (K.homology m) (fun p => ?_) j
      exact hstalk p m (fun S D f u v hf hpo => hst p S D f u v hf hpo m (enat_lt_add_of_lt d m _ (by omega)))
  exact e.subsingleton

end LateralTheory.EWeil.LerayCut
