import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RowStarCoreAtUOfRowStarCoreU
import Development.AbelianVarietyTheory.Definitions.Divisors.GenTyL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

theorem Lacunary.mono {J K : Finset ℤ} (h : Lacunary J) (hK : K ⊆ J) : Lacunary K :=
  fun A B hA hB => h A B (hA.trans hK) (hB.trans hK)

theorem lacunary_of_growth {J : Finset ℤ} (hpos : ∀ x ∈ J, 0 < x) (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * x < y) :
    Lacunary J := by
  classical
  have key : ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → B.Nonempty → ∀ m ∈ A, (∀ b ∈ B, b < m) →
      (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
    intro A B hA hB hBn m hm hlt
    have h1 : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun x hx => (hpos x (hA hx)).le) hm
    have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
    have h2 : ∑ b ∈ B, (A.card : ℤ) * b < ∑ _b ∈ B, m := by
      refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
      have := hg b (hB hb) m (hA hm) (hlt b hb)
      have := mul_le_mul_of_nonneg_right hc (hpos b (hB hb)).le
      linarith
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (B.card : ℤ) * m ≤ B.card * A.sum id := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_lt_of_le h2 h3
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (key A B hA hB hBn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (key B A hB hA hAn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem not_lacunary_three (k : ℤ) : ¬ Lacunary ({k, k + 1, k + 2} : Finset ℤ) := by
  intro h
  have h02 : k ≠ k + 2 := by omega
  refine h {k, k + 2} {k + 1} ?_ ?_ ?_ (by simp) (by simp) ?_
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]; omega
  · rw [Finset.sum_pair h02, Finset.card_pair h02]; simp; ring

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

example : ¬ Lacunary (wtJumps (⟨fun _ => 0, antitone_const⟩ : DomWeight 3)) := by
  have : wtJumps (⟨fun _ => 0, antitone_const⟩ : DomWeight 3) = {0, 0 + 1, 0 + 2} := by
    simp only [wtJumps]; decide
  rw [this]
  exact not_lacunary_three 0

example : Lacunary {1, 10, 100} := lacunary_of_growth (by decide) (by decide)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def SeedCase (a : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E))
    (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  NonSplitSet T ∧ (∀ w ∈ S, IsSplitAt w) ∧ ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal ∧ IsSplitAt w₀ ∧ w₀ ∈ S ∧
    IsAutRepU U ∧ (∀ w, ¬ IsSplitAt w → w ∉ T → IsUnramU U w) ∧ ScU U w₀

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def CrysKilledAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ)
    (B : Multiset ℂˣ) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O)
    (hj : Pst.Induces Bw), IsCrysAt P Bw (ρ.comp (Dec (F := E) A).subtype) ∧
      ∀ g : Weil h, (wdAt P ι Bw h hj (ρ.comp (Dec (F := E) A).subtype)).charPol g ∣
        ((GlobalTheory.RoadU.satWD h a B).charPol g) ^ d

def WtJumpsAt {d a : ℕ} (ι : Qbar l ≃+* ℂ) (U : Submodule ℂ (UA E a → ℂ)) (ρ : G E Ω →* GL (Fin d) (Qbar l))
    (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∀ lam : DomWeight a, HasWeightAt U (ι.toRingHom.comp τ) lam →
          ∃ J : Multiset ℤ, IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J ∧ ∀ n ∈ wtJumps lam, n ∈ J

def HTRichAt {dd : ℕ} (ρ : G E Ω →* GL (Fin dd) (Qbar l)) (a : ℕ) (v' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A v' →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      ∃ (τ : E →+* Om l) (J : Multiset ℤ), IsJumpsAt P Bw (ρ.comp (Dec (F := E) A).subtype) τ J ∧
        ∃ K : Finset ℤ, (∀ n ∈ K, n ∈ J) ∧ a ≤ K.card ∧ Lacunary K

def HTRich {d : ℕ} (ρ : G E Ω →* GL (Fin d) (Qbar l)) (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∃ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal ∧ IsSplitAt v' ∧ v' ∉ S ∧ HTRichAt ρ a v'

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

def LacWt : SeedWtU :=
  SeedWtU.ofWeightPredicate fun _ _ _ _ _ _ _ ι v' U' => LacWtAt ι v' U'

def VData {d : ℕ} (ι : Qbar l ≃+* ℂ) (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ρ : G E Ω →* GL (Fin d) (Qbar l)) : Prop :=
  0 < d ∧ Continuous ρ ∧ IsSSRep ρ ∧ ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → w ∉ S → ∀ B : Multiset ℂˣ, SatAtU U w B →
    (((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ESAt ι ρ w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (((l : ℕ) : 𝓞 E) ∈ w.asIdeal → CrysKilledAt ι ρ w a B ∧ WtJumpsAt ι U ρ w)

def VData2 {dd : ℕ} (ι : Qbar l ≃+* ℂ) (a d : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (S Y : Finset (HeightOneSpectrum (𝓞 E)))
    (w₀ v' : HeightOneSpectrum (𝓞 E)) (ρ : G E Ω →* GL (Fin dd) (Qbar l)) : Prop :=
  0 < dd ∧ Continuous ρ ∧ IsSSRep ρ ∧
    (∃ X : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), (w ∉ X ∨ w ∈ Y) → UsPl d w →
      ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w → ∀ B : Multiset ℂˣ, SatU U w B →
        ESAt ι ρ w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w →
      ∀ B : Multiset ℂˣ, SatU U w B → CrysKilledAt ι ρ w a B ∧ WtJumpsAt ι U ρ w)

def DetData (ι : Qbar l ≃+* ℂ) (a d : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (S Y : Finset (HeightOneSpectrum (𝓞 E)))
    (ψ : G E Ω →* (Qbar l)ˣ) : Prop :=
  Continuous ψ ∧ ∃ X : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), (w ∉ X ∨ w ∈ Y) → UsPl d w →
    ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w → ∀ B : Multiset ℂˣ, SatU U w B →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ψ s = 1) ∧
        ∀ σ : G E Ω, IsFrob A (normV w) σ → ι (ψ σ⁻¹ : Qbar l) = (UpperTheory.V.Af.algSat a (normV w) B).prod

def SeedRep (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (ι : Qbar l ≃+* ℂ) (a d : ℕ) (U' : Submodule ℂ (UA E a → ℂ))
    (S Y : Finset (HeightOneSpectrum (𝓞 E))) (w₀ v' : HeightOneSpectrum (𝓞 E)) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ IsSSRep r ∧
    (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
      ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
        ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
          (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
            ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
              ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
    (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
      ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
    (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

def GeoV : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)),
      SeedCase (l := l) a S T w₀ U →
      ∀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal → IsSplitAt v' → v' ∉ S → LacWtAt ι v' U →
      ∃ (d : ℕ) (ρ : G E Ω →* GL (Fin d) (Qbar l)), VData ι a U S ρ ∧ HTRichAt ρ a v'

def DivL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 E))) (w₀ : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)),
      SeedCase (l := l) a S T w₀ U →
      ∀ (d : ℕ) (ρ : G E Ω →* GL (Fin d) (Qbar l)), VData ι a U S ρ → HTRich ρ a S →
        ∃ r : G E Ω →* GL (Fin a) (Qbar l), HasRepU ι U S r

def GeometricRealisation (Ty : UnitaryAutomorphicTypeClass) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → LacWtAt ι v' U' → Ty E l a w₀ U' → SphOffU w₀ S U' →
        ∃ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VData2 ι a d U' S Y w₀ v' ρ ∧ HTRichAt ρ a v'

def DivisionStatementAlt (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → Ty E l a w₀ U' → SphOffU w₀ S U' → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∀ N : Finset (HeightOneSpectrum (𝓞 E)), Y ⊆ N → Z₀ ⊆ N →
      ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VData2 ι a d U' S N w₀ v' ρ → HTRichAt ρ a v' →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), SeedRep Gen ι a d U' S Y w₀ v' r

def DivisionGivenDeterminant (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → Ty E l a w₀ U' → SphOffU w₀ S U' → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∀ N : Finset (HeightOneSpectrum (𝓞 E)), Y ⊆ N → Z₀ ⊆ N →
      ∀ (dd : ℕ) (ρ : G E Ω →* GL (Fin dd) (Qbar l)), VData2 ι a d U' S N w₀ v' ρ → HTRichAt ρ a v' →
      ∀ ψ : G E Ω →* (Qbar l)ˣ, DetData ι a d U' S N ψ →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), SeedRep Gen ι a d U' S Y w₀ v' r

def DeterminantCharacterStatement : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (d : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U →
    ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)), ∃ ψ : G E Ω →* (Qbar l)ˣ, DetData ι a d U S Y ψ

end GlobalTheory.Published

end
