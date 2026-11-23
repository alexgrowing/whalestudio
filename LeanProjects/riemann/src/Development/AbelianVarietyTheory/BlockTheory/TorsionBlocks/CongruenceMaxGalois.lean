import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.CyclotomicNorms.StatementI

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N

def Zbar (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

def CongrMax {l : ℕ} [Fact l.Prime] (a b : Qbar l) : Prop := ‖a - b‖ < 1

def IsReduction {Γ : Type} [Group Γ] [TopologicalSpace Γ] {l a : ℕ} [Fact l.Prime]
    (r : Γ →* GL (Fin a) (Qbar l)) (rb : Γ →* GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  IsSSRep rb ∧ IsOpen (rb.ker : Set Γ) ∧
    ∃ red : Zbar l →+* Formalism.CyclotomicNorms.Fbar l, ∀ g : Γ, ∃ p : (Zbar l)[X],
      p.map (Zbar l).subtype = ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly ∧
      p.map red = ((rb g : GL (Fin a) (Formalism.CyclotomicNorms.Fbar l)) :
        Matrix (Fin a) (Fin a) (Formalism.CyclotomicNorms.Fbar l)).charpoly

def IsWildAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (B : ValuationSubring Ω) (u : G E Ω) : Prop :=
  ∀ y : Ω, y ≠ 0 → B.valuation (u y / y - 1) < 1

def UnramOver {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (L : IntermediateField E Ω) (g : ℕ) : Prop :=
  ∀ w ∈ placesOver E g, ∀ B : ValuationSubring Ω, IsPlaceOver (F := E) B w →
    Ine (F := E) B ≤ L.fixingSubgroup

variable (D : D7)

abbrev GalE : Type := G D.host.E D.nd.Om

def IsGaloisRepOf {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (φ : GalE D),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) φ →
    ((r φ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))

def IsTameLift (k : Fin 2) (v : D.nd.PlG k) (t : GalE D) : Prop :=
  ∃ h u : GalE D, IsWildAt (D.nd.plOm.1 (D.naut.plGw k v)) u ∧
    (t = h * (D.ntypes.tg k v * u) * h⁻¹ ∨
      ∃ c : D.nd.Om ≃+* D.nd.Om, IsCMConjOm D.host.E D.nd.Om c ∧
        ∀ x, t x = c ((h * (D.ntypes.tg k v * u) * h⁻¹) (c.symm x)))

def bracket (k : Fin 2) (x : (ZMod (D.host.g k))ˣ) : ℂ :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  D.ntypes.teichC k (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (x : ZMod (D.host.g k)))

def IsRowAt (j : ℕ) (σ : D.what₂.FT) : Prop :=
  D.what₂.isot j σ ≠ ⊥ ∨ σ ∈ Set.range D.what₂.ft ∨ σ ∈ Set.range D.what₂.ft0

def IsCuspBaseChange (i : D.nd.Loc) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧ D.naut.ralg π ∧
    ∀ w, IsSplitPl D.host w → D.naut.locG π w = D.naut.locW i σ w

def ResidIrred (l : ℕ) [Fact l.Prime] (rb : GalE D →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar l)) : Prop :=
  Formalism.CyclotomicNorms.IrredOn rb ⊤ ∧
  ∀ (L : IntermediateField D.host.E D.nd.Om), FiniteDimensional D.host.E L → IsGalois D.host.E L →
    IsSolvable (L ≃ₐ[D.host.E] L) →
    ∀ k : Fin 2, l ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) → UnramOver L (D.host.g k) →
      Formalism.CyclotomicNorms.IrredOn rb L.fixingSubgroup

def TameAvoids (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : GalE D →* GL (Fin D.R.r) (Qbar l)) : Prop :=
  ∀ k : Fin 2, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) (t : GalE D), IsTameLift D k v t →
    ∀ (j : Fin D.R.m) (α : Qbar l),
      ((r t : GL (Fin D.R.r) (Qbar l)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar l)).charpoly.IsRoot α →
      ¬ CongrMax α (ι.symm (bracket D k (D.nd.chiT k v j))) ∧
      ¬ CongrMax α (ι.symm (bracket D k (D.nd.chiT k v j)⁻¹))

def GoodRowIrreducibility : Prop :=
  Disjoint (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 0)) (Formalism.CyclotomicNorms.BB D.R.r (D.host.g 1)) →
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), IsRowAt D (D.nd.j i) σ → D.nd.goodRow σ →
    ∃ π : D.naut.CG D.R.r, IsCuspBaseChange D i σ π ∧
      ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
        (∃ r rb, IsGaloisRepOf D π l ι r ∧ IsReduction r rb) ∧
        ∀ r, IsGaloisRepOf D π l ι r →
          (∀ rb, IsReduction r rb → ResidIrred D l rb) ∧ TameAvoids D l ι r

end GlobalTheory.IndefiniteRowSideFullHecke.CongruenceMaxGalois

end
