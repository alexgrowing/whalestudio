import Formalism.GaloisCohomology.Statement
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

namespace UpperTheory.V.LDataCardLeFinrank

section

variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]

def decImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Dec (F := F) A).map (cycZ F Ω l)

def ineImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Ine (F := F) A).map (cycZ F Ω l)

theorem ineImage_le_decImage (A : ValuationSubring Ω) : ineImage F l A ≤ decImage F l A := Subgroup.map_mono (Ine_le_Dec A)

variable (Ω) in

def qzG (e : ℤ) : Representation ℤ_[l] (G F Ω) (QZ l) := scalRep (QZ l) (cycZ F Ω l ^ (-e))

variable {F l}

theorem qzG_apply (e : ℤ) (g : G F Ω) (x : QZ l) :
    qzG F Ω l e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := rfl

theorem qzTw_comp_toGS (D : LData F Ω l) (e : ℤ) : (qzTw D e).comp (toGS Ω _) = qzG F Ω l e := by
  ext g x
  simp [qzG, qzTw, scalRep, ← D.hchi]

end

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

def ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) : Submodule R (H1 ρ) :=
  (⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∈ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val)) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val)

theorem mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (x : H1 ρ) :
    x ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val x = 0) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val x = 0 := by
  simp only [ShaAbs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem resH1_mk_eq_zero_iff_coboundary (ρ : Representation R (G F Ω) M) (z : Z1 ρ) (H : Subgroup (G F Ω)) :
    resH1 ρ H.subtype continuous_subtype_val (Submodule.Quotient.mk z) = 0 ↔
      ∃ m, ∀ g ∈ H, z.1 g = ρ g m - m := by
  simp [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_coboundaries1, restrictCocycles1]

theorem mk_mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Dec (F := F) A, z.1 g = ρ g m - m) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Ine (F := F) A, z.1 g = ρ g m - m := by
  simp only [mem_ShaAbs, resH1_mk_eq_zero_iff_coboundary]

end

def shaInv (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (e : ℤ) : ℕ∞ :=
  Module.length ℤ_[l] (ShaAbs (qzG F (AlgebraicClosure F) l e) (Above F l))

def levelDec (l N : ℕ) : Subgroup (ZMod N)ˣ :=
  (Subgroup.closure {u : (ZMod (ordCompl[l] N))ˣ | (u : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N))}).comap
    (ZMod.unitsMap (Nat.ordCompl_dvd N l))

def nuBound (l N e : ℕ) : ℕ :=
  if l ∣ N ∨ l - 1 ∣ e then max (N.factorization l) (if l = 2 then 2 else 1) + e.factorization l else 0

end UpperTheory.V.LDataCardLeFinrank

end
