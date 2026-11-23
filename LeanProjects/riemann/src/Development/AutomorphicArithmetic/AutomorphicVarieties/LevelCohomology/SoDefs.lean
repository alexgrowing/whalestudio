import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.Base

namespace UpperTheory.V.X

section Dat

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O]

structure SoDat (S : Finset (HeightOneSpectrum (𝓞 k))) (e : ℕ) (ψ : G k Ω →* Oˣ)
    (Θ : GS Ω (S : Set (HeightOneSpectrum (𝓞 k))) →* Oˣ) : Prop where
  odd : l ≠ 2 ∨ IsTotallyComplex k
  above : ContainsAbove S l
  e_pos : 1 ≤ e
  opn : IsOpen (ψ.ker : Set (G k Ω))
  lift : Θ.comp (toGS Ω _) = Chr.Psi l (e + 1) ψ

def locSum (e : ℕ) (ψ : G k Ω →* Oˣ) (S : Finset (HeightOneSpectrum (𝓞 k))) (A : S → ValuationSubring Ω) : ℕ∞ :=
  ∑ v : S, Chr.h0 l e ψ (Dec (F := k) (A v))

end Dat

section Lev

variable {O : Type} [CommRing O]

def Lev (a : O) : Type := O ⧸ Ideal.span {a}

instance (a : O) : AddCommGroup (Lev a) := inferInstanceAs (AddCommGroup (O ⧸ Ideal.span {a}))
instance (a : O) : Module O (Lev a) := inferInstanceAs (Module O (O ⧸ Ideal.span {a}))
instance (a : O) : TopologicalSpace (Lev a) := ⊥
instance (a : O) : DiscreteTopology (Lev a) := ⟨rfl⟩

def Lev.mk (a : O) : O →ₗ[O] Lev a := (Ideal.span {a} : Submodule O O).mkQ

theorem Lev.mk_surjective (a : O) : Function.Surjective (Lev.mk a) := Submodule.mkQ_surjective _

theorem Lev.mk_eq_zero (a x : O) : Lev.mk a x = 0 ↔ a ∣ x :=
  (Submodule.Quotient.mk_eq_zero _).trans Ideal.mem_span_singleton

variable {Γ M : Type} [Group Γ] [AddCommGroup M] [Module O M]

structure IsLev (a : O) (θ : Γ →* Oˣ) (ρ : Representation O Γ M) : Prop where
  ne : a ≠ 0
  cyc : Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a}))
  act : ∀ g m, ρ g m = (θ g : O) • m

theorem isLev_lev {a : O} (ha : a ≠ 0) (θ : Γ →* Oˣ) : IsLev a θ (scalRep (Lev a) θ) := ⟨ha, ⟨LinearEquiv.refl O _⟩, fun g m => scalRep_apply (Lev a) θ g m⟩

theorem IsLev.comp {a : O} {θ : Γ →* Oˣ} {ρ : Representation O Γ M} (h : IsLev a θ ρ) {D : Type} [Group D] (φ : D →* Γ) :
    IsLev a (θ.comp φ) (ρ.comp φ : Representation O D M) := ⟨h.ne, h.cyc, fun g m => h.act (φ g) m⟩

def Coc (θ : Γ →* Oˣ) (z : Γ → O) : Prop := ∀ g h, z (g * h) = z g + (θ g : O) * z h

def CobOn (θ : Γ →* Oˣ) (z : Γ → O) (D : Subgroup Γ) : Prop :=
  ∃ a : O, a ≠ 0 ∧ ∃ m : O, ∀ g ∈ D, a * z g = (θ g : O) * m - m

theorem CobOn.mono {θ : Γ →* Oˣ} {z : Γ → O} {D D' : Subgroup Γ} (h : CobOn θ z D) (hD : D' ≤ D) : CobOn θ z D' := by
  obtain ⟨a, ha, m, hm⟩ := h
  exact ⟨a, ha, m, fun g hg => hm g (hD hg)⟩

theorem cobOn_of_eq_zero [Nontrivial O] (θ : Γ →* Oˣ) {z : Γ → O} {D : Subgroup Γ} (h : ∀ g ∈ D, z g = 0) : CobOn θ z D :=
  ⟨1, one_ne_zero, 0, fun g hg => by simp [h g hg]⟩

end Lev

section Add

variable {R R' Γ N W : Type} [CommRing R] [CommRing R'] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  [AddCommGroup W] [Module R' W] [TopologicalSpace W] [DiscreteTopology W]
  (τ : Representation R Γ N) (σ : Representation R' Γ W) (ι : N →+ W) (h : ∀ g n, ι (τ g n) = σ g (ι n))

def cocycleMapOfEquivariant : Z1 τ →+ Z1 σ where
  toFun z := ⟨fun g => ι (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g g' => by
    simp only [z.2.2 g g', map_add, h]⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero ι)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add ι _ _)

def h1MapOfAdditive : H1 τ →+ H1 σ :=
  QuotientAddGroup.map ((B1 τ).comap (Z1 τ).subtype).toAddSubgroup ((B1 σ).comap (Z1 σ).subtype).toAddSubgroup
    (cocycleMapOfEquivariant τ σ ι h) fun z hz => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 τ _).1 hz
      exact (mem_coboundaries1 σ _).2 ⟨ι m, fun g => (congrArg ι (hm g)).trans (by rw [map_sub, h])⟩

theorem h1MapOfAdditive_mk (z : Z1 τ) :
    h1MapOfAdditive τ σ ι h (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cocycleMapOfEquivariant τ σ ι h z) := rfl

end Add

end UpperTheory.V.X

end
