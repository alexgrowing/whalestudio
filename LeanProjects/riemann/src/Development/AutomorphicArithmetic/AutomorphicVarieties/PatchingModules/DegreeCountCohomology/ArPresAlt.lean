import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.W

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime] {Lc : Loc} {G : Glob l Lc} {q d : ℕ}

structure ArPres (a : ArData G q d) (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] where
  S : Set (HeightOneSpectrum (𝓞 F))
  above : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S
  e : GS Ω S ≃ₜ* G.Γ
  e_ε : ∀ g, G.ε (e (toGS Ω S g)) = cycZ F Ω l g
  pl : ArData.W Lc q ≃ S
  pl_l : ∀ w, ((l : ℕ) : 𝓞 F) ∈ (pl w).1.asIdeal ↔ ∃ v, w = .inl v
  A : ArData.W Lc q → ValuationSubring Ω
  isOver : ∀ w, IsPlaceOver (A w) (pl w).1
  α : ∀ w, a.D w ≃ₜ* Dec (F := F) (A w)
  ι_eq : ∀ w g, a.ι w g = e (toGS Ω S (α w g : Formalism.ConjugateSelfDual.G F Ω))
  dv_eq : ∀ v, a.dv v = locDeg (pl (.inl v)).1
  ip : Fin d ≃ InfinitePlace F
  c : Fin d → Formalism.ConjugateSelfDual.G F Ω
  cc : ∀ i, IsCCAt (ip i) (c i)
  cw_eq : ∀ i, a.cw i = e (toGS Ω S (c i))

end UpperTheory.V.Pa
