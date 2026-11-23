import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.rkTransport :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ),
      XRk l N (cycU l (⊤ : Subgroup (G K Ω))) r ↔ XRk l N (cycU l (galOf F K Ω)) r := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ N r
  obtain ⟨hDI, -, -, -⟩ := galEmbFam F K Ω l
  obtain ⟨hE, -, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := K) A :=
    fun A σ => by rw [← (hDI A).1]; rfl
  have hI : ∀ (A : ValuationSubring Ω) (σ : G K Ω), galEmb F K Ω σ ∈ Ine (F := F) A ↔ σ ∈ Ine (F := K) A :=
    fun A σ => by rw [← (hDI A).2]; rfl
  have hle : cycU l (galOf F K Ω) ≤ galOf F K Ω := inf_le_left
  let e : cycU l (⊤ : Subgroup (G K Ω)) → cycU l (galOf F K Ω) :=
    fun u => ⟨galEmb F K Ω u.1, galEmb_mem F K Ω u.1, u.2.2⟩
  let e' : cycU l (galOf F K Ω) → cycU l (⊤ : Subgroup (G K Ω)) :=
    fun u => ⟨toGal K hle u, trivial, u.2.2⟩
  have hee : ∀ u, e (e' u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have hee' : ∀ u, e' (e u) = u := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl)
  have he : Continuous e := (hE.continuous.comp continuous_subtype_val).subtype_mk _
  have he' : Continuous e' := by
    refine Continuous.subtype_mk ?_ _
    exact hE.continuous_iff.2 continuous_subtype_val
  have hm : ∀ a b, e (a * b) = e a * e b := fun a b => Subtype.ext (map_mul (galEmb F K Ω) a.1 b.1)
  have hm' : ∀ a b, e' (a * b) = e' a * e' b := fun a b => Subtype.ext (map_mul (toGal K hle) a b)
  constructor
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e, φ.2.1.comp_continuous he,
      fun a b => by simp only [Function.comp, hm]; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e u) ((hI A u.1).2 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e u) ((hD A u.1).2 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e' u)
    simpa only [Function.comp, hee] using this
  · intro h
    refine CardLe.of_injective h (fun φ => ⟨φ.1 ∘ e', φ.2.1.comp_continuous he',
      fun a b => by simp only [Function.comp, hm']; exact φ.2.2.1 _ _,
      fun A u hu => φ.2.2.2.1 A (e' u) ((hI A (e' u).1).1 hu),
      fun A hA u hu => φ.2.2.2.2 A hA (e' u) ((hD A (e' u).1).1 hu)⟩) fun φ ψ hh => Subtype.ext (funext fun u => ?_)
    have := congrFun (congrArg Subtype.val hh) (e u)
    simpa only [Function.comp, hee'] using this
