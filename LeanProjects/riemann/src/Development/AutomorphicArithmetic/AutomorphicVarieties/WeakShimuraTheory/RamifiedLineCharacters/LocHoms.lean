import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CharRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rescale {l : ℕ} [Fact l.Prime] (a : ZMod (l ^ 1)) (ha : a ≠ 0) : ∃ b : ZMod (l ^ 1), b * a = 1 := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  exact ⟨a⁻¹, inv_mul_cancel₀ ha⟩

theorem UpperTheory.V.Ws.Gys.locHoms :
    LocalTateDuality → LocalEulerChar → UnramifiedOrthogonality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) →
      ∃ φ₁ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), ∃ φ₂ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))),
        (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ₁ g = 0) ∧ (∃ g, φ₁ g = 1) ∧ ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ₂ g = 1 := by
  intro hT hE hU F Ω _ _ _ _ _ l _ A v hA hl hμ
  obtain ⟨f, hf, hf0⟩ := UpperTheory.V.Ws.Gys.locNe hT hE F Ω l A v hA hl hμ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) := Representation.trivial _ _ _
  let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
  have hχ : ∀ g, χ g = 1 := fun g => hμ g.1 g.2
  have hc : ContAction ρ := continuous_snd
  obtain ⟨hU1, hU2⟩ := hU F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hl (fun _ _ => rfl) hc
  have hinj := (hT F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hc).2.2.1.1
  let T : ZMod (l ^ 1) → TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) := fun t => TDual.mk (LinearMap.mul _ _ t)
  have htriv : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), twDual χ ρ g m = m := fun g m => by
    ext t
    rw [twDual_apply, hχ, Units.val_one, one_mul]
    rfl
  let y : Z1 (twDual χ ρ) := ⟨fun g => T (f g), (continuous_of_discreteTopology (f := T)).comp hf.1, fun g h => by
    rw [htriv]
    ext m
    change f (g * h) * m = f g * m + f h * m
    rw [hf.2, add_mul]
    rfl⟩
  have hy : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), y.1 g = twDual χ ρ g m - m → f g = 0 := fun g m h => by
    rw [htriv, sub_self] at h
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) => φ 1) h
    change f g * 1 = 0 at h1
    rwa [mul_one] at h1
  have ha : ∃ φ ∈ Z1 ρ, (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ g = 0) ∧ φ ≠ 0 := by
    by_contra H
    push Not at H
    refine hf0 (H f hf fun g hg => ?_)
    have h := (hU2 (Submodule.Quotient.mk y)).2 fun x hx => by
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      have : x = 0 := Subtype.ext (H x.1 x.2 fun g hg => (hm ⟨g, hg⟩).trans (sub_self _))
      rw [this]
      exact map_zero _
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact hy g m (hm ⟨g, hg⟩)
  have hb : ∃ φ ∈ Z1 ρ, ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ g ≠ 0 := by
    by_contra H
    push Not at H
    have hyu : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) ∈
        H1ur (twDual χ ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun j => ?_⟩)
      rw [map_zero, sub_zero]
      ext m
      change f j.1 * m = 0
      rw [H f hf j.1 j.2, zero_mul]
    have h0 : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) = 0 := by
      refine hinj ?_
      refine Eq.trans ?_ (map_zero _).symm
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      exact (hU1 (Submodule.Quotient.mk x)).1
        ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2
          ⟨0, fun j => (H x.1 x.2 j.1 j.2).trans (sub_self _).symm⟩)) _ hyu
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact hf0 (funext fun g => hy g m (hm g))
  obtain ⟨φ₁, h₁, hI, hne⟩ := ha
  obtain ⟨φ₂, h₂, g₂, hg₂, hne₂⟩ := hb
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 hne
  obtain ⟨b₁, e₁⟩ := rescale _ hg₁
  obtain ⟨b₂, e₂⟩ := rescale _ hne₂
  refine ⟨b₁ • φ₁, Submodule.smul_mem _ _ h₁, b₂ • φ₂, Submodule.smul_mem _ _ h₂, fun g hg => ?_, ⟨g₁, e₁⟩, g₂, hg₂, e₂⟩
  rw [Pi.smul_apply, hI g hg, smul_zero]
