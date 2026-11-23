import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem twtr_cont_of_mem (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) : Continuous ψ.1 :=
  GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level

theorem twtr_integrable (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {f : GA E n → ℂ} (hf : Continuous f) (x : GA E n) :
    Integrable (fun y : H E n 0 => φ y * f (x * y.1)) μ := by
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => μ.finiteAt_nhdsWithin x K⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hφ.1.mul (hf.comp (continuous_const.mul continuous_fst))
  · exact hφ.2.mul_right

end

theorem twTrEx_holds : TwTrEx := by
  intro E _ _ _ n _ D π hθ φ hφ hfin
  have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  obtain ⟨W, hWV, hWfd, hW⟩ := hfin
  have hth : ∀ ψ : π.V, ∃ ψ'' : Sm E n, ψ'' ∈ π.V ∧ ∀ g, ψ''.1 g = ψ.1.1 (thetaA E n g) := fun ψ => by
    obtain ⟨ψ'', h1, h2⟩ := hθ.2 ψ.1 ψ.2
    exact ⟨ψ'', h1, h2⟩
  have hInt : ∀ (ψ : π.V) (x : GA E n),
      Integrable (fun y : H E n 0 => φ y * ψ.1.1 (thetaA E n (x * y.1))) D.μ := by
    intro ψ x
    obtain ⟨ψ'', h1, h2⟩ := hth ψ
    have e : (fun y : H E n 0 => φ y * ψ.1.1 (thetaA E n (x * y.1))) = fun y => φ y * ψ''.1 (x * y.1) := by
      funext y
      rw [h2]
    rw [e]
    exact twtr_integrable D.μ hφ (twtr_cont_of_mem π h1) x
  have hK : ∀ ψ : π.V, ∃ ψ' : Sm E n, ψ' ∈ W ∧
      ∀ x, ψ'.1 x = ∫ y, φ y * ψ.1.1 (thetaA E n (x * y.1)) ∂D.μ := by
    intro ψ
    obtain ⟨ψ'', h1, h2⟩ := hth ψ
    obtain ⟨ψ', h3, h4⟩ := hW (fun _ => 1) continuous_const ψ'' h1
    refine ⟨ψ', h3, fun x => ?_⟩
    rw [h4 x]
    congr 1
    funext y
    simp only [mul_one, h2]
  choose Lf hLfW hLf using hK
  have hLfV : ∀ ψ, Lf ψ ∈ π.V := fun ψ => hWV (hLfW ψ)
  have hext : ∀ a b : π.V, (∀ x, a.1.1 x = b.1.1 x) → a = b := fun a b h =>
    Subtype.ext (Subtype.ext (funext h))
  obtain ⟨L, hL⟩ : ∃ L : π.V →ₗ[ℂ] π.V, ∀ ψ, (L ψ : Sm E n) = Lf ψ := by
    refine ⟨{ toFun := fun ψ => ⟨Lf ψ, hLfV ψ⟩, map_add' := ?_, map_smul' := ?_ }, fun _ => rfl⟩
    · intro ψ₁ ψ₂
      apply hext
      intro x
      show (Lf (ψ₁ + ψ₂)).1 x = (Lf ψ₁).1 x + (Lf ψ₂).1 x
      have hs : ∀ z, (ψ₁ + ψ₂).1.1 z = ψ₁.1.1 z + ψ₂.1.1 z := fun _ => rfl
      rw [hLf, hLf, hLf, ← integral_add (hInt ψ₁ x) (hInt ψ₂ x)]
      congr 1
      funext y
      rw [hs, mul_add]
    · intro c ψ
      apply hext
      intro x
      show (Lf (c • ψ)).1 x = c * (Lf ψ).1 x
      have hs : ∀ z, (c • ψ).1.1 z = c * ψ.1.1 z := fun _ => rfl
      rw [hLf, hLf, ← integral_const_mul]
      congr 1
      funext y
      rw [hs]
      ring
  have hrange : ∀ v ∈ LinearMap.range L, (v : Sm E n) ∈ W := by
    rintro v ⟨ψ, rfl⟩
    rw [hL]
    exact hLfW ψ
  let j : LinearMap.range L →ₗ[ℂ] W :=
    LinearMap.codRestrict W (π.V.subtype.comp (LinearMap.range L).subtype) (fun v => hrange v.1 v.2)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [j, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at h
    exact Subtype.ext (Subtype.ext h)
  have := hWfd
  have : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective j hj
  refine ⟨LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x),
    ⟨L, fun ψ x => by rw [hL]; exact hLf ψ x, inferInstance, rfl⟩, ?_⟩
  rintro t ⟨L', hL', _, rfl⟩
  have hLL : L' = L := by
    apply LinearMap.ext
    intro ψ
    apply hext
    intro x
    rw [hL' ψ x, hL ψ, hLf ψ x]
  subst hLL
  rfl

end DiscreteGroups.T1.G

end
