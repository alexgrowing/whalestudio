import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.Wt.famOf_of : ExpBasic → PevExp → SqExp → TopUp → WExp → FamOfA → FamOf := by
  intro hB hP hS hT hW hA E _ _ _ a τ C hC n hn W Q _ f hf P
  obtain ⟨hLe, hGe, hmono, -, hconst, -⟩ := hB
  obtain ⟨d₀, hd₀⟩ := hW E a τ W
  refine ⟨Finset.univ.sup (fun q => (P q).totalDegree) + d₀, fun ν X => ?_⟩
  have hsum : ∀ (T : Submodule ℂ (Circle → ℂ)) (F : Q → Circle → ℂ), (∀ q, F q ∈ T) → (fun z => ∑ q, F q z) ∈ T := by
    intro T F h
    have : (fun z => ∑ q, F q z) = ∑ q, F q := by funext z; simp [Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun q _ => h q
  refine ⟨(hA E a τ C hC n hn W ν Q f P X).1, ?_, ?_, ?_, ?_, ?_, (hA E a τ C hC n hn W ν Q f P X).2⟩
  · intro k hk y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.lev k hk]
    exact Finset.sum_congr rfl fun q _ => by rw [hf q k hk]
  · intro x y₁ y₂ v
    funext g
    rw [RU_apply, famOf_apply, famOf_apply, hn.inf x x.2]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [(f q).2.2 x v, RU_apply, mul_assoc (n g), mul_assoc (n g)]
  · intro b hb y₁ y₂ v
    funext g
    rw [Pi.smul_apply, famOf_apply, famOf_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : delta ν (X q * (n g * (y₁ * b))) = chi ν b * delta ν (X q * (n g * y₁)) := by
      have e : X q * (n g * (y₁ * b)) = X q * (n g * y₁) * b := by simp only [mul_assoc]
      unfold delta
      rw [e, map_mul, Module.End.mul_apply, hT a ν b hb, map_smul, map_smul, smul_eq_mul]
    rw [this]; ring
  · intro k x hx y₁ y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).1
    have h2 : (fun z => delta ν (X q * (n g * (tor a k z * y₁)))) ∈ ExpLe (psum ν k) := by
      have := (hS a k ν (sqRep ℂ a ν y₁ (top ν)) ((ev1 ν) ∘ₗ (sqRep ℂ a ν (X q * n g)))).1
      refine (congrArg (· ∈ ExpLe (psum ν k)) (funext fun z => ?_)).mpr this
      rw [delta, LinearMap.comp_apply, ← mul_assoc (X q), map_mul (sqRep ℂ a ν) (X q * n g), map_mul (sqRep ℂ a ν) (tor a k z),
        Module.End.mul_apply, Module.End.mul_apply]
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).1
    refine (hmono _ _ ?_).1 (hLe _ _ _ _ (hLe _ _ _ _ h1 h2) h3)
    have : (P q).totalDegree ≤ Finset.univ.sup (fun q => (P q).totalDegree) :=
      Finset.le_sup (f := fun q => (P q).totalDegree) (Finset.mem_univ q)
    push_cast
    omega
  · intro k x hx y₂ v g
    simp only [famOf_apply]
    refine hsum _ _ fun q => ?_
    have h1 := (hP a k (P q) (n g) y₂).2
    have h2 := (hconst (delta ν (X q * (n g * 1)))).2
    have h3 := (hd₀ k x hx v ((LinearMap.proj g) ∘ₗ (f q).1)).2
    refine (hmono _ _ ?_).2 (hGe _ _ _ _ (hGe _ _ _ _ h1 h2) h3)
    push_cast
    omega
