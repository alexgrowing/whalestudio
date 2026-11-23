import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAlgebraicModularFormMulArchInvariantStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tyStep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.KerOpen → UpperTheory.Gal.Gen.CharSum → UpperTheory.Gal.Gen.TwistPart → UpperTheory.Gal.Gen.TyStep := by
  intro hLev hEll hKer hCS hTw E _ _ _ l _ ι a w₀ hs K hK W J hJo hJc htf m θ f hf
  classical
  obtain ⟨hLvl, -, hC, -, -, -⟩ := hLev E a w₀ hs K hK J hJo hJc
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (l ^ m))) :=
    inferInstanceAs (Finite (ZMod (l ^ m)))
  let lam : (lev K w₀ J) →* Multiplicative (ZMod (l ^ m)) :=
    θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2)
  have hlam : ∀ c : lev K w₀ J, lam c = θ ⟨cLoc w₀ c.1, hC c.1 c.2⟩ := fun c => rfl
  obtain ⟨N, hNo, hN1, hN⟩ := hKer E w₀ a J hJo _ θ
  obtain ⟨ℓ, hℓi, hℓC, hℓa⟩ := hEll E a (lev K w₀ J) hLvl _ lam
    ⟨cLoc w₀ ⁻¹' N, hNo.preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀), by simpa using hN1,
      fun c hc => hN ⟨cLoc w₀ c.1, hC c.1 c.2⟩ hc⟩
    (fun c hc => by
      obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
      have h1 : (cLoc w₀ c.1) ^ k = 1 := by
        have h0 : c.1 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← map_pow, h0, map_one]
      have h2 := htf _ (hC c.1 c.2) k hk0 h1
      have h3 : (⟨cLoc w₀ c.1, hC c.1 c.2⟩ : J) = 1 := Subtype.ext h2
      rw [hlam, h3, map_one])
  obtain ⟨s, hs1, hs2⟩ := hCS (l ^ m)
  have hex : ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ,
      ∃ F : algForms W, ∀ v g, F.1 v g = ((χ (ℓ g) : ℂˣ) : ℂ) * f.1 v g := fun χ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => ((χ (ℓ g) : ℂˣ) : ℂ)) (hℓa fun y => ((χ y : ℂˣ) : ℂ))
      fun g x hx => by simp only [hℓi g x hx]
  choose F hF using hex
  have hpart : ∀ χ ∈ s, F χ ∈ part W K
      (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ GlobalTheory.CongW.HasTypeVec w₀ K J θ χ U) := by
    intro χ hχ
    have h := hTw E a w₀ K W J _ θ χ hC (fun k hk => hK.one k hk w₀ (not_apart_self w₀)) (F χ)
      (fun c hc v g => by
        rw [hF, hF, hℓC g ⟨c, hc⟩, hf c hc v g, map_mul, Units.val_mul, hlam, mul_comm (((χ (ℓ g) : ℂˣ) : ℂ))]
        ring)
    refine (?_ : part W K _ ≤ part W K _) h
    exact iSup₂_le fun π hπ => le_iSup₂_of_le π ⟨χ, hs1 χ hχ, hπ⟩ le_rfl
  refine ⟨-∑ χ ∈ s, F χ, neg_mem (sum_mem hpart), fun g => 1 + ∑ χ ∈ s, ((χ (ℓ g) : ℂˣ) : ℂ), ?_, ?_⟩
  · intro g
    rcases hs2 (ℓ g) with h | h
    · simp only [h, map_zero, norm_zero]
      positivity
    · simp only [h]
      rw [map_natCast, Nat.cast_pow, norm_pow]
  · intro v g
    have e : ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = -∑ χ ∈ s, (F χ).1 v g := by
      simp [Finset.sum_apply, LinearMap.sum_apply]
    change f.1 v g - ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = _
    rw [e, Finset.sum_congr rfl fun χ _ => hF χ v g, ← Finset.sum_mul]
    ring
