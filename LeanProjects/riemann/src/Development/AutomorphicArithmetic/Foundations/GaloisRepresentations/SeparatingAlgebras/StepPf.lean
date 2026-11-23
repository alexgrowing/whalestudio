import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenSubgroupCharacterKernel
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.step_pf :
    UpperTheory.Gal.Gen.SmoothAt → UpperTheory.Gal.Gen.Tower → UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.CountGen → UpperTheory.Gal.Gen.StepCore → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Step := by
  intro hSm hTw hLev hEll hCG hSC hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf
  obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs W f
  obtain ⟨J, hJ, hJN, htf, hpow⟩ := hTw E w₀ a l (Fact.out) hl ha N hN
  obtain ⟨n, hfd, hcard⟩ := hCG E a w₀ hs K hK J hJ W S Φ hS
  obtain ⟨lv0, mem0, inJ0, -, sec0, tr0⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  obtain ⟨-, memn, inJn, -, -, -⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  haveI hnorm : ((J n).subgroupOf (J 0)).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hJ.normal n g.1 g.2 x.1 hx⟩
  haveI : CompactSpace (J 0) := isCompact_iff_compactSpace.1 (hJ.compact 0)
  haveI hfin : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) :=
    Subgroup.quotient_finite_of_isOpen _ ((hJ.isOpen n).preimage continuous_subtype_val)
  have hp : IsPGroup l (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hpow n x.1 x.2
  let φ : lev K w₀ (J 0) →* J 0 :=
    ((cLoc w₀).comp (lev K w₀ (J 0)).subtype).codRestrict (J 0) (fun c => inJ0 c.1 c.2)
  let lam : lev K w₀ (J 0) →* (J 0 ⧸ (J n).subgroupOf (J 0)) := (QuotientGroup.mk' _).comp φ
  have hlam : ∀ c : lev K w₀ (J 0), lam c = 1 ↔ cLoc w₀ c.1 ∈ J n := fun c => by
    change ((φ c : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective lam := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, hxy⟩ := sec0 y.1
    have hxC : x ∈ lev K w₀ (J 0) :=
      (mem0 x).2 ⟨1, one_mem _, x, hx, hxy ▸ y.2, (one_mul x).symm⟩
    refine ⟨⟨x, hxC⟩, ?_⟩
    change ((φ ⟨x, hxC⟩ : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = _
    congr 1
    exact Subtype.ext hxy
  have hle : lev K w₀ (J n) ≤ lev K w₀ (J 0) := fun c hc => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (memn c).1 hc
    exact (mem0 _).2 ⟨k, hk, x, hx, hJ.anti (Nat.zero_le n) hxJ, rfl⟩
  have hiff : ∀ c : lev K w₀ (J 0), c.1 ∈ lev K w₀ (J n) ↔ lam c = 1 := fun c => by
    rw [hlam]
    exact ⟨inJn c.1, tr0 (J n) c.1 c.2⟩
  obtain ⟨ℓ, hℓ₁, hℓ₂, hℓ₃⟩ := hEll E a (lev K w₀ (J 0)) lv0 _ lam
    ⟨cLoc w₀ ⁻¹' (J n : Set (GL (Fin a) (w₀.adicCompletion E))), (hJ.isOpen n).preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀),
      by simp [one_mem], fun c hc => (hlam c).2 hc⟩
    (fun c hc => by
      have h1 : cLoc w₀ c.1 = 1 :=
        htf _ (inJ0 c.1 c.2) (MonoidHom.isOfFinOrder ((cLoc w₀).comp (lev K w₀ (J 0)).subtype) hc)
      exact (hlam c).2 (h1 ▸ one_mem _))
  have hfC : f ∈ fixedBy W (lev K w₀ (J 0)) := fun c hc v g => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (mem0 c).1 hc
    rw [← mul_assoc, hfN x hx (hJN hxJ) v (g * k)]
    exact hf k hk v g
  obtain ⟨G, hG, e, he, hfe⟩ := hSC E l ι a W (lev K w₀ (J 0)) (lev K w₀ (J n)) lv0.fin _ hp lam hsurj hle hiff
    ℓ hℓ₁ hℓ₂ hℓ₃ (fun U => ∀ w ∈ S, GenAt w (Φ w) U) hfd hcard f hfC
  exact ⟨G, (hPF E a W (lev K w₀ (J n)) _).2.2.1 K le_sup_left hG, e, he, hfe⟩
