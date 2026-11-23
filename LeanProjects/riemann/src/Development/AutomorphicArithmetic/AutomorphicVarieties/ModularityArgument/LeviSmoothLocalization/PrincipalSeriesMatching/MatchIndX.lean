import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.MatchIndOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

open private absNorm_pow exists_over finite_above pick pick_spec sat_unique sat_card bound_cx
  cnt_zero cnt_zero_of_unr exists_bad unrAt_iff ind_key Key Key.sat key_twist norm_units
  from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.MatchIndOf
open private pol_one cnt_of_pol comp_cancel from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

private theorem indCore [IsTotallyComplex K] [IsTotallyComplex M]
    (h2 : Module.finrank K M = 2) (P : CuspSub K (2 * 2)) (π : CuspSub M 2) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hkey : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S → Key (CG.mk π).HasSat (CG.mk P).HasSat w)
    (hK : GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S)
    (hM : ∀ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M, w.under (𝓞 K) ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (sK : ∀ u : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (u.adicCompletion K)))
    (sM : ∀ w : HeightOneSpectrum (𝓞 M), Multiset (IrrGL (w.adicCompletion M)))
    (hsK : ∀ u, SuppAt P u (sK u)) (hsM : ∀ w, SuppAt π w (sM w))
    (zK : ∀ u ∈ S, u ≠ v → cnt (sK u) 1 = 0)
    (zM : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∈ S → w.under (𝓞 K) ≠ v → cnt (sM w) 1 = 0) :
    pol (sK v) 1 = ∏ w : PlacesOver M v, (pol (sM w.1) 1).comp (X ^ fdeg w) := by
  have hOps := pairGOps
  have hCross : CrossG := crossGOf Inf.expAlg Inf.expIndep secDiff
  obtain ⟨cP, hcP⟩ := satBd K (2 * 2) P
  obtain ⟨cπ, hcπ⟩ := satBd M 2 π
  have hfin := finite_above (M := M) (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet
  obtain ⟨SM, memSM⟩ : ∃ SM : Finset (HeightOneSpectrum (𝓞 M)), ∀ w, w ∈ SM ↔ w.under (𝓞 K) ∈ S :=
    ⟨hfin.toFinset, fun w => by rw [Set.Finite.mem_toFinset]; rfl⟩
  obtain ⟨BK, hBK⟩ : ∃ BK, BK = pick (CG.mk P).HasSat := ⟨_, rfl⟩
  obtain ⟨BM, hBM⟩ : ∃ BM, BM = pick (CG.mk π).HasSat := ⟨_, rfl⟩
  have satK : ∀ p ∉ S, (CG.mk P).HasSat p (BK p) := fun p hp => by
    obtain ⟨w, rfl⟩ := exists_over (M := M) p
    rw [hBK]
    obtain ⟨B, h⟩ := (Key.sat (hkey w hp)).2
    exact pick_spec h
  have satM : ∀ w ∉ SM, (CG.mk π).HasSat w (BM w) := fun w hw => by
    rw [hBM]
    obtain ⟨B, h⟩ := (Key.sat (hkey w fun h => hw ((memSM w).2 h))).1
    exact pick_spec h
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨β, hβ, pK⟩ := sideX K (2 * 2) (by norm_num) P S hK BK satK sK _ (fun _ => 1) hq
    fun u hu => ⟨hsK u, fun h => by
      rw [pow_one, not_not.1 fun e => h (zK u hu e)]⟩
  obtain ⟨β', hβ', pM⟩ := sideX M 2 le_rfl π SM (fun w hw => (memSM w).2 (hM w hw)) BM satM sM _
    (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq fun w hw => ⟨hsM w, fun h => by
      have e : w.under (𝓞 K) = v := not_not.1 fun e => h (zM w ((memSM w).1 hw) e)
      rw [← e]
      exact absNorm_pow w⟩
  obtain ⟨c, hc⟩ := regroup K M h2 (S : Set (HeightOneSpectrum (𝓞 K))) (SM : Set (HeightOneSpectrum (𝓞 M))) (cx BK) (cx BM)
    (max cP cπ) 4 (fun w => by simpa using memSM w)
    (fun p hp => by
      have hs := satK p (by simpa using hp)
      refine ⟨by simp [cx, sat_card P hs], bound_cx p (le_max_left cP cπ) (hcP p _ hs)⟩)
    (fun w hw => by
      have hs := satM w (by simpa using hw)
      refine ⟨by simp [cx, sat_card π hs], bound_cx w (le_max_right cP cπ) (hcπ w _ hs)⟩)
    (fun w hw => by
      have hw₁ : w ∉ SM := by simpa using hw
      have hw' : w.under (𝓞 K) ∉ S := fun h => hw₁ ((memSM w).2 h)
      have s1 := satK _ hw'
      have s2 := satM w hw₁
      rcases hkey w hw' with ⟨hN, w', hne, hu, B, B', h1, h3, h4⟩ | ⟨hN, B, B', h1, h3, h4⟩
      · left
        refine ⟨hN, w', hne, hu, ?_⟩
        have s3 := satM w' fun h => hw' (hu ▸ (memSM w').1 h)
        rw [cx, cx, cx, sat_unique P s1 h4, sat_unique π s2 h1, sat_unique π s3 h3, Multiset.map_add]
      · right
        refine ⟨hN, B'.map fun b : ℂˣ => (b : ℂ), ?_, ?_⟩
        · rw [cx, sat_unique π s2 h1, Multiset.map_map, Multiset.map_map]
          exact Multiset.map_congr rfl fun b _ => by simp
        · rw [cx, sat_unique P s1 h4, h3, Multiset.map_add, Multiset.map_map, Multiset.map_map]
          congr 1)
  have pM' := hOps.2.2.1 _ _ _ _ _ _ _ c pM (fun s hs => ((hc s).1 hs).symm) (fun s hs => ((hc s).2 hs).symm)
  have e1 : ∏ w ∈ SM, (pol (sM w) 1).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal) =
      ∏ w : PlacesOver M v, (pol (sM w.1) 1).comp (X ^ fdeg w) := by
    have hsub : (Finset.univ : Finset (PlacesOver M v)).map (Function.Embedding.subtype _) ⊆ SM := fun w hw => by
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hw
      have : w.1.under (𝓞 K) = v := HeightOneSpectrum.ext w.2.over.symm
      exact (memSM w.1).2 (by rw [this]; exact hv)
    rw [← Finset.prod_subset hsub (fun w hw hw' => ?_), Finset.prod_map]
    · rfl
    · rw [pol_one _ (zM w ((memSM w).1 hw) fun e => hw' ?_), one_comp]
      exact Finset.mem_map.2 ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal e.symm⟩⟩, Finset.mem_univ _, rfl⟩
  have e2 : ∏ u ∈ S, (pol (sK u) 1).comp (X ^ 1) = pol (sK v) 1 := by
    rw [Finset.prod_eq_single_of_mem v hv (fun u hu hne => by rw [pol_one _ (zK u hu hne), one_comp]), pow_one, comp_X]
  rw [e1] at pM'
  rw [e2] at pK
  refine hCross _ _ _ _ _ _ _ (by exact_mod_cast hq) hβ hβ' ((polFacts _).2.2.2 _ 1).1 ?_ pK pM'
  rw [eval_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [eval_comp, eval_pow, eval_X, zero_pow (normVal K M v w 1).2.2.1.ne']
  exact ((polFacts _).2.2.2 _ 1).1

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.matchIndX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.MatchIndX := by
  intro K M _ _ _ _ _ _ _ h2 P π hI v s s' hs hs' θ hθ
  obtain ⟨S₁, hkey⟩ := ind_key h2 _ _ hI
  obtain ⟨⟨T, hT⟩, -⟩ := norm_units h2
  have FK := suppFacts K (2 * 2) (by norm_num) P
  have FM := suppFacts M 2 (by norm_num) π
  choose sK hsK using fun u => (FK u).1
  choose sM hsM using fun w => (FM w).1
  choose bK hbK using fun u => exists_bad (sK u)
  choose bM hbM using fun w => exists_bad (sM w)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S₀ ↔ u = v ∨ u ∈ S₁ ∨ u ∈ T ∨
      u ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∨
      ∃ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M, w.under (𝓞 K) = u :=
    ⟨insert v (S₁ ∪ (T ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∪
      (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces M).image fun w => w.under (𝓞 K)))), fun u => by simp⟩
  obtain ⟨χ, hχv, hχ⟩ := globTw K M v θ hθ S₀ bK bM
  obtain ⟨ξ, hξ⟩ := normLoc K M χ
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ χ.UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset, fun u => by simp⟩
  choose tK htK using fun u => suppTw K (2 * 2) (by norm_num) P u χ _ (hsK u)
  choose tM htM using fun w => suppTw M 2 (by norm_num) π w ξ _ (hsM w)
  have k₀ : ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∉ S₀ → Key (CG.mk π).HasSat (CG.mk P).HasSat w :=
    fun w hw => hkey w fun h => hw ((hS₀ _).2 (Or.inr (Or.inl h)))
  have main := indCore h2 (P.twist χ) (π.twist ξ) S
    (fun w hw => key_twist h2 χ ξ (fun w hu => (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).2.1 hu)
      (not_not.1 fun h => hw ((hS _).2 (Or.inr h))) (k₀ w fun h => hw ((hS _).2 (Or.inl h))))
    (fun u hu => (hS _).2 (Or.inl ((hS₀ _).2 (by tauto))))
    (fun w hw => (hS _).2 (Or.inl ((hS₀ _).2 (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩)))))))
    v ((hS _).2 (Or.inl ((hS₀ _).2 (Or.inl rfl)))) tK tM (fun u => (htK u).1) (fun w => (htM w).1)
    (fun u hu hne => by
      have e : cnt (tK u) 1 = cnt (sK u) (χ.loc u * 1) := cnt_of_pol ((htK u).2.1 1)
      rw [e, mul_one]
      by_cases h0 : u ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ u h0 hne).1 ζ (hbK u ζ hζ hy)
      · obtain ⟨w, rfl⟩ := exists_over (M := M) u
        obtain ⟨B, hB⟩ := (Key.sat (k₀ w h0)).2
        exact cnt_zero_of_unr _ _ ((FK _).2.2.2.1 _ B (hsK _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2 h))
    (fun w hu hne => by
      have e : cnt (tM w) 1 = cnt (sM w) (ξ.loc w * 1) := cnt_of_pol ((htM w).2.1 1)
      rw [e, mul_one, (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 K) ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ _ h0 hne).2 ⟨w, ⟨rfl⟩⟩ ζ (hbM w ζ hζ hy)
      · obtain ⟨B, hB⟩ := (Key.sat (k₀ w h0)).1
        exact cnt_zero_of_unr _ _ ((FM _).2.2.2.1 _ B (hsM _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2
            (hT _ (fun h' => h0 ((hS₀ _).2 (by tauto))) _ _ (GlobalTheory.HeckeComp.smooth_loc χ _) h)))
  obtain ⟨μ, hμ, hχθ⟩ : ∃ μ, IsUnram μ ∧ χ.loc v = θ * μ :=
    ⟨χ.loc v * θ⁻¹, hχv, by rw [mul_comm (χ.loc v), mul_inv_cancel_left]⟩
  obtain ⟨a, ha⟩ : ∃ a : ℂˣ, a = μ (unif (v.adicCompletion K)) := ⟨_, rfl⟩
  have eL : pol (tK v) 1 = (pol s θ).comp (C (a : ℂ) * X) := by
    rw [(htK v).2.1, (FK v).2.1 _ _ (hsK v) hs, ha, ← ((polFacts _).2.2.2 s _).2.2.2 μ hμ, hχθ, mul_one]
  have eR : ∀ w : PlacesOver M v, (pol (tM w.1) 1).comp (X ^ fdeg w) =
      ((pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w)).comp (C (a : ℂ) * X) := fun w => by
    obtain ⟨n1, n2⟩ := (normVal K M v w μ).1 hμ
    have e0 : pol (tM w.1) 1 = (pol (s' w) (θ.comp (nm w))).comp (C ((a : ℂ) ^ fdeg w) * X) := by
      have e1 : (θ * μ).comp (nm w) = θ.comp (nm w) * μ.comp (nm w) := rfl
      have e2 : (((μ.comp (nm w)) (unif (w.1.adicCompletion M)) : ℂˣ) : ℂ) = (a : ℂ) ^ fdeg w := by
        rw [MonoidHom.comp_apply, n2, ← ha, Units.val_pow_eq_pow_val]
      rw [(htM w.1).2.1, (hξ v w).1, (FM w.1).2.1 _ _ (hsM w.1) (hs' w), mul_one, hχθ, e1,
        ((polFacts _).2.2.2 _ _).2.2.2 _ n1, e2]
    rw [e0, comp_assoc, comp_assoc]
    congr 1
    simp [mul_pow]
  refine comp_cancel a.ne_zero ?_
  rw [Polynomial.prod_comp, ← eL, Finset.prod_congr rfl fun w _ => (eR w).symm]
  exact main
