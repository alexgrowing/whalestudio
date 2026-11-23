import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIwVecTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

namespace GlobalTheory.TorusEigenform

section General

variable {G V : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace.SeparableSpace G] [AddCommGroup V] [Module ℂ V]

theorem exists_char_of_isIrreducible {σ : Representation ℂ G V} (hs : IsSmooth σ) (hi : σ.IsIrreducible) :
    ∃ μ : G →* ℂˣ, ∀ g w, σ g w = (μ g : ℂ) • w := by
  have := nontrivial_of_irreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h : ∀ g, ∃ c : ℂ, ∀ w, σ g w = c • w := fun g =>
    LocGL.exists_eq_smul_of_isSmooth hs hi
      ⟨σ g, fun a => by rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_comm]⟩
  choose c hc using h
  let m : G →* ℂ :=
    { toFun := c
      map_one' := smul_left_injective ℂ hv (by simp [← hc])
      map_mul' := fun a b => smul_left_injective ℂ hv (by
        show c (a * b) • v = (c a * c b) • v
        rw [← hc, map_mul, Module.End.mul_apply, hc b, hc a, smul_smul]) }
  exact ⟨m.toHomUnits, fun g w => hc g w⟩

theorem exists_eigenform {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {χ : G →* ℂˣ} (hχ : IsSmoothChar χ) {x : V} (hx : x ≠ 0)
    (hxH : ∀ t ∈ H, ρ t x = (χ t : ℂ) • x) :
    ∃ (μ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (μ g : ℂ) * l v) ∧ ∀ h ∈ H, μ h = χ h := by
  let ρ' := twist ρ χ⁻¹
  have hρ' : ∀ g v, ρ' g v = ((χ g)⁻¹ : ℂˣ) • ρ g v := fun _ _ => rfl
  have hc := LocGL.isCompl_fixed_twKer (isSmooth_twist hρ hχ.inv) hH
  let T : Subrepresentation ρ := ⟨twKer ρ' H 1, fun g v hv => by
    have h1 : ρ' g v ∈ twKer ρ' H 1 :=
      twKer_le_comap ρ' H g (by rw [Subgroup.normalizer_eq_top]; trivial) hv
    have h2 := (twKer ρ' H 1).smul_mem (χ g : ℂ) h1
    rwa [hρ', ← Units.smul_def, smul_inv_smul] at h2⟩
  have hT : T ≠ ⊤ := fun h => by
    have h1 : x ∈ T.toSubmodule := by rw [h]; trivial
    have h2 : x ∈ fixed ρ' H := fun t => by
      rw [hρ', hxH t t.2, ← Units.smul_def, inv_smul_smul]; simp
    exact hx ((Submodule.disjoint_def.1 hc.disjoint) x h2 h1)
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  refine ⟨μ, l, hl0, hle, fun h hh => ?_⟩
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hl0 (LinearMap.ext hn)
  have h1 : ρ' h v - v ∈ T.toSubmodule := Submodule.subset_span ⟨⟨h, hh⟩, v, by simp⟩
  have h2 := hlM (hTM h1)
  rw [LinearMap.mem_ker, map_sub, hρ', Units.smul_def, map_smul, hle, sub_eq_zero, smul_eq_mul,
    ← mul_assoc] at h2
  have h3 := mul_right_cancel₀ hv (h2.trans (one_mul _).symm)
  rw [← Units.val_mul, Units.val_eq_one, inv_mul_eq_one] at h3
  exact h3.symm

end General

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem secondCountableTopology_units : SecondCountableTopology kˣ := by
  have : SecondCountableTopology k := by
    letI := IsTopologicalAddGroup.rightUniformSpace k
    haveI := isUniformAddGroup_of_addCommGroup (G := k)
    letI : (Valued.v (R := k)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
    have : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
    infer_instance
  exact Units.isEmbedding_val₀.secondCountableTopology

variable {k} in

theorem isSmoothChar_torusChar {n : ℕ} {θ : Fin n → kˣ →* ℂˣ} (hθ : ∀ i, IsSmoothChar (θ i)) :
    IsSmoothChar (torusChar θ) :=
  Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) (by
    show IsOpen _
    rw [MonoidHom.ker_one]
    exact isOpen_univ) fun i _ => (hθ i).comp _ (continuous_apply i)

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  intro k _ _ _ _ n V _ _ ρ x θ hρ hl hθ hx hxH
  haveI := secondCountableTopology_units k
  obtain ⟨μ, l, hl0, hle, hμ⟩ := exists_eigenform hρ hl (SmGL.UnramFixed.isCompact_torusO k (Fin n))
    (isSmoothChar_torusChar hθ) hx hxH
  refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), l, hl0, fun t y => ?_, fun i u hu => ?_⟩
  · rw [hle, torusChar_apply]
    conv_lhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  · have h := hμ (Pi.mulSingle i u) fun j => by
      by_cases h : j = i
      · subst h; simpa using hu
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj])
      (by simp), Pi.mulSingle_eq_same] at h
    exact h

end GlobalTheory.TorusEigenform
