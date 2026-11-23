import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLatticeStabilizerDetRoot
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.MemberDetLaws

theorem exists_potential {G M X A : Type} [Group G] [CommGroup A] (act : G → M → M)
    (act_one : ∀ m, act 1 m = m) (act_mul : ∀ g h m, act (g * h) m = act g (act h m))
    (v : X → M) (χ : G →* A)
    (hχ : ∀ (x : X) (g : G), v x = act g (v x) → χ g = 1) :
    ∃ φ : X → A, ∀ (x y : X) (g : G), v y = act g (v x) → φ y = χ g * φ x := by
  classical
  let s : Setoid X :=
    { r := fun x y => ∃ g : G, v y = act g (v x)
      iseqv :=
        { refl := fun x => ⟨1, (act_one _).symm⟩
          symm := fun {x y} ⟨g, hg⟩ => ⟨g⁻¹, by rw [hg, ← act_mul, inv_mul_cancel, act_one]⟩
          trans := fun {x y z} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by rw [hh, hg, act_mul]⟩ } }
  have hb : ∀ x : X, ∃ g : G, v x = act g (v (Quotient.mk s x).out) := fun x =>
    Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun x y g hg => ?_⟩
  have hq : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, hg⟩
  have hx := hc x
  have hy := hc y
  rw [← hq] at hy
  have h1 : χ ((c y)⁻¹ * (g * c x)) = 1 := by
    apply hχ (Quotient.mk s x).out
    rw [act_mul, act_mul, ← hx, ← hg, hy, ← act_mul, inv_mul_cancel, act_one]
  rw [map_mul, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem smulLat_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

theorem smulLat_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    (g h : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (g * h) L = SDLat.smulLat g (SDLat.smulLat h L) := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_mul, ← Submodule.map_comp]
  rfl

def detU (E : Type) [Field E] [StarRing E] (N : ℕ) :
    Matrix.unitaryGroup (Fin N) E →* unitary E where
  toFun γ := ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

noncomputable def invProd {E ι : Type} [Field E] [StarRing E] [Fintype ι] (σ : ι → E →+* ℂ) :
    unitary E →* ℂˣ :=
  ∏ i, ((Units.map (σ i : E →* ℂ)).comp Unitary.toUnits)⁻¹

theorem invProd_coe {E ι : Type} [Field E] [StarRing E] [Fintype ι] (σ : ι → E →+* ℂ)
    (z : unitary E) : ((invProd σ z : ℂˣ) : ℂ) = ∏ i, (σ i (z : E))⁻¹ := by
  unfold invProd
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl

private theorem pow_eq_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

private theorem prod_emb_eq_one {R : Ranks} (H : Formalism.BasicNotions.Host R) [Fintype R.Psi] (x : H.E)
    (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : ∏ τ : R.Psi, H.emb (τ : R.GG) x = 1 := by
  classical
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  have h := Algebra.norm_eq_prod_automorphisms H.K x
  rw [H.der.norm_mu x hx, map_one] at h
  have h2 := congrArg H.φ₀ h
  rw [map_one, map_prod] at h2
  rw [h2]
  symm
  have hmem : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ : H.E ≃ₐ[H.K] H.E => (⟨H.gal (σ.restrictScalars ℚ), hmem σ⟩ : R.Psi))
    ⟨fun σ τ hst => ?_, fun g => ?_⟩ _ _ fun σ => ?_
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val hst))
  · have hfix : H.gal.symm g.1 H.sqd = H.sqd :=
      (H.galE_mem_Psi_iff _).1 (by
        show H.gal (H.gal.symm g.1) ∈ _
        rw [MulEquiv.apply_symm_apply]; exact g.2)
    have hK : ∀ y : H.K, H.gal.symm g.1 (y : H.E) = y := by
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.gal.symm g.1)) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        exact (Subgroup.zpowers_le.2
          (show H.gal.symm g.1 ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd from hfix)) hf
      intro y
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle y.2) _ (Subgroup.mem_zpowers _)
    refine ⟨AlgEquiv.ofRingEquiv (f := (H.gal.symm g.1).toRingEquiv) hK, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply g.1
  · show H.φ₀ (σ x) = H.φ₀ (H.gal.symm (H.gal (σ.restrictScalars ℚ)) x)
    rw [MulEquiv.symm_apply_apply]
    rfl

theorem det_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), letI := H.cmStar; ∃ (e1 : unitary H.E →* ℂˣ) (rel : ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ ⧸ (⊥ : Subgroup ℂˣ)), (∀ z : unitary H.E, ((e1 z : ℂˣ) : ℂ) = ∏ᶠ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) ∧ (∀ N L, rel N L L = 1) ∧ (∀ N L L' L'', rel N L L' * rel N L' L'' = rel N L L'') ∧ ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → rel N L L' = QuotientGroup.mk (e1 ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H
  letI := H.cmStar
  letI : Fintype (R.Psi) := Fintype.ofFinite _
  let e1 : unitary H.E →* ℂˣ := invProd fun τ : R.Psi => H.emb (τ : R.GG)
  have he1 : ∀ z : unitary H.E, ((e1 z : ℂˣ) : ℂ) =
      ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹ := invProd_coe _
  have hφ : ∀ N, ∃ φ : SDLat H.E N → ℂˣ,
      ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
        L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
          φ L' = (e1.comp (detU H.E N)) γ * φ L := by
    intro N
    refine exists_potential
      (fun (γ : Matrix.unitaryGroup (Fin N) H.E) L =>
        SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L)
      (fun m => smulLat_one m) (fun g h m => smulLat_mul _ _ m)
      (fun L : SDLat H.E N => L.1) _ ?_
    intro L γ hγ
    apply Units.ext
    rw [MonoidHom.comp_apply, he1]
    change ∏ τ : R.Psi, (H.emb (τ : R.GG) (γ : Matrix (Fin N) (Fin N) H.E).det)⁻¹ = 1
    rw [Finset.prod_inv_distrib, prod_emb_eq_one H _ (pow_eq_one_of_unitary H _
      (Matrix.det_of_mem_unitary γ.2)
      (GlobalTheory.Mem.StabDet.isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)), inv_one]
    rw [hγ]
    exact ⟨v, hv, by simp⟩
  choose φ hφ using hφ
  refine ⟨e1, fun N L L' => QuotientGroup.mk (φ N L' / φ N L), fun z => ?_, fun N L => ?_,
    fun N L L' L'' => ?_, fun N L L' γ hγ => ?_⟩
  · rw [he1, finprod_eq_prod_of_fintype]
  · simp
  · rw [← QuotientGroup.mk_mul, mul_comm, div_mul_div_cancel]
  · show QuotientGroup.mk (φ N L' / φ N L) = _
    rw [hφ N L L' γ hγ, mul_div_cancel_right]
    rfl

end GlobalTheory.MemberDetLaws
