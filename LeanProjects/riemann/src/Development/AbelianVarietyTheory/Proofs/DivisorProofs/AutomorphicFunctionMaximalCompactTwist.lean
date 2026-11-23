import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUnique
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin
open GlobalTheory.LeviPlane

noncomputable section
namespace GlobalTheory.CtLeviLevel
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_levi_mat (σ : E →ₐ[F] E) (B : Base F E) (hσ : ∀ x, σ (σ x) = x) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E d d₁) {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (t : (AE F E)ˣ) :
    ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m ∧
      mat m = lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (t : AE F E)
        (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) := by
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hc : ∀ x, c (c x) = x := fun x => cA_invol hσ x
  have hJ : ∀ i j, c (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [hcdef, incM, Matrix.map_apply, cAr_inclR, hW.skew, map_neg]
  have hxx : fm c (incM F W.J) (incV F H'.x) (incV F H'.x) = 0 := by rw [fm_inc, hH.xx, map_zero]
  have hyy : fm c (incM F W.J) (incV F H'.y) (incV F H'.y) = 0 := by rw [fm_inc, hH.yy, map_zero]
  have hxy : fm c (incM F W.J) (incV F H'.x) (incV F H'.y) = 1 := by rw [fm_inc, hH.xy, map_one]
  have hι : ∀ j, fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.x) = 0 ∧
      fm c (incM F W.J) (fun i => incM F H'.ι i j) (incV F H'.y) = 0 := by
    intro j
    have hcol : (fun i => incM F H'.ι i j) = incV F (H'.ι *ᵥ Pi.single j 1) := by
      ext i; simp [incV, incM]
    rw [hcol, fm_inc, fm_inc, (hH.orth _).1, (hH.orth _).2, map_zero]; exact ⟨rfl, rfl⟩
  let L : AE F E → AE F E → Matrix (Fin d) (Fin d) (AE F E) :=
    fun s r => lev c (incM F W.J) (incV F H'.x) (incV F H'.y) s r
  have hmul : ∀ s r s' r', L s r * L s' r' = L (s * s') (r * r') := fun s r s' r' =>
    lev_mul hc hJ hxx hyy hxy s r s' r'
  have h1 : L 1 1 = 1 := lev_one hc hJ hxx hyy hxy
  let g : GL (Fin d) (AE F E) :=
    ⟨L (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)), L ((t⁻¹ : (AE F E)ˣ) : AE F E) (cA σ (t : AE F E)),
      by rw [hmul, ← map_mul, Units.mul_inv, Units.inv_mul, map_one, h1],
      by rw [hmul, ← map_mul, Units.inv_mul, Units.mul_inv, map_one, h1]⟩
  have hg : g ∈ GlobalTheory.WeilM.UG (cA σ) (incM F W.J) := by
    show (L _ _)ᵀ * incM F W.J * (L _ _).map (cA σ) = incM F W.J
    exact lev_unitary hc hJ hxx hyy hxy (t : AE F E) (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E))
      (by show (t : AE F E) * cA σ (cA σ _) = 1; rw [cA_invol hσ, Units.mul_inv])
  refine ⟨⟨g, hg⟩, ⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩, rfl⟩
  have : mat (1 : UA σ W₁.J) = 1 := rfl
  rw [this, Matrix.mul_one]
  exact lev_mul_ι _ hι _ _

section Levi
variable (σ : E →ₐ[F] E) (B : Base F E) (hσ : ∀ x, σ (σ x) = x) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E d d₁) {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
include hσ hW hH

theorem isLevi_levi (t : (AE F E)ˣ) : IsLevi (W₁ := W₁) H' t 1 (leviElt σ W W₁ H' t) :=
  isLevi_leviElt ((exists_levi_mat σ B hσ W hW W₁ H' hH t).imp fun _ h => h.1)

theorem mat_levi (t : (AE F E)ˣ) : mat (leviElt σ W W₁ H' t) =
    lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (t : AE F E)
      (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) := by
  obtain ⟨m, hm, e⟩ := exists_levi_mat σ B hσ W hW W₁ H' hH t
  rw [GlobalTheory.LeviUniq.levi_unique F E σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t _ _ (isLevi_levi σ B hσ W hW W₁ H' hH t) hm, e]

theorem levi_mul (t s : (AE F E)ˣ) :
    leviElt σ W W₁ H' (t * s) = leviElt σ W W₁ H' t * leviElt σ W W₁ H' s := by
  obtain ⟨t1, t2, t3⟩ := isLevi_levi σ B hσ W hW W₁ H' hH t
  obtain ⟨s1, s2, s3⟩ := isLevi_levi σ B hσ W hW W₁ H' hH s
  have hm : ∀ g g' : UA σ W.J, mat (g * g') = mat g * mat g' := fun _ _ => rfl
  have h1 : mat (1 : UA σ W₁.J) = 1 := rfl
  rw [h1, Matrix.mul_one] at t3 s3
  refine GlobalTheory.LeviUniq.levi_unique F E σ B d r _ W hW d₁ W₁ H' i₀ i₁ hH (t * s) _ _
    (isLevi_levi σ B hσ W hW W₁ H' hH _) ⟨?_, ?_, ?_⟩
  · rw [hm, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_smul, t1, smul_smul, Units.val_mul, mul_comm]
  · rw [hm, ← Matrix.mulVec_mulVec, s2, Matrix.mulVec_smul, t2, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [hm, Matrix.mul_assoc, s3, t3, h1, Matrix.mul_one]

def leviHom : (AE F E)ˣ →* UA σ W.J :=
  MonoidHom.mk' (leviElt σ W W₁ H') (levi_mul σ B hσ W hW W₁ H' hH)

theorem continuous_levi : Continuous (leviElt σ W W₁ H') := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hcA : Continuous (cA (F := F) (E := E) σ) :=
    IsModuleTopology.continuous_of_linearMap (cA (F := F) (E := E) σ).toLinearMap
  have hLc : Continuous fun p : AE F E × AE F E =>
      lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) p.1 p.2 := by
    simp only [lev]
    fun_prop
  have hmat : Continuous fun t => mat (leviElt σ W W₁ H' t) :=
    (hLc.comp (Units.continuous_val.prodMk (hcA.comp Units.continuous_coe_inv))).congr fun t =>
      (mat_levi σ B hσ W hW W₁ H' hH t).symm
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hmat, ?_⟩)
  refine (hmat.comp continuous_inv).congr fun t => ?_
  exact congrArg mat (map_inv (leviHom σ B hσ W hW W₁ H' hH) t)

theorem levi_mem_finPts (c : E) (hc : c ≠ 0) {u : (AE F E)ˣ} (hu : u ∈ idelesFin F E) :
    toGAd hσ W.J hc (leviElt σ W W₁ H' u) ∈ finPts σ (c • W.J.map σ) := by
  let φ : AE F E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  let e : AF F := ((1 : Ainf F), (0 : Af F))
  have hφ : ∀ z : AE F E, e • z = 0 → φ z = 0 := by
    intro z hz
    have h1 : e • z = (e ⊗ₜ[F] (1 : E)) * z := by rw [Algebra.smul_def]; rfl
    have h2 : φ (e ⊗ₜ[F] (1 : E)) = 1 := rfl
    have := congrArg φ hz
    rwa [h1, map_mul, h2, one_mul, map_zero] at this
  have hu1 : e • ((u : AE F E) - 1) = 0 := hu e rfl
  have hu2 : e • (cA σ ((u⁻¹ : (AE F E)ˣ) : AE F E) - 1) = 0 := by
    have h3 : ((u⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -((u⁻¹ : (AE F E)ˣ) : AE F E) * ((u : AE F E) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]; ring
    rw [← map_one (cA σ), ← map_sub, ← map_smul, h3, ← mul_smul_comm, hu1, mul_zero, map_zero]
  have key : (mat (leviElt σ W W₁ H' u)).map φ = 1 := by
    rw [mat_levi σ B hσ W hW W₁ H' hH u]
    ext i j
    simp only [lev, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_sub φ, map_add φ, map_mul φ, map_mul φ, hφ _ hu1, hφ _ hu2, zero_mul, zero_mul, add_zero, sub_zero, Matrix.one_apply, Matrix.one_apply, apply_ite φ, map_one, map_zero]
  exact Units.ext key

end Levi

theorem ctLevi_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ f : UA σ G.W.J → ℂ, (∃ K, IsMaxCpt σ (c • G.W.J.map σ) K ∧ IsAut σ (c • G.W.J.map σ) K (fun x => f ((toGAd hσ G.W.J hc).symm x))) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ h : UA σ G.W.J, ∃ U : Subgroup (AE F E)ˣ, IsOpen (U : Set (AE F E)ˣ) ∧ ∀ u ∈ U, u ∈ idelesFin F E → ∀ t, ctLevi σ G.W W₁ H' μ 𝓕 f h (t * u) = ctLevi σ G.W W₁ H' μ 𝓕 f h t := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hH hσ c hc _ f hf μ 𝓕 _ _ _ h
  obtain ⟨K, -, hA⟩ := hf
  obtain ⟨U, hU, hl⟩ := hA.mod.level
  let e := toGAd hσ G.W.J hc
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  let m := leviHom σ B hσ G.W hT.geo.hW W₁ H' hH
  have hm : Continuous fun u => e (m u) := he.comp (continuous_levi σ B hσ G.W hT.geo.hW W₁ H' hH)
  let ψ : (AE F E)ˣ →* GAd σ (c • G.W.J.map σ) :=
    (MulAut.conj (e h)⁻¹).toMonoidHom.comp (e.toMonoidHom.comp m)
  have hψ : ∀ u, ψ u = (e h)⁻¹ * e (m u) * (e h)⁻¹⁻¹ := fun _ => rfl
  have hψc : Continuous ψ := ((continuous_const.mul hm).mul continuous_const).congr fun u => (hψ u).symm
  refine ⟨U.comap ψ, hU.preimage hψc, fun u hu hf t => ?_⟩
  have hfin : ψ u ∈ finPts σ (c • G.W.J.map σ) := by
    have h0 : e (m u) ∈ finPts σ (c • G.W.J.map σ) := levi_mem_finPts σ B hσ G.W hT.geo.hW W₁ H' hH c hc hf
    rw [mem_finPts] at h0 ⊢
    rw [hψ, map_mul, map_mul, h0, mul_one, ← map_mul, mul_inv_cancel, map_one]
  rw [ctLevi_apply, ctLevi_apply]
  congr 1
  funext n
  have key := hl (ψ u) hu hfin (e (n.1 * (m t * h)))
  have e1 : e (n.1 * (m t * h)) * ψ u = e (n.1 * (m (t * u) * h)) := by
    rw [hψ]
    simp only [map_mul, inv_inv, mul_assoc, mul_inv_cancel_left]
  rw [e1] at key
  simp only [e, MulEquiv.symm_apply_apply] at key
  exact key

end GlobalTheory.CtLeviLevel
