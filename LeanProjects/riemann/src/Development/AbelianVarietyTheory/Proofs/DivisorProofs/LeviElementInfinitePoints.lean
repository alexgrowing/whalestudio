import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUnique
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section
namespace GlobalTheory.LeviArch
open GlobalTheory.LeviPlane
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem leviElt_mat (σ : E →ₐ[F] E) (B : Base F E) (hcm : IsCMExt F E σ) {d r s : ℕ} (W : Spc F E d)
    (hW : W.IsSkew σ B r s) {d₁ : ℕ} (W₁ : Spc F E d₁) (H' : Plane E d d₁) {i₀ i₁ : ℕ}
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (t : (AE F E)ˣ) :
    mat (leviElt σ W W₁ H' t) = lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (t : AE F E)
      (cA σ ((t⁻¹ : (AE F E)ˣ) : AE F E)) := by
  set c : AE F E →+* AE F E := (cA σ).toRingHom with hcdef
  have hσ := sigma_invol hcm
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
      ext i; simp [incV, incM, Matrix.mulVec_single_one]
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
  let m : UA σ W.J := ⟨g, hg⟩
  have hm : IsLevi (W₁ := W₁) H' t 1 m := by
    refine ⟨lev_X hxx hxy _ _, lev_Y hc hJ hxx hyy hxy _ _, ?_⟩
    have : mat (1 : UA σ W₁.J) = 1 := rfl
    rw [this, Matrix.mul_one]
    exact lev_mul_ι _ hι _ _
  have e : leviElt σ W W₁ H' t = m :=
    GlobalTheory.LeviUniq.levi_unique F E σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t _ _ (isLevi_leviElt ⟨_, hm⟩) hm
  rw [e]
  rfl

theorem map_lev {R S : Type} [CommRing R] [CommRing S] (c : R →+* R) (φ : R →+* S) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) :
    (lev c J X Y s r).map φ = 1 + (φ s - 1) • Matrix.vecMulVec (fun i => φ (X i)) (fun i => φ ((J *ᵥ fun k => c (Y k)) i))
      - (φ r - 1) • Matrix.vecMulVec (fun i => φ (Y i)) (fun i => φ ((J *ᵥ fun k => c (X k)) i)) := by
  ext i j
  simp only [lev, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul, map_add, map_sub, map_mul]
  split_ifs <;> simp

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  simp [piInf, compInf, inclR, Algebra.TensorProduct.map_tmul]

theorem compInf_cA (σ : E →ₐ[F] E) (w : InfinitePlace F) (b : AE F E) :
    compInf F E w (cA σ b) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem compFin_cA (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (b : AE F E) :
    compFin F E v (cA σ b) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compFin F E v b) := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e => rfl

theorem piInf_cA {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (b : AE F E) :
    piInf τ (cA σ b) = star (piInf τ b) := by
  simp only [piInf, RingHom.comp_apply, compInf_cA]
  exact (infEmb_sigR hcm τ _).symm

theorem compFin_of_mem {t : (AE F E)ˣ} (ht : t ∈ idelesInf F E) (v : HeightOneSpectrum (𝓞 F)) :
    compFin F E v (t : AE F E) = 1 := by
  let u : AF F := (0, 1)
  have hu : evI F u = 0 := by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h0 : u • ((t : AE F E) - 1) = 0 := ht u hu
  have hs : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
    have h2 : sndA F u = 1 := rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (u ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.map_tmul, evFin, AlgHom.comp_apply, h2, map_one, AlgHom.id_apply]
    rfl
  have h1 := congrArg (compFin F E v) h0
  rw [Algebra.smul_def, map_mul, hs, one_mul, map_sub, map_one, map_zero] at h1
  exact sub_eq_zero.1 h1

theorem leviElt_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ a ∈ idelesInf F E, toGAd hσ W.J hc (leviElt σ W W₁ H' a) ∈ infPts σ (c • W.J.map σ) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w), ∃ z : ℂ, z ≠ 0 ∧ GlobalTheory.Orb.archMat σ (c • W.J.map σ) τ (projArch σ (c • W.J.map σ) w (toGAd hσ W.J hc (leviElt σ W W₁ H' a))) = torMat ((c • W.J.map σ).map τ.1) (fun i => τ.1 (H'.x i)) (fun i => τ.1 (c⁻¹ * H'.y i)) z := by
  intro F E _ _ _ _ _ σ B hcm d r s W hW hσ c hc hcs d₁ W₁ H' i₀ i₁ hH a ha
  set g := toGAd hσ W.J hc (leviElt σ W W₁ H' a) with hg
  have hM : ((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
      lev (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) (a : AE F E)
        (cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E)) := by
    rw [matHom_apply, hg, toGAd_mat]
    exact leviElt_mat σ B hcm W hW W₁ H' hH a
  refine ⟨?_, fun w τ => ?_⟩
  · rw [mem_infPts_iff_forall]
    intro v
    apply matHom_injective
    rw [matHom_proj, map_one]
    apply Units.ext
    show (((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)).map (compFin F E v)) = 1
    have h1 := compFin_of_mem ha v
    have h2 : compFin F E v ((a⁻¹ : (AE F E)ˣ) : AE F E) = 1 := by
      have := congrArg (compFin F E v) a.mul_inv
      rwa [map_mul, h1, one_mul, map_one] at this
    rw [hM, map_lev, compFin_cA, h1, h2, map_one]
    simp
  · have hz : piInf τ (a : AE F E) ≠ 0 := by
      intro h
      have := congrArg (piInf τ) a.mul_inv
      rw [map_mul, h, zero_mul, map_one] at this
      exact zero_ne_one this
    refine ⟨piInf τ (a : AE F E), hz, ?_⟩
    rw [GlobalTheory.Orb.archMat_apply, matHom_projArch]
    change ((((matHom _ σ (c • W.J.map σ) g : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)).map
      (compInf F E w)).map (infEmb τ)) = _
    rw [hM, Matrix.map_map]
    change (lev _ _ _ _ _ _).map (piInf τ) = _
    have hinv : piInf τ ((a⁻¹ : (AE F E)ˣ) : AE F E) = (piInf τ (a : AE F E))⁻¹ := by
      have := congrArg (piInf τ) a.mul_inv
      rw [map_mul, map_one] at this
      exact eq_inv_of_mul_eq_one_right this
    rw [map_lev, piInf_cA hcm, hinv, star_inv₀]
    have hst : ∀ e : E, star (τ.1 e) = τ.1 (σ e) := fun e => (hcm.2.2.2 τ.1 e).symm
    have hcc : τ.1 c⁻¹ * τ.1 c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    set z := piInf τ (a : AE F E)
    ext i j
    simp only [torMat, projL, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, incV, incM, Matrix.map_apply, piInf_inclR,
      AlgHom.coe_toRingHom, cA_inclR, Pi.star_apply, hst]
    have hτc : τ.1 c ≠ 0 := (map_ne_zero _).2 hc
    have hs1 : ∀ k, star (τ.1 c⁻¹ * τ.1 (H'.y k)) * (τ.1 c * τ.1 (σ (W.J k j))) = τ.1 (W.J j k) * τ.1 (σ (H'.y k)) := by
      intro k
      rw [star_mul', hst, hst, hW.skew, map_inv₀, hcs]
      simp only [map_neg, map_inv₀, inv_neg]
      field_simp
    have hs2 : ∀ k, τ.1 (σ (H'.x k)) * (τ.1 c * τ.1 (σ (W.J k j))) = -τ.1 c * (τ.1 (W.J j k) * τ.1 (σ (H'.x k))) := by
      intro k
      rw [hW.skew, map_neg]
      ring
    simp only [cAr_inclR, piInf_inclR, hs1, hs2, ← Finset.mul_sum]
    linear_combination ((star z)⁻¹ - 1) * τ.1 (H'.y i) * (∑ k, τ.1 (W.J j k) * τ.1 (σ (H'.x k))) * hcc

end GlobalTheory.LeviArch
