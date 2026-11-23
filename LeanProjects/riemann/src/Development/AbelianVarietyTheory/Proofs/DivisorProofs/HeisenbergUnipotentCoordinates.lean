import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainExists

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem algebraMap_norm {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (z : AE F E) :
    algebraMap (AF F) (AE F E) (Algebra.norm (AF F) z) = z * cA σ z :=
  GlobalTheory.Doubling.algebraMap_norm_eq hcm z

theorem cA_algebraMap (σ : E →ₐ[F] E) (a : AF F) :
    cA σ (algebraMap (AF F) (AE F E) a) = algebraMap (AF F) (AE F E) a := (cA σ).commutes a

theorem exists_retraction {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) :
    ∃ π : AE F E →ₗ[AF F] AF F, (∀ a, π (algebraMap (AF F) (AE F E) a) = a) ∧
      ∀ z, cA σ z = z → algebraMap (AF F) (AE F E) (π z) = z := by
  obtain ⟨f, hf⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hf1 : f 1 = 1 := by simpa using LinearMap.congr_fun hf 1
  let π : AE F E →ₗ[AF F] AF F :=
    (TensorProduct.AlgebraTensorModule.rid F (AF F) (AF F)).toLinearMap ∘ₗ LinearMap.baseChange (AF F) f
  have hπ : ∀ a, π (algebraMap (AF F) (AE F E) a) = a := by
    intro a
    show π (a ⊗ₜ[F] (1 : E)) = a
    simp [π, hf1]
  refine ⟨π, hπ, fun z hz => ?_⟩
  have h2 : (2 : AF F) * algebraMap F (AF F) 2⁻¹ = 1 := by
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have h2' := congrArg (algebraMap (AF F) (AE F E)) h2
  rw [map_mul, map_ofNat, map_one] at h2'
  have e : z = algebraMap (AF F) (AE F E)
      (algebraMap F (AF F) 2⁻¹ * (Algebra.norm (AF F) (1 + z) - 1 - Algebra.norm (AF F) z)) := by
    rw [map_mul, map_sub, map_sub, map_one, algebraMap_norm hcm, algebraMap_norm hcm, map_add, map_one, hz]
    linear_combination (-z) * h2'
  rw [e, hπ]

theorem exists_leftInv {d d₁ : ℕ} (hd : d = d₁ + 2) (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hspan : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • x + ι *ᵥ u + t • y) :
    ∃ L : Matrix (Fin d₁) (Fin d) E, L * ι = 1 := by
  let T : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin d → E) :=
    (Matrix.mulVecLin ι).coprod ((LinearMap.toSpanSingleton E _ x).coprod (LinearMap.toSpanSingleton E _ y))
  have hs : Function.Surjective T := by
    intro v
    obtain ⟨s, t, u, rfl⟩ := hspan v
    refine ⟨(u, s, t), ?_⟩
    simp only [T, LinearMap.coprod_apply, Matrix.mulVecLin_apply, LinearMap.toSpanSingleton_apply]
    abel
  have hi : Function.Injective T :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hd])).2 hs
  have hι : LinearMap.ker (Matrix.toLin' ι) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    have : T (u, 0, 0) = T 0 := by
      rw [map_zero]
      simpa [T] using hu
    exact congrArg Prod.fst (hi this)
  obtain ⟨g, hg⟩ := (Matrix.toLin' ι).exists_leftInverse_of_injective hι
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem incM_mul {l m n : ℕ} (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin n) E) :
    incM F A * incM F B = incM F (A * B) := (Matrix.map_mul (f := inclR (F := F) (AF F))).symm

theorem incM_one {n : ℕ} : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem conj_nmat {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (m : UA σ J)
    (x u : Fin n → AE F E) (c t : AE F E) (hx : mat m *ᵥ x = cA σ t • x) (hu : mat m *ᵥ u = u) :
    mat m * nmat σ J x u c * mat m⁻¹ = nmat σ J x (t • u) (t * cA σ t * c) := by
  have h1 : mat m * mat m⁻¹ = 1 := by
    rw [show mat m * mat m⁻¹ = mat (m * m⁻¹) from rfl, mul_inv_cancel]; rfl
  have key : ∀ v, (mat m * nmat σ J x u c * mat m⁻¹) *ᵥ v = nmat σ J x (t • u) (t * cA σ t * c) *ᵥ v := by
    intro v
    have hv : mat m *ᵥ (mat m⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    have e1 : hA σ J (mat m⁻¹ *ᵥ v) x = t * hA σ J v x := by
      rw [← StdMat.hA_mat_eq σ m, hv, hx, StdMat.hA_smul_r, cA_cA hσ]
    have e2 : hA σ J (mat m⁻¹ *ᵥ v) u = hA σ J v u := by
      rw [← StdMat.hA_mat_eq σ m, hv, hu]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, nmat_mulVec, nmat_mulVec, e1, e2, StdMat.hA_smul_r]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, hv, hx, hu]
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have h4 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h4

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem continuous_hA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {X : Type} [TopologicalSpace X]
    {u w : X → Fin n → AE F E} (hu : Continuous u) (hw : Continuous w) : Continuous fun p => hA σ J (u p) (w p) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  unfold hA
  exact hu.dotProduct (continuous_const.matrix_mulVec (continuous_pi fun i => hs.comp ((continuous_apply i).comp hw)))

theorem exists_coord_skew (hcm : IsCMExt F E σ) (h : Hyp σ W H') (hd : d = d₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hyy : form σ W.J H'.y H'.y = 0) (hxy : form σ W.J H'.x H'.y = 1)
    (horth : ∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0)
    (hspan : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) :
    ∃ (Φ : unip σ W H' ≃ₜ (Fin d₁ → AE F E) × AF F) (β : (Fin d₁ → AE F E) → (Fin d₁ → AE F E) → AF F),
      Continuous (Function.uncurry β) ∧
      (∀ u v, Φ (u * v) = ((Φ u).1 + (Φ v).1, (Φ u).2 + (Φ v).2 + β (Φ u).1 (Φ v).1)) ∧
      ∀ (t : AE F E) (m : UA σ W.J), mat m *ᵥ incV F H'.x = cA σ t • incV F H'.x → mat m * incM F H'.ι = incM F H'.ι →
        ∀ u : unip σ W H', ∃ h : m * u.1 * m⁻¹ ∈ unip σ W H',
          Φ ⟨m * u.1 * m⁻¹, h⟩ = (cA σ t • (Φ u).1, Algebra.norm (AF F) t * (Φ u).2) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hs : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have halg : Continuous (algebraMap (AF F) (AE F E)) := by
    exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AE F E))
  obtain ⟨π, hπ1, hπ2⟩ := exists_retraction hcm
  have hπc : Continuous π := IsModuleTopology.continuous_of_linearMap π
  obtain ⟨L, hL⟩ := exists_leftInv hd H'.x H'.y H'.ι hspan
  have hstd := GlobalTheory.T.hyperbolic_pair_decomposition F E σ h.σσ d d₁ W H' h.skew hxx hyy hxy horth hspan
  have hXY : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV, hxy, map_one]
  have hιY : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 :=
    StdMat.hA_ι_incV_eq σ W.J H'.ι H'.y (fun u => (horth u).2)
  have hLι : incM F L * incM F H'.ι = 1 := by rw [incM_mul, hL, incM_one]
  set ι := incM F H'.ι with hι
  set X := incV F H'.x with hX
  set Y := incV F H'.y with hY
  set half : AE F E := inclR (F := F) (AF F) (2⁻¹ : E) with hhalf_def
  have hhalf : (2 : AE F E) * half = 1 := by
    rw [hhalf_def, ← map_ofNat (inclR (F := F) (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  have hσhalf : cA σ half = half := by rw [hhalf_def, cA_inclR, map_inv₀, map_ofNat]
  have hsk : ∀ v w, cA σ (hA σ W.J v w) = -hA σ W.J w v := hA_skew h.σσ h.skew
  have hYX : hA σ W.J Y X = -1 := by
    have := hsk X Y
    rw [hXY, map_one] at this
    linear_combination this
  have hYι : ∀ z, hA σ W.J Y (ι *ᵥ z) = 0 := fun z => by
    have := hsk (ι *ᵥ z) Y
    rw [hιY, map_zero] at this
    linear_combination this
  let bar : (Fin d₁ → AE F E) → Fin d₁ → AE F E := fun b j => cA σ (b j)
  have hbar : ∀ b, bar (bar b) = b := fun b => funext fun j => cA_cA h.σσ _
  have hbarc : Continuous bar := continuous_pi fun i => hs.comp (continuous_apply i)
  let Q : (Fin d₁ → AE F E) → AE F E := fun b => half * hA σ W.J (ι *ᵥ b) (ι *ᵥ b)
  have hQc : Continuous Q := continuous_const.mul
    (continuous_hA σ W.J (continuous_const.matrix_mulVec continuous_id) (continuous_const.matrix_mulVec continuous_id))
  let C : unip σ W H' → AE F E := fun g => hA σ W.J (mat g.1 *ᵥ Y - Y) Y
  let Bv : unip σ W H' → Fin d₁ → AE F E := fun g => incM F L *ᵥ (mat g.1 *ᵥ Y - Y - C g • X)
  have hmatc : Continuous fun g : unip σ W H' => mat g.1 :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hCc : Continuous C :=
    continuous_hA σ W.J ((hmatc.matrix_mulVec continuous_const).sub continuous_const) continuous_const
  have hBc : Continuous Bv := continuous_const.matrix_mulVec
    (((hmatc.matrix_mulVec continuous_const).sub continuous_const).sub (hCc.smul continuous_const))
  let φ : unip σ W H' → (Fin d₁ → AE F E) × AF F := fun g => (bar (Bv g), π (C g + Q (Bv g)))
  have hφ : ∀ (g : unip σ W H') b c, mat g.1 = nmat σ W.J X (ι *ᵥ b) c → φ g = (bar b, π (c + Q b)) := by
    intro g b c hg
    have e1 : mat g.1 *ᵥ Y - Y = ι *ᵥ b + c • X := by
      rw [hg, nmat_mulVec, hYX, hYι]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have e2 : C g = c := by
      simp only [C]
      rw [e1, hA_add_left, hιY, StdMat.hA_smul_l, hXY]; ring
    have e3 : Bv g = b := by
      simp only [Bv]
      rw [e1, e2, add_sub_cancel_right, Matrix.mulVec_mulVec, hLι, Matrix.one_mulVec]
    simp only [φ, e2, e3]
  have hfix : ∀ b c, c - cA σ c = -hA σ W.J (ι *ᵥ b) (ι *ᵥ b) → cA σ (c + Q b) = c + Q b := by
    intro b c hc
    simp only [Q, map_add, map_mul, hσhalf, hsk]
    linear_combination (-1 : AE F E) * hc - (hA σ W.J (ι *ᵥ b) (ι *ᵥ b)) * hhalf
  have hcf : ∀ p : (Fin d₁ → AE F E) × AF F, (algebraMap (AF F) (AE F E) p.2 - Q (bar p.1)) -
      cA σ (algebraMap (AF F) (AE F E) p.2 - Q (bar p.1)) = -hA σ W.J (ι *ᵥ bar p.1) (ι *ᵥ bar p.1) := by
    intro p
    simp only [Q, map_sub, map_mul, hσhalf, hsk, cA_algebraMap]
    linear_combination (-hA σ W.J (ι *ᵥ bar p.1) (ι *ᵥ bar p.1)) * hhalf
  let ψ : (Fin d₁ → AE F E) × AF F → unip σ W H' := fun p => elt h (bar p.1) _ (hcf p)
  have hψc : Continuous ψ := by
    have h1 : Continuous fun p : (Fin d₁ → AE F E) × AF F => bar p.1 := hbarc.comp continuous_fst
    have h2 : Continuous fun p : (Fin d₁ → AE F E) × AF F => algebraMap (AF F) (AE F E) p.2 - Q (bar p.1) :=
      (halg.comp continuous_snd).sub (hQc.comp h1)
    refine Continuous.subtype_mk (Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _) _
    · exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec h1) h2
    · exact continuous_nmat σ W.J _ (continuous_const.matrix_mulVec h1.neg) (h2.neg.sub
        (continuous_hA σ W.J (continuous_const.matrix_mulVec h1) (continuous_const.matrix_mulVec h1)))
  let Φ : unip σ W H' ≃ₜ (Fin d₁ → AE F E) × AF F :=
    { toFun := φ
      invFun := ψ
      left_inv := fun g => by
        obtain ⟨b, c, hc, hg⟩ := hstd g.1 g.2
        rw [hφ g b c hg]
        apply unip_ext
        show nmat σ W.J X (ι *ᵥ bar (bar b)) (algebraMap (AF F) (AE F E) (π (c + Q b)) - Q (bar (bar b))) = _
        rw [hbar, hπ2 _ (hfix b c hc), add_sub_cancel_right, hg]
      right_inv := fun p => by
        rw [hφ (ψ p) _ _ rfl, hbar, sub_add_cancel, hπ1]
      continuous_toFun := (hbarc.comp hBc).prodMk (hπc.comp (hCc.add (hQc.comp hBc)))
      continuous_invFun := hψc }
  refine ⟨Φ, fun l l' => π (half * (hA σ W.J (ι *ᵥ bar l) (ι *ᵥ bar l') - hA σ W.J (ι *ᵥ bar l') (ι *ᵥ bar l))),
    ?_, ?_, ?_⟩
  · have h1 : Continuous fun p : (Fin d₁ → AE F E) × (Fin d₁ → AE F E) => ι *ᵥ bar p.1 :=
      continuous_const.matrix_mulVec (hbarc.comp continuous_fst)
    have h2 : Continuous fun p : (Fin d₁ → AE F E) × (Fin d₁ → AE F E) => ι *ᵥ bar p.2 :=
      continuous_const.matrix_mulVec (hbarc.comp continuous_snd)
    exact hπc.comp (continuous_const.mul ((continuous_hA σ W.J h1 h2).sub (continuous_hA σ W.J h2 h1)))
  · intro u v
    obtain ⟨b, c, -, hu⟩ := hstd u.1 u.2
    obtain ⟨b', c', -, hv⟩ := hstd v.1 v.2
    have huv : mat (u * v).1 = nmat σ W.J X (ι *ᵥ (b + b')) (c + c' - hA σ W.J (ι *ᵥ b') (ι *ᵥ b)) := by
      show mat u.1 * mat v.1 = _
      rw [hu, hv, nmat_mul h]
    show φ (u * v) = ((φ u).1 + (φ v).1, (φ u).2 + (φ v).2 +
      π (half * (hA σ W.J (ι *ᵥ bar (φ u).1) (ι *ᵥ bar (φ v).1) - hA σ W.J (ι *ᵥ bar (φ v).1) (ι *ᵥ bar (φ u).1))))
    rw [hφ _ _ _ huv, hφ _ _ _ hu, hφ _ _ _ hv]
    refine Prod.ext (funext fun j => map_add (cA σ) _ _) ?_
    simp only [hbar, ← map_add]
    congr 1
    simp only [Q, Matrix.mulVec_add, hA_add_left, hA_add_right]
    linear_combination (hA σ W.J (ι *ᵥ b') (ι *ᵥ b)) * hhalf
  · intro t m hx hm u
    obtain ⟨b, c, -, hu⟩ := hstd u.1 u.2
    have e : mat (m * u.1 * m⁻¹) = nmat σ W.J X (ι *ᵥ (t • b)) (t * cA σ t * c) := by
      show mat m * mat u.1 * mat m⁻¹ = _
      rw [hu, conj_nmat h.σσ m X (ι *ᵥ b) c t hx (by rw [Matrix.mulVec_mulVec, hm]), Matrix.mulVec_smul]
    refine ⟨mem_unip h _ _ _ e, ?_⟩
    show φ _ = (cA σ t • (φ u).1, Algebra.norm (AF F) t * (φ u).2)
    rw [hφ _ _ _ e, hφ _ _ _ hu]
    refine Prod.ext (funext fun j => map_mul (cA σ) _ _) ?_
    show π _ = Algebra.norm (AF F) t • π _
    rw [← map_smul, Algebra.smul_def (Algebra.norm (AF F) t), algebraMap_norm hcm]
    congr 1
    simp only [Q, Matrix.mulVec_smul, StdMat.hA_smul_l, StdMat.hA_smul_r]
    ring

end GlobalTheory.UnipCoord

namespace GlobalTheory.UnipCoord
open GlobalTheory.UnipMassHerm

theorem exists_coord_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ →
  ∃ (Φ : unip σ Y H ≃ₜ (Fin n₁ → AE F E) × AF F) (β : (Fin n₁ → AE F E) → (Fin n₁ → AE F E) → AF F), Continuous (Function.uncurry β) ∧
    (∀ u v, Φ (u * v) = ((Φ u).1 + (Φ v).1, (Φ u).2 + (Φ v).2 + β (Φ u).1 (Φ v).1)) ∧
    ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H (Units.map (cA σ : AE F E →* AE F E) t) 1 m →
      ∀ u : unip σ Y H, ∃ h : m * u.1 * m⁻¹ ∈ unip σ Y H,
        Φ ⟨m * u.1 * m⁻¹, h⟩ = (cA σ (t : AE F E) • (Φ u).1, Algebra.norm (AF F) (t : AE F E) * (Φ u).2) := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H r s i₀ i₁ hB hV hH
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  have hspan : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
    intro v
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := by
      rw [hV.lat.span_eq_top]; trivial
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, hz⟩ := hH.split z hz
      exact ⟨s, t, u, hz⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, t, u, rfl⟩ := hy
      obtain ⟨s', t', u', rfl⟩ := hz
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a y _ hy =>
      obtain ⟨s, t, u, rfl⟩ := hy
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  obtain ⟨δ, hδ0, hδ⟩ := exists_anti hB.cm
  let W' : Spc F E n := ⟨δ • Y.J, Y.L, Y.θ, Y.bas⟩
  let H'' : Plane E n n₁ := ⟨H.x, (-δ⁻¹) • H.y, H.ι, H.𝔟⟩
  have hform : ∀ v w, form σ W'.J v w = δ * form σ Y.J v w := form_smul_mat σ Y.J δ
  have hσt : σ (-δ⁻¹) = δ⁻¹ := by rw [map_neg, map_inv₀, hδ, inv_neg, neg_neg]
  have hxx : form σ W'.J H''.x H''.x = 0 := by rw [hform]; show δ * form σ Y.J H.x H.x = 0; rw [hH.xx, mul_zero]
  have hyy : form σ W'.J H''.y H''.y = 0 := by
    rw [hform]; show δ * form σ Y.J ((-δ⁻¹) • H.y) ((-δ⁻¹) • H.y) = 0
    rw [form_smul_left, form_smul_right, hH.yy]; ring
  have hxy : form σ W'.J H''.x H''.y = 1 := by
    rw [hform]; show δ * form σ Y.J H.x ((-δ⁻¹) • H.y) = 1
    rw [form_smul_right, hH.xy, hσt, mul_one, mul_inv_cancel₀ hδ0]
  have horth : ∀ u, form σ W'.J (H''.ι *ᵥ u) H''.x = 0 ∧ form σ W'.J (H''.ι *ᵥ u) H''.y = 0 := by
    intro u
    refine ⟨?_, ?_⟩
    · rw [hform]; show δ * form σ Y.J (H.ι *ᵥ u) H.x = 0; rw [(hH.orth u).1, mul_zero]
    · rw [hform]; show δ * form σ Y.J (H.ι *ᵥ u) ((-δ⁻¹) • H.y) = 0; rw [form_smul_right, (hH.orth u).2]; ring
  have hspan'' : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H''.x + H''.ι *ᵥ u + t • H''.y := by
    intro v
    obtain ⟨s, t, u, hv⟩ := hspan v
    refine ⟨s, t * -δ, u, ?_⟩
    show v = s • H.x + H.ι *ᵥ u + (t * -δ) • (-δ⁻¹) • H.y
    rw [smul_smul, show t * -δ * -δ⁻¹ = t by field_simp, hv]
  have hyp : Hyp σ W' H'' := by
    refine ⟨hσ, fun i j => ?_, by rw [hA_incV, hxx, map_zero],
      StdMat.hA_ι_incV_eq σ W'.J H''.ι H''.x fun u => (horth u).1⟩
    show σ (δ * Y.J j i) = -(δ * Y.J i j)
    rw [map_mul, hδ, hV.herm]; ring
  obtain ⟨Φ, β, hβ, hmul, hconj⟩ := exists_coord_skew hB.cm hyp hH.rank hxx hyy hxy horth hspan''
  have hUG := UG_smul (F := F) σ Y.J hδ0
  let φ : UA σ W'.J →* UA σ Y.J := Subgroup.inclusion hUG.le
  let φ' : UA σ Y.J →* UA σ W'.J := Subgroup.inclusion hUG.ge
  have hmap : (unip σ W' H'').map φ ≤ unip σ Y H := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  have hmap' : (unip σ Y H).map φ' ≤ unip σ W' H'' := by
    rw [unip, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  let Ψ : unip σ Y H ≃ₜ unip σ W' H'' :=
    { toFun := fun g => ⟨φ' g.1, hmap' ⟨g.1, g.2, rfl⟩⟩
      invFun := fun g => ⟨φ g.1, hmap ⟨g.1, g.2, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _
      continuous_invFun :=
        Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) _ }
  refine ⟨Ψ.trans Φ, β, hβ, fun u v => hmul (Ψ u) (Ψ v), fun t m hm u => ?_⟩
  have hm3 : mat m * incM F H.ι = incM F H.ι := by
    rw [hm.2.2]; exact Matrix.mul_one _
  obtain ⟨h1, h2⟩ := hconj t (φ' m) hm.1 hm3 (Ψ u)
  exact ⟨hmap ⟨_, h1, rfl⟩, h2⟩

end GlobalTheory.UnipCoord
