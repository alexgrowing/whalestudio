import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.HeisThetaF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Alg

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}

theorem symplOHF_add_left (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add]

theorem symplOHF_add_right (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]

theorem cAF_algebraMap (c : AF F) :
    cAF σ (algebraMap (AF F) (AEF F E) c) = algebraMap (AF F) (AEF F E) c := by
  show Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (c ⊗ₜ[F] (1 : E)) = c ⊗ₜ[F] (1 : E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem symplOHF_smul_left (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (c • x) y = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT (c • x) y = algebraMap (AF F) (AEF F E) c * hOF σ JS JT x y := by
    simp only [hOF, Matrix.smul_apply, Algebra.smul_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  unfold symplOHF symplOF
  rw [h, mul_left_comm (incAF F E xi0), ← Algebra.smul_def c, LinearMap.map_smul, smul_eq_mul, mul_left_comm]

theorem symplOHF_smul_right (c : AF F) (x y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (c • y) = c * symplOHF σ JS JT xi0 x y := by
  have h : hOF σ JS JT x (c • y) = algebraMap (AF F) (AEF F E) c * hOF σ JS JT x y := by
    simp only [hOF, Matrix.smul_apply, Algebra.smul_def, map_mul, cAF_algebraMap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  unfold symplOHF symplOF
  rw [h, mul_left_comm (incAF F E xi0), ← Algebra.smul_def c, LinearMap.map_smul, smul_eq_mul, mul_left_comm]

theorem symplOHF_zero_left (y : WOF F E nS nT) : symplOHF σ JS JT xi0 0 y = 0 := by
  have := symplOHF_smul_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (0 : AF F) 0 y
  rwa [zero_smul, zero_mul] at this

theorem symplOHF_zero_right (x : WOF F E nS nT) : symplOHF σ JS JT xi0 x 0 = 0 := by
  have := symplOHF_smul_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (0 : AF F) x 0
  rwa [zero_smul, zero_mul] at this

end Alg

section Parts

theorem smul_eq_zero_of_infPartF {z : AEF F E} (hz : infPartF F E z = 0) : (pairA F 1 0) • z = 0 := by
  have key : ∀ z : AEF F E,
      (pairA F 1 0) • z = LinearMap.rTensor E (LinearMap.inl F (Ainf F) (Af F)) (infPartF F E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]; rfl
    | tmul a e =>
      have h1 : infPartF F E (a ⊗ₜ[F] e) = fstA F a ⊗ₜ[F] e := Algebra.TensorProduct.map_tmul _ _ _ _
      rw [TensorProduct.smul_tmul', h1, LinearMap.rTensor_tmul]
      congr 1
      refine Prod.ext ?_ ?_
      · show 1 * a.1 = a.1
        rw [one_mul]
      · show 0 * a.2 = 0
        rw [zero_mul]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]; rfl
  rw [key, hz, map_zero]; rfl

theorem smul_eq_zero_of_finPartF {z : AEF F E} (hz : finPartF F E z = 0) : (pairA F 0 1) • z = 0 := by
  have key : ∀ z : AEF F E,
      (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F)) (finPartF F E z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, map_zero]; rfl
    | tmul a e =>
      have h1 : finPartF F E (a ⊗ₜ[F] e) = sndA F a ⊗ₜ[F] e := Algebra.TensorProduct.map_tmul _ _ _ _
      rw [TensorProduct.smul_tmul', h1, LinearMap.rTensor_tmul]
      congr 1
      refine Prod.ext ?_ ?_
      · show 0 * a.1 = 0
        rw [zero_mul]
      · show 1 * a.2 = a.2
        rw [one_mul]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]; rfl
  rw [key, hz, map_zero]; rfl

end Parts

section Top

variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}

theorem isTopologicalRing_AEF : IsTopologicalRing (AEF F E) := by
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  exact IsModuleTopology.isTopologicalRing (AF F) _

theorem continuous_trace_AEF : Continuous (Algebra.trace (AF F) (AEF F E)) := by
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap _

theorem continuous_cAF : Continuous (cAF (F := F) (E := E) σ) := by
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  let L : AEF F E →ₗ[AF F] AEF F E :=
    { toFun := cAF σ
      map_add' := map_add _
      map_smul' := fun c z => by
        simp only [Algebra.smul_def, map_mul, cAF_algebraMap, RingHom.id_apply] }
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_symplOHF_left (y : WOF F E nS nT) : Continuous fun x => symplOHF σ JS JT xi0 x y := by
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  have ht := continuous_trace_AEF (F := F) (E := E)
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
  exact continuous_const.mul ((continuous_apply a).comp (continuous_apply d))

theorem continuous_symplOHF_right (x : WOF F E nS nT) : Continuous fun y => symplOHF σ JS JT xi0 x y := by
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  have ht := continuous_trace_AEF (F := F) (E := E)
  have hc := continuous_cAF (F := F) (E := E) (σ := σ)
  unfold symplOHF symplOF hOF
  refine continuous_const.mul (ht.comp (continuous_const.mul ?_))
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    continuous_finset_sum _ fun c _ => continuous_finset_sum _ fun d _ => ?_
  exact ((continuous_const.mul (hc.comp ((continuous_apply b).comp (continuous_apply c)))).mul
    continuous_const).mul continuous_const

variable (F) in

theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
      fun x => ((fun v : {w : InfinitePlace F // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

end Top

section Fin

theorem nonarch_of_isInducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

variable (F) in

theorem nonarch_Af : NonarchimedeanAddGroup (Af F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_isInducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

theorem exists_openAddSubgroup_psi_fin (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ K : OpenAddSubgroup (Af F), ∀ y ∈ K, ψ (pairA F 0 y) = 1 := by
  haveI := nonarch_Af F
  have hι : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  have hW : {y : Af F | ‖ψ (pairA F 0 y) - 1‖ < 1 / 2} ∈ nhds (0 : Af F) := by
    refine (isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const).mem_nhds ?_
    show ‖ψ (pairA F 0 0) - 1‖ < 1 / 2
    have : pairA F 0 0 = 0 := rfl
    rw [this, AddChar.map_zero_eq_one, sub_self, norm_zero]
    norm_num
  obtain ⟨K, hK⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hW
  refine ⟨K, fun y hy => GroundTheory.Global.eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k => ?_⟩
  have h1 : ψ (pairA F 0 y) ^ (2 ^ k) = ψ (pairA F 0 ((2 ^ k : ℕ) • y)) := by
    rw [← AddChar.map_nsmul_eq_pow]
    congr 1
    show (2 ^ k : ℕ) • ((0 : Ainf F), y) = ((0 : Ainf F), (2 ^ k : ℕ) • y)
    rw [Prod.smul_mk, smul_zero]
  rw [h1]
  exact hK (K.toAddSubgroup.nsmul_mem hy _)

theorem fstA_mul_idem (a : AF F) : fstA F (pairA F 1 0 * a) = fstA F a := by
  show 1 * a.1 = a.1
  rw [one_mul]

theorem sndA_mul_idem (a : AF F) : sndA F (pairA F 0 1 * a) = sndA F a := by
  show 1 * a.2 = a.2
  rw [one_mul]

theorem smul_eq_zero_of_map_infPartF {nS nT : ℕ} {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) :
    pairA F 1 0 • u = 0 := by
  ext i j
  exact smul_eq_zero_of_infPartF (congrFun (congrFun hu i) j)

theorem smul_eq_zero_of_map_finPartF {nS nT : ℕ} {u : WOF F E nS nT} (hu : u.map (finPartF F E) = 0) :
    pairA F 0 1 • u = 0 := by
  ext i j
  exact smul_eq_zero_of_finPartF (congrFun (congrFun hu i) j)

end Fin

theorem isThetaFunOF_heisOF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf
  have hψ : Continuous B.ψ := hB.std.1
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K, hK⟩ := exists_openAddSubgroup_psi_fin B.ψ hψ
    let φ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u
        map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero]
        map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }
    have hφ : Continuous φ := (continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)
    let ρ : WOF F E nS nT →+ Af F := (sndA F).toRingHom.toAddMonoidHom.comp φ
    have hρ : Continuous ρ := continuous_snd.comp hφ
    refine ⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩
    have h1 : pairA F 1 0 • u = 0 := smul_eq_zero_of_map_infPartF h0
    have hfst : fstA F (φ u) = 0 := by
      rw [← fstA_mul_idem]
      show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0
      rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right,
        sub_zero, map_zero]
    have hφu : φ u = pairA F 0 (ρ u) := Prod.ext hfst rfl
    have hone : B.ψ (φ u) = 1 := by rw [hφu]; exact hK _ hu.2
    have hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u) := by
      have : symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u := by
        show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _
        abel
      rw [this, AddChar.map_add_eq_mul, hone, one_mul]
    funext w
    have hw := congrFun (hUf u hu.1 h0) (w + w₀)
    simp only [heisOF] at hw ⊢
    rw [← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hswap]
    ring
  · show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)
    exact (hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · intro k L hL h0 w
    let φ₁ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀
        map_zero' := symplOHF_zero_left w₀
        map_add' := fun u v => symplOHF_add_left u v w₀ }
    let ev : AF F →+ ℝ :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)
    have hev : Continuous ev :=
      (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
        ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
    let g : (Fin k → ℝ) →+ ℝ := ev.comp (φ₁.comp L)
    have hg : Continuous g := hev.comp ((continuous_symplOHF_left w₀).comp hL)
    let gL := g.toRealLinearMap hg
    have hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) := by
      intro t
      have hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0 := by
        have h1 : pairA F 0 1 • L t = 0 := smul_eq_zero_of_map_finPartF (h0 t)
        rw [← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]
      rw [hB.std.2.2 _ ?_]
      · rfl
      · intro v hv
        have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv
        refine Prod.ext ?_ ?_
        · show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0
          rw [hv1, zero_mul]
        · show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0
          rw [show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]
    have hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t =>
        B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) *
          f (w + w₀ + L t) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]
    rw [hfun]
    refine (contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp

end GlobalTheory.HeisThetaF
