import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import GroundTheory.AutomorphicForms.SphericalCommutative

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {ν : Measure G} [ν.IsHaarMeasure] {J : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem mem_dc {x y : G} :
    y ∈ (J : Set G) * {x} * (J : Set G) ↔ ∃ a ∈ J, ∃ b ∈ J, y = a * x * b := by
  constructor
  · rintro ⟨p, ⟨a, ha, q, hq, rfl⟩, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a * x, ⟨a, ha, x, rfl, rfl⟩, b, hb, rfl⟩

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem dc_compact (hJc : IsCompact (J : Set G)) (x : G) :
    IsCompact ((J : Set G) * {x} * (J : Set G)) :=
  (hJc.mul isCompact_singleton).mul hJc

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G]
  [BorelSpace G] in
private theorem dc_open (hJo : IsOpen (J : Set G)) (x : G) :
    IsOpen ((J : Set G) * {x} * (J : Set G)) :=
  hJo.mul_left

variable (ν) in

private noncomputable def dcF (hJc : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (x : G) : HeckeAlgebra ν :=
  HeckeAlgebra.mk ν (((J : Set G) * {x} * (J : Set G)).indicator fun _ => (1 : ℂ))
    (indicator_mem_locallyConstantCompactSupport (dc_compact hJc x) (dc_open hJo x) _)

private theorem dcF_apply (hJc : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (x y : G) :
    dcF ν hJc hJo x y = ((J : Set G) * {x} * (J : Set G)).indicator (fun _ => (1 : ℂ)) y := rfl

private theorem dcF_mem (hJc : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (x : G) :
    dcF ν hJc hJo x ∈ HeckeAlgebra.biInvariant ν J := by
  intro k hk y
  have hl : k * y ∈ (J : Set G) * {x} * (J : Set G) ↔ y ∈ (J : Set G) * {x} * (J : Set G) := by
    simp only [mem_dc]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨k⁻¹ * a, mul_mem (inv_mem hk) ha, b, hb, by
        rw [mul_assoc, mul_assoc, ← mul_assoc a, ← h, inv_mul_cancel_left]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨k * a, mul_mem hk ha, b, hb, by simp only [mul_assoc]⟩
  have hr : y * k ∈ (J : Set G) * {x} * (J : Set G) ↔ y ∈ (J : Set G) * {x} * (J : Set G) := by
    simp only [mem_dc]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨a, ha, b * k⁻¹, mul_mem hb (inv_mem hk), by
        rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩
  have key : ∀ a b, (a ∈ (J : Set G) * {x} * (J : Set G) ↔ b ∈ (J : Set G) * {x} * (J : Set G)) →
      ((J : Set G) * {x} * (J : Set G)).indicator (fun _ => (1 : ℂ)) a =
        ((J : Set G) * {x} * (J : Set G)).indicator (fun _ => (1 : ℂ)) b := by
    intro a b h
    by_cases hb : b ∈ (J : Set G) * {x} * (J : Set G)
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h.2 hb)]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (fun ha => hb (h.1 ha))]
  exact ⟨key _ _ hl, key _ _ hr⟩

private theorem act_eq_sum (hJc : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G)) (x : G)
    (S : Finset (G ⧸ J)) (hS : (S : Set (G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)})
    {v : V} (hv : v ∈ fixedVectors ρ J) :
    heckeAct ν ρ (dcF ν hJc hJo x) v = ((ν.real (J : Set G) : ℝ) : ℂ) • ∑ c ∈ S, ρ c.out v := by
  refine eq_of_forall_dual fun φ => ?_
  rw [dual_heckeAct ν (dcF ν hJc hJo x).mem (smooth_of_mem_fixedVectors hJo hv) φ]
  have hout : ∀ c ∈ S, c.out ∈ (J : Set G) * {x} * (J : Set G) := by
    intro c hc
    have hc' : c ∈ (S : Set (G ⧸ J)) := hc
    rw [hS] at hc'
    obtain ⟨k, hk, rfl⟩ := hc'
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J (k * x)
    rw [mem_dc]
    exact ⟨k, hk, j, j.2, hj⟩
  have hfs : (finite_image_mk_of_isCompact (⟨J, hJo⟩ : OpenSubgroup G) (dc_compact hJc x)).toFinset = S := by
    refine Finset.coe_injective ?_
    rw [Set.Finite.coe_toFinset, hS]
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_dc.1 hy
      exact ⟨a, ha, (QuotientGroup.mk_mul_of_mem _ hb)⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k * x, mem_dc.2 ⟨k, hk, 1, one_mem _, by simp⟩, rfl⟩
  have key := integral_eq_smul_sum_coset ν (⟨J, hJo⟩ : OpenSubgroup G) hJc (dc_compact hJc x)
    (f := fun g => dcF ν hJc hJo x g * φ (ρ g v))
    (fun y hy => by
      by_contra h
      exact hy (by rw [dcF_apply, Set.indicator_of_notMem h, zero_mul]))
    (fun g k hk => by
      have h1 := ((dcF_mem (ν := ν) hJc hJo x) k hk g).2
      have h2 : ρ k v = v := hv k hk
      simp only [h1, map_mul, Module.End.mul_apply, h2])
  rw [key, hfs, map_smul, map_sum, Complex.real_smul, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [dcF_apply, Set.indicator_of_mem (hout c hc), one_mul]

private theorem comm_abstract (hJc : IsCompact (J : Set G)) (hJo : IsOpen (J : Set G))
    (hcomm : ∀ a b : HeckeAlgebra.HeckeAlgebraLevel ν J hJc hJo, a * b = b * a)
    (Tx Ty : V → V) (x y : G) (Sx Sy : Finset (G ⧸ J))
    (hSx : (Sx : Set (G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * x)})
    (hSy : (Sy : Set (G ⧸ J)) = {c | ∃ k ∈ J, c = QuotientGroup.mk (k * y)})
    (hTx : ∀ v ∈ fixedVectors ρ J, Tx v = ∑ c ∈ Sx, ρ c.out v)
    (hTy : ∀ v ∈ fixedVectors ρ J, Ty v = ∑ c ∈ Sy, ρ c.out v)
    (hmx : ∀ v ∈ fixedVectors ρ J, Tx v ∈ fixedVectors ρ J)
    (hmy : ∀ v ∈ fixedVectors ρ J, Ty v ∈ fixedVectors ρ J)
    {v : V} (hv : v ∈ fixedVectors ρ J) : Tx (Ty v) = Ty (Tx v) := by
  have hc : ((ν.real (J : Set G) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (HeckeAlgebra.measureReal_compactOpen_pos ν hJc hJo).ne'
  have ax : ∀ u ∈ fixedVectors ρ J, heckeAct ν ρ (dcF ν hJc hJo x) u = ((ν.real (J : Set G) : ℝ) : ℂ) • Tx u :=
    fun u hu => by rw [act_eq_sum hJc hJo x Sx hSx hu, hTx u hu]
  have ay : ∀ u ∈ fixedVectors ρ J, heckeAct ν ρ (dcF ν hJc hJo y) u = ((ν.real (J : Set G) : ℝ) : ℂ) • Ty u :=
    fun u hu => by rw [act_eq_sum hJc hJo y Sy hSy hu, hTy u hu]
  have hs := smooth_of_mem_fixedVectors hJo hv
  have e1 : heckeAct ν ρ (dcF ν hJc hJo x) (heckeAct ν ρ (dcF ν hJc hJo y) v) =
      heckeAct ν ρ (dcF ν hJc hJo y) (heckeAct ν ρ (dcF ν hJc hJo x) v) := by
    have h := hcomm (HeckeAlgebra.HeckeAlgebraLevel.mk hJc hJo _ (dcF_mem hJc hJo x))
      (HeckeAlgebra.HeckeAlgebraLevel.mk hJc hJo _ (dcF_mem hJc hJo y))
    have h' := congrArg (HeckeAlgebra.HeckeAlgebraLevel.val hJc hJo) h
    have h'' : dcF ν hJc hJo x * dcF ν hJc hJo y = dcF ν hJc hJo y * dcF ν hJc hJo x := h'
    rw [← HeckeAlgebra.heckeAct_mul _ _ hs, ← HeckeAlgebra.heckeAct_mul _ _ hs, h'']
  rw [ay v hv, ax v hv, heckeAct_smul_right (dcF ν hJc hJo x).mem _ (smooth_of_mem_fixedVectors hJo (hmy v hv)),
    heckeAct_smul_right (dcF ν hJc hJo y).mem _ (smooth_of_mem_fixedVectors hJo (hmx v hv)),
    ax _ (hmy v hv), ay _ (hmx v hv)] at e1
  exact smul_right_injective V hc (smul_right_injective V hc e1)

end Abstract

section Concrete

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K)

private theorem rhoL_mul (g h : GL (Fin n) (w.adicCompletion K)) :
    rhoL μ w (g * h) = rhoL μ w g ∘L rhoL μ w h := by
  unfold rhoL
  rw [map_mul]
  exact (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1 _ _

private theorem rhoL_one : rhoL μ w (1 : GL (Fin n) (w.adicCompletion K)) = 1 := by
  unfold rhoL
  rw [map_one]
  exact (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.1

private noncomputable def locRep : Representation ℂ (GL (Fin n) (w.adicCompletion K)) (LL μ) where
  toFun g := (rhoL μ w g : LL μ →ₗ[ℂ] LL μ)
  map_one' := by
    rw [rhoL_one]
    rfl
  map_mul' g h := by
    rw [rhoL_mul]
    rfl

private theorem mem_fixL_iff (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (v : LL μ) :
    v ∈ fixL μ w J ↔ v ∈ fixedVectors (locRep μ w) J := by
  have h := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ (J.map (AdelicGLn.localEmbedding w))).2.1 v
  constructor
  · intro hv k hk
    exact (h.1 hv) _ (Subgroup.mem_map_of_mem _ hk)
  · intro hv
    refine h.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hv k hk

private theorem comm_same (x y : GL (Fin n) (w.adicCompletion K)) :
    Commute (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x)
      (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) y) := by
  letI : MeasurableSpace (GL (Fin n) (w.adicCompletion K)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.adicCompletion K)) := ⟨rfl⟩
  have hJc := GLnLocal.isCompact_integralGL (w.adicCompletion K) n
  have hJo := GLnLocal.isOpen_integralGL (w.adicCompletion K) n
  obtain ⟨fx, mx, px, sx, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w _ x hJo hJc
  obtain ⟨fy, my, py, sy, -, -⟩ := UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w _ y hJo hJc
  have red : ∀ (z : GL (Fin n) (w.adicCompletion K))
      (f : {c : GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.integralGL (w.adicCompletion K) n |
        ∃ k ∈ GLnLocal.integralGL (w.adicCompletion K) n, c = QuotientGroup.mk (k * z)}.Finite)
      (s : ∀ (ι : Type) [Fintype ι] (y : ι → GL (Fin n) (w.adicCompletion K)),
        Function.Injective (fun i => (QuotientGroup.mk (y i) :
          GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.integralGL (w.adicCompletion K) n)) →
        Set.range (fun i => (QuotientGroup.mk (y i) :
          GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.integralGL (w.adicCompletion K) n)) =
          {c | ∃ k ∈ GLnLocal.integralGL (w.adicCompletion K) n, c = QuotientGroup.mk (k * z)} →
        ∀ v ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n),
          Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) z v = ∑ i, rhoL μ w (y i) v),
      ∀ v ∈ fixedVectors (locRep μ w) (GLnLocal.integralGL (w.adicCompletion K) n),
        Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) z v =
          ∑ c ∈ f.toFinset, locRep μ w c.out v := by
    intro z f s v hv
    have := s (↥f.toFinset) (fun i => i.1.out)
      (fun a b h => Subtype.ext (by
        have h' : (QuotientGroup.mk a.1.out :
            GL (Fin n) (w.adicCompletion K) ⧸ GLnLocal.integralGL (w.adicCompletion K) n) =
            QuotientGroup.mk b.1.out := h
        rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'))
      (by
        ext c
        constructor
        · rintro ⟨i, rfl⟩
          simpa [QuotientGroup.out_eq'] using (f.mem_toFinset.1 i.2)
        · intro hc
          exact ⟨⟨c, f.mem_toFinset.2 hc⟩, QuotientGroup.out_eq' c⟩)
      v ((mem_fixL_iff μ w _ v).2 hv)
    rw [this, ← Finset.sum_coe_sort f.toFinset]
    rfl
  have hcomm := GroundTheory.Automorphic.Spherical.heckeAlgebraLevel_mul_comm
    (F := w.adicCompletion K) (n := n) (μ := Measure.haar)
  have main := fun (p : LL μ) (hp : p ∈ fixedVectors (locRep μ w) (GLnLocal.integralGL (w.adicCompletion K) n)) =>
    comm_abstract (ν := Measure.haar) (ρ := locRep μ w) hJc hJo hcomm
      (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x)
      (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) y) x y fx.toFinset fy.toFinset
      (by simp) (by simp) (red x fx sx) (red y fy sy)
      (fun v _ => (mem_fixL_iff μ w _ _).1 (mx v)) (fun v _ => (mem_fixL_iff μ w _ _).1 (my v)) hp
  refine ContinuousLinearMap.ext fun v => ?_
  have hp := (mem_fixL_iff μ w _ _).1
    ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ((GLnLocal.integralGL (w.adicCompletion K) n).map (AdelicGLn.localEmbedding w))).2.2.1 v)
  have ex : ∀ u, Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x u =
      Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x (prj (fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n)) u) :=
    fun u => (congrArg (fun T => T u) px).symm
  have ey : ∀ u, Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) y u =
      Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) y (prj (fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n)) u) :=
    fun u => (congrArg (fun T => T u) py).symm
  change Hop μ w _ x (Hop μ w _ y v) = Hop μ w _ y (Hop μ w _ x v)
  rw [ey v, ex v]
  exact main _ hp

private theorem rhoL_comm {w w' : Pl K} (h : w ≠ w') (g : GL (Fin n) (w.adicCompletion K))
    (g' : GL (Fin n) (w'.adicCompletion K)) : Commute (rhoL μ w g) (rhoL μ w' g') := by
  have hm := (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1
  have hc := (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.2.2.1 w' h.symm g g'
  change rhoF μ _ ∘L rhoF μ _ = rhoF μ _ ∘L rhoF μ _
  rw [← hm, ← hm]
  unfold rhoL at *
  rw [hc]

end Concrete

theorem UpperTheory.ConvolutionTheory.Tf.tsphComm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w w' : Pl K),
      (∀ x y : GL (Fin n) (w.adicCompletion K), Commute (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) y)) ∧
      (w ≠ w' → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)) (J' : Subgroup (GL (Fin n) (w'.adicCompletion K))) (x' : GL (Fin n) (w'.adicCompletion K)),
        IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) → IsOpen (J' : Set (GL (Fin n) (w'.adicCompletion K))) →
        IsCompact (J' : Set (GL (Fin n) (w'.adicCompletion K))) → Commute (Hop μ w J x) (Hop μ w' J' x')) ∧
      ∀ i i', Commute (Tsph μ w i) (Tsph μ w' i') := by
  intro K _ _ n μ _ w w'
  have hd : w ≠ w' → ∀ (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K)) (J' : Subgroup (GL (Fin n) (w'.adicCompletion K))) (x' : GL (Fin n) (w'.adicCompletion K)),
        IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) → IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))) → IsOpen (J' : Set (GL (Fin n) (w'.adicCompletion K))) →
        IsCompact (J' : Set (GL (Fin n) (w'.adicCompletion K))) → Commute (Hop μ w J x) (Hop μ w' J' x') := by
    intro h J x J' x' hJo hJc hJo' hJc'
    have b := (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x hJo hJc).2.2.2.2.1
    have b' := (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w' J' x' hJo' hJc').2.2.2.2.1
    refine (b _ fun g => ?_).symm
    exact (b' _ fun g' => (rhoL_comm μ h g g')).symm
  refine ⟨comm_same μ w, hd, fun i i' => ?_⟩
  unfold Tsph
  refine Commute.smul_left (Commute.smul_right ?_ _) _
  by_cases h : w = w'
  · subst h
    exact comm_same μ w _ _
  · exact hd h _ _ _ _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)
