import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TvDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.EigBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate Classical InnerProductSpace

namespace UpperTheory.TypeLine

section Avg

variable {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]

private theorem chi_one {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) : χ 1 = 1 := by
  have h1 : χ 1 * χ 1 = χ 1 * 1 := by
    have := h.2.2 1 J.one_mem 1 J.one_mem
    rw [mul_one] at this
    rw [mul_one]
    exact this.symm
  have h2 : χ 1 ≠ 0 := fun e => by
    have := h.2.1 1 J.one_mem
    rw [e] at this
    simp at this
  exact mul_left_cancel₀ h2 h1

private theorem chi_conj {J : Subgroup G} {χ : G → ℂ} (h : IsChr J χ) {j : G} (hj : j ∈ J) :
    χ j * conj (χ j) = 1 := by
  rw [RCLike.mul_conj, h.2.1 j hj]
  simp

private theorem exists_avg (ρ : Representation ℂ G X) (hs : ∀ x, IsOpen {g | ρ g x = x}) {J : Subgroup G}
    {χ : G → ℂ} (hJ : CO J) (hχ : IsChr J χ) (y : X) :
    ∃ (ι : Type) (_ : Fintype ι) (t : ι → G), Nonempty ι ∧ (∀ i, t i ∈ J) ∧
      ∀ j ∈ J, ρ j (∑ i, conj (χ (t i)) • ρ (t i) y) = χ j • ∑ i, conj (χ (t i)) • ρ (t i) y := by
  classical
  haveI : CompactSpace J := isCompact_iff_compactSpace.1 hJ.1
  have h1 := chi_one hχ
  let H : Subgroup J :=
    { carrier := {j | ρ j.1 y = y ∧ χ j.1 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · show ρ (a.1 * b.1) y = y
          rw [map_mul, Module.End.mul_apply, hb, ha]
        · show χ (a.1 * b.1) = 1
          rw [hχ.2.2 _ a.2 _ b.2, ha', hb', one_mul]
      one_mem' := ⟨by simp, h1⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, ?_⟩
        · show ρ a.1⁻¹ y = y
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        · show χ a.1⁻¹ = 1
          have := hχ.2.2 _ a.2 _ (J.inv_mem a.2)
          rw [mul_inv_cancel, h1, ha', one_mul] at this
          exact this.symm }
  have hHo : IsOpen (H : Set J) := by
    have : (H : Set J) = Subtype.val ⁻¹' ({g | ρ g y = y} ∩ χ ⁻¹' {1}) := rfl
    rw [this]
    exact ((hs y).inter (hχ.1.isOpen_fiber 1)).preimage continuous_subtype_val
  haveI : Finite (J ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (J ⧸ H) := Fintype.ofFinite _
  refine ⟨J ⧸ H, inferInstance, fun c => (c.out : J).1, ⟨QuotientGroup.mk 1⟩, fun c => c.out.2, fun j hj => ?_⟩
  let F : J ⧸ H → X := fun c => conj (χ (c.out : J).1) • ρ (c.out : J).1 y
  have hF : ∀ a : J, F (QuotientGroup.mk a) = conj (χ a.1) • ρ a.1 y := by
    intro a
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H a
    show conj (χ ((QuotientGroup.mk a : J ⧸ H).out : J).1) • ρ ((QuotientGroup.mk a : J ⧸ H).out : J).1 y = _
    rw [hh]
    show conj (χ (a.1 * h.1.1)) • ρ (a.1 * h.1.1) y = _
    rw [hχ.2.2 _ a.2 _ h.1.2, h.2.2, mul_one, map_mul, Module.End.mul_apply, h.2.1]
  have hact : ∀ (a : J) (c : J ⧸ H), F (a • c) = conj (χ a.1) • ρ a.1 (F c) := by
    intro a c
    induction c using QuotientGroup.induction_on with
    | H b =>
      have e : a • (QuotientGroup.mk b : J ⧸ H) = QuotientGroup.mk (a * b) := rfl
      rw [e, hF, hF]
      show conj (χ (a.1 * b.1)) • ρ (a.1 * b.1) y = _
      rw [hχ.2.2 _ a.2 _ b.2, map_mul, map_mul, Module.End.mul_apply, map_smul, smul_smul]
  show ρ j (∑ c, F c) = χ j • ∑ c, F c
  let a : J := ⟨j, hj⟩
  have hsum : ∑ c, F c = ∑ c, F (a • c) := (Equiv.sum_comp (MulAction.toPerm a) F).symm
  calc ρ j (∑ c, F c) = ∑ c, ρ j (F c) := map_sum _ _ _
    _ = ∑ c, χ j • F (a • c) := Finset.sum_congr rfl fun c _ => by
        rw [hact, smul_smul]
        show ρ j (F c) = (χ j * conj (χ j)) • ρ j (F c)
        rw [chi_conj hχ hj, one_smul]
    _ = χ j • ∑ c, F c := by rw [← Finset.smul_sum, ← hsum]

end Avg

section Dense

variable {G H X : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [AddCommGroup X] [Module ℂ X]

private theorem ker_gen (R : UnitaryRep G H) {W V : Submodule ℂ H} (hV : IsSummandOf R W V) {f₀ : X →ₗ[ℂ] H}
    (hf0 : f₀ ≠ 0) (hf0V : ∀ x, f₀ x ∈ V) (Q : H →L[ℂ] H) (hQ : ∀ x y, Q (R x (f₀ y)) = 0) :
    ∀ v ∈ V, Q v = 0 := by
  set I : Submodule ℂ H := Submodule.span ℂ {v | ∃ x y, v = R x (f₀ y)} with hI
  have hIV : I ≤ V := Submodule.span_le.2 (by
    rintro _ ⟨x, y, rfl⟩
    exact hV.inv x _ (hf0V y))
  have hWV : I.topologicalClosure ≤ V := Submodule.topologicalClosure_minimal _ hIV hV.closed
  have hinvI : ∀ x, ∀ v ∈ I, R x v ∈ I := by
    intro x v hv
    have h : I ≤ I.comap (R x : H →ₗ[ℂ] H) := Submodule.span_le.2 (by
      rintro _ ⟨x', y, rfl⟩
      exact Submodule.subset_span ⟨x * x', y, (UnitaryRep.map_mul_apply _ _ _ _).symm⟩)
    exact h hv
  have hinvW : R.IsInvariant I.topologicalClosure := fun x v hv =>
    map_mem_closure (R x).continuous hv fun u hu => hinvI x u hu
  have hW : I.topologicalClosure = V := by
    rcases hV.irred _ hWV (Submodule.isClosed_topologicalClosure _) hinvW with h | h
    · exfalso
      refine hf0 (LinearMap.ext fun y => ?_)
      have h1 : f₀ y ∈ I.topologicalClosure :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨1, y, by simp⟩)
      rw [h] at h1
      simpa using h1
    · exact h
  have hIQ : I ≤ LinearMap.ker (Q : H →ₗ[ℂ] H) := Submodule.span_le.2 (by
    rintro _ ⟨x, y, rfl⟩
    exact hQ x y)
  have hWQ : V ≤ LinearMap.ker (Q : H →ₗ[ℂ] H) := by
    rw [← hW]
    exact Submodule.topologicalClosure_minimal _ hIQ (ContinuousLinearMap.isClosed_ker Q)
  exact fun v hv => hWQ hv

private theorem inter_gen {G' : Type*} [Group G'] (τ : Representation ℂ G' X) (A : G' → H →L[ℂ] H) (B : H →L[ℂ] H)
    (hB : ∀ g v, B (A g v) = A g (B v)) (f : X →ₗ[ℂ] H) (hf : ∀ g x, f (τ g x) = A g (f x)) (g : G') (x : X) :
    ((B : H →ₗ[ℂ] H) ∘ₗ f) (τ g x) = A g (((B : H →ₗ[ℂ] H) ∘ₗ f) x) := by
  show B (f (τ g x)) = A g (B (f x))
  rw [hf, hB]

end Dense

section Main

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]

private theorem mem_eigL {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {v : LL μ} :
    v ∈ eigL μ w J χ ↔ ∀ x ∈ J, rhoL μ w x v = χ x • v := by
  simp only [eigL, Submodule.mem_iInf, LinearMap.mem_eqLocus, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
    LinearMap.id_apply]

private theorem rhoL_inner (w : Pl K) (a : Gw n w) (u v : LL μ) :
    ⟪rhoL μ w a u, rhoL μ w a v⟫_ℂ = ⟪u, v⟫_ℂ :=
  UnitaryRep.inner_map_map _ _ _ _

private theorem prj_avg {w : Pl K} {J : Subgroup (Gw n w)} {χ : Gw n w → ℂ} {ι : Type} [Fintype ι] [Nonempty ι]
    (t : ι → Gw n w) (ht : ∀ i, t i ∈ J) (x z : LL μ)
    (hz : z = (Fintype.card ι : ℂ)⁻¹ • ∑ i, conj (χ (t i)) • rhoL μ w (t i) x) (hm : z ∈ eigL μ w J χ) :
    prj (eigL μ w J χ) x = z := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.le_topologicalClosure _ hm) fun u hu => ?_
  have h0 : x - z ∈ (eigL μ w J χ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' := (mem_eigL μ).1 hu
    have h1 : ∀ i, ⟪u, conj (χ (t i)) • rhoL μ w (t i) x⟫_ℂ = ⟪u, x⟫_ℂ := fun i => by
      rw [inner_smul_right, ← inner_smul_left, ← hu' _ (ht i), rhoL_inner]
    have hc : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [inner_sub_right, hz, inner_smul_right, inner_sum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, sub_self]
  rw [← Submodule.orthogonal_closure] at h0
  exact (Submodule.mem_orthogonal' _ _).1 h0 u hu

private theorem exists_split (w : Pl K) (x : normOneGL K n) :
    ∃ (c : normOneGL K n) (a : Gw n w),
      x = c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w a) ∧
      ∀ g : Gw n w, c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) =
        MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) * c := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj x
  obtain ⟨-, h2, -, -, h5⟩ := UpperTheory.ConvolutionTheory.Tf.locEmb K n w
  have e : ∀ y : AdelicGLn.FiniteAdelicGL K n,
      finAt w (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y w := fun y => by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n y)).2) w = _
    rw [prodEquiv_finEmb]
  set a := finAt w (finEmb K n u) with ha
  set u' := u * (AdelicGLn.localEmbedding w a)⁻¹ with hu'
  have hu1 : finAt w (finEmb K n u') = 1 := by
    rw [e, hu', map_mul, map_inv, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, ← e, ← e, h2, ← ha,
      mul_inv_cancel]
  refine ⟨archProj K n A * MultiplicityOne.finProj K n u', a, ?_, fun g => ?_⟩
  · rw [mul_assoc, ← map_mul, hu', inv_mul_cancel_right]
  · have h := h5 u' hu1 g
    rw [mul_assoc, ← map_mul, ← h, map_mul, ← mul_assoc, ← mul_assoc,
      MultiplicityOne.finProj_mul_archProj_comm]

private theorem rho_comm {w : Pl K} {c : normOneGL K n}
    (hc : ∀ g : Gw n w, c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) =
      MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g) * c) (g : Gw n w) (v : LL μ) :
    rightRegularRep (rationalGLOne K n) μ c (rhoL μ w g v) =
      rhoL μ w g (rightRegularRep (rationalGLOne K n) μ c v) := by
  have h := UnitaryRep.map_mul_apply (rightRegularRep (rationalGLOne K n) μ) c
    (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v
  have h' := UnitaryRep.map_mul_apply (rightRegularRep (rationalGLOne K n) μ)
    (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) c v
  rw [hc g] at h
  exact h.symm.trans h'

private theorem ker_of_all {V : Submodule ℂ (LL μ)} (hV : IsSummand μ V) {w : Pl K} {π : SmIrr (Gw n w)}
    (hocc : Occurs μ V w π) (Q : LL μ →L[ℂ] LL μ)
    (hQ : ∀ f : π.V →ₗ[ℂ] LL μ, (∀ g x, f (π.ρ g x) = rhoL μ w g (f x)) → ∀ y, Q (f y) = 0) :
    ∀ v ∈ V, Q v = 0 := by
  obtain ⟨f₀, hf0, hf0V, hf0i⟩ := hocc
  refine ker_gen _ hV hf0 hf0V Q fun x y => ?_
  obtain ⟨c, a, rfl, hc⟩ := exists_split (n := n) w x
  have h2 := hQ _ (inter_gen π.ρ (rhoL μ w) (rightRegularRep (rationalGLOne K n) μ c) (rho_comm μ hc) f₀ hf0i) (π.ρ a y)
  have e2 : rightRegularRep (rationalGLOne K n) μ (c * MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w a)) (f₀ y) =
      rightRegularRep (rationalGLOne K n) μ c (f₀ (π.ρ a y)) :=
    (UnitaryRep.map_mul_apply _ c _ (f₀ y)).trans (congrArg _ (hf0i a y).symm)
  rw [e2]
  exact h2

end Main

end UpperTheory.TypeLine

open UpperTheory.TypeLine in
theorem UpperTheory.exists_unique_eigenline_of_rankOne_occurs :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
        IsSummand μ V → ∀ (w : Pl K) (τ : SmIrr (Gw n w)), Occurs μ V w τ → ∀ (J : Subgroup (Gw n w)) (χ : Gw n w → ℂ),
        CO J → IsChr J χ → RankOne μ V w J χ → V ⊓ eigL μ w J χ ≠ ⊥ →
        ∃ e : τ.V, e ≠ 0 ∧ (∀ g ∈ J, τ.ρ g e = χ g • e) ∧ ∀ x : τ.V, (∀ g ∈ J, τ.ρ g x = χ g • x) → ∃ c : ℂ, x = c • e := by
  intro K _ _ n μ _ V hV w τ hocc J χ hJ hχ hrk hne
  set P := prj (eigL μ w J χ) with hP
  let IsE : τ.V → Prop := fun x => ∀ g ∈ J, τ.ρ g x = χ g • x
  have hself : ∀ u ∈ eigL μ w J χ, P u = u := fun u hu =>
    Submodule.starProjection_eq_self_iff.2 (Submodule.le_topologicalClosure _ hu)
  have hE : ∀ y, ∃ y', IsE y' ∧ ∀ f : τ.V →ₗ[ℂ] LL μ, (∀ g x, f (τ.ρ g x) = rhoL μ w g (f x)) →
      P (f y) = f y' := by
    intro y
    obtain ⟨ι, _, t, hne', ht, hav⟩ := exists_avg τ.ρ τ.smooth hJ hχ y
    have hy : IsE ((Fintype.card ι : ℂ)⁻¹ • ∑ i, conj (χ (t i)) • τ.ρ (t i) y) := fun g hg => by
      rw [map_smul, hav g hg, smul_comm]
    refine ⟨_, hy, fun f hf => ?_⟩
    refine prj_avg μ t ht _ _ ?_ ((mem_eigL μ).2 fun g hg => ?_)
    · simp only [map_smul, map_sum, hf]
    · rw [← hf, hy g hg, map_smul]
  have hex : ∃ e, e ≠ 0 ∧ IsE e := by
    by_contra hno
    have hz : ∀ y, IsE y → y = 0 := fun y hy => by
      by_contra h
      exact hno ⟨y, h, hy⟩
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have h0 := ker_of_all μ hV hocc P (fun f hf y => by
      obtain ⟨y', h1, h2⟩ := hE y
      rw [h2 f hf, hz y' h1, map_zero]) v hv.1
    exact hv0 ((hself v hv.2).symm.trans h0)
  obtain ⟨e, he0, he⟩ := hex
  refine ⟨e, he0, he, fun x hx => ?_⟩
  obtain ⟨f, hf0, hfV, hfi⟩ := hocc
  have hirr := (isIrreducible_iff τ.ρ).1 τ.irred
  have hinj : LinearMap.ker f = ⊥ := (hirr.2 _ (fun g v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hfi, hv, map_zero])).resolve_right fun h => hf0 (LinearMap.ker_eq_top.1 h)
  have hfe : f e ∈ V ⊓ eigL μ w J χ :=
    ⟨hfV e, (mem_eigL μ).2 fun g hg => by rw [← hfi, he g hg, map_smul]⟩
  set S : Submodule ℂ τ.V := Submodule.span ℂ (Set.range fun g => τ.ρ g e) with hSdef
  have heS : e ∈ S := Submodule.subset_span ⟨1, by simp⟩
  have hS : S = ⊤ := by
    refine (hirr.2 S fun g v hv => ?_).resolve_left fun h => he0 (by simpa [h] using heS)
    have h : S ≤ S.comap (τ.ρ g) := Submodule.span_le.2 (by
      rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by simp [map_mul]⟩)
    exact h hv
  have hSW : ∀ y ∈ S, ∃ c : ℂ, P (f y) = c • f e := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hy
      obtain ⟨c, hc⟩ := hrk g
      exact ⟨c, by rw [hfi]; exact hc _ hfe⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [map_add, map_add, hc, hd, add_smul]⟩
    | smul a b _ hb =>
      obtain ⟨c, hc⟩ := hb
      exact ⟨a * c, by rw [map_smul, map_smul, hc, smul_smul]⟩
  obtain ⟨c, hc⟩ := hSW x (hS ▸ Submodule.mem_top)
  have hfx : P (f x) = f x := hself _ ((mem_eigL μ).2 fun g hg => by rw [← hfi, hx g hg, map_smul])
  refine ⟨c, LinearMap.ker_eq_bot.1 hinj ?_⟩
  rw [map_smul, ← hc, hfx]
