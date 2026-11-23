import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteAdeleStrongApproximationModNat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionFractionalIdealProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharFin

theorem finite_order_of_small {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [TopologicalSpace R] [TopologicalSpace A] [TopologicalSpace B] [ContinuousAdd B]
    (p : R →+* A) (q : R →+* B) (s : A × B → R) (hs : Continuous s) (hsz : ∀ z, s (p z, q z) = z)
    (S : Subring B) (hsmall : ∀ W ∈ 𝓝 (0 : B), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ S, N • y ∈ W)
    (hfin : ∀ N : ℕ, 0 < N → Finite (S ⧸ Ideal.span {(N : S)}))
    (χ : Rˣ →* Circle) (hχ : Continuous χ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) →
      (∃ y ∈ S, q x - 1 = N • y) → χ x = 1) ∧
      ∃ m : ℕ, 0 < m ∧ ∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) → χ x ^ m = 1 := by
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Rˣ) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  let f : B → R := fun b => s (1, 1 + b)
  have hf : Continuous f := hs.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hf0 : f 0 = 1 := by simpa [f] using hsz 1
  have h1 : f ⁻¹' T1 ∈ 𝓝 (0 : B) := hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hT1)
  have h2 : (fun b => MulOpposite.op (f b)) ⁻¹' T2 ∈ 𝓝 (0 : B) :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, hf0]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := hsmall _ (Filter.inter_mem h1 h2)
  have hpinv : ∀ x : Rˣ, p x = 1 → p (x⁻¹ : Rˣ) = 1 := fun x hx => by
    have := congrArg p x.mul_inv
    rwa [map_mul, hx, one_mul, map_one] at this
  let G : Subgroup Rˣ :=
    { carrier := {x | p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by simp [hx.1, hy.1], ?_, ?_⟩
        · rw [Units.val_mul, map_mul]; exact mul_mem hx.2.1 hy.2.1
        · rw [mul_inv, Units.val_mul, map_mul]; exact mul_mem hx.2.2 hy.2.2
      inv_mem' := fun {x} hx => ⟨hpinv x hx.1, hx.2.2, by simpa using hx.2.1⟩ }
  let ψ : G →* S :=
    { toFun := fun x => ⟨q (x : Rˣ), x.2.2.1⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  let φ : G →* (S ⧸ Ideal.span {(N : S)})ˣ :=
    ((Ideal.Quotient.mk (Ideal.span {(N : S)})).toMonoidHom.comp ψ).toHomUnits
  have hφ : ∀ x : G, φ x = 1 ↔ ∃ y ∈ S, q (x : Rˣ) - 1 = N • y := by
    intro x
    have : φ x = 1 ↔ Ideal.Quotient.mk (Ideal.span {(N : S)}) (ψ x) = Ideal.Quotient.mk _ 1 := by
      rw [Units.ext_iff]; rfl
    rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by simpa [ψ] using congrArg Subtype.val hy⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ] using h)⟩
  have hfx : ∀ x : G, φ x = 1 → ∃ y ∈ S, ((x : Rˣ) : R) = f (N • y) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := (hφ x).1 hx
    refine ⟨y, hy, ?_⟩
    have := hsz (x : Rˣ)
    rw [x.2.1] at this
    simp only [f, ← h, add_sub_cancel, this]
  have harc : ∀ x : G, φ x = 1 → χ x ∈ Circle.centeredArc (Real.pi / 2) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hfx x hx
    obtain ⟨y', hy', h'⟩ := hfx x⁻¹ (by rw [map_inv, hx, inv_one])
    refine hTV (hTT ⟨?_, ?_⟩)
    · change ((x : Rˣ) : R) ∈ T1
      rw [h]; exact (hNW y hy).1
    · change MulOpposite.op (((x⁻¹ : G) : Rˣ) : R) ∈ T2
      rw [h']; exact (hNW y' hy').2
  have hker : ∀ x : G, φ x = 1 → χ x = 1 := by
    intro x hx
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have := harc (x ^ n) (by rw [map_pow, hx, one_pow])
    rwa [Subgroup.coe_pow, map_pow] at this
  haveI := hfin N hN
  refine ⟨N, hN, fun x hx h => hker ⟨x, hx⟩ ((hφ _).2 h),
    Nat.card (S ⧸ Ideal.span {(N : S)})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have := hker ((⟨x, hx⟩ : G) ^ Nat.card (S ⧸ Ideal.span {(N : S)})ˣ)
    (by rw [map_pow, pow_card_eq_one'])
  rwa [Subgroup.coe_pow, map_pow] at this

open GlobalTheory.AdLat

section Integral

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' := fun hx hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) hx hy

theorem mem_hatRing (z : RA F E) :
    z ∈ hatRing F E ↔ z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := Iff.rfl

theorem exists_int_add_nsmul (N : ℕ) (hN : 0 < N) (z : RA F E)
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ (x : 𝓞 E), ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + N • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hz
    obtain ⟨r, b, hb, rfl⟩ := (strong_approximation_mod_nat F N hN).2 a ha
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r * x, _, tmul_mem_adelicCompletion_of_integral F hb ⟨x, rfl⟩, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one (r : F),
      TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    obtain ⟨y, w, hw, rfl⟩ := hy
    refine ⟨x + y, u + w, add_mem hu hw, ?_⟩
    rw [show ((x + y : 𝓞 E) : E) = (x : E) + y from rfl, TensorProduct.tmul_add, smul_add]; abel
  | neg x _ hx =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    refine ⟨-x, -u, neg_mem hu, ?_⟩
    rw [show ((-x : 𝓞 E) : E) = -(x : E) from rfl, TensorProduct.tmul_neg, smul_neg]; abel

theorem finite_quotient_hatRing (N : ℕ) (hN : 0 < N) :
    Finite (hatRing F E ⧸ Ideal.span {(N : hatRing F E)}) := by
  let ι : 𝓞 E →+* hatRing F E :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F)
      (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _
      fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)})
    (Ideal.span {(N : hatRing F E)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : hatRing F E)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := exists_int_add_nsmul F E N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : RA F E) - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) = ((N : hatRing F E) : RA F E) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

end Integral

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_finUnit_finite_order : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  intro D χ hχ
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (RA D.host.F D.host.E) := ⟨rfl⟩
  haveI : ContinuousAdd (RA D.host.F D.host.E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) _
  have hsmall := (OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (by simp)).2
  have := finite_order_of_small (infPart D) (finPart D) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (hatRing D.host.F D.host.E) hsmall (finite_quotient_hatRing D.host.F D.host.E) χ hχ
  unfold FinUnit
  rw [integralFiniteAdeles_eq_adelicCompletion_integers]
  exact this

end GlobalTheory.CharFin
