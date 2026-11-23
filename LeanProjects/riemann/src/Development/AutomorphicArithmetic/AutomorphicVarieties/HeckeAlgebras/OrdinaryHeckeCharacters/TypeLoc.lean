import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LeSpanIntegralValuedOfGaloisStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralRepDetectingInvariantSubspace
open GlobalTheory.CuspRep

noncomputable section

namespace UpperTheory.V.Hi.TyLoc

private theorem avg {Q N : Type} [Group Q] [Fintype Q] [AddCommGroup N] [Module ℂ N] {d : ℕ}
    (ξ : Representation ℂ Q (Fin d → ℂ)) (π : Representation ℂ Q N) :
    (∃ f : (Fin d → ℂ) →ₗ[ℂ] N, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π k (f v)) ↔
      ∃ i v n, ∑ g, ξ g⁻¹ v i • π g n ≠ 0 := by
  classical
  constructor
  · rintro ⟨f, hf, he⟩
    by_contra hc
    push Not at hc
    refine hf (LinearMap.ext fun v => ?_)
    have h1 : ∀ g, ∑ i, ξ g⁻¹ v i • π g (f (Pi.single i 1)) = f v := fun g => by
      have : ∑ i, ξ g⁻¹ v i • (Pi.single i 1 : Fin d → ℂ) = ξ g⁻¹ v := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      simp only [← map_smul, ← map_sum]
      rw [this, ← he, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h2 : ∑ g : Q, f v = 0 := by
      rw [← Finset.sum_congr rfl fun g _ => h1 g, Finset.sum_comm]
      exact Finset.sum_eq_zero fun i _ => hc i v _
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact (smul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · rintro ⟨i, v, n, h⟩
    refine ⟨∑ g, (LinearMap.toSpanSingleton ℂ N (π g n)) ∘ₗ (LinearMap.proj i) ∘ₗ ξ g⁻¹, fun h0 => h ?_, fun k v => ?_⟩
    · simpa using LinearMap.congr_fun h0 v
    · simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.proj_apply, map_sum, map_smul]
      rw [← Equiv.sum_comp (Equiv.mulLeft k)]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Equiv.coe_mulLeft, ← Module.End.mul_apply (ξ _), ← map_mul, mul_inv_rev, inv_mul_cancel_right, map_mul,
        Module.End.mul_apply]

private def Tw (_γ : ℂ ≃+* ℂ) (V : Type) : Type := V

private instance (γ : ℂ ≃+* ℂ) (V : Type) [h : AddCommGroup V] : AddCommGroup (Tw γ V) := h

private instance (γ : ℂ ≃+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] : Module ℂ (Tw γ V) :=
  Module.compHom V γ.toRingHom

private theorem twist {G : Type} [Group G] [TopologicalSpace G] (γ : ℂ ≃+* ℂ) (σ' : SmIrr G) :
    ∃ (σ : SmIrr G) (f : σ.V ≃+ σ'.V), (∀ (z : ℂ) v, f (z • v) = γ z • f v) ∧ ∀ g v, f (σ.ρ g v) = σ'.ρ g (f v) := by
  let ρ : Representation ℂ G (Tw γ σ'.V) :=
    { toFun := fun g =>
        { toFun := fun v => σ'.ρ g v
          map_add' := fun x y => map_add (σ'.ρ g) x y
          map_smul' := fun z x => (σ'.ρ g).map_smul (γ z) x }
      map_one' := LinearMap.ext fun v => LinearMap.congr_fun (map_one σ'.ρ) v
      map_mul' := fun a b => LinearMap.ext fun v => LinearMap.congr_fun (map_mul σ'.ρ a b) v }
  obtain ⟨h0, h⟩ := (isIrreducible_iff _).1 σ'.irred
  refine ⟨⟨Tw γ σ'.V, ρ, σ'.smooth, (isIrreducible_iff _).2 ⟨h0, fun W hW => ?_⟩⟩, AddEquiv.refl _, fun _ _ => rfl,
    fun _ _ => rfl⟩
  let W' : Submodule ℂ σ'.V :=
    { carrier := W.carrier
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := fun z x hx => by
        have h1 : γ (γ.symm z) • x ∈ W.carrier := W.smul_mem (γ.symm z) hx
        rwa [γ.apply_symm_apply] at h1 }
  refine (h W' hW).imp (fun e => ?_) fun e => ?_
  · exact (Submodule.eq_bot_iff _).2 fun x hx => (Submodule.eq_bot_iff _).1 e x hx
  · exact Submodule.eq_top_iff'.2 fun x => Submodule.eq_top_iff'.1 e x

end UpperTheory.V.Hi.TyLoc

open UpperTheory.V.Hi.TyLoc in
theorem UpperTheory.V.Hi.typeLoc : ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Algebra O ℂ] [FaithfulSMul O ℂ] [Algebra.IsAlgebraic O ℂ] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsCompact (K : Set G) → ∀ (P : SmIrr G → Prop) (d : ℕ) (ξ : Representation ℂ K (Fin d → ℂ)), GlobalTheory.PRep.IsSmooth ξ → (∀ π : SmIrr G, (∃ f : (Fin d → ℂ) →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ k v, f (ξ k v) = π.ρ k (f v)) ↔ P π) → (∀ (γ : ℂ ≃ₐ[O] ℂ) (σ σ' : SmIrr G) (f : σ.V ≃+ σ'.V), (∀ (z : ℂ) v, f (z • v) = γ z • f v) → (∀ g v, f (σ.ρ g v) = σ'.ρ g (f v)) → P σ → P σ') → ∃ (m : ℕ) (τ : K →* GL (Fin m) O), IsOpen (τ.ker : Set K) ∧ ∀ π : SmIrr G, (∃ y : Fin m → π.V, y ≠ 0 ∧ ∀ (k : K) i, ∑ a, algebraMap O ℂ (τ k i a) • π.ρ k (y a) = y i) ↔ P π := by
  intro O _ _ _ _ _ _ G _ _ _ K hK P d ξ hξ hP hγ
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : Subgroup K := MonoidHom.ker ξ
  have hU : IsOpen (U : Set K) := by
    have : (U : Set K) = ⋂ i : Fin d, {g | ξ g (Pi.single i 1) = Pi.single i 1} := by
      ext g
      simp only [U, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      refine ⟨fun h i => by rw [h]; rfl, fun h => (Pi.basisFun ℂ (Fin d)).ext fun i => by simpa using h i⟩
    rw [this]
    exact isOpen_iInter_of_finite fun i => hξ _
  haveI : Finite (K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  letI : Fintype (K ⧸ U) := Fintype.ofFinite _
  let R : ∀ π : SmIrr G, Representation ℂ K π.V := fun π => π.ρ.comp K.subtype
  let N : ∀ π : SmIrr G, Submodule ℂ π.V := fun π => Representation.invariants ((R π).comp U.subtype)
  let RQ : ∀ π : SmIrr G, Representation ℂ (K ⧸ U) (N π) := fun π => (R π).quotientToInvariants U
  have hRQ : ∀ π (k : K) (v : N π), (RQ π (k : K ⧸ U) v : π.V) = π.ρ k v := fun π k v => rfl
  let ξQ : Representation ℂ (K ⧸ U) (Fin d → ℂ) := QuotientGroup.lift U ξ le_rfl
  have hPQ : ∀ π, (∃ i v n, ∑ g, ξQ g⁻¹ v i • RQ π g n ≠ 0) ↔ P π := fun π => by
    rw [← avg, ← hP]
    constructor
    · rintro ⟨f, hf, he⟩
      refine ⟨(N π).subtype ∘ₗ f, fun h0 => hf (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h0 v)), fun k v => ?_⟩
      exact congrArg Subtype.val (he (k : K ⧸ U) v)
    · rintro ⟨f, hf, he⟩
      have hm : ∀ v, f v ∈ N π := fun v u => by
        have h1 : ξ u.1 = 1 := u.2
        have := he u.1 v
        rw [h1] at this
        exact this.symm
      refine ⟨f.codRestrict _ hm, fun h0 => hf (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun h0 v)),
        fun k v => ?_⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k
      exact Subtype.ext (he k v)
  let I : Submodule ℂ (K ⧸ U → ℂ) :=
    { carrier := {x | ∀ π, ¬ P π → ∀ v, ∑ g, x g • RQ π g v = 0}
      add_mem' := fun {a b} ha hb π hπ v => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ha π hπ v, hb π hπ v, add_zero]
      zero_mem' := fun π _ v => by simp
      smul_mem' := fun z x hx π hπ v => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hx π hπ v, smul_zero] }
  obtain ⟨m, τ, hτ⟩ := UpperTheory.exists_integral_rep_detecting_invariant_subspace O (K ⧸ U) I (fun g x hx π hπ v => by
      rw [← Equiv.sum_comp (Equiv.mulLeft g)]
      have := congrArg (RQ π g) (hx π hπ v)
      simp only [map_sum, map_smul, map_zero] at this
      simpa only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply] using this)
    (UpperTheory.le_span_integralValued_of_galoisStable O (K ⧸ U) I fun γ x hx π' hπ' v' => by
      obtain ⟨π, f, hf, he⟩ := twist γ.toRingEquiv π'
      have hv : f.symm v' ∈ N π := fun u => f.injective <| by
        refine (he _ _).trans ?_
        rw [f.apply_symm_apply]
        exact v'.2 u
      have h1 := congrArg (fun y : N π => f y) (hx π (fun h => hπ' (hγ γ π π' f hf he h)) ⟨_, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hf, Submodule.coe_zero, map_zero] at h1
      refine Subtype.ext ?_
      rw [Submodule.coe_sum, Submodule.coe_zero, ← h1]
      refine Finset.sum_congr rfl fun g _ => ?_
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
      rw [Submodule.coe_smul, hRQ, hRQ, he, f.apply_symm_apply]
      rfl)
  refine ⟨m, τ.comp (QuotientGroup.mk' U), Subgroup.isOpen_mono (fun u hu => ?_) hU, fun π => ?_⟩
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu, map_one]
  have h2 : (∃ x ∈ I, ∃ v, ∑ g, x g • RQ π g v ≠ 0) ↔ P π := by
    refine ⟨fun ⟨x, hx, v, hv⟩ => by_contra fun h => hv (hx π h v), fun h => ?_⟩
    obtain ⟨i, v, n, hn⟩ := (hPQ π).2 h
    exact ⟨fun g => ξQ g⁻¹ v i, fun π' hπ' n' => by_contra fun h' => hπ' ((hPQ π').1 ⟨i, v, n', h'⟩), n, hn⟩
  rw [← h2, ← hτ]
  constructor
  · rintro ⟨y, hy, he⟩
    have hm : ∀ a, y a ∈ N π := fun a u => by
      have := he u.1 a
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u.1).2 u.2, map_one] at this
      change π.ρ u.1 (y a) = y a
      simpa [Matrix.one_apply, apply_ite] using this
    refine ⟨fun a => ⟨y a, hm a⟩, fun h0 => hy (funext fun a => congrArg Subtype.val (congrFun h0 a)), fun g i => ?_⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    refine Subtype.ext ?_
    rw [Submodule.coe_sum]
    exact he k i
  · rintro ⟨F, hF, he⟩
    refine ⟨fun a => F a, fun h0 => hF (funext fun a => Subtype.ext (congrFun h0 a)), fun k i => ?_⟩
    have := congrArg Subtype.val (he (k : K ⧸ U) i)
    rw [Submodule.coe_sum] at this
    exact this
