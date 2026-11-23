import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, ?_⟩
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H g =>
    by_contra hg
    have hgN : g ∉ N := fun h => hg ((QuotientGroup.eq_one_iff g).mpr h)
    have hcl := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G) ⟨N, hN⟩
    have hnot : g ∉ sInf {K : Subgroup G | IsOpen (K : Set G) ∧ ((⟨N, hN⟩ : ClosedSubgroup G) : Subgroup G) ≤ K} := by
      rw [← hcl]
      exact hgN
    rw [Subgroup.mem_sInf] at hnot
    push_neg at hnot
    obtain ⟨K, ⟨hKo, hNK⟩, hgK⟩ := hnot
    have hNK' : N ≤ K := hNK
    have hpre : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' ((QuotientGroup.mk : G → G ⧸ N) '' (K : Set G)) = K := by
      ext y
      constructor
      · rintro ⟨k, hk, hky⟩
        have h1 : k⁻¹ * y ∈ N := QuotientGroup.eq.mp hky
        simpa using K.mul_mem hk (hNK' h1)
      · intro hy
        exact ⟨y, hy, rfl⟩
    have hclo : IsClopen ((QuotientGroup.mk : G → G ⧸ N) '' (K : Set G)) := by
      rw [← (QuotientGroup.isQuotientMap_mk N).isClopen_preimage, hpre]
      exact ⟨K.isClosed_of_isOpen hKo, hKo⟩
    have hsub := hclo.connectedComponent_subset (x := 1) ⟨1, K.one_mem, rfl⟩
    obtain ⟨k, hk, hkg⟩ := hsub hx
    apply hgK
    have h2 : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hkg
    simpa using K.mul_mem hk (hNK' h2)

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h1 : (QuotientGroup.mk (g⁻¹ * x.out) : Γ ⧸ H) = QuotientGroup.mk ((g⁻¹ • x).out) := by
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' x]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have h2 := QuotientGroup.eq.mp h1
  simpa [_root_.mul_inv_rev, mul_assoc] using h2

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  unfold PhiCond
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [← (QuotientGroup.isQuotientMap_mk H).isOpen_preimage]
      have hpre : (QuotientGroup.mk : Γ → Γ ⧸ H) ⁻¹' {(g : Γ ⧸ H)} = (fun y => g⁻¹ * y) ⁻¹' (H : Set Γ) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
        rw [QuotientGroup.eq, ← H.inv_mem_iff]
        simp [_root_.mul_inv_rev]
      rw [hpre]
      exact hH.preimage (continuous_const.mul continuous_id)
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  have hcont : ReciprocityTheory.Gal.ContAction (permR (ZMod n) H) := by
    unfold ReciprocityTheory.Gal.ContAction
    apply continuous_prod_of_discrete_right.mpr
    intro m
    apply continuous_pi
    intro x
    simp only [permR_apply]
    exact (continuous_of_discreteTopology (f := m)).comp (continuous_inv.smul continuous_const)
  haveI := h (Γ ⧸ H → ZMod n) (permR (ZMod n) H) hcont
  let cf : (H →* Multiplicative (ZMod n)) → Γ → Γ ⧸ H → ZMod n := fun φ g x =>
    Multiplicative.toAdd (φ ⟨(x.out)⁻¹ * g * (g⁻¹ • x).out, sec_mem H g x⟩)
  have hcoc : ∀ (φ : H →* Multiplicative (ZMod n)) (g k : Γ),
      cf φ (g * k) = cf φ g + permR (ZMod n) H g (cf φ k) := by
    intro φ g k
    funext x
    simp only [cf, permR_apply, Pi.add_apply]
    rw [← toAdd_mul, ← map_mul]
    refine congrArg (fun y => Multiplicative.toAdd (φ y)) ?_
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [_root_.mul_inv_rev, mul_smul]
    group
  have hcont_c : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous (cf φ) := by
    intro φ hφ
    have hK : IsOpen (Subtype.val '' (φ.ker : Set H) : Set Γ) := hH.isOpenMap_subtype_val _ hφ
    let U : Set Γ := ⋂ y : Γ ⧸ H, (fun u => (y.out)⁻¹ * u * y.out) ⁻¹' (Subtype.val '' (φ.ker : Set H))
    have hUo : IsOpen U :=
      isOpen_iInter_of_finite (fun y => hK.preimage ((continuous_const.mul continuous_id).mul continuous_const))
    have h1U : (1 : Γ) ∈ U := by
      simp only [U, Set.mem_iInter, Set.mem_preimage]
      intro y
      exact ⟨1, φ.ker.one_mem, by simp⟩
    have hzero : ∀ u ∈ U, cf φ u = 0 := by
      intro u hu
      funext y
      obtain ⟨k, hk, hkv⟩ := Set.mem_iInter.mp hu y
      have hkv' : (k : Γ) = (y.out)⁻¹ * u * y.out := hkv
      have hmem : (y.out)⁻¹ * u * y.out ∈ H := by
        rw [← hkv']
        exact k.2
      have huy : u • y = y := by
        conv_rhs => rw [← QuotientGroup.out_eq' y]
        conv_lhs => rw [← QuotientGroup.out_eq' y]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
        have := H.inv_mem hmem
        simpa [_root_.mul_inv_rev, mul_assoc] using this
      have hy : u⁻¹ • y = y := inv_smul_eq_iff.mpr huy.symm
      have hel : (⟨(y.out)⁻¹ * u * (u⁻¹ • y).out, sec_mem H u y⟩ : H) = k := by
        apply Subtype.ext
        simp only
        rw [hy]
        exact hkv'.symm
      simp only [cf, Pi.zero_apply]
      rw [hel, φ.mem_ker.mp hk, toAdd_one]
    rw [continuous_iff_continuousAt]
    intro g
    have hnb : (fun g' => g⁻¹ * g') ⁻¹' U ∈ nhds g :=
      (hUo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1U)
    refine (continuousAt_const : ContinuousAt (fun _ : Γ => cf φ g) g).congr ?_
    filter_upwards [hnb] with g' hg'
    have h2 := hcoc φ g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hzero _ hg', map_zero, add_zero] at h2
    exact h2.symm
  let Φ : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → H1 (permR (ZMod n) H) :=
    fun φ => Submodule.Quotient.mk
      (⟨cf φ.1, by unfold Z1; exact ⟨hcont_c φ.1 φ.2, hcoc φ.1⟩⟩ : Z1 (permR (ZMod n) H))
  have hinj : Function.Injective Φ := by
    rintro ⟨φ, hφ⟩ ⟨ψ, hψ⟩ heq
    apply Subtype.ext
    simp only [Φ] at heq
    rw [Submodule.Quotient.eq, Submodule.mem_comap] at heq
    unfold B1 at heq
    obtain ⟨m, hm⟩ := LinearMap.mem_range.mp heq
    ext k
    have ho : ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) ∈ H := by
      have h0 : (QuotientGroup.mk ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) : Γ ⧸ H) = QuotientGroup.mk 1 :=
        QuotientGroup.out_eq' _
      have := QuotientGroup.eq.mp h0
      simpa using this
    set o := ((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out) with ho_def
    have hhH : o * (k : Γ) * o⁻¹ ∈ H := H.mul_mem (H.mul_mem ho k.2) (H.inv_mem ho)
    have hx₀ : (o * (k : Γ) * o⁻¹)⁻¹ • (QuotientGroup.mk (1 : Γ) : Γ ⧸ H) = QuotientGroup.mk 1 := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
      simpa using hhH
    have hk' : (⟨((QuotientGroup.mk (1 : Γ) : Γ ⧸ H).out)⁻¹ * (o * (k : Γ) * o⁻¹) *
        ((o * (k : Γ) * o⁻¹)⁻¹ • (QuotientGroup.mk (1 : Γ) : Γ ⧸ H)).out,
        sec_mem H _ _⟩ : H) = k := by
      apply Subtype.ext
      simp only
      rw [hx₀, ← ho_def]
      group
    have hev := congrFun (congrFun hm (o * (k : Γ) * o⁻¹)) (QuotientGroup.mk 1)
    unfold ReciprocityTheory.Gal.d0 at hev
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, permR_apply,
      Submodule.coe_sub, Submodule.subtype_apply] at hev
    rw [hx₀, sub_self] at hev
    simp only [cf] at hev
    rw [hk'] at hev
    have hfin : Multiplicative.toAdd (φ k) - Multiplicative.toAdd (ψ k) = (0 : ZMod n) := hev.symm
    have h4 : Multiplicative.toAdd (φ k) = Multiplicative.toAdd (ψ k) := sub_eq_zero.mp hfin
    exact Multiplicative.toAdd.injective h4
  exact Finite.of_injective Φ hinj

theorem UpperTheory.V.UnitaryThreeInertia.hostFrame_phi :
    GlobalFiniteness → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    PhiCond (Gam Ω S) l ∧ CompactSpace (Gam Ω S) ∧ T2Space (Gam Ω S) ∧ TotallyDisconnectedSpace (Gam Ω S) ∧ CompactSpace (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ T2Space (Formalism.ConjugateSelfDual.G ℚ Ω) ∧ TotallyDisconnectedSpace (Formalism.ConjugateSelfDual.G ℚ Ω) := by
  intro hGF Ω _ _ _ l _ c N _ e ψ o₁ _hD S A F hF
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hT2 : T2Space (Gam Ω S) := by
    haveI : IsClosed (NS Ω (↑S : Set Pl) : Set (Formalism.ConjugateSelfDual.G ℚ Ω)) := isClosed_NS (F := ℚ) Ω _
    unfold Gam
    infer_instance
  have hTD : TotallyDisconnectedSpace (Gam Ω S) := by
    unfold Gam
    exact totDisc_quot _ (isClosed_NS (F := ℚ) Ω _)
  have hCA : ReciprocityTheory.Gal.ContainsAbove (F := ℚ) S l := by
    unfold ReciprocityTheory.Gal.ContainsAbove
    intro v hv
    apply (hF.mem v).mpr
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hv
  unfold GlobalFiniteness at hGF
  have key : ∀ k : ℕ, k = l ^ 1 → ∀ (M : Type) [AddCommGroup M] [Module (ZMod k) M] [TopologicalSpace M]
      [DiscreteTopology M] [Finite M] (ρ : Representation (ZMod k) (Gam Ω S) M),
      ReciprocityTheory.Gal.ContAction ρ → Finite (H1 ρ) := by
    intro k hk
    subst hk
    intro M _ _ _ _ _ ρ hρ
    have hGFa := hGF ℚ Ω l 1 M S ρ
    unfold ReciprocityTheory.Gal.GlobalFinitenessAt at hGFa
    exact (hGFa Nat.one_pos hCA hρ).2.1
  have hPhi : PhiCond (Gam Ω S) l := by
    apply phi_condition_of_finite_cohomology l
    intro M _ _ _ _ _ ρ hρ
    exact key l (pow_one l).symm M ρ hρ
  exact ⟨hPhi, inferInstance, hT2, hTD, inferInstance, inferInstance, inferInstance⟩
