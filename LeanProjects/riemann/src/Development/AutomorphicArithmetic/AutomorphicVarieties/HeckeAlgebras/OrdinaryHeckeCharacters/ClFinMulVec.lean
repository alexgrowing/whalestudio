import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwahoriProUnipotentFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IwMemMul
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem clFin_mulVec {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {n : ℕ} (L : Submodule O Ω)
    (M : Matrix (Fin n) (Fin n) Ω) (hM : ∀ i j, M i j ∈ (algebraMap O Ω).range) (v : Fin n → Ω)
    (hv : ∀ k, v k ∈ L) (k : Fin n) : (M *ᵥ v) k ∈ L := by
  simp only [mulVec, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨x, hx⟩ := hM k j
  rw [← hx, ← Algebra.smul_def]
  exact L.smul_mem x (hv j)

private theorem clFin_key {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {O Ω : Type}
    [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) {m : ℕ}
    (τ : X.Ub →* GL (Fin m) Ω) (hτ : ∀ u i j, (τ u).val i j ∈ (algebraMap O Ω).range) (φ : X.I.T →* Ωˣ) (c : ℕ)
    (hc : W.c0 ≤ c) (hφ : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) (U : Subgroup X.Ub) (hU : X.FinLevel U) :
    ∃ S : Finset (Ga × Gp), ∀ F ∈ X.Cl τ W.ξ U c φ, ∀ L : Submodule O Ω,
      (∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k ∈ L) → ∀ g i k, (((W.ξ g.2)⁻¹).val *ᵥ F i g) k ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hU
  haveI : Finite (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)) := Nat.finite_of_card_ne_zero (iwFin Gp X.I c).2
  haveI := Fintype.ofFinite (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0))
  refine ⟨(s ×ˢ (Finset.univ : Finset (X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)))).image
    (fun p => p.1 * (1, ((p.2.out : X.I.Iw 0) : Gp))), ?_⟩
  rintro F ⟨⟨hA, hU⟩, hN, hM, hT⟩ L hL g i
  obtain ⟨γ, x, hx, u, hu, b, hb, rfl⟩ := hs g
  obtain ⟨e, he⟩ := QuotientGroup.mk_out_eq_mul ((X.I.I1 c).subgroupOf (X.I.Iw 0)) ⟨b, hb⟩
  have he1 : ((e : X.I.Iw 0) : Gp) ∈ X.I.I1 c := Subgroup.mem_subgroupOf.1 e.2
  set r : Gp := ((⟨b, hb⟩ : X.I.Iw 0) : X.I.Iw 0 ⧸ (X.I.I1 c).subgroupOf (X.I.Iw 0)).out.1 with hr
  have hr2 : r = b * ((e : X.I.Iw 0) : Gp) := by rw [hr, he]; rfl
  have hL1 := hL (x * (1, r)) (Finset.mem_image.2 ⟨(x, _), Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩, rfl⟩)
  generalize ((e : X.I.Iw 0) : Gp) = e' at he1 hr2
  have hfix : ∀ w ∈ X.I.I1 c, X.rpF Ω (W.d + 1) m w F = F := by
    intro w hw
    obtain ⟨n, hn, t, ht, y, hy, rfl⟩ := (iwMem Gp X.I c w).2.1.1 hw
    have h3 := hT ⟨t, X.I.Tc_le c ht⟩
    rw [hφ _ ht, inv_one, Units.val_one, one_smul] at h3
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hM y hy, h3, hN n hn]
  have hint : ∀ v : Fin (W.d + 1) → Ω, (∀ k, v k ∈ L) → ∀ k, ((W.ξ e').val *ᵥ v) k ∈ L := by
    intro v hv
    obtain ⟨n, hn, t, ht, y, hy, rfl⟩ := (iwMem Gp X.I c _).2.1.1 he1
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec]
    exact clFin_mulVec L _ (W.int_N n hn) _ (clFin_mulVec L _ (W.integral_torusCharacter t (X.I.Tc_le c ht)) _
      (clFin_mulVec L _ (W.int_Nm y (X.I.Nm_anti hc hy)) _ hv))
  have e1 : X.glob γ * x * ((u : Ga), b) = X.glob γ * (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹)) := by
    rw [hr2]; simp [mul_assoc]
  have e2 : F i (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹)) = F i (x * (1, r) * ((u : Ga), 1)) :=
    congrFun (congrFun (hfix _ (inv_mem he1)) i) _
  have e3 : F i (x * (1, r) * ((u : Ga), 1)) = ∑ j, (τ u⁻¹).val i j • F j (x * (1, r)) := by
    funext k
    have := congrFun (congrFun (congrFun (hU u⁻¹ (inv_mem hu)) i) (x * (1, r) * ((u : Ga), 1))) k
    rw [← this]
    change ((τ u⁻¹).val *ᵥ fun j => F j (x * (1, r) * ((u : Ga), 1) * (((u⁻¹ : X.Ub) : Ga), 1)) k) i = _
    simp [mulVec, dotProduct, mul_assoc, ← Prod.one_eq_mk]
  have e4 : ((W.ξ (X.glob γ * (x * (1, r) * ((u : Ga), 1) * (1, e'⁻¹))).2)⁻¹).val * (W.ξ (X.glob γ).2).val
      = (W.ξ e').val * ((W.ξ (x * (1, r)).2)⁻¹).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    simp [mul_assoc]
  rw [e1, hA i trivial γ, mulVec_mulVec, e4, ← mulVec_mulVec, e2, e3]
  refine hint _ fun k => ?_
  rw [mulVec_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨a, ha⟩ := hτ u⁻¹ i j
  rw [mulVec_smul, ← ha, Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def]
  exact L.smul_mem a (hL1 j k)

private theorem clFin_zero {Ω : Type} [Field Ω] {n : ℕ} (M : GL (Fin n) Ω) (v : Fin n → Ω)
    (h : (M⁻¹).val *ᵥ v = 0) : v = 0 := by
  have := congrArg (M.val *ᵥ ·) h
  simpa [mulVec_mulVec] using this

theorem UpperTheory.V.Hi.clFin :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsDomain O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) →
      ∀ (W : WtRep X.I O Ω) (m : ℕ) (τ : X.Ub →* GL (Fin m) O) (θ φ : X.I.T →* Oˣ) (c : ℕ), W.c0 ≤ c →
      (∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → φ t = 1) →
      (∀ t : X.I.T, algebraMap O Ω (θ t) = algebraMap O Ω (φ t) * W.χ ⟨t, X.I.T_le t.2⟩) →
      ∀ U : Subgroup X.Ub, X.FinLevel U → X.Free τ θ U → FiniteDimensional Ω (X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)) ∧ ∀ a : X.I.P, (∀ F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), X.UF m W a F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)) ∧ ∀ F ∈ X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ), F ≠ 0 → ∀ μ : Ω, X.UF m W a F = μ • F → IsIntegral O μ := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ _ _ _ W m τ θ φ c hc hφ _ U hU _
  classical
  have hτ : ∀ u i j, (((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) u).val i j ∈ (algebraMap O Ω).range :=
    fun u i j => ⟨(τ u).val i j, rfl⟩
  have hφ' : ∀ t : X.I.T, (t : Gp) ∈ X.I.Tc c → ((Units.map (algebraMap O Ω).toMonoidHom).comp φ) t = 1 :=
    fun t ht => by rw [MonoidHom.comp_apply, hφ t ht, map_one]
  generalize (Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ = τ' at hτ ⊢
  generalize (Units.map (algebraMap O Ω).toMonoidHom).comp φ = φ' at hφ' ⊢
  obtain ⟨S, hS⟩ := clFin_key X W τ' hτ φ' c hc hφ' U hU
  have hz : ∀ F ∈ X.Cl τ' W.ξ U c φ', (∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k = 0) → F = 0 := by
    intro F hF h
    funext i g
    exact clFin_zero (W.ξ g.2) _ (funext fun k => hS F hF ⊥ h g i k)
  refine ⟨?_, fun a => ?_⟩
  · let ev : X.Cl τ' W.ξ U c φ' →ₗ[Ω] (S → Fin m → Fin (W.d + 1) → Ω) :=
      { toFun := fun F x i => F.1 i x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine FiniteDimensional.of_injective ev ((injective_iff_map_eq_zero ev).2 fun F h => Subtype.ext ?_)
    refine hz F.1 F.2 fun x hx i k => ?_
    have : F.1 i x = 0 := congrFun (congrFun h ⟨x, hx⟩) i
    rw [this, mulVec_zero]; rfl
  obtain ⟨⟨s, hs, hu⟩, h2⟩ := uOpSum Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) a a.2
  have hsum : ∀ F ∈ X.Cl τ' W.ξ U c φ', X.UF m W a F =
      (((W.χ ⟨a, X.I.P_le a a.2⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, X.rpF Ω (W.d + 1) m (u * a) F := by
    intro F hF
    rw [← (h2 s hs hu).2 F hF.2.1]; rfl
  refine ⟨fun F hF => ⟨?_, ?_⟩, fun F hF h0 μ hμ => ?_⟩
  · rw [hsum F hF]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun u _ => ⟨fun i _ γ g => ?_, fun w hw => ?_⟩)
    · change F i (X.glob γ * g * (1, u * a)) = _ *ᵥ F i (g * (1, u * a))
      rw [mul_assoc]
      exact hF.1.1 i trivial γ _
    · funext i g k
      have := congrFun (congrFun (congrFun (hF.1.2 w hw) i) (g * (1, u * a))) k
      refine Eq.trans ?_ this
      change ((τ' w).val *ᵥ fun j => F j (g * ((w : Ga), 1) * (1, u * a)) k) i =
        ((τ' w).val *ᵥ fun j => F j (g * (1, u * a) * ((w : Ga), 1)) k) i
      simp [mul_assoc]
  · exact Submodule.smul_mem _ _ (((uOpLevel Gp X.I Ω _ (X.rpF Ω (W.d + 1) m) c).2.2 φ' hφ').1 a a.2 F hF.2)
  let L : Submodule O Ω := Submodule.span O (Set.range
    fun p : S × Fin m × Fin (W.d + 1) => (((W.ξ p.1.1.2)⁻¹).val *ᵥ F p.2.1 p.1.1) p.2.2)
  have hL0 : ∀ x ∈ S, ∀ i k, (((W.ξ x.2)⁻¹).val *ᵥ F i x) k ∈ L :=
    fun x hx i k => Submodule.subset_span ⟨(⟨x, hx⟩, i, k), rfl⟩
  have hL := hS F hF L hL0
  have hμL : ∀ g i k, μ * (((W.ξ g.2)⁻¹).val *ᵥ F i g) k ∈ L := by
    intro g i k
    have e : μ • F i g = (((W.χ ⟨a, X.I.P_le a a.2⟩)⁻¹ : Ωˣ) : Ω) • ∑ u ∈ s, F i (g * (1, u * a)) := by
      have := congrFun (congrFun (hμ.symm.trans (hsum F hF)) i) g
      simp only [Pi.smul_apply, Finset.sum_apply] at this
      exact this
    rw [← smul_eq_mul, ← Pi.smul_apply, ← mulVec_smul, e, Finset.smul_sum, mulVec_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ fun u hu => ?_
    have e4 : ((W.ξ g.2)⁻¹).val = (W.ξ u).val * ((W.ξ a).val * ((W.ξ (g * (1, u * a)).2)⁻¹).val) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      simp [mul_assoc]
    rw [e4, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_smul, mulVec_smul, ← smul_mulVec]
    exact clFin_mulVec L _ (W.int_N u (hs u hu)) _ (clFin_mulVec L _ (W.int_P a a.2) _ (hL _ i)) k
  refine isIntegral_of_smul_mem_submodule L (fun h => h0 (hz F hF fun x hx i k => ?_))
    (Submodule.fg_span (Set.finite_range _)) μ fun n hn => ?_
  · have := hL0 x hx i k
    rwa [h] at this
  · induction hn using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      exact hμL _ _ _
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [smul_comm]; exact L.smul_mem r hx
