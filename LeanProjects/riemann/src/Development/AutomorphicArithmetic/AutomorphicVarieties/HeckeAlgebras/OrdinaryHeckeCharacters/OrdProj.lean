import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk

open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ordProj_higman {A G M : Type} [CommRing A] [Group G] [Fintype G] [AddCommGroup M] [Module A M]
    [Module.Projective A M] (ρ : Representation A G M) (φ : Module.End A M)
    (h' : ∀ v, ∑ g, ρ g (φ (ρ g⁻¹ v)) = v) : Module.Projective (MonoidAlgebra A G) ρ.asModule := by
  classical
  obtain ⟨s, hs⟩ := ‹Module.Projective A M›.out
  let e := ρ.asModuleEquiv
  let L : G → (ρ.asModule →ₗ[A] (ρ.asModule →₀ MonoidAlgebra A G)) := fun g =>
    Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle (R := A) g) ∘ₗ Finsupp.lmapDomain A A e.symm ∘ₗ
      s ∘ₗ φ ∘ₗ ρ g⁻¹ ∘ₗ e.toLinearMap
  have hsm : ∀ (g : G) (a : A) (x : M),
      (MonoidAlgebra.single g a : MonoidAlgebra A G) • e.symm x = e.symm (a • ρ g x) := by
    intro g a x
    apply e.injective
    (simp [e]) <;> rfl
  have hL : ∀ g v, Finsupp.linearCombination (MonoidAlgebra A G) id (L g v) =
      e.symm (ρ g (φ (ρ g⁻¹ (e v)))) := by
    intro g v
    simp only [L, LinearMap.comp_apply, Finsupp.mapRange.linearMap_apply, Finsupp.lmapDomain_apply,
      LinearEquiv.coe_coe]
    conv_rhs => rw [← hs (φ (ρ g⁻¹ (e v)))]
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (by simp), Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
    simp only [Finsupp.sum, map_sum, map_smul, id, MonoidAlgebra.lsingle_apply, hsm]
  have hk : ∀ (k g : G) v, MonoidAlgebra.single k (1 : A) • L g v = L (k * g) (MonoidAlgebra.single k (1 : A) • v) := by
    intro k g v
    have he : e (MonoidAlgebra.single k (1 : A) • v) = ρ k (e v) := by (simp [e]) <;> rfl
    have hinv : ρ (k * g)⁻¹ (ρ k (e v)) = ρ g⁻¹ (e v) := by
      rw [_root_.mul_inv_rev, map_mul, Module.End.mul_apply, ← Module.End.mul_apply (ρ k⁻¹), ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, he, hinv]
    ext x
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, MonoidAlgebra.single_mul_single]
  have hF : ∀ (k : G) (v : ρ.asModule), (∑ g, L g) (MonoidAlgebra.single k (1 : A) • v) =
      MonoidAlgebra.single k (1 : A) • (∑ g, L g) v := by
    intro k v
    simp only [LinearMap.sum_apply, Finset.smul_sum, hk]
    exact (Equiv.sum_comp (Equiv.mulLeft k) (fun g => L g (MonoidAlgebra.single k (1 : A) • v))).symm
  refine ⟨⟨MonoidAlgebra.equivariantOfLinearOfComm (∑ g, L g) hF, fun v => ?_⟩⟩
  rw [MonoidAlgebra.equivariantOfLinearOfComm_apply]
  simp only [LinearMap.sum_apply, map_sum, hL]
  apply e.injective
  simp only [map_sum, LinearEquiv.apply_symm_apply]
  exact h' (e v)

private theorem ordProj_dc {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (U V : Subgroup H) [Fintype (U ⧸ V.subgroupOf U)] (v : M) (hv : v ∈ fixd ρ V) :
    dc ρ U V 1 v = ∑ q : U ⧸ V.subgroupOf U, ρ (q.out : U) v := by
  classical
  let f : U ⧸ V.subgroupOf U → H := fun q => ((q.out : U) : H)
  have hinj : Function.Injective f := fun q q' h => Quotient.out_injective (Subtype.val_injective h)
  have hq : ∀ q q' : U ⧸ V.subgroupOf U, ((f q : H) : H ⧸ V) = ((f q' : H) : H ⧸ V) → q = q' := by
    intro q q' h
    rw [QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [f] using h
  have hcov : ∀ u : U, ((f (QuotientGroup.mk u) : H) : H ⧸ V) = ((u : H) : H ⧸ V) := by
    intro u
    have h := QuotientGroup.out_eq' (QuotientGroup.mk u : U ⧸ V.subgroupOf U)
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    rw [QuotientGroup.eq]
    simpa [f] using h
  have hsm : ∀ u : U, u • ((1 : H) : H ⧸ V) = ((u : H) : H ⧸ V) := by
    intro u
    change ((u : H) • ((1 : H) : H ⧸ V)) = _
    exact congrArg _ (mul_one _)
  have horb : ∀ p, p ∈ MulAction.orbit U ((1 : H) : H ⧸ V) ↔ ∃ u : U, ((u : H) : H ⧸ V) = p := by
    intro p
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, (hsm u).symm⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, hsm u⟩
  have hfin : (MulAction.orbit U ((1 : H) : H ⧸ V)).Finite := by
    apply (Set.finite_range (fun q : U ⧸ V.subgroupOf U => ((f q : H) : H ⧸ V))).subset
    intro p hp
    obtain ⟨u, rfl⟩ := (horb p).1 hp
    exact ⟨QuotientGroup.mk u, hcov u⟩
  have hs1 : ∀ y ∈ Finset.univ.image f, ((y : H) : H ⧸ V) ∈ MulAction.orbit U ((1 : H) : H ⧸ V) := by
    intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (horb _).2 ⟨q.out, rfl⟩
  have hs2 : ∀ p ∈ MulAction.orbit U ((1 : H) : H ⧸ V),
      ∃! y, y ∈ Finset.univ.image f ∧ ((y : H) : H ⧸ V) = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := (horb p).1 hp
    refine ⟨f (QuotientGroup.mk u), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), hcov u⟩, ?_⟩
    rintro y ⟨hy, hyu⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← hcov u] at hyu
    exact congrArg f (hq _ _ hyu)
  rw [(dcSum A H M ρ U V 1 hfin).1 (Finset.univ.image f) hs1 hs2 v hv, Finset.sum_image (fun x _ y _ h => hinj h)]

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)

private def ordProj_rel (U : Subgroup X.Ub) : Setoid (Ga × Gp) where
  r x y := ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw 0, y = X.glob γ * x * ((u : Ga), b)
  iseqv :=
    { refl := fun x => ⟨1, 1, one_mem _, 1, one_mem _, by simp [← Prod.one_eq_mk]⟩
      symm := by
        rintro x y ⟨γ, u, hu, b, hb, rfl⟩
        refine ⟨γ⁻¹, u⁻¹, inv_mem hu, b⁻¹, inv_mem hb, ?_⟩
        ext <;> simp [mul_assoc]
      trans := by
        rintro x y z ⟨γ, u, hu, b, hb, rfl⟩ ⟨γ', u', hu', b', hb', rfl⟩
        refine ⟨γ' * γ, u * u', mul_mem hu hu', b * b', mul_mem hb hb', ?_⟩
        ext <;> simp [mul_assoc] }

private theorem ordProj_chi (A : Type) [CommRing A] (U V : Subgroup X.Ub) (hVU : V ≤ U) (hN : X.Neat U)
    [Fintype (U ⧸ V.subgroupOf U)] :
    ∃ χ : Ga × Gp → A, (∀ γ g, ∀ u ∈ V, ∀ b ∈ X.I.Iw 0, χ (X.glob γ * g * ((u : Ga), b)) = χ g) ∧
      ∀ g, ∑ q : U ⧸ V.subgroupOf U, χ (g * ((((q.out : U) : X.Ub) : Ga), 1)) = 1 := by
  classical
  let R : Ga × Gp → Ga × Gp := fun x => (Quotient.mk (ordProj_rel X U) x).out
  have hRsound : ∀ x y : Ga × Gp,
      (∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw 0, y = X.glob γ * x * ((u : Ga), b)) → R y = R x := by
    intro x y h
    have h' : Quotient.mk (ordProj_rel X U) x = Quotient.mk (ordProj_rel X U) y := Quotient.sound h
    simp only [R, h']
  have hRout : ∀ x : Ga × Gp, ∃ γ, ∃ u ∈ U, ∃ b ∈ X.I.Iw 0, x = X.glob γ * R x * ((u : Ga), b) := by
    intro x
    exact Quotient.mk_out (s := ordProj_rel X U) x
  have uniq : ∀ (r : Ga × Gp) (γ γ' : Γ) (a a' : X.Ub), a ∈ U → a' ∈ U → ∀ b b' : Gp,
      b ∈ X.I.Iw 0 → b' ∈ X.I.Iw 0 →
      X.glob γ * r * ((a : Ga), b) = X.glob γ' * r * ((a' : Ga), b') → a = a' := by
    intro r γ γ' a a' ha ha' b b' hb hb' h
    have hp : (((a' * a⁻¹ : X.Ub) : Ga), b' * b⁻¹) = ((a' : Ga), b') * ((a : Ga), b)⁻¹ := by
      ext <;> simp
    have key := hN r (γ'⁻¹ * γ) (a' * a⁻¹) (mul_mem ha' (inv_mem ha)) (b' * b⁻¹)
      (mul_mem hb' (inv_mem hb)) (by
        rw [hp, map_mul, map_inv, mul_assoc, eq_mul_inv_of_mul_eq h]
        group)
    exact (mul_inv_eq_one.1 key.1).symm
  let P : Ga × Gp → Prop := fun x => ∃ γ, ∃ u ∈ V, ∃ b ∈ X.I.Iw 0, x = X.glob γ * R x * ((u : Ga), b)
  refine ⟨fun x => if P x then 1 else 0, ?_, ?_⟩
  · intro γ g u hu b hb
    have hR : R (X.glob γ * g * ((u : Ga), b)) = R g := hRsound g _ ⟨γ, u, hVU hu, b, hb, rfl⟩
    have hiff : P (X.glob γ * g * ((u : Ga), b)) ↔ P g := by
      simp only [P, hR]
      generalize R g = r
      constructor
      · rintro ⟨γ2, u2, hu2, b2, hb2, h2⟩
        refine ⟨γ⁻¹ * γ2, u2 * u⁻¹, mul_mem hu2 (inv_mem hu), b2 * b⁻¹, mul_mem hb2 (inv_mem hb), ?_⟩
        have e : g = (X.glob γ)⁻¹ * (X.glob γ * g * ((u : Ga), b)) * ((u : Ga), b)⁻¹ := by group
        rw [e, h2]
        ext <;> simp [mul_assoc]
      · rintro ⟨γ1, u1, hu1, b1, hb1, h1⟩
        refine ⟨γ * γ1, u1 * u, mul_mem hu1 hu, b1 * b, mul_mem hb1 hb, ?_⟩
        rw [h1]
        ext <;> simp [mul_assoc]
    simp only [hiff]
  · intro g
    obtain ⟨γ0, u0, hu0, b0, hb0, h0⟩ := hRout g
    have hterm : ∀ q : U ⧸ V.subgroupOf U,
        P (g * ((((q.out : U) : X.Ub) : Ga), 1)) ↔ u0 * ((q.out : U) : X.Ub) ∈ V := by
      intro q
      have hR : R (g * ((((q.out : U) : X.Ub) : Ga), 1)) = R g :=
        hRsound g _ ⟨1, (q.out : U), (q.out).2, 1, one_mem _, by simp⟩
      simp only [P, hR]
      generalize R g = r at h0
      constructor
      · rintro ⟨γ2, u2, hu2, b2, hb2, h2⟩
        have e := uniq r γ0 γ2 (u0 * ((q.out : U) : X.Ub)) u2 (mul_mem hu0 (q.out).2) (hVU hu2) b0 b2
          hb0 hb2 (by
            rw [← h2, h0]
            ext <;> simp [mul_assoc])
        rw [e]
        exact hu2
      · intro h
        refine ⟨γ0, _, h, b0, hb0, ?_⟩
        rw [h0]
        ext <;> simp [mul_assoc]
    have hsum : ∀ q : U ⧸ V.subgroupOf U, u0 * ((q.out : U) : X.Ub) ∈ V ↔
        ((⟨u0⁻¹, inv_mem hu0⟩ : U) : U ⧸ V.subgroupOf U) = q := by
      intro q
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rw [QuotientGroup.eq]
      simp [Subgroup.mem_subgroupOf]
    simp only [hterm, hsum]
    simp

end

section

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] [IsCNL A] {m : ℕ}
  (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)

private theorem ordProj_val (k : ℕ) (f : X.Fn A m) : f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := by
  simp [Frame.valIn, Submodule.mem_pi]

private theorem ordProj_valra (k : ℕ) (u : X.Ub) (f : X.Fn A m) (hf : f ∈ X.valIn A m k) :
    X.ra τ u f ∈ X.valIn A m k := by
  rw [ordProj_val] at hf ⊢
  intro g i
  rw [Frame.ra_apply]
  simp only [mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hf _ j)

private theorem ordProj_pow (hθ : X.I.ContChar θ) (u : X.Ub) (n : ℕ) (f : X.Fn A m) :
    X.ra τ u ((X.U A m X.I.z ^ n) f) = (X.U A m X.I.z ^ n) (X.ra τ u f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih,
      (spStab _ _ _ X A m τ θ hθ).2.2.1 _ X.I.z_mem]

private theorem ordProj_sp (hθ : X.I.ContChar θ) (U V : Subgroup X.Ub) [hn : (V.subgroupOf U).Normal] (hVU : V ≤ U)
    (u : U) (f : X.Fn A m) (hf : f ∈ X.Sp τ θ V) : X.ra τ u f ∈ X.Sp τ θ V := by
  rw [Frame.Sp.eq_1, Submodule.mem_inf] at hf ⊢
  refine ⟨(spStab _ _ _ X A m τ θ hθ).2.1 u f hf.1, ?_⟩
  have hf2 : ∀ w ∈ V, X.ra τ w f = f := hf.2
  have key : ∀ w ∈ V, X.ra τ w (X.ra τ u f) = X.ra τ u f := by
    intro w hw
    have hmem : (u : X.Ub)⁻¹ * w * u ∈ V := by
      have h1 : (⟨w, hVU hw⟩ : U) ∈ V.subgroupOf U := by simpa [Subgroup.mem_subgroupOf] using hw
      have h2 := hn.conj_mem _ h1 u⁻¹
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using h2
    have e : w * (u : X.Ub) = (u : X.Ub) * ((u : X.Ub)⁻¹ * w * u) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hf2 _ hmem]
  exact key

private theorem ordProj_ord (hθ : X.I.ContChar θ) (U V : Subgroup X.Ub) [(V.subgroupOf U).Normal] (hVU : V ≤ U)
    (u : U) (f : X.Fn A m) (hf : f ∈ X.Ord τ θ V) : X.ra τ u f ∈ X.Ord τ θ V := by
  rw [mem_ord_iff] at hf ⊢
  refine ⟨ordProj_sp X τ θ hθ U V hVU u f hf.1, fun k => ?_⟩
  obtain ⟨n, hn⟩ := hf.2 k
  refine ⟨n, ?_⟩
  rw [← ordProj_pow X τ θ hθ, ← map_sub]
  exact ordProj_valra X τ k u _ hn

private theorem ordProj_mul (V : Subgroup X.Ub) (χ : Ga × Gp → A)
    (hχ : ∀ γ g, ∀ u ∈ V, ∀ b ∈ X.I.Iw 0, χ (X.glob γ * g * ((u : Ga), b)) = χ g) (f : X.Fn A m)
    (hf : f ∈ X.Sp τ θ V) : (fun g => χ g • f g : X.Fn A m) ∈ X.Sp τ θ V := by
  have hrp : ∀ (b : Gp) (F : X.Fn A m) g, X.rp A m b F g = F (g * (1, b)) := fun _ _ _ => rfl
  have hI : ∀ b, b ∈ X.I.Iw 0 → ∀ g, χ (g * (1, b)) = χ g := by
    intro b hb g
    simpa using hχ 1 g 1 V.one_mem b hb
  have hN : ∀ b ∈ X.I.N, b ∈ X.I.Iw 0 := fun b hb => by
    rw [Iwa.Iw.eq_1]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hb)
  have hT : ∀ b ∈ X.I.T, b ∈ X.I.Iw 0 := fun b hb => by
    rw [Iwa.Iw.eq_1]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)
  have hM : ∀ c, ∀ b ∈ X.I.Nm c, b ∈ X.I.Iw 0 := fun c b hb => by
    rw [Iwa.Iw.eq_1]
    exact Subgroup.mem_sup_right (X.I.Nm_anti (Nat.zero_le c) hb)
  rw [Frame.Sp.eq_1, Submodule.mem_inf] at hf ⊢
  obtain ⟨hA, hV⟩ := hf
  have hV' : ∀ w ∈ V, X.ra τ w f = f := hV
  rw [Frame.Amb.eq_1] at hA ⊢
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq] at hA ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hA
  have h2' : ∀ b ∈ X.I.N, X.rp A m b f = f := h2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : χ (X.glob γ * g) = χ g := by
      have e0 := hχ γ g 1 V.one_mem 1 (one_mem _)
      simp only [OneMemClass.coe_one] at e0
      rwa [show ((1 : Ga), (1 : Gp)) = 1 from rfl, mul_one] at e0
    simp only [e, h1]
  · have key : ∀ b ∈ X.I.N, X.rp A m b (fun g => χ g • f g) = fun g => χ g • f g := by
      intro b hb
      funext g
      have e := congrFun (h2' b hb) g
      rw [hrp] at e
      simp only [hrp, hI b (hN b hb), e]
    exact key
  · intro t
    funext g
    have e := congrFun (h3 t) g
    rw [hrp, Pi.smul_apply] at e
    simp only [hrp, Pi.smul_apply, hI _ (hT _ t.2), e]
    exact smul_comm _ _ _
  · intro k
    obtain ⟨c, hc⟩ := h4 k
    refine ⟨c, fun y hy g i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, hI y (hM c y hy)]
    rw [← mul_sub]
    exact Ideal.mul_mem_left _ _ (hc y hy g i)
  · have key : ∀ w ∈ V, X.ra τ w (fun g => χ g • f g) = fun g => χ g • f g := by
      intro w hw
      funext g
      have hw' : χ (g * ((w : Ga), 1)) = χ g := by simpa using hχ 1 g w hw 1 (one_mem _)
      have e := congrFun (hV' w hw) g
      rw [Frame.ra_apply] at e
      simp only [Frame.ra_apply, hw', Matrix.mulVec_smul, e]
    exact key

private theorem ordProj_phi (hθ : X.I.ContChar θ) (U V : Subgroup X.Ub) [(V.subgroupOf U).Normal] (hVU : V ≤ U)
    [Fintype (U ⧸ V.subgroupOf U)] (hN : X.Neat U) (hV : X.FinLevel V) (hF : X.Free τ θ V)
    (ρ : Representation A (U ⧸ V.subgroupOf U) (X.Ord τ θ V))
    (hρ : ∀ (u : U) f, (ρ (u : U ⧸ V.subgroupOf U) f : X.Fn A m) = X.ra τ u f) :
    ∃ φ : Module.End A (X.Ord τ θ V), ∀ v, ∑ g, ρ g (φ (ρ g⁻¹ v)) = v := by
  classical
  obtain ⟨χ, hχ1, hχ2⟩ := ordProj_chi X A U V hVU hN
  obtain ⟨-, -, -, -, e, he1, he2⟩ := ordStruct X τ θ hθ V hV hF
  have hOS : ∀ f ∈ X.Ord τ θ V, f ∈ X.Sp τ θ V := fun f hf => ((mem_ord_iff X τ θ V f).1 hf).1
  let Mχ : X.Ord τ θ V →ₗ[A] X.Sp τ θ V :=
    { toFun := fun f => ⟨fun g => χ g • (f : X.Fn A m) g, ordProj_mul X τ θ V χ hχ1 f (hOS f f.2)⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext g
        simp [smul_add]
      map_smul' := fun c a => by
        apply Subtype.ext
        funext g
        show χ g • (c • (a : X.Fn A m)) g = c • (χ g • (a : X.Fn A m) g)
        rw [Pi.smul_apply, smul_comm] }
  have hMχ : ∀ f, ((Mχ f : X.Sp τ θ V) : X.Fn A m) = fun g => χ g • (f : X.Fn A m) g := fun f => rfl
  have hc : ∀ (q : U ⧸ V.subgroupOf U) (w : X.Ord τ θ V),
      ((ρ q w : X.Ord τ θ V) : X.Fn A m) = X.ra τ ((q.out : U) : X.Ub) (w : X.Fn A m) := by
    intro q w
    have h0 := hρ q.out w
    rwa [QuotientGroup.out_eq'] at h0
  have hgg : ∀ q v, ρ q (ρ q⁻¹ v) = v := by
    intro q v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hK : ∀ F : X.Fn A m, (∀ k, F ∈ X.valIn A m k) → F = 0 := by
    intro F hF
    funext x i
    have h0 : F x i ∈ ⨅ k, maximalIdeal A ^ k :=
      (Submodule.mem_iInf _).2 fun k => (ordProj_val X k F).1 (hF k) x i
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top] at h0
    simpa using h0
  refine ⟨e ∘ₗ Mχ, fun v => ?_⟩
  have hd : ∑ q, X.ra τ ((q.out : U) : X.Ub) ((Mχ (ρ q⁻¹ v) : X.Sp τ θ V) : X.Fn A m) = (v : X.Fn A m) := by
    funext x
    rw [Finset.sum_apply]
    have e1 : ∀ q : U ⧸ V.subgroupOf U, X.ra τ ((q.out : U) : X.Ub) ((Mχ (ρ q⁻¹ v) : X.Sp τ θ V) : X.Fn A m) x
        = χ (x * ((((q.out : U) : X.Ub) : Ga), 1)) • (v : X.Fn A m) x := by
      intro q
      have hw : X.ra τ ((q.out : U) : X.Ub) ((ρ q⁻¹ v : X.Ord τ θ V) : X.Fn A m) = v := by
        rw [← hc, hgg]
      have hw' := congrFun hw x
      rw [Frame.ra_apply] at hw'
      rw [Frame.ra_apply, hMχ]
      simp only [Matrix.mulVec_smul, hw']
    simp_rw [e1]
    rw [← Finset.sum_smul, hχ2 x, one_smul]
  apply Subtype.ext
  refine sub_eq_zero.1 (hK _ fun k => ?_)
  choose J hJ using fun q => he2 (Mχ (ρ q⁻¹ v)) k
  obtain ⟨J0, hJ0⟩ := he2 ⟨v, hOS v v.2⟩ k
  set n := (Finset.univ.sup J ⊔ J0).factorial with hn
  have ha : ∀ q, (X.U A m X.I.z ^ n) ((Mχ (ρ q⁻¹ v) : X.Sp τ θ V) : X.Fn A m)
      - ((e (Mχ (ρ q⁻¹ v)) : X.Ord τ θ V) : X.Fn A m) ∈ X.valIn A m k :=
    fun q => hJ q _ (le_sup_of_le_left (Finset.le_sup (Finset.mem_univ q)))
  have hb : (X.U A m X.I.z ^ n) (v : X.Fn A m) - v ∈ X.valIn A m k := by
    have h0 := hJ0 (Finset.univ.sup J ⊔ J0) le_sup_right
    rw [← hn, he1 ⟨v, hOS v v.2⟩ v.2] at h0
    exact h0
  have hexp : ((∑ q, ρ q ((e ∘ₗ Mχ) (ρ q⁻¹ v)) : X.Ord τ θ V) : X.Fn A m) - v
      = (∑ q, X.ra τ ((q.out : U) : X.Ub) (((e (Mχ (ρ q⁻¹ v)) : X.Ord τ θ V) : X.Fn A m)
          - (X.U A m X.I.z ^ n) ((Mχ (ρ q⁻¹ v) : X.Sp τ θ V) : X.Fn A m)))
        + ((X.U A m X.I.z ^ n) (v : X.Fn A m) - v) := by
    have hs : ∑ q, X.ra τ ((q.out : U) : X.Ub) ((X.U A m X.I.z ^ n) ((Mχ (ρ q⁻¹ v) : X.Sp τ θ V) : X.Fn A m))
        = (X.U A m X.I.z ^ n) (v : X.Fn A m) := by
      simp_rw [ordProj_pow X τ θ hθ]
      rw [← map_sum, hd]
    rw [Submodule.coe_sum]
    simp only [LinearMap.comp_apply, hc, map_sub, Finset.sum_sub_distrib, hs]
    abel
  rw [hexp]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun q _ => ordProj_valra X τ k _ _ ?_) hb
  rw [← neg_sub]
  exact Submodule.neg_mem _ (ha q)

end

theorem UpperTheory.V.Hi.ordProj :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (A : Type) [CommRing A] [IsCNL A] (m : ℕ) (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ), X.I.ContChar θ → ∀ (U V : Subgroup X.Ub) [(V.subgroupOf U).Normal], V ≤ U → V.relIndex U ≠ 0 → X.FinLevel U → X.Neat U → (∃ ρ : Representation A (U ⧸ V.subgroupOf U) (X.Ord τ θ V), (∀ (u : U) f, (ρ (u : U ⧸ V.subgroupOf U) f : X.Fn A m) = X.ra τ u f) ∧ Module.Projective (MonoidAlgebra A (U ⧸ V.subgroupOf U)) ρ.asModule) ∧ (X.Ord τ θ V).map (dc (X.ra τ) U V 1) = X.Ord τ θ U ∧ X.Ord τ θ V ⊓ LinearMap.ker (dc (X.ra τ) U V 1) = Submodule.span A {y | ∃ u ∈ U, ∃ f ∈ X.Ord τ θ V, y = X.ra τ u f - f} := by
  intro Γ Ga Gp _ _ _ X A _ _ m τ θ hθ U V _ hVU hidx hU hN
  classical
  have hFU : X.Free τ θ U := by
    intro g γ u hu b hb h
    obtain ⟨rfl, rfl⟩ := hN g γ u hu b hb h
    refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    have h1 : (⟨1, Subgroup.one_mem _⟩ : ↥X.I.T) = 1 := rfl
    simp [h1]
  obtain ⟨hV, hFV, hUV⟩ := ordLevel Γ Ga Gp X A m τ θ hθ U V hVU hidx hU hFU
  obtain ⟨_, hfree, _⟩ := ordFree Γ Ga Gp X A m τ θ hθ V hV hFV
  haveI : (V.subgroupOf U).FiniteIndex := ⟨hidx⟩
  letI : Fintype (U ⧸ V.subgroupOf U) := Fintype.ofFinite _
  have hOS : ∀ f ∈ X.Ord τ θ V, f ∈ X.Sp τ θ V := fun f hf => ((mem_ord_iff X τ θ V f).1 hf).1
  have hfixd : ∀ f ∈ X.Ord τ θ V, f ∈ fixd (X.ra τ) V := fun f hf => by
    have h := hOS f hf
    rw [Frame.Sp.eq_1, Submodule.mem_inf] at h
    exact h.2
  have hfixV : ∀ f ∈ X.Ord τ θ V, ∀ w ∈ V, X.ra τ w f = f := fun f hf => hfixd f hf
  let σ : U →* Module.End A (X.Ord τ θ V) :=
    { toFun := fun u => (X.ra τ (u : X.Ub)).restrict (fun f hf => ordProj_ord X τ θ hθ U V hVU u f hf)
      map_one' := by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        simp [map_mul] }
  have hker : V.subgroupOf U ≤ σ.ker := by
    intro u hu
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    show X.ra τ (u : X.Ub) (f : X.Fn A m) = f
    exact hfixV f f.2 u (Subgroup.mem_subgroupOf.1 hu)
  let ρ : Representation A (U ⧸ V.subgroupOf U) (X.Ord τ θ V) := QuotientGroup.lift (V.subgroupOf U) σ hker
  have hρ : ∀ (u : U) f, ((ρ (u : U ⧸ V.subgroupOf U) f : X.Ord τ θ V) : X.Fn A m) = X.ra τ u f :=
    fun u f => rfl
  haveI : Module.Free A (X.Ord τ θ V) := hfree
  obtain ⟨φ, hφ⟩ := ordProj_phi X τ θ hθ U V hVU hN hV hFV ρ hρ
  have hc : ∀ (q : U ⧸ V.subgroupOf U) (w : X.Ord τ θ V),
      ((ρ q w : X.Ord τ θ V) : X.Fn A m) = X.ra τ ((q.out : U) : X.Ub) (w : X.Fn A m) := by
    intro q w
    have h0 := hρ q.out w
    rwa [QuotientGroup.out_eq'] at h0
  have htr : ∀ w : X.Ord τ θ V,
      dc (X.ra τ) U V 1 (w : X.Fn A m) = ((∑ q, ρ q w : X.Ord τ θ V) : X.Fn A m) := by
    intro w
    rw [ordProj_dc (X.ra τ) U V _ (hfixd _ w.2), Submodule.coe_sum]
    simp only [hc]
  have htrinv : ∀ (w : X.Ord τ θ V) (u : U ⧸ V.subgroupOf U), ∑ q, ρ q (ρ u w) = ∑ q, ρ q w := by
    intro w u
    have h0 : ∀ q, ρ q (ρ u w) = ρ (q * u) w := fun q => by rw [map_mul, Module.End.mul_apply]
    simp_rw [h0]
    exact Fintype.sum_equiv (Equiv.mulRight u) _ _ (fun q => rfl)
  have htrinvL : ∀ (w : X.Ord τ θ V) (u : U ⧸ V.subgroupOf U), ∑ q, ρ u (ρ q w) = ∑ q, ρ q w := by
    intro w u
    have h0 : ∀ q, ρ u (ρ q w) = ρ (u * q) w := fun q => by rw [map_mul, Module.End.mul_apply]
    simp_rw [h0]
    exact Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun q => rfl)
  refine ⟨⟨ρ, hρ, ordProj_higman ρ φ hφ⟩, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨f, hf, rfl⟩
      rw [hUV]
      have e1 : dc (X.ra τ) U V 1 f = ((∑ q, ρ q ⟨f, hf⟩ : X.Ord τ θ V) : X.Fn A m) := htr ⟨f, hf⟩
      rw [e1]
      refine Submodule.mem_inf.2 ⟨Subtype.mem _, ?_⟩
      have key : ∀ u ∈ U, X.ra τ u ((∑ q, ρ q ⟨f, hf⟩ : X.Ord τ θ V) : X.Fn A m)
          = ((∑ q, ρ q ⟨f, hf⟩ : X.Ord τ θ V) : X.Fn A m) := by
        intro u hu
        rw [show X.ra τ u = X.ra τ ((⟨u, hu⟩ : U) : X.Ub) from rfl, ← hρ, map_sum, htrinvL]
      exact key
    · intro f hf
      have hfV : f ∈ X.Ord τ θ V := by
        rw [hUV] at hf
        exact (Submodule.mem_inf.1 hf).1
      have hfU : ∀ u ∈ U, X.ra τ u f = f := by
        rw [hUV] at hf
        exact (Submodule.mem_inf.1 hf).2
      refine ⟨(φ ⟨f, hfV⟩ : X.Fn A m), (φ ⟨f, hfV⟩).2, ?_⟩
      rw [htr]
      have hq : ∀ q : U ⧸ V.subgroupOf U, ρ q⁻¹ ⟨f, hfV⟩ = ⟨f, hfV⟩ := fun q => by
        apply Subtype.ext
        rw [hc]
        exact hfU _ (q⁻¹.out).2
      have h0 := hφ ⟨f, hfV⟩
      simp only [hq] at h0
      rw [h0]
  · apply le_antisymm
    · rintro f ⟨hfV, hk⟩
      have hf0 : (∑ q, ρ q ⟨f, hfV⟩) = 0 := by
        apply Subtype.ext
        rw [← htr]
        simpa using LinearMap.mem_ker.1 hk
      have hsumw : ∑ q, φ (ρ q⁻¹ ⟨f, hfV⟩) = 0 := by
        rw [← map_sum, Fintype.sum_equiv (Equiv.inv _) (fun q => ρ q⁻¹ ⟨f, hfV⟩) (fun q => ρ q ⟨f, hfV⟩)
          (fun q => rfl), hf0, map_zero]
      have hfe : (⟨f, hfV⟩ : X.Ord τ θ V) = ∑ q, (ρ q (φ (ρ q⁻¹ ⟨f, hfV⟩)) - φ (ρ q⁻¹ ⟨f, hfV⟩)) := by
        rw [Finset.sum_sub_distrib, hsumw, sub_zero]
        exact (hφ _).symm
      have h1 : f = ((∑ q, (ρ q (φ (ρ q⁻¹ ⟨f, hfV⟩)) - φ (ρ q⁻¹ ⟨f, hfV⟩)) : X.Ord τ θ V) : X.Fn A m) :=
        congrArg Subtype.val hfe
      rw [h1, Submodule.coe_sum]
      refine Submodule.sum_mem _ fun q _ => Submodule.subset_span
        ⟨((q.out : U) : X.Ub), (q.out).2, _, (φ (ρ q⁻¹ ⟨f, hfV⟩)).2, ?_⟩
      rw [Submodule.coe_sub, hc]
    · rw [Submodule.span_le]
      rintro _ ⟨u, hu, f, hf, rfl⟩
      refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ (ordProj_ord X τ θ hθ U V hVU ⟨u, hu⟩ f hf) hf, ?_⟩
      rw [LinearMap.mem_ker, map_sub]
      have e2 : dc (X.ra τ) U V 1 (X.ra τ u f)
          = ((∑ q, ρ q (ρ ((⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U) ⟨f, hf⟩) : X.Ord τ θ V) : X.Fn A m) :=
        htr (ρ ((⟨u, hu⟩ : U) : U ⧸ V.subgroupOf U) ⟨f, hf⟩)
      have e1 : dc (X.ra τ) U V 1 f = ((∑ q, ρ q ⟨f, hf⟩ : X.Ord τ θ V) : X.Fn A m) := htr ⟨f, hf⟩
      rw [e2, e1, htrinv, sub_self]
