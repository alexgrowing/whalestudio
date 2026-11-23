import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniquePairsToTower

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory

namespace PDivGroup

open PDiv

variable {p : ℕ} [hp : Fact p.Prime]

theorem finrank_eq_of_semilinear_surjective {W k M V : Type} [CommRing W] [Nontrivial W] [Field k]
    [AddCommGroup M] [Module W M] [Module.Free W M] [Module.Finite W M] [AddCommGroup V] [Module k V]
    {σ : W →+* k} (hσ : Function.Surjective σ) {q : ℕ} (hq : (q : k) = 0) (r : M →ₛₗ[σ] V)
    (hr : Function.Surjective r) (hk : ∀ m, r m = 0 → ∃ n, m = q • n) :
    Module.Finite k V ∧ Module.finrank k V = Module.finrank W M := by
  let b := Module.finBasis W M
  have h1 : LinearIndependent k fun i => r (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    choose w hw using fun i => hσ (c i)
    obtain ⟨n, hn⟩ := hk (∑ i, w i • b i) (by simpa only [map_sum, map_smulₛₗ, hw] using hc)
    have e := congrArg (fun m => σ (b.repr m i)) hn
    simpa [hq, hw, Finsupp.single_apply] using e
  have h2 : ⊤ ≤ Submodule.span k (Set.range fun i => r (b i)) := fun v _ => by
    obtain ⟨m, rfl⟩ := hr v
    rw [← b.sum_repr m, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨.of_basis (.mk h1 h2), by rw [Module.finrank_eq_card_basis (.mk h1 h2), Fintype.card_fin]⟩

section BaseChange

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S] {G H : PDivGroup p R}

theorem baseChangeMap_prime_smul_id :
    baseChangeMap S ((p : ℤ_[p]) • 𝟙 G) = (p : ℤ_[p]) • 𝟙 (G.baseChange S) :=
  baseChange_hom_ext fun n a => by
    rw [prime_smul_id_app, ← toBase_app, ← SemiBialgHom.map_mulBy, ← prime_smul_id_app]
    rfl

theorem rigExtMap_baseChangeMap_comp_liftSemi (f : G ⟶ H) :
    rigExtMap (baseChangeMap S f) ∘ₗ liftSemi (H.toBase S).rig =
      liftSemi (G.toBase S).rig ∘ₗ (rigExtMap f).baseChange S :=
  LinearMap.ext fun y => by
    induction y with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r x =>
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, liftSemi_tmul,
        liftSemi_tmul, map_smul,
        (G.toBase S).rig_naturality (H.toBase S) f (baseChangeMap S f) fun _ _ => rfl]

end BaseChange

variable (hW : Published.BarsottiTateDieudonne.WittModule) {K : Type} [Field K] (h : (p : K) = 0)
include hW h

theorem finrank_rigExt (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height := by
  let L := AlgebraicClosure K
  have hL : (p : L) = 0 := natCast_eq_zero_of_algebra h L
  haveI : CharP L p := (CharP.charP_iff_prime_eq_zero hp.out).2 hL
  obtain ⟨M, _, red, h1, -⟩ := hW p L
  obtain ⟨_, _, h2, h3, h4, -⟩ := h1 (G.baseChange L)
  obtain ⟨_, h5⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hL
    (red _) h3 fun m => (h4 m).1
  let e := LinearEquiv.ofBijective _ (G.liftSemi_rig_bijective L h (.inl inferInstance))
  haveI := Module.Finite.equiv e.symm
  exact ⟨.of_finite_tensorProduct_of_faithfullyFlat L,
    by rw [← Module.finrank_baseChange (R := L), e.finrank_eq, h5, h2]⟩

theorem finrank_omega_add_finrank_dual_omega (G : PDivGroup p K) :
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  obtain ⟨_, h1⟩ := finrank_rigExt hW h G
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h), h1] at e
  rw [← e, add_comm, ← Subspace.dual_finrank_eq]

theorem ker_rigExtMap_eq_range_of_field {G H : PDivGroup p K} {f : G ⟶ H} {g : H ⟶ G}
    (hf : f ≫ g = (p : ℤ_[p]) • 𝟙 G) (hg : g ≫ f = (p : ℤ_[p]) • 𝟙 H) :
    LinearMap.ker (rigExtMap f) = LinearMap.range (rigExtMap g) := by
  let L := AlgebraicClosure K
  haveI : CharP L p := (CharP.charP_iff_prime_eq_zero hp.out).2 (natCast_eq_zero_of_algebra h L)
  have hc : ∀ {A B : PDivGroup p K} {u : A ⟶ B} {v : B ⟶ A}, u ≫ v = (p : ℤ_[p]) • 𝟙 A →
      baseChangeMap L u ≫ baseChangeMap L v = (p : ℤ_[p]) • 𝟙 _ := fun e => by
    rw [← baseChangeMap_prime_smul_id, ← e]
    exact ((baseChangeFunctor p K L).map_comp _ _).symm
  have h1 := LinearMap.exact_iff.2 (ker_rigExtMap_eq_range (hW p L) (hc hf) (hc hg))
  let e := fun A : PDivGroup p K =>
    LinearEquiv.ofBijective _ (A.liftSemi_rig_bijective L h (.inl inferInstance))
  have h2 := (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e G) (e₂ := e H) (e₃ := e G)
    (rigExtMap_baseChangeMap_comp_liftSemi L g) (rigExtMap_baseChangeMap_comp_liftSemi L f)).1 h1
  exact LinearMap.exact_iff.1 ((Module.FaithfullyFlat.lTensor_exact_iff_exact K L _ _).1 h2)

omit hW in

theorem range_rigExtMap_relFrob (G : PDivGroup p K) :
    LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span K (Set.range (absFrob h G).rig) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    have key : ∀ (P : (frobTwist h G).RigExt → Prop), P 0 → (∀ (r : K) y, P (r • (frobProj h G).rig y)) →
        (∀ x y, P x → P y → P (x + y)) → P x := fun P h0 h1 h2 => by
      letI := (frobRing h).toAlgebra
      obtain ⟨y, rfl⟩ := (liftSemi_rig_bijective (R := K) K G h
        (.inl (@Module.Flat.of_free K K _ _ (_) (@Module.Free.of_divisionRing K K _ _ (_))))).2 x
      induction y with
      | zero => exact (congrArg P (map_zero _)).mpr h0
      | add x y hx hy => exact (congrArg P (map_add _ _ _)).mpr (h2 _ _ hx hy)
      | tmul r y => exact h1 r y
    refine key (fun x => rigExtMap (relFrob h G) x ∈ Submodule.span K (Set.range (absFrob h G).rig))
      (by simp only [map_zero, zero_mem]) (fun r y => ?_) fun x y hx hy => ?_
    · rw [map_smul, rigExtMap_relFrob_rig]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
    · rw [map_add]
      exact add_mem hx hy
  · rintro _ ⟨y, rfl⟩
    exact ⟨_, rigExtMap_relFrob_rig h G y⟩

omit hW h hp in

theorem rigExt_field (hW : Published.BarsottiTateDieudonne.WittModule) (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧
    Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height ∧
    LinearMap.range (rigExtMap (verschiebung h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (relFrob h G)) = LinearMap.range (frobTwist h G).rigOfOmega ∧
    LinearMap.ker (rigExtMap (verschiebung h G)) = LinearMap.range (rigExtMap (relFrob h G)) ∧
    LinearMap.range (rigExtMap (relFrob h G)) = Submodule.span K (Set.range (absFrob h G).rig) := by
  have h1 := ker_rigExtMap_eq_range_of_field hW h (relFrob_comp_verschiebung h G)
    (verschiebung_comp_relFrob h G)
  have h2 := range_rigExtMap_verschiebung_le h G
  have h3 := LinearMap.range_le_ker_iff.2 (rigExtMap_relFrob_comp_rigOfOmega h G)
  exact ⟨(finrank_rigExt hW h G).1, (finrank_rigExt hW h G).2,
    finrank_omega_add_finrank_dual_omega hW h G, le_antisymm h2 (h1 ▸ h3), le_antisymm (h1 ▸ h2) h3,
    ker_rigExtMap_eq_range_of_field hW h (verschiebung_comp_relFrob h G)
      (relFrob_comp_verschiebung h G), range_rigExtMap_relFrob h G⟩

end PDivGroup

end GlobalTheory
