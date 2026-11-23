import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem krull_dim_quotient_comap_eq {k Z A B C : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] [AddCommGroup C] [Module k C] [Module.Finite k A] [Module.Finite k C]
    (δ : Z →ₗ[k] A) (β : A →ₗ[k] B) (p : B →ₗ[k] C) (h0 : Function.Injective δ)
    (h1 : LinearMap.range δ = LinearMap.ker β) (h2 : LinearMap.range β = LinearMap.ker p) :
    Module.finrank k Z + Module.finrank k B = Module.finrank k A + Module.finrank k (LinearMap.range p) := by
  have hB : Module.Finite k B := by
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker p (IsNoetherian.noetherian _) ?_⟩
    rw [top_inf_eq, ← h2, LinearMap.range_eq_map]
    exact Submodule.FG.map _ Module.Finite.fg_top
  have e1 := LinearMap.finrank_range_add_finrank_ker β
  have e2 := LinearMap.finrank_range_add_finrank_ker p
  have e3 := LinearMap.finrank_range_of_inj h0
  rw [← h1, h2] at e1
  omega

private theorem cob_lc {k Γ M : Type} [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module k M] (ρ : Representation k Γ M) (h : IsOpen (ρ.ker : Set Γ)) (m : M) :
    IsLocallyConstant (fun g => ρ g m - m) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ρ.ker : Set Γ), h.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  have hy' : ρ (x⁻¹ * y) = 1 := hy
  have : ρ y = ρ x := by
    conv_lhs => rw [← mul_inv_cancel_left x y, map_mul, hy', mul_one]
  rw [this]

theorem UpperTheory.V.Alg.finrank_compact_support_H1 :
    ∀ (k Γ M : Type) [Field k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M]
      (ρ : Representation k Γ M), IsOpen (ρ.ker : Set Γ) → ∀ (F : Frame Γ), (∀ q, ∀ n ∈ F.N q, ρ (F.ψ q n) = 1) → Module.Finite k (ReciprocityTheory.Gal.H1 ρ) →
      Module.finrank k (ReciprocityTheory.Gal.H0 ρ) + Module.finrank k (F.H1c ρ) = ∑ v, Module.finrank k (ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) +
        Module.finrank k (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
  intro k Γ M _ _ _ _ _ _ _ _ _ _ _ ρ hρ F hN hfin
  classical
  let δ : ReciprocityTheory.Gal.H0 ρ →ₗ[k] (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) :=
    LinearMap.pi fun v => ReciprocityTheory.Gal.resH0 ρ (F.φ v)
  let β : (∀ v, ReciprocityTheory.Gal.H0 (ρ.comp (F.φ v) : Representation k _ M)) →ₗ[k] F.H1c ρ :=
    { toFun := fun b => ⟨(fun g => ρ g (-(b F.v0).1) - (-(b F.v0).1), fun v => (b v).1 - (b F.v0).1),
        cob_lc ρ hρ _, fun s t => by
          simp only [map_mul, Module.End.mul_apply, map_sub]; abel,
        fun q n hn => by simp [hN q n hn],
        fun v s => by
          have : ρ (F.φ v s) (b v).1 = (b v).1 := (b v).2 s
          simp only [map_sub, map_neg, this]; abel,
        sub_self _⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp; abel
        · simp; abel
      map_smul' := fun c b => by
        apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · simp [smul_add]
        · simp [smul_sub] }
  let p0 : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.Z1 ρ :=
    { toFun := fun x => ⟨x.1.1, x.2.1.continuous, x.2.2.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : F.H1c ρ →ₗ[k] ReciprocityTheory.Gal.H1 ρ := (Submodule.mkQ _).comp p0
  have h0 : Function.Injective δ := by
    intro x y hxy
    have := congrArg (fun b => (b F.v0).1) hxy
    exact Subtype.ext this
  have h1 : LinearMap.range δ = LinearMap.ker β := by
    ext b
    rw [LinearMap.mem_ker]
    constructor
    · rintro ⟨m, rfl⟩
      apply Subtype.ext
      refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
      · change ρ g (-m.1) - (-m.1) = 0
        rw [map_neg, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ m.1).1 m.2 g, sub_self]
      · exact sub_self m.1
    · intro hb
      have e1 : ∀ g, ρ g (-(b F.v0).1) - (-(b F.v0).1) = 0 := fun g =>
        congrArg (fun x : F.H1c ρ => x.1.1 g) hb
      have e2 : ∀ v, (b v).1 - (b F.v0).1 = 0 := fun v =>
        congrArg (fun x : F.H1c ρ => x.1.2 v) hb
      refine ⟨⟨(b F.v0).1, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere ρ _).2 fun g => ?_⟩, funext fun v => Subtype.ext ?_⟩
      · have := e1 g
        rw [map_neg, sub_eq_zero] at this
        exact neg_injective this
      · exact (sub_eq_zero.1 (e2 v)).symm
  have h2 : LinearMap.range β = LinearMap.ker p := by
    ext x
    rw [LinearMap.mem_ker]
    change _ ↔ Submodule.Quotient.mk (p0 x) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨-(b F.v0).1, fun g => rfl⟩
    · rintro ⟨m, hm⟩
      have hm' : ∀ g, x.1.1 g = ρ g m - m := hm
      obtain ⟨-, -, -, a4, a5⟩ := x.2
      refine ⟨fun v => ⟨x.1.2 v - m, (ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun s => ?_⟩, ?_⟩
      · change ρ (F.φ v s) (x.1.2 v - m) = x.1.2 v - m
        have := a4 v s
        rw [hm'] at this
        rw [map_sub, sub_eq_sub_iff_sub_eq_sub, this]
      · apply Subtype.ext
        refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
        · change ρ g (-(x.1.2 F.v0 - m)) - (-(x.1.2 F.v0 - m)) = x.1.1 g
          rw [a5, hm']; simp
        · change x.1.2 v - m - (x.1.2 F.v0 - m) = x.1.2 v
          rw [a5]; abel
  have key : ∀ c : ReciprocityTheory.Gal.Z1 ρ, (Submodule.Quotient.mk c : ReciprocityTheory.Gal.H1 ρ) ∈
      (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) ↔
      (∀ v, ∃ m, ∀ s, c.1 (F.φ v s) = ρ (F.φ v s) m - m) ∧ ∀ q, ∀ n ∈ F.N q, c.1 (F.ψ q n) = 0 := by
    intro c
    rw [Submodule.mem_inf, ReciprocityTheory.Gal.mem_Sel, ReciprocityTheory.Gal.Sha1, Submodule.mem_iInf]
    refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun q => ?_)
    · rw [LinearMap.mem_ker, ReciprocityTheory.Gal.resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      rfl
    · rw [ReciprocityTheory.Gal.H1ur, LinearMap.mem_ker, ReciprocityTheory.Gal.resH1]
      refine (Submodule.Quotient.mk_eq_zero _).trans ?_
      rw [ Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
      constructor
      · rintro ⟨m, hm⟩ n hn
        have : c.1 (F.ψ q n) = ρ (F.ψ q n) m - m := hm ⟨n, hn⟩
        rw [this, hN q n hn]; simp
      · intro h
        refine ⟨0, fun n => ?_⟩
        change c.1 (F.ψ q n.1) = ρ (F.ψ q n.1) 0 - 0
        rw [h n.1 n.2]; simp
  have h3 : LinearMap.range p = (ReciprocityTheory.Gal.Sha1 ρ F.φ F.hφ ⊓ ReciprocityTheory.Gal.Sel ρ F.ψ F.hψ (fun q => ReciprocityTheory.Gal.H1ur (ρ.comp (F.ψ q) : Representation k _ M) (F.N q)) : Submodule k (ReciprocityTheory.Gal.H1 ρ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨-, -, a3, a4, -⟩ := x.2
      exact (key (p0 x)).2 ⟨fun v => ⟨x.1.2 v, a4 v⟩, a3⟩
    · intro hy
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨k1, k2⟩ := (key c).1 hy
      choose m hm using k1
      refine ⟨⟨(fun g => c.1 g - (ρ g (m F.v0) - m F.v0), fun v => m v - m F.v0),
        ((IsLocallyConstant.iff_continuous _).2 c.2.1).sub (cob_lc ρ hρ _), fun s t => ?_, fun q n hn => ?_,
        fun v s => ?_, sub_self _⟩, ?_⟩
      · simp only [c.2.2 s t, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [k2 q n hn, hN q n hn]
      · simp only [hm, map_sub]; abel
      · change Submodule.Quotient.mk _ = _
        rw [Submodule.Quotient.eq, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
        refine ⟨-m F.v0, fun g => ?_⟩
        change c.1 g - (ρ g (m F.v0) - m F.v0) - c.1 g = _
        rw [map_neg]; abel
  have := krull_dim_quotient_comap_eq δ β p h0 h1 h2
  rw [h3, Module.finrank_pi_fintype] at this
  exact this
