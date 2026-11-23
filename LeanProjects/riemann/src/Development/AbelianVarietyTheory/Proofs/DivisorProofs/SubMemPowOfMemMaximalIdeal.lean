import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtUniq

theorem sub_mem_pow_of_mem_maximalIdeal {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ x ∈ maximalIdeal W, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 2) := by
  intro x hx
  rw [← hm] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    have := congrArg (fun f => f a) hO
    simp only [RingHom.comp_apply] at this
    rw [this, sub_self]; exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_sub_add_comm]; exact add_mem hx hy
  | smul a x hx' hx =>
    have hx'' : x ∈ maximalIdeal W := by rw [← hm]; exact hx'
    have h2 : θ₂ x ∈ maximalIdeal V :=
      (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx'' (isUnit_of_map_unit θ₂ x h)
    simp only [smul_eq_mul, map_mul]
    have e : θ₁ a * θ₁ x - θ₂ a * θ₂ x = θ₁ a * (θ₁ x - θ₂ x) + (θ₁ a - θ₂ a) * θ₂ x := by ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hx) ?_
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
    exact Ideal.mul_mem_mul (hk a) h2

abbrev Gr (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Type :=
  ↥(maximalIdeal V ^ (k + 1)) ⧸ (maximalIdeal V • (⊤ : Submodule V ↥(maximalIdeal V ^ (k + 1))))

noncomputable instance (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Module (ResidueField V) (Gr V k) :=
  inferInstanceAs (Module (V ⧸ maximalIdeal V) (Gr V k))

noncomputable abbrev grModule {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (θ : W →+* V) [IsLocalHom θ] (k : ℕ) : Module (ResidueField W) (Gr V k) :=
  Module.compHom _ (ResidueField.map θ)

theorem gr_mk_eq_zero_iff (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (v : ↥(maximalIdeal V ^ (k + 1))) :
    (Submodule.Quotient.mk v : Gr V k) = 0 ↔ (v : V) ∈ maximalIdeal V ^ (k + 2) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

theorem gr_mk_eq_mk (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (u v : ↥(maximalIdeal V ^ (k + 1))) (h : (u : V) - v ∈ maximalIdeal V ^ (k + 2)) :
    (Submodule.Quotient.mk u : Gr V k) = Submodule.Quotient.mk v := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, gr_mk_eq_zero_iff]; simpa using h

theorem sub_mem_pow_succ {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (hu : ((residue W).comp φ).FormallyUnramified)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 2) := by
  have hW := sub_mem_pow_of_mem_maximalIdeal φ hm θ₁ θ₂ hO k hk
  letI : Algebra O (ResidueField W) := ((residue W).comp φ).toAlgebra
  haveI : Algebra.FormallyUnramified O (ResidueField W) := hu
  letI : Module (ResidueField W) (Gr V k) := grModule θ₁ k
  letI : Module O (Gr V k) := Module.compHom _ (algebraMap O (ResidueField W))
  haveI : IsScalarTower O (ResidueField W) (Gr V k) := ⟨fun a b x => by
    show ResidueField.map θ₁ (a • b) • x = ResidueField.map θ₁ (algebraMap O _ a) • (ResidueField.map θ₁ b • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let δ₀ : W → Gr V k := fun w => Submodule.Quotient.mk ⟨θ₁ w - θ₂ w, hk w⟩
  have hsm : ∀ (c : W) (v : ↥(maximalIdeal V ^ (k + 1))), residue W c • (Submodule.Quotient.mk v : Gr V k) =
      Submodule.Quotient.mk (θ₁ c • v) := by
    intro c v
    show ResidueField.map θ₁ (residue W c) • (Submodule.Quotient.mk v : Gr V k) = _
    rw [ResidueField.map_residue]
    rfl
  let s := Function.surjInv (residue_surjective (R := W))
  have hs : ∀ w, δ₀ (s (residue W w)) = δ₀ w := by
    intro w
    refine gr_mk_eq_mk V k _ _ ?_
    have hmem : s (residue W w) - w ∈ maximalIdeal W := by
      rw [← Ideal.Quotient.eq]
      exact Function.surjInv_eq _ _
    have := hW _ hmem
    simp only [map_sub] at this ⊢
    convert this using 1; ring
  let D : Derivation O (ResidueField W) (Gr V k) :=
    { toFun := fun x => δ₀ (s x)
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        rw [← map_add, hs, hs, hs, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, map_add]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := residue_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, show algebraMap O (ResidueField W) c = residue W (φ c) from rfl,
          ← map_mul, hs, hs]
        show _ = residue W (φ c) • δ₀ a
        rw [hsm]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
        have := congrArg (fun f => f c) hO
        simp only [RingHom.comp_apply] at this
        rw [this]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_one_eq_zero' := by
        show δ₀ (s 1) = 0
        rw [← map_one (residue W), hs]
        show (Submodule.Quotient.mk _ : Gr V k) = 0
        rw [gr_mk_eq_zero_iff]; simp
      leibniz' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        show δ₀ (s _) = residue W a • δ₀ (s _) + residue W b • δ₀ (s _)
        rw [← map_mul, hs, hs, hs, hsm, hsm, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
        have e : θ₁ a * θ₁ b - θ₂ a * θ₂ b - (θ₁ a * (θ₁ b - θ₂ b) + θ₁ b * (θ₁ a - θ₂ a)) =
            (θ₁ a - θ₂ a) * (θ₂ b - θ₁ b) := by ring
        rw [e, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
        refine Ideal.mul_mem_mul (hk a) ?_
        have := Ideal.pow_le_self (n := k + 1) (I := maximalIdeal V) (by omega) (hk b)
        rw [← neg_sub]; exact neg_mem this }
  have hD : ∀ x, D x = 0 := by
    intro x
    rw [← Derivation.liftKaehlerDifferential_comp_D D x,
      Subsingleton.elim (KaehlerDifferential.D O (ResidueField W) x) 0, map_zero]
  intro w
  have h1 : δ₀ w = 0 := by
    rw [← hs]
    exact hD (residue W w)
  exact (gr_mk_eq_zero_iff V k _).1 h1

theorem localHom_ext : ∀ (O W V : Type) [CommRing O] [IsLocalRing O] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (φ : O →+* W), IsAdicComplete (maximalIdeal W) W → IsEtaleCompletion φ → ((residue W).comp φ).FormallyUnramified → ∀ θ₁ θ₂ : W →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp φ = θ₂.comp φ → (∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V) → θ₁ = θ₂ := by
  intro O W V _ _ _ _ _ _ _ _ φ _ hφ hu θ₁ θ₂ h₁ h₂ hO hres
  have hk : ∀ k w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using hres
    | succ k ih => exact sub_mem_pow_succ φ hφ.2.1 hu θ₁ θ₂ hO k ih
  ext w
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro i
  cases i with
  | zero => simp
  | succ i => exact hk i w

end GlobalTheory.EtUniq
