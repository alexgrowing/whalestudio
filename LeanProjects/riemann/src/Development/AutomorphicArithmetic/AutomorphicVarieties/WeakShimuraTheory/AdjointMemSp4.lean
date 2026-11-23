import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2

noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.Ws

section Frame

variable {O Γ Γb : Type} [CommRing O] [Group Γ] [Group Γb] (Φ : Fr O Γ)

abbrev Fr.noMu : Fr O Γ := { Φ with Mu := fun _ => ∅ }

def Fr.loc (π : Γ →* Γb) (v : Φ.ι) : Φ.Gv v →* Γb := π.comp (Φ.Gv v).subtype

structure Fr.Quo [TopologicalSpace Γ] [IsTopologicalGroup Γ] [TopologicalSpace Γb] (π : Γ →* Γb) : Prop where
  cont : Continuous π
  onto : Function.Surjective π
  ker : π.ker = (Subgroup.normalClosure Φ.N).topologicalClosure

end Frame

section Ad

variable {Γ k : Type} [Group Γ] [CommRing k]

theorem adjoint_mem_sp4 {r : Γ →* M4 k} (h : ∀ g, ∃ ν, IsGSp ν (r g)) (g : Γ) {X : M4 k} (hX : X ∈ sp4 k) :
    r g * X * r g⁻¹ ∈ sp4 k := by
  obtain ⟨hmul, -, -, -, -, -, hinv, -⟩ := grp k
  obtain ⟨ν, hν⟩ := h g
  obtain ⟨ν', hν'⟩ := h g⁻¹
  have e1 : r g * r g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have e2 : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have a1 := hinv ν _ _ hν e1
  have a2 := hinv ν' _ _ hν' e2
  have a3 : adj (r g⁻¹) * adj (r g) = 1 := by
    obtain ⟨-, -, -, -, h1, -⟩ := grp k
    rw [← hmul, e1, h1]
  have hX' : adj X = -X := hX
  show adj _ = -_
  have a4 : (ν' * ν) • (1 : M4 k) = 1 := by
    rw [a1, a2, smul_mul_assoc, mul_smul_comm, e1, smul_smul] at a3
    exact a3
  rw [hmul, hmul, hX', a1, a2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, neg_mul, mul_neg, smul_neg, mul_assoc]
  rw [← one_mul (r g * (X * r g⁻¹)), ← smul_mul_assoc, mul_comm ν ν', a4]

def adSp (r : Γ →* M4 k) (h : ∀ g, ∃ ν, IsGSp ν (r g)) : Representation k Γ (sp4 k) where
  toFun s :=
    { toFun := fun Y => ⟨r s * Y.1 * r s⁻¹, adjoint_mem_sp4 h s Y.2⟩
      map_add' := fun Y Y' => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun c Y => Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun Y => Subtype.ext (by simp)
  map_mul' s t := LinearMap.ext fun Y => Subtype.ext (by simp [mul_assoc])

theorem adSp_val (r : Γ →* M4 k) (h : ∀ g, ∃ ν, IsGSp ν (r g)) (s : Γ) (Y : sp4 k) :
    (adSp r h s Y).1 = r s * Y.1 * r s⁻¹ := rfl

def bor (n : M4 k) : Submodule k (sp4 k) where
  carrier := {X | IsUp (adj n * X.1 * n)}
  add_mem' {X Y} hX hY i j h := by
    rw [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, Matrix.smul_apply, hX i j h, smul_zero]

def nil (n : M4 k) : Submodule k (sp4 k) where
  carrier := {X | ∀ i j, i ≤ j → (adj n * X.1 * n) i j = 0}
  add_mem' {X Y} hX hY i j h := by
    rw [Submodule.coe_add, mul_add, add_mul, Matrix.add_apply, hX i j h, hY i j h, add_zero]
  zero_mem' i j _ := by simp
  smul_mem' c X hX i j h := by
    rw [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, Matrix.smul_apply, hX i j h, smul_zero]

variable (k) in

def tor : Submodule k (sp4 k) where
  carrier := {X | X.1.IsDiag}
  add_mem' hX hY := hX.add hY
  zero_mem' := Matrix.isDiag_zero
  smul_mem' c _ hX := hX.smul c

end Ad

section Cone

variable {k G W V : Type} [CommRing k] [Group G] [TopologicalSpace G] [AddCommGroup W] [Module k W]
  {Gv : V → Type} [∀ v, Group (Gv v)]

def TanC (loc : ∀ v, Gv v →* G) (ρ : Representation k G W) (b n : V → Submodule k W) (g0 : G) (t : Submodule k W) :
    Submodule k ((G → W) × (V → W)) :=
  Fr.Z1C loc ρ b ⊓ Submodule.prod (t.comap (LinearMap.proj g0)) (Submodule.pi Set.univ n)

end Cone

section Weak

variable {Γ V : Type} [Group Γ] {Gv : V → Type} [∀ v, Group (Gv v)] (loc : ∀ v, Gv v →* Γ)

structure WP {R : Type} [CommRing R] (ν : Γ → R) (r : Γ →* M4 R) (n : V → M4 R) : Prop where
  mult : ∀ g, IsGSp (ν g) (r g)
  sp : ∀ v, IsGSp 1 (n v)
  flag : ∀ v s, IsUp (adj (n v) * r (loc v s) * n v)

variable [TopologicalSpace Γ] [∀ v, TopologicalSpace (Gv v)] {Λ : Type} [CommRing Λ] (ν : Γ →* Λˣ)
  {R : Type} [CommRing R] [Algebra Λ R] (r : Γ →* M4 R) (n : V → M4 R)
  {A : Type} [CommRing A] [Algebra Λ A] [IsLocalRing A] (p : A →ₐ[Λ] R)

def WLift : Prop :=
  ∃ (r' : Γ →* M4 A) (n' : V → M4 A), WP loc (fun g => algebraMap Λ A (ν g)) r' n' ∧
    (∀ i j, AdicCont (maximalIdeal A) fun g => r' g i j) ∧ (∀ g, (r' g).map p = r g) ∧ ∀ v, (n' v).map p = n v

structure SL where
  rt : Γ → M4 A
  rt_cont : ∀ i j, AdicCont (maximalIdeal A) fun g => rt g i j
  rt_mult : ∀ g, IsGSp (algebraMap Λ A (ν g)) (rt g)
  rt_map : ∀ g, (rt g).map p = r g
  nt : V → M4 A
  nt_sp : ∀ v, IsGSp 1 (nt v)
  nt_map : ∀ v, (nt v).map p = n v
  t : ∀ v, Gv v → M4 A
  t_cont : ∀ v i j, AdicCont (maximalIdeal A) fun s => t v s i j
  t_mult : ∀ v s, IsGSp (algebraMap Λ A (ν (loc v s))) (t v s)
  t_up : ∀ v s, IsUp (t v s)
  t_map : ∀ v s, (t v s).map p = adj (n v) * r (loc v s) * n v

variable {loc ν r n p}

def SL.om (D : SL loc ν r n p) (s t : Γ) : M4 A := D.rt s * D.rt t - D.rt (s * t)

def SL.de (D : SL loc ν r n p) (v : V) (s : Gv v) : M4 A := D.rt (loc v s) - D.nt v * D.t v s * adj (D.nt v)

end Weak

def Obs (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (R : Type) [CommRing R] [Algebra Λ R] (V : Type) [AddCommGroup V]
    [Module (ResidueField Λ) V]
    (Q : ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'], (A' →ₐ[Λ] R) → Prop) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (p : A →ₐ[Λ] R), Function.Surjective p →
    maximalIdeal A * RingHom.ker p = ⊥ →
    ∀ (κ : Type) [Fintype κ] (ε : κ → A), RingHom.ker p = Ideal.span (Set.range ε) →
      (∀ c : κ → Λ, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal Λ) →
      ∃ o : κ → V, ∀ c : κ → Λ, ∑ u, residue Λ (c u) • o u = 0 →
        ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p' : A →ₐ[Λ] A') (p'' : A' →ₐ[Λ] R) (η : A'),
          Function.Surjective p' → p''.comp p' = p → (∀ x ∈ maximalIdeal A', x * η = 0) → p'' η = 0 →
          (∀ u, p' (ε u) = c u • η) → Q A' p''

def HasPres (Λ R : Type) [CommRing Λ] [CommRing R] [Algebra Λ R] (a b : ℕ) : Prop :=
  ∃ (π : MvPowerSeries (Fin a) Λ →ₐ[Λ] R) (f : Fin b → MvPowerSeries (Fin a) Λ), Function.Surjective π ∧
    RingHom.ker π = Ideal.span (Set.range f)

def MuGen {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (H : Subgroup Γ) (M : Set Γ) (ζ : Γ) : Prop :=
  ζ ∈ M ∧ ∀ s ∈ M, ∃ n : ℕ, s * (ζ ^ n)⁻¹ ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure

end UpperTheory.V.Ws

end
