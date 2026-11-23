import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.CycTateNegOneOrbitEquivSymmMk

namespace GroundTheory.Global

open GroundTheory.GroupCoh

noncomputable section

section KerModRangeProd

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def kerModRangeProdEquiv (F G : A × B →+ A × B) (fA gA : A →+ A) (fB gB : B →+ B)
    (hF : ∀ x, F x = (fA x.1, fB x.2)) (hG : ∀ x, G x = (gA x.1, gB x.2)) :
    KerModRange F G ≃+ KerModRange fA gA × KerModRange fB gB :=
  kerModRangeEquivOfSurjective
    (AddMonoidHom.prod
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.fst A B).comp F.ker.subtype).codRestrict fA.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.fst ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2)))))
      ((QuotientAddGroup.mk' _).comp
        (((AddMonoidHom.snd A B).comp F.ker.subtype).codRestrict fB.ker fun x ↦
          AddMonoidHom.mem_ker.2 (congrArg Prod.snd ((hF x).symm.trans (AddMonoidHom.mem_ker.1 x.2))))))
    (by
      rintro ⟨y₁, y₂⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y₁
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y₂
      refine ⟨⟨((a : A), (b : B)), AddMonoidHom.mem_ker.2 ?_⟩, rfl⟩
      rw [hF, AddMonoidHom.mem_ker.1 a.2, AddMonoidHom.mem_ker.1 b.2, Prod.mk_zero_zero])
    (by
      intro x
      constructor
      · intro h
        have h1 : (x : A × B).1 ∈ gA.range :=
          (KerModRange.mk_eq_zero_iff (g := gA) _).1 (congrArg Prod.fst h)
        have h2 : (x : A × B).2 ∈ gB.range :=
          (KerModRange.mk_eq_zero_iff (g := gB) _).1 (congrArg Prod.snd h)
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.1 h1
        obtain ⟨b, hb⟩ := AddMonoidHom.mem_range.1 h2
        exact AddMonoidHom.mem_range.2 ⟨(a, b), by rw [hG, ha, hb]⟩
      · intro h
        obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.1 h
        rw [hG] at hy
        exact Prod.ext
          ((KerModRange.mk_eq_zero_iff (g := gA) _).2
            (AddMonoidHom.mem_range.2 ⟨y.1, congrArg Prod.fst hy⟩))
          ((KerModRange.mk_eq_zero_iff (g := gB) _).2
            (AddMonoidHom.mem_range.2 ⟨y.2, congrArg Prod.snd hy⟩)))

end KerModRangeProd

section Prod

variable {k G V W : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

theorem cycSubOne_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G)
    (x : V × W) : cycSubOne (ρ.prod ρ') σ x = (cycSubOne ρ σ x.1, cycSubOne ρ' σ x.2) := by
  rw [cycSubOne_apply, cycSubOne_apply, cycSubOne_apply]
  rfl

variable [Fintype G]

theorem cycNorm_prod_apply (ρ : Representation k G V) (ρ' : Representation k G W)
    (x : V × W) : cycNorm (ρ.prod ρ') x = (cycNorm ρ x.1, cycNorm ρ' x.2) := by
  rw [cycNorm_apply, cycNorm_apply, cycNorm_apply]
  exact Prod.ext (by rw [Prod.fst_sum]; rfl) (by rw [Prod.snd_sum]; rfl)

def cycTateZeroProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateZero (ρ.prod ρ') σ ≃+ CycTateZero ρ σ × CycTateZero ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycSubOne_prod_apply ρ ρ' σ) (cycNorm_prod_apply ρ ρ')

def cycTateNegOneProdEquiv (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    CycTateNegOne (ρ.prod ρ') σ ≃+ CycTateNegOne ρ σ × CycTateNegOne ρ' σ :=
  kerModRangeProdEquiv _ _ _ _ _ _ (cycNorm_prod_apply ρ ρ') (cycSubOne_prod_apply ρ ρ' σ)

theorem cycHerbrand_prod_eq_mul (ρ : Representation k G V) (ρ' : Representation k G W) (σ : G) :
    cycHerbrand (ρ.prod ρ') σ = cycHerbrand ρ σ * cycHerbrand ρ' σ := by
  simp only [cycHerbrand_eq]
  rw [Nat.card_congr (cycTateZeroProdEquiv ρ ρ' σ).toEquiv,
    Nat.card_congr (cycTateNegOneProdEquiv ρ ρ' σ).toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm]

end Prod

section Mul

variable {G : Type*} [Group G]

def additiveProdEquiv (M N : Type*) [CommGroup M] [CommGroup N] :
    Additive (M × N) ≃+ Additive M × Additive N where
  toFun x := (Additive.ofMul x.toMul.1, Additive.ofMul x.toMul.2)
  invFun y := Additive.ofMul (y.1.toMul, y.2.toMul)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

def additivePiEquiv {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] :
    Additive (∀ i, M i) ≃+ ∀ i, Additive (M i) where
  toFun x i := Additive.ofMul (x.toMul i)
  invFun y := Additive.ofMul fun i ↦ (y i).toMul
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

section Prod

variable (M N : Type*) [CommGroup M] [CommGroup N] [MulDistribMulAction G M]
  [MulDistribMulAction G N] [Fintype G]

def cycTateZeroMulProdEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (M × N)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction G M) σ ×
        CycTateZero (Representation.ofMulDistribMulAction G N) σ :=
  (cycTateZeroCongr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroProdEquiv _ _ σ)

def cycTateNegOneMulProdEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (M × N)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction G M) σ ×
        CycTateNegOne (Representation.ofMulDistribMulAction G N) σ :=
  (cycTateNegOneCongr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneProdEquiv _ _ σ)

theorem cycHerbrand_mulProd (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (M × N)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction G M) σ *
        cycHerbrand (Representation.ofMulDistribMulAction G N) σ := by
  rw [cycHerbrand_congr (ρ' := (Representation.ofMulDistribMulAction G M).prod
      (Representation.ofMulDistribMulAction G N)) (additiveProdEquiv M N) (fun _ _ ↦ rfl) σ,
    cycHerbrand_prod_eq_mul]

end Prod

section Pi

variable {ι : Type*} (M : ι → Type*) [∀ i, CommGroup (M i)] [∀ i, MulDistribMulAction G (M i)]
  [Fintype G]

def cycTateZeroMulPiEquiv (σ : G) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateZero (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateZeroCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateZeroPiEquiv _ σ)

def cycTateNegOneMulPiEquiv (σ : G) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ i, M i)) σ ≃+
      ∀ i, CycTateNegOne (Representation.ofMulDistribMulAction G (M i)) σ :=
  (cycTateNegOneCongr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ).trans (cycTateNegOnePiEquiv _ σ)

theorem cycHerbrand_mulPi [Fintype ι] (σ : G) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ i, M i)) σ =
      ∏ i, cycHerbrand (Representation.ofMulDistribMulAction G (M i)) σ := by
  rw [cycHerbrand_congr (ρ' := piRep fun i ↦ Representation.ofMulDistribMulAction G (M i))
      (additivePiEquiv M) (fun _ _ ↦ rfl) σ, cycHerbrand_pi]

end Pi

section Orbit

variable {X : Type*} {U : X → Type*} [∀ x, CommGroup (U x)] [MulDistribMulAction G (∀ x, U x)]

variable (G U) in

def mulPiRep : Representation ℤ G (∀ x, Additive (U x)) where
  toFun g := AddMonoidHom.toIntLinearMap ((additivePiEquiv U).toAddMonoidHom.comp
    ((Representation.ofMulDistribMulAction G (∀ x, U x) g).toAddMonoidHom.comp
      (additivePiEquiv U).symm.toAddMonoidHom))
  map_one' := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (one_smul G fun x ↦ (y x).toMul)
  map_mul' g h := LinearMap.ext fun y ↦ funext fun x ↦
    congrArg (fun f : ∀ x, U x ↦ Additive.ofMul (f x)) (mul_smul g h fun x ↦ (y x).toMul)

variable [MulAction G X]

theorem permutesFactors_mulPiRep
    (h : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) :
    PermutesFactors (mulPiRep G U) := fun g f x hf ↦
  congrArg Additive.ofMul (h g (fun x ↦ (f x).toMul) x hf)

variable [Fintype G] [MulAction.IsPretransitive G X]

def cycTateZeroMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateZero (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateZero (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateZeroCongr (ρ' := mulPiRep G U) (additivePiEquiv U) (fun _ _ ↦ rfl) σ).trans
    (cycTateZeroOrbitEquiv (mulPiRep G U) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

def cycTateNegOneMulOrbitEquiv
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    CycTateNegOne (Representation.ofMulDistribMulAction G (∀ x, U x)) σ ≃+
      CycTateNegOne (Representation.ofMulDistribMulAction D (U x₀)) τ :=
  (cycTateNegOneCongr (ρ' := mulPiRep G U) (additivePiEquiv U) (fun _ _ ↦ rfl) σ).trans
    (cycTateNegOneOrbitEquiv (mulPiRep G U) (permutesFactors_mulPiRep hU) x₀ D hD
      (Representation.ofMulDistribMulAction D (U x₀))
      (fun d f ↦ congrArg Additive.ofMul (hU₀ d fun x ↦ (f x).toMul)) σ hσ τ hτ)

theorem cycHerbrand_mulOrbit
    (hU : ∀ (g : G) (f : ∀ x, U x) (x : X), f x = 1 → (g • f) (g • x) = 1) (x₀ : X)
    (D : Subgroup G) [Fintype D] (hD : ∀ g, g ∈ D ↔ g • x₀ = x₀) [MulDistribMulAction D (U x₀)]
    (hU₀ : ∀ (d : D) (f : ∀ x, U x), ((d : G) • f) x₀ = d • f x₀) (σ : G)
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (τ : D) (hτ : ∀ d, d ∈ Subgroup.zpowers τ) :
    cycHerbrand (Representation.ofMulDistribMulAction G (∀ x, U x)) σ =
      cycHerbrand (Representation.ofMulDistribMulAction D (U x₀)) τ := by
  rw [cycHerbrand_eq, cycHerbrand_eq,
    Nat.card_congr (cycTateZeroMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv,
    Nat.card_congr (cycTateNegOneMulOrbitEquiv hU x₀ D hD hU₀ σ hσ τ hτ).toEquiv]

end Orbit

end Mul

end

end GroundTheory.Global
