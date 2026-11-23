import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSimR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyLeBaseChange
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAway

theorem flat_centralizer (R B L : Type) [CommRing R] [Algebra ℚ R] [Ring B] [Algebra ℚ B] [Ring L] [Algebra ℚ L]
    (γ : B) (f : L →ₐ[ℚ] B) (hf : Function.Injective f)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R) f) ∧
      ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) = ((1 : R) ⊗ₜ[ℚ] γ) * y ↔
        y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id R R) f) := by
  let ad : B →ₗ[ℚ] B := LinearMap.mulRight ℚ γ - LinearMap.mulLeft ℚ γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id R R) f y = LinearMap.lTensor R f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) - ((1 : R) ⊗ₜ[ℚ] γ) * y = LinearMap.lTensor R ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact R hex
  refine ⟨?_, fun y => ?_⟩
  · have h := Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.toLinearMap hf
    intro a b hab
    rw [hmap, hmap] at hab
    exact h hab
  · rw [← sub_eq_zero, had, hex' y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hmap z⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (hmap z).symm⟩

variable {p : ℕ} [Fact p.Prime]

def incl (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    R ⊗[ℚ] algF P →ₐ[R] R ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id R R) ((algF P).val.restrictScalars ℚ)

theorem incl_tmul (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (a : R) (m : algF P) :
    incl R P (a ⊗ₜ m) = a ⊗ₜ (m : G.C) := rfl

theorem cent_iff {G : HTGroup p} (P : Pair G) (x : G.C) :
    x * P.γ = P.γ * x ↔ x ∈ Set.range ((algF P).val.restrictScalars ℚ) := by
  have h := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro hx
    have hm : x ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact hx.symm
    rw [h] at hm
    exact ⟨⟨x, hm⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    have hm : (m : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [h]; exact m.2
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ (Set.mem_singleton _)).symm

theorem incl_facts (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (incl R P) ∧ ∀ y : R ⊗[ℚ] G.C, y * inC G R P.γ = inC G R P.γ * y ↔ y ∈ Set.range (incl R P) :=
  flat_centralizer R G.C (algF P) (P.γ : G.C) _ Subtype.val_injective (cent_iff P)

theorem exists_retr (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    ∃ π : R ⊗[ℚ] algF P →ₗ[R] R, ∀ a, π (algebraMap R _ a) = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ (algF P))
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ (algF P)).injective)
  have h1 : φ 1 = 1 := by
    have := LinearMap.congr_fun hφ 1
    simpa using this
  refine ⟨(TensorProduct.AlgebraTensorModule.rid ℚ R R).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor R R φ, fun a => ?_⟩
  simp [Algebra.TensorProduct.algebraMap_apply, h1]

theorem alg_inj (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (algebraMap R (R ⊗[ℚ] algF P)) := by
  obtain ⟨π, hπ⟩ := exists_retr R P
  intro a b h
  rw [← hπ a, ← hπ b, h]

theorem incl_extC (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (z : R ⊗[ℚ] algF P) :
    incl R P (extC R c z) =
      inC G R P.β * (starT G.star R (incl R P z)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [incl_tmul, starT_tmul]
    simp only [extC, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, incl_tmul, hc, inC, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sh]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, MulOpposite.unop_add, mul_add, add_mul]

theorem incl_sim (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (y : R ⊗[ℚ] algF P) (s : R) (hy : y * extC R c y = algebraMap R _ s) :
    incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop = algebraMap R (R ⊗[ℚ] G.C) s * inC G R P.β := by
  have h1 := congrArg (incl R P) hy
  rw [map_mul, incl_extC R P c hc, AlgHom.commutes] at h1
  have hb : inC G R ((P.β⁻¹ : G.Cˣ) : G.C) * inC G R P.β = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  calc incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop
      = incl R P y * (inC G R P.β * (starT G.star R (incl R P y)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C)) *
          inC G R P.β := by
        simp only [mul_assoc, hb, mul_one]
    _ = _ := by rw [h1]

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

variable {p : ℕ} [Fact p.Prime]

section Generic

variable (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)

def nu (y : simR R (extC R c)) : Rˣ := (mem_simR.1 y.2).choose

theorem nu_spec (y : simR R (extC R c)) :
    ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ ((nu R P c y : Rˣ) : R) :=
  (mem_simR.1 y.2).choose_spec

theorem nu_eq (y : simR R (extC R c)) (s : Rˣ)
    (h : ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ (s : R)) : nu R P c y = s :=
  Units.ext (alg_inj R P (by rw [← nu_spec, h]))

def nuHom : simR R (extC R c) →* Rˣ where
  toFun := nu R P c
  map_one' := nu_eq R P c 1 1 (by simp [Algebra.TensorProduct.one_def])
  map_mul' y z := nu_eq R P c _ _ (by
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    rw [show ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) *
        (extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) =
        (((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) *
        (((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) by ring,
      nu_spec, nu_spec])

def conjHom (x : (R ⊗[ℚ] G.C)ˣ) : simR R (extC R c) →* (R ⊗[ℚ] G.C)ˣ :=
  (MulAut.conj x).toMonoidHom.comp
    ((Units.map (incl R P).toRingHom.toMonoidHom).comp (simR R (extC R c)).subtype)

def phi0 (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R P.β x t) : simR R (extC R c) →* UPts G.star R :=
  ((conjHom R P c x).prod (nuHom R P c)).codRestrict _ fun y =>
    conj_mul_star (starT G.star R) (inC G R P.β) x
      (Units.map (incl R P).toRingHom.toMonoidHom (y : (R ⊗[ℚ] algF P)ˣ)) t ((nu R P c y : Rˣ) : R) hx
      (incl_sim R P c hc _ _ (nu_spec R P c y))

end Generic

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

def phi {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    simR (AfP p) (extC (AfP p) c) →* twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self) :=
  (phi0 (AfP p) P c hc x t hx).codRestrict _ fun y => by
    have hYΓ : Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
        Units.map (inC G (AfP p)).toMonoidHom P.γ =
        Units.map (inC G (AfP p)).toMonoidHom P.γ * Units.map (incl (AfP p) P).toRingHom.toMonoidHom y :=
      Units.ext (((incl_facts (AfP p) P).2 _).2 ⟨_, rfl⟩)
    refine Subtype.ext (Prod.ext ?_ (mul_comm _ _))
    change x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹ *
        (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) =
      x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹ *
        (x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹)
    calc _ = x * (Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
          Units.map (inC G (AfP p)).toMonoidHom P.γ) * x⁻¹ := by group
      _ = _ := by rw [hYΓ]; group

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentAway
