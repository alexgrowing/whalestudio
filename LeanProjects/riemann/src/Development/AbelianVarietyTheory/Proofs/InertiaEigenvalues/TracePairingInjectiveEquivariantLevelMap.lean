import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.TraceLevel

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]
  {A A' : GRep ↥(GK K) ℚ_[l] LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
  {m : A.V →ₗ[LL] A'.V →ₗ[LL] LL} {lam : LL →ₗ[ℚ_[l]] ℚ_[l]}
  (h2 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, m x y = algebraMap O LL a)
  (hlam : ∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔
      ∃ b : O, algebraMap O LL b = a)

include h2 hlam in

theorem norm_le_one (x : ↥LA.T) (y : ↥LA'.T) : ‖lam (m x y)‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := (h2 y).1 y.2 x x.2
  obtain ⟨u, hu⟩ := (hlam (m x y)).2 ⟨a, ha.symm⟩ 1
  rw [map_one, mul_one] at hu
  rw [hu]
  exact u.norm_le_one

def uv (x : ↥LA.T) (y : ↥LA'.T) : ℤ_[l] :=
  ⟨lam (m x y), norm_le_one h2 hlam x y⟩

theorem coe_uv (x : ↥LA.T) (y : ↥LA'.T) :
    ((uv h2 hlam x y : ℤ_[l]) : ℚ_[l]) = lam (m x y) := rfl

theorem lam_natPow_mul (z : LL) (r : ℕ) :
    lam ((l : LL) ^ r * z) = (l : ℚ_[l]) ^ r * lam z := by
  have : (l : LL) ^ r * z = ((l : ℚ_[l]) ^ r) • z := by
    rw [Algebra.smul_def]; simp
  rw [this, map_smul, smul_eq_mul]

theorem uv_add_left (x x' : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam (x + x') y = uv h2 hlam x y + uv h2 hlam x' y := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_add_right (x : ↥LA.T) (y y' : ↥LA'.T) :
    uv h2 hlam x (y + y') = uv h2 hlam x y + uv h2 hlam x y' := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_zero_left (y : ↥LA'.T) : uv h2 hlam 0 y = 0 := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_zero_right (x : ↥LA.T) : uv h2 hlam x 0 = 0 := by
  apply Subtype.ext; simp [coe_uv]

theorem uv_smul_left (r : ℕ) (x : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam ((((l : ℕ) : O) ^ r) • x) y = (l : ℤ_[l]) ^ r * uv h2 hlam x y := by
  apply Subtype.ext
  rw [coe_uv, PadicInt.coe_mul, coe_uv]
  have : (((((l : ℕ) : O) ^ r) • x : ↥LA.T) : A.V) = ((l : LL) ^ r) • (x : A.V) := by
    rw [Submodule.coe_smul, ← algebraMap_smul LL]; simp
  rw [this, map_smul, LinearMap.smul_apply, smul_eq_mul, lam_natPow_mul]
  simp

theorem uv_smul_right (r : ℕ) (x : ↥LA.T) (y : ↥LA'.T) :
    uv h2 hlam x ((((l : ℕ) : O) ^ r) • y) = (l : ℤ_[l]) ^ r * uv h2 hlam x y := by
  apply Subtype.ext
  rw [coe_uv, PadicInt.coe_mul, coe_uv]
  have : (((((l : ℕ) : O) ^ r) • y : ↥LA'.T) : A'.V) = ((l : LL) ^ r) • (y : A'.V) := by
    rw [Submodule.coe_smul, ← algebraMap_smul LL]; simp
  rw [this, map_smul, smul_eq_mul, lam_natPow_mul]
  simp

theorem toZModPow_natPow_mul (r : ℕ) (u : ℤ_[l]) :
    PadicInt.toZModPow r ((l : ℤ_[l]) ^ r * u) = 0 := by
  rw [map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

abbrev lr (r : ℕ) {V : Type} [AddCommGroup V] [Module O V] (T : Submodule O V) : Submodule O ↥T :=
  Ideal.span {((l : ℕ) : O) ^ r} • ⊤

theorem mem_lr {r : ℕ} {V : Type} [AddCommGroup V] [Module O V] {T : Submodule O V} {x : ↥T}
    (hx : x ∈ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥T)) :
    ∃ x' : ↥T, (((l : ℕ) : O) ^ r) • x' = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨x', -, hx'⟩ := hx
  exact ⟨x', hx'⟩

def pr (r : ℕ) (y : ↥LA'.T) : ↥LA.T →+ ZMod (l ^ r) where
  toFun x := PadicInt.toZModPow r (uv h2 hlam x y)
  map_zero' := by rw [uv_zero_left, map_zero]
  map_add' a b := by rw [uv_add_left, map_add]

def psi0 (r : ℕ) (y : ↥LA'.T) :
    (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) →+ ZMod (l ^ r) :=
  ((((Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)).restrictScalars ℤ).liftQ
      (pr h2 hlam r y).toIntLinearMap (by
        intro x hx
        obtain ⟨x', rfl⟩ := mem_lr ((Submodule.restrictScalars_mem ℤ _ _).1 hx)
        rw [LinearMap.mem_ker]
        show PadicInt.toZModPow r (uv h2 hlam _ y) = 0
        rw [uv_smul_left, toZModPow_natPow_mul])).toAddMonoidHom.comp
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)).symm.toLinearMap.toAddMonoidHom

theorem tracePairingLevelMap_mk (r : ℕ) (y : ↥LA'.T) (x : ↥LA.T) :
    psi0 h2 hlam r y (Submodule.Quotient.mk x) = PadicInt.toZModPow r (uv h2 hlam x y) := by
  simp [psi0, pr]

variable {r : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M]
  (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M)

def psi1 (y : ↥LA'.T) : TDual (ZMod (l ^ r)) M :=
  TDual.mk (((psi0 h2 hlam r y).comp e.symm.toAddMonoidHom).toZModLinearMap (l ^ r))

theorem tracePairingLevelDual_apply (y : ↥LA'.T) (x : ↥LA.T) :
    psi1 h2 hlam e y (e (Submodule.Quotient.mk x)) = PadicInt.toZModPow r (uv h2 hlam x y) := by
  simp [psi1, tracePairingLevelMap_mk]

theorem tracePairingLevelDual_ext {φ φ' : TDual (ZMod (l ^ r)) M}
    (h : ∀ x : ↥LA.T, φ (e (Submodule.Quotient.mk x)) = φ' (e (Submodule.Quotient.mk x))) :
    φ = φ' := by
  apply TDual.ext
  intro z
  obtain ⟨q, rfl⟩ := e.surjective z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact h x

theorem tracePairingLevelDual_zero : psi1 h2 hlam e 0 = 0 :=
  tracePairingLevelDual_ext e fun x => by
    rw [tracePairingLevelDual_apply h2 hlam e, uv_zero_right, map_zero]; exact (LinearMap.zero_apply _).symm

theorem tracePairingLevelDual_add (y y' : ↥LA'.T) :
    psi1 h2 hlam e (y + y') = psi1 h2 hlam e y + psi1 h2 hlam e y' :=
  tracePairingLevelDual_ext e fun x => by
    rw [TDual.add_apply, tracePairingLevelDual_apply h2 hlam e, tracePairingLevelDual_apply h2 hlam e, tracePairingLevelDual_apply h2 hlam e,
      uv_add_right, map_add]

def psi1Hom : ↥LA'.T →+ TDual (ZMod (l ^ r)) M where
  toFun := psi1 h2 hlam e
  map_zero' := tracePairingLevelDual_zero h2 hlam e
  map_add' := tracePairingLevelDual_add h2 hlam e

def psiQ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+
    TDual (ZMod (l ^ r)) M :=
  ((((Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)).restrictScalars ℤ).liftQ
      (psi1Hom h2 hlam e).toIntLinearMap (by
        intro y hy
        obtain ⟨y', rfl⟩ := mem_lr ((Submodule.restrictScalars_mem ℤ _ _).1 hy)
        rw [LinearMap.mem_ker]
        show psi1 h2 hlam e _ = 0
        refine tracePairingLevelDual_ext e fun x => ?_
        rw [tracePairingLevelDual_apply h2 hlam e, uv_smul_right, toZModPow_natPow_mul]; exact (LinearMap.zero_apply _).symm)).toAddMonoidHom.comp
    (Submodule.Quotient.restrictScalarsEquiv ℤ
      (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)).symm.toLinearMap.toAddMonoidHom

theorem psiQ_mk (y : ↥LA'.T) (x : ↥LA.T) :
    psiQ h2 hlam e (Submodule.Quotient.mk y) (e (Submodule.Quotient.mk x)) =
      PadicInt.toZModPow r (uv h2 hlam x y) := by
  rw [← tracePairingLevelDual_apply h2 hlam e y x]
  rfl

include e in
theorem psiQ_injective : Function.Injective (psiQ h2 hlam e) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl : (l : LL) ≠ 0 := by
    intro h
    apply hl0
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    exact (map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective).1 h'
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨y, hyq⟩ := Submodule.Quotient.mk_surjective
    (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) q
  subst hyq
  have hx : ∀ x : ↥LA.T, ∃ c : ℤ_[l], (l : ℤ_[l]) ^ r * c = uv h2 hlam x y := by
    intro x
    have h0 : PadicInt.toZModPow r (uv h2 hlam x y) = 0 := by
      rw [← psiQ_mk h2 hlam e y x, hq]
      exact LinearMap.zero_apply _
    have h1 : uv h2 hlam x y ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := h0
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  obtain ⟨z, hz⟩ : ∃ z : A'.V, z = ((l : LL) ^ r)⁻¹ • (y : A'.V) := ⟨_, rfl⟩
  have hzT : z ∈ LA'.T := by
    rw [h2]
    intro x hxT
    suffices hs : ∀ b : O, ∃ u : ℤ_[l], lam (m x z * algebraMap O LL b) = (u : ℚ_[l]) by
      obtain ⟨a, ha⟩ := (hlam (m x z)).1 hs
      exact ⟨a, ha.symm⟩
    intro b
    obtain ⟨c', hc'⟩ := hx (b • ⟨x, hxT⟩)
    refine ⟨c', ?_⟩
    have hb : ((b • (⟨x, hxT⟩ : ↥LA.T) : ↥LA.T) : A.V) = algebraMap O LL b • x := by
      rw [Submodule.coe_smul, algebraMap_smul]
    have e1 : m x z * algebraMap O LL b =
        ((l : LL) ^ r)⁻¹ * m ((b • (⟨x, hxT⟩ : ↥LA.T) : ↥LA.T) : A.V) y := by
      rw [hb, hz]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have e2 : ((l : LL) ^ r)⁻¹ = algebraMap ℚ_[l] LL (((l : ℚ_[l]) ^ r)⁻¹) := by
      rw [map_inv₀, map_pow, map_natCast]
    rw [e1, e2, ← Algebra.smul_def, map_smul, smul_eq_mul, ← coe_uv h2 hlam, ← hc',
      PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hl0), one_mul]
  have hy : (((l : ℕ) : O) ^ r) • (⟨z, hzT⟩ : ↥LA'.T) = y := by
    apply Subtype.ext
    rw [Submodule.coe_smul, ← algebraMap_smul LL, map_pow, map_natCast]
    show ((l : LL) ^ r) • z = (y : A'.V)
    rw [hz, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
  rw [Submodule.Quotient.mk_eq_zero, ← hy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

omit [TopologicalSpace LL] in
theorem rho_inv {G V : Type} [Group G] [AddCommGroup V] [Module LL V] (ρ : Representation LL G V)
    (h : G) (v : V) : ρ h (ρ h⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem uv_act (c : ↥(GK K) → LL)
    (h1 : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = c g * m x y)
    (hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l], c g = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)))
    (g : Formalism.GaloisCohomology.GK l K.1) (x : ↥LA.T) (y : ↥LA'.T) :
    PadicInt.toZModPow r
        (uv h2 hlam x (actT LA' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y)) =
      ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
        PadicInt.toZModPow r
          (uv h2 hlam (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x) y) := by
  obtain ⟨w, hw1, hw2⟩ := hc ((IntermediateField.fixingSubgroupEquiv K.1).symm g)
  rw [MulEquiv.apply_symm_apply] at hw2
  rw [← hw2, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [PadicInt.coe_mul, coe_uv, coe_uv]
  generalize (IntermediateField.fixingSubgroupEquiv K.1).symm g = h at hw1
  show lam (m (x : A.V) (A'.ρ h y)) = (w : ℚ_[l]) * lam (m (A.ρ h⁻¹ x) y)
  have key := h1 h (A.ρ h⁻¹ x) y
  rw [show A.ρ h (A.ρ h⁻¹ (x : A.V)) = x from rho_inv A.ρ h x] at key
  rw [key, hw1, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [TopologicalSpace LL] in
theorem actQ_mk' {G V : Type} [Group G] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (h : G) (x : ↥L.T) :
    actQ L I hI h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (actT L h x) := rfl

include e in
theorem psiQ_equivariant (c : ↥(GK K) → LL)
    (h1 : ∀ g x y, m (A.ρ g x) (A'.ρ g y) = c g * m x y)
    (hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l], c g = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)))
    (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T))
    (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T))
    (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M)
    (hrho : ∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x))
    (g : Formalism.GaloisCohomology.GK l K.1) (q : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) :
    psiQ h2 hlam e (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) q) =
      ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (psiQ h2 hlam e q) := by
  induction q using Submodule.Quotient.induction_on with
  | H y =>
  apply tracePairingLevelDual_ext e
  intro x
  have key : psiQ h2 hlam e (Submodule.Quotient.mk
        (actT LA' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y))
        (e (Submodule.Quotient.mk x)) =
      ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
        psiQ h2 hlam e (Submodule.Quotient.mk y) (e (Submodule.Quotient.mk
          (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x))) := by
    rw [psiQ_mk h2 hlam e, psiQ_mk h2 hlam e]
    exact uv_act h2 hlam c h1 hc g x y
  have hinv : (IntermediateField.fixingSubgroupEquiv K.1).symm g⁻¹ =
      ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ := map_inv _ g
  have hr : rho g⁻¹ (e (Submodule.Quotient.mk x)) = e (Submodule.Quotient.mk
      (actT LA ((IntermediateField.fixingSubgroupEquiv K.1).symm g)⁻¹ x)) := by
    have h0 := hrho g⁻¹ (Submodule.Quotient.mk x)
    rw [hinv] at h0
    exact h0.trans (congrArg e (actQ_mk' LA _ hI _ x))
  have hA' := actQ_mk' LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y
  have s1 := congrArg (fun q => psiQ h2 hlam e q (e (Submodule.Quotient.mk x))) hA'
  have s2 := congrArg (fun t => ((Formalism.GaloisCohomology.cycK l K.1 r g : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) *
    psiQ h2 hlam e (Submodule.Quotient.mk y) t) hr
  have s3 := ReciprocityTheory.Gal.twDual_apply (Formalism.GaloisCohomology.cycK l K.1 r) rho g
    (psiQ h2 hlam e (Submodule.Quotient.mk y)) (e (Submodule.Quotient.mk x))
  beta_reduce at s1 s2
  exact s1.trans (key.trans (s2.symm.trans s3.symm))

end GlobalTheory.TraceLevel

namespace GlobalTheory

open TraceLevel in

theorem tracePairing_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  intro l _ P K LL _ _ _ O _ _ A A' LA LA' m hm lam hlam r hI hI' hchi M _ _ e rho hrho
  have hc : ∀ g : ↥(GK K), ∃ w : ℤ_[l],
      ((Formalism.MainNotions.N.cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap ℚ_[l] LL (w : ℚ_[l]) ∧
      (PadicInt.toZModPow r w : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) :
          ZMod (l ^ r)) := by
    intro g
    obtain ⟨w, hw1, hw2⟩ := hchi g
    exact ⟨w, by rw [← hw1]; rfl, hw2⟩
  exact ⟨psiQ hm.2 hlam e, psiQ_injective hm.2 hlam e,
    psiQ_equivariant hm.2 hlam e (fun h => ((Formalism.MainNotions.N.cycLL (P.PD K) LL h : LLˣ) : LL)) hm.1.1 hc
      hI hI' rho hrho⟩

end GlobalTheory
