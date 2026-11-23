import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAndResidualTrivComplexConj

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CocycleKernel

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {rho : Representation R Γ M} (x : Z1 rho) {L : Subgroup Γ}

theorem cocycle_one : x.1 1 = 0 := by
  have h := x.2.2 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem cocycle_conj (hL : ∀ g ∈ L, ∀ m, rho g m = m) (k : Γ) {g : Γ} (hg : g ∈ L) :
    x.1 (k * g * k⁻¹) = rho k (x.1 g) := by
  have h := x.2.2 k k⁻¹
  rw [mul_inv_cancel, cocycle_one] at h
  rw [x.2.2, x.2.2, map_mul, Module.End.mul_apply, hL g hg, add_right_comm, ← h, zero_add]

def zeros (L : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ L ∧ x.1 g = 0}
  one_mem' := ⟨L.one_mem, cocycle_one x⟩
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by rw [x.2.2, ha.2, hb.2, map_zero, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    have h := x.2.2 a⁻¹ a
    rwa [inv_mul_cancel, cocycle_one, ha.2, map_zero, add_zero, eq_comm] at h⟩

theorem zeros_normal (hN : L.Normal) (hL : ∀ g ∈ L, ∀ m, rho g m = m) : (zeros x L).Normal :=
  ⟨fun g hg k => ⟨hN.conj_mem g hg.1 k, by rw [cocycle_conj x hL k hg.1, hg.2, map_zero]⟩⟩

theorem isOpen_zeros [DiscreteTopology M] (hO : IsOpen (L : Set Γ)) : IsOpen (zeros x L : Set Γ) :=
  hO.inter ((isOpen_discrete ({0} : Set M)).preimage x.2.1)

theorem cocycle_eq (hL : ∀ g ∈ L, ∀ m, rho g m = m) {h σ g : Γ} (hh : h ∈ L)
    (hu : g * σ * g⁻¹ * h⁻¹ ∈ zeros x L) : x.1 σ = rho g⁻¹ (x.1 h) := by
  have e : σ = g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ := by group
  rw [e, cocycle_conj x hL _ (L.mul_mem hu.1 hh), x.2.2, hu.2, hL _ hu.1, zero_add]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem dot_repOn {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ)
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (k : GE N) (a b : Fin D.R.r → A) :
    repOn (Tgl i s) κ A k a ⬝ᵥ repOn ρ κ⁻¹ A k b =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) * a ⬝ᵥ b := by
  have e : (Tmat i s k).transpose * Tdual i s k = ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ (X.O0 i)) := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, ← Tgl_coe, ← Matrix.coe_units_inv, Units.inv_mul,
      Matrix.transpose_one]
  have e2 : ((Tmat i s k).map (algebraMap (X.O0 i) A)).transpose * (Tdual i s k).map (algebraMap (X.O0 i) A) =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ A) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, e]
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  change ((κ k : A) • ((Tgl i s k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec a) ⬝ᵥ
    ((((κ k)⁻¹ : Aˣ) : A) • ((ρ k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec b) = _
  rw [hρ k, Tgl_coe, smul_dotProduct, dotProduct_smul, smul_smul, Units.mul_inv, one_smul, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]

theorem exists_open_normal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  intro D N X i s hl M L z hM hS A _ _ _ _ κ ρ hK hρ hκ x y h hh hb
  have h1 : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ ρ hK hρ A g hg).1, hκ g hg, Units.val_one, one_smul]
  have h2 : ∀ g ∈ L, ∀ m, repOn ρ κ⁻¹ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ⁻¹ ρ hK hρ A g hg).2.1, MonoidHom.inv_apply, hκ g hg, inv_one,
      Units.val_one, one_smul]
  obtain ⟨⟨hO, hN, hc, -⟩, -⟩ := hS
  have hc' : ∀ g ∈ L, cConj X g ∈ L := fun g hg => (hc g _ (cConj_apply X g)).1 hg
  haveI := zeros_normal x hN h1
  haveI := zeros_normal y hN h2
  refine ⟨(zeros x L ⊓ (zeros x L).comap (cConj X)) ⊓ (zeros y L ⊓ (zeros y L).comap (cConj X)),
    ((isOpen_zeros x hO).inter (isOpen_comap_cConj X (isOpen_zeros x hO))).inter
      ((isOpen_zeros y hO).inter (isOpen_comap_cConj X (isOpen_zeros y hO))), inferInstance,
    fun g hg => hg.1.1.1, fun g hg a b c d => ⟨⟨⟨hg, a⟩, hc' g hg, b⟩, ⟨hg, c⟩, hc' g hg, d⟩, ?_⟩
  rintro σ g ⟨⟨a, b⟩, c, d⟩ h0
  have e : cConj X (g * σ * g⁻¹ * h⁻¹) = cConj X g * cConj X σ * (cConj X g)⁻¹ * (cConj X h)⁻¹ := by
    simp only [map_mul, map_inv]
  have b' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros x L := b
  have d' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros y L := d
  rw [e] at b' d'
  rw [bform, cocycle_eq x h1 hh a, cocycle_eq y h2 hh c, cocycle_eq x h1 (hc' h hh) b', cocycle_eq y h2 (hc' h hh) d',
    dot_repOn i s κ hρ, dot_repOn i s κ hρ, ← map_inv (cConj X), GlobalTheory.ResConjTriv.auxiliaryCharacter_complexConj_invariant, ← mul_sub] at h0
  exact hb (((Units.isUnit _).map (algebraMap (X.O0 i) A)).mul_right_eq_zero.1 h0)

end GlobalTheory.CocycleKernel
