import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.ResSel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

variable (X) in

def IsCj (g g' : GE N) : Prop := ∀ x, g' x = X.cc (g (X.cc.symm x))

def IsDual (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Prop :=
  ∀ g, (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = Tdual i s g

def ResTriv (g : GE N) : Prop :=
  (Tmat i s g).map (IsLocalRing.residue (X.O0 i)) = 1 ∧ IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1

def Small (L : Subgroup (GE N)) (z : GE N) : Prop :=
  IsOpen (L : Set (GE N)) ∧ L.Normal ∧ (∀ g g', IsCj X g g' → (g ∈ L ↔ g' ∈ L)) ∧ (∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ g ∈ L, ResTriv i s g

section Field

variable (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]

def IsRes : Prop := ∀ x ∈ IsLocalRing.maximalIdeal (X.O0 i), algebraMap (X.O0 i) K x = 0

def ResIso : Prop :=
  ∃ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A ∧
    ∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)

abbrev red (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) : Representation K (GE N) (Fin D.R.r → K) := repOn ρ (1 : GE N →* Kˣ) K

variable {i K}

abbrev cl {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) : H1 (red i K ρ) := Submodule.Quotient.mk x

def form {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) : K :=
  x.1 g ⬝ᵥ y.1 h - x.1 g' ⬝ᵥ y.1 h'

end Field

def SpanOdd : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ¬ ResIso i s K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ (n n' : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n' → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → LinearIndependent K (fun b => cl (y b)) → ∀ c : Fin n → Fin n' → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → c = 0

def SpanTwo : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    ∀ ρ, IsDual i s ρ → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L, Small i s L z →
    ∀ A : Matrix (Fin D.R.r) (Fin D.R.r) K, IsUnit A →
      (∀ g g', IsCj X g g' → (Tdual i s g').map (algebraMap (X.O0 i) K) * A = A * (Tmat i s g).map (algebraMap (X.O0 i) K)) →
    ∀ (n : ℕ) (x : Fin n → Z1 (red i K (Tgl i s))) (y : Fin n → Z1 (red i K ρ)),
      LinearIndependent K (fun a => cl (x a)) → (∀ a g g', IsCj X g g' → (y a).1 g' = A.mulVec ((x a).1 g)) →
      ∀ c : Fin n → Fin n → K,
      (∀ h ∈ L, ∀ h', IsCj X h h' → ∑ a, ∑ b, c a b * form (x a) (y b) h h h' h' = 0) → ∀ a b, c a b = c b a

def EqDim : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    Module.Finite K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) ∧ Module.Finite K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅) ∧
      Module.finrank K (selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) = Module.finrank K (selOn bkP i ρ (1 : GE N →* Kˣ) K ∅)

def Position (M : ℕ) {R : ℕ} (P : Fin R ⊕ Fin R → PlE D.host)
    (d : Fin R ⊕ Fin R → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (φ φ' : Fin R → GE N) : Prop :=
  SlopeTestRemainingChoices X i M ∅ P d ∧ (∃ z L, IsTameInertiaElementAtTwistPrime X i z ∧ Small i s L z ∧ Steps X i M L z P d) ∧
    ∀ a, (∀ g ∈ DecV N (P (.inr a)), ResTriv i s g) ∧ IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧
      IsCj X (φ a) (φ' a)

def FirstHalf : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ', 1 ≤ M → Position i s M P d φ φ' →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ a v, Over (P (.inl a)) v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

def FirstPlace : Prop :=
  ∀ (P : PlE D.host) (z : GE N) (L : Subgroup (GE N)), IsTameInertiaElementAtTwistPrime X i z → Small i s L z →
    (∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1) →
    (∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) →
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] [IsLocalHom (algebraMap (X.O0 i) Λ)] (κ : GE N →* Λˣ),
    IsOpen (κ.ker : Set (GE N)) → (∀ g, ∃ n : ℕ, κ g ^ (X.l i ^ n) = 1) →
    ∀ (B : Type) [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B], Tors Λ B →
    ∀ ρ, (ρ = Tgl i s ∨ IsDual i s ρ) → ∀ v, Over P v →
      H0 ((repOn ρ κ B).comp (DecV N v).subtype) = ⊥ ∧ Subsingleton (H1 ((repOn ρ κ B).comp (DecV N v).subtype)) ∧
        Subsingleton (H2 ((repOn ρ κ B).comp (DecV N v).subtype))

theorem mod_l_eq_one {M n : ℕ} (hM : 1 ≤ M) (hn : n % (2 * X.l i ^ M) = 1) : n % X.l i = 1 := by
  have hd : X.l i ∣ 2 * X.l i ^ M := Dvd.dvd.mul_left (dvd_pow_self _ (by omega)) 2
  rw [← Nat.mod_mod_of_dvd _ hd, hn, Nat.mod_eq_of_lt (Fact.out : (X.l i).Prime).one_lt]

theorem FirstPlace.firstHalf (h : FirstPlace i s) : FirstHalf i s := by
  intro M R P d φ φ' hM hP Λ _ _ _ _ κ hκ hκ' B _ _ _ _ hB ρ hρ a v hv
  obtain ⟨hA, ⟨z, L, hz, hL, hS⟩, -⟩ := hP
  refine h (P (.inl a)) z L hz hL (fun w hw => ?_) (hS.1 a) Λ κ hκ hκ' B hB ρ hρ v hv
  obtain ⟨-, -, -, h0, -, hn⟩ := hA.1 _ w hw
  exact ⟨h0, mod_l_eq_one i hM hn⟩

def Recip : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ →
    ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 1 ≤ M → Position i s M P d φ φ' → IsQ P Q →
    ∀ γ γ' : Fin R → GE N, (∀ a, γ a ∈ Ine (F := D.host.E) (N.plOm.1 (P (.inr a))) ∧
      d (.inr a) (γ a) = Multiplicative.ofAdd 1 ∧ IsCj X (γ a) (γ' a)) →
    ∃ c : Fin R → Kˣ, ∀ (x : Z1 (red i K (Tgl i s))) (y : Z1 (red i K ρ)),
      cl x ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K Q → cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
      ∑ a, (c a : K) * form x y (γ a) (φ a) (γ' a) (φ' a) = 0

variable (X) in

def StepAB : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ H S d, AdmFam X i M H S d → ∀ z, IsTameInertiaElementAtTwistPrime X i z →
    ∀ U : Subgroup (GE N), IsOpen (U : Set (GE N)) → U.Normal → ∀ (A : Finset (PlE D.host)) (R : ℕ) (h : Fin R → GE N),
    (∀ a, h a ∈ H ∧ ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → h a ζ = ζ) →
    ∃ P : Fin R ⊕ Fin R → PlE D.host, SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧ Steps X i M U z P (fun q => d (P q)) ∧
      (∀ q v, Over (P q) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧
      ∀ a, ∃ σ g : GE N, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ ∧ g * σ * g⁻¹ * (h a)⁻¹ ∈ U

def Corank {R : ℕ} (φ φ' : Fin R → GE N) (e : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K →
    Function.Surjective (algebraMap (X.O0 i) K) → ∀ ρ, IsDual i s ρ → ∃ c : Fin R → K,
    ∀ x : Fin (e + 1) → Z1 (red i K (Tgl i s)), (∀ a, cl (x a) ∈ selOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K ∅) →
      (∀ a (y : Z1 (red i K ρ)), cl y ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K ∅ →
        ∑ b, c b * form (x a) y (φ b) (φ b) (φ' b) (φ' b) = 0) → ¬ LinearIndependent K (fun a => cl (x a))

def ResBound : Prop :=
  ∀ (M R : ℕ) (P : Fin R ⊕ Fin R → PlE D.host) d φ φ' (Q : Finset (PlE D.host)), 4 * D.R.r * R + 2 < X.l i ^ M →
    Position i s M P d φ φ' → IsQ P Q →
    ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin R))), Computes bkP i s M d Q Φ →
      (Corank bkP i s φ φ' 0 → ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.det →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m)) ∧
      (Corank bkP i s φ φ' 1 → a = 0 ∨ ∃ b c, ∀ F, toLam X i M (Fin R ⊕ Fin R) F = Φ.adjugate b c →
        ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ 4 * D.R.r * R ∧ IsUnit (F.coeff m))

def ChooseH : Prop :=
  ∀ T : Set (X.Sig i), (∀ s ∈ T, GalHyp bkP i s) → ∃ R : ℕ, ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ L : Subgroup (GE N), IsOpen (L : Set (GE N)) → L.Normal → (∀ s ∈ T, Small i s L z) →
    ∃ (h : Fin R → GE N) (U : Subgroup (GE N)), (∀ a, h a ∈ L) ∧ IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧
      ∀ φ φ' : Fin R → GE N, (∀ a, IsCj X (φ a) (φ' a) ∧ ∃ g, g * φ a * g⁻¹ * (h a)⁻¹ ∈ U) →
        ∀ s ∈ T, Corank bkP i s φ φ' (if nu X i = 0 then 0 else 1)

theorem IsCj.unique {g g' g'' : GE N} (h : IsCj X g g') (h' : IsCj X g g'') : g' = g'' :=
  AlgEquiv.ext fun x => (h x).trans (h' x).symm

theorem isCj_one : IsCj X (1 : GE N) 1 := fun x => by simp

theorem IsCj.mul {g g' h h' : GE N} (hg : IsCj X g g') (hh : IsCj X h h') : IsCj X (g * h) (g' * h') := fun x => by
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hh x, hg]
  simp

theorem IsDual.unique {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (h : IsDual i s ρ) (h' : IsDual i s ρ') : ρ = ρ' :=
  MonoidHom.ext fun g => Units.ext ((h g).trans (h' g).symm)

example : IsRes i (IsLocalRing.ResidueField (X.O0 i)) := fun x hx =>
  (IsLocalRing.residue_eq_zero_iff x).2 hx

theorem form_swap {K : Type} [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    {ρ ρ' : GE N →* GL (Fin D.R.r) (X.O0 i)} (x : Z1 (red i K ρ)) (y : Z1 (red i K ρ')) (g h g' h' : GE N) :
    form x y g' h' g h = -form x y g h g' h' := by
  simp [form]

def dualRep : GE N →* GL (Fin D.R.r) (X.O0 i) :=
  MonoidHom.toHomUnits
    { toFun := Tdual i s
      map_one' := by
        rw [Tdual, ← Tgl_coe, map_one, map_one]
        simp
      map_mul' := fun g h => by
        simp only [Tdual, ← Tgl_coe, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul]
        rw [smul_mul_smul_comm] }

theorem isDual_dualRep : IsDual i s (dualRep i s) := fun _ => rfl

end GlobalTheory.ResSel
