import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsFF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

noncomputable section

open Matrix

namespace Formalism.UG.P

open Formalism.UG

section Loc

variable {L : Type} [Field L]

theorem tjcosets_card_orbit {G : Type} [Group G] (K : Subgroup G) (d : G) :
    Nat.card {x : G ⧸ K // ∃ a ∈ K, ∃ b ∈ K, x.out = a * d * b} =
      (MulAction.stabilizer K (QuotientGroup.mk d : G ⧸ K)).index := by
  have key : ∀ x : G ⧸ K, (∃ a ∈ K, ∃ b ∈ K, x.out = a * d * b) ↔
      x ∈ MulAction.orbit K (QuotientGroup.mk d : G ⧸ K) := by
    intro x
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      have hx : x = QuotientGroup.mk x.out := (QuotientGroup.out_eq' x).symm
      rw [hx, h]
      change (QuotientGroup.mk (a * d) : G ⧸ K) = QuotientGroup.mk (a * d * b)
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hb
    · rintro ⟨⟨a, ha⟩, h⟩
      change (QuotientGroup.mk (a * d) : G ⧸ K) = x at h
      have h2 : (QuotientGroup.mk (a * d) : G ⧸ K) = QuotientGroup.mk x.out := by
        rw [h, QuotientGroup.out_eq']
      rw [QuotientGroup.eq] at h2
      exact ⟨a, ha, (a * d)⁻¹ * x.out, h2, by rw [← mul_assoc, mul_inv_cancel, one_mul]⟩
  exact Nat.card_congr ((Equiv.subtypeEquivRight key).trans
    (MulAction.orbitEquivQuotientStabilizer K (QuotientGroup.mk d : G ⧸ K)))

theorem tjcosets_bc_injective (n : ℕ) (O : Subring L) :
    Function.Injective (bc (n := Fin n) O.subtype) := by
  intro g h hgh
  refine Units.ext (Matrix.ext fun a b => Subtype.ext ?_)
  have := congrArg (fun u : GL (Fin n) L => (u : Matrix (Fin n) (Fin n) L) a b) hgh
  exact this

theorem tjcosets_bc_apply {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (n : ℕ)
    (g : GL (Fin n) A) (a b : Fin n) :
    ((bc (n := Fin n) φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) a b = φ ((g : Matrix (Fin n) (Fin n) A) a b) := by
  rfl

def tjcosets_iso (n : ℕ) (O : Subring L) : GL (Fin n) O ≃* GLint (Fin n) O :=
  MonoidHom.ofInjective (tjcosets_bc_injective n O)

theorem tjcosets_iso_coe (n : ℕ) (O : Subring L) (g : GL (Fin n) O) :
    ((tjcosets_iso n O g : GLint (Fin n) O) : GL (Fin n) L) = bc O.subtype g := by
  exact MonoidHom.ofInjective_apply (tjcosets_bc_injective n O)

variable (O : Subring L) [IsLocalRing O]

def tjcosets_red (n : ℕ) : GLint (Fin n) O →* GL (Fin n) (IsLocalRing.ResidueField O) :=
  (bc (IsLocalRing.residue O)).comp (tjcosets_iso n O).symm.toMonoidHom

theorem tjcosets_red_iso (n : ℕ) (g : GL (Fin n) O) :
    tjcosets_red O n (tjcosets_iso n O g) = bc (IsLocalRing.residue O) g := by
  show bc _ ((tjcosets_iso n O).symm (tjcosets_iso n O g)) = _
  rw [MulEquiv.symm_apply_apply]

theorem tjcosets_red_surjective (n : ℕ) : Function.Surjective (tjcosets_red O n) := by
  intro g
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) O,
      M.map (IsLocalRing.residue O) = g.1 := by
    refine ⟨fun a b => (IsLocalRing.residue_surjective (g.1 a b)).choose, ?_⟩
    ext a b
    exact (IsLocalRing.residue_surjective (g.1 a b)).choose_spec
  have hdet : IsUnit M.det := by
    have h1 : IsLocalRing.residue O M.det = g.1.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    have hu : IsUnit g.1.det := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
    by_contra hne
    have h0 : IsLocalRing.residue O M.det = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hne))
    rw [h1] at h0
    exact hu.ne_zero h0
  refine ⟨tjcosets_iso n O (Matrix.GeneralLinearGroup.mk'' M hdet), ?_⟩
  rw [tjcosets_red_iso]
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [tjcosets_bc_apply]
  show IsLocalRing.residue O (M a b) = _
  rw [← hM]
  rfl

variable {O}

def tjcosets_dG (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) : GL (Fin n) L :=
  ⟨diagJ n ϖ j, diagJ n ϖ⁻¹ j, by
    unfold diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ], by
    unfold diagJ
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; split_ifs <;> simp [hϖ]⟩

theorem tjcosets_dG_val (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) :
    ((tjcosets_dG n j ϖ hϖ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagJ n ϖ j := rfl

theorem tjcosets_conj_apply (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) (g : GL (Fin n) L) (a b : Fin n) :
    (((tjcosets_dG n j ϖ hϖ)⁻¹ * g * tjcosets_dG n j ϖ hϖ : GL (Fin n) L) :
        Matrix (Fin n) (Fin n) L) a b =
      (if (a : ℕ) < j then ϖ⁻¹ else 1) * (g : Matrix (Fin n) (Fin n) L) a b *
        (if (b : ℕ) < j then ϖ else 1) := by
  rw [Units.val_mul, Units.val_mul]
  have hinv : (((tjcosets_dG n j ϖ hϖ)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagJ n ϖ⁻¹ j := rfl
  rw [hinv, tjcosets_dG_val]
  unfold diagJ
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem tjcosets_mem_K_iff (n : ℕ) (U : GL (Fin n) L) :
    U ∈ GLint (Fin n) O ↔ (∀ a b, (U : Matrix (Fin n) (Fin n) L) a b ∈ O) ∧
      (∀ a b, ((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) := by
  unfold GLint
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · exact ((g : Matrix (Fin n) (Fin n) O) a b).2
    · rw [← map_inv]
      exact (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) a b).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) O := fun a b => ⟨(U : Matrix (Fin n) (Fin n) L) a b, h1 a b⟩
    let N : Matrix (Fin n) (Fin n) O :=
      fun a b => ⟨((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b, h2 a b⟩
    have hM : M.map O.subtype = (U : Matrix (Fin n) (Fin n) L) := by ext a b; rfl
    have hN : N.map O.subtype = ((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext a b; rfl
    have inj : Function.Injective (fun P : Matrix (Fin n) (Fin n) O => P.map O.subtype) :=
      fun P Q h => by ext a b; exact congrFun (congrFun h a) b
    have hMN : M * N = 1 := inj (by
      show (M * N).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hM, hN, U.mul_inv]
      exact (map_one (RingHom.mapMatrix O.subtype)).symm)
    have hNM : N * M = 1 := inj (by
      show (N * M).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hM, hN, U.inv_mul]
      exact (map_one (RingHom.mapMatrix O.subtype)).symm)
    exact ⟨⟨M, N, hMN, hNM⟩, Units.ext hM⟩

theorem tjcosets_entries (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] (h : GL (Fin n) O) (hϖO : ϖ ∈ O) :
    (∀ a b : Fin n, (if (a : ℕ) < j then ϖ⁻¹ else 1) *
        (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * (if (b : ℕ) < j then ϖ else 1) ∈ O) ↔
      bc (IsLocalRing.residue O) h ∈ tjcosets_par n j := by
  rw [tjcosets_mem_par]
  constructor
  · intro hall a b ha hb
    have h1 := hall a b
    rw [if_pos ha, if_neg (not_lt.2 hb), mul_one] at h1
    rw [tjcosets_bc_apply]
    exact (hmax _).1 h1
  · intro hpar a b
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · rw [if_pos ha, if_pos hb, mul_comm ϖ⁻¹, mul_assoc, inv_mul_cancel₀ hϖ, mul_one]
      exact ((h : Matrix (Fin n) (Fin n) O) a b).2
    · rw [if_pos ha, if_neg hb, mul_one]
      apply (hmax _).2
      have := hpar a b ha (not_lt.1 hb)
      rw [tjcosets_bc_apply] at this
      exact this
    · rw [if_neg ha, if_pos hb, one_mul]
      exact O.mul_mem ((h : Matrix (Fin n) (Fin n) O) a b).2 hϖO
    · rw [if_neg ha, if_neg hb, one_mul, mul_one]
      exact ((h : Matrix (Fin n) (Fin n) O) a b).2

theorem tjcosets_stab (n j : ℕ) (ϖ : L) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] :
    MulAction.stabilizer (GLint (Fin n) O)
        (QuotientGroup.mk (tjcosets_dG n j ϖ hϖ) : GL (Fin n) L ⧸ GLint (Fin n) O) =
      (tjcosets_par n j).comap (tjcosets_red O n) := by
  ext g
  obtain ⟨h, rfl⟩ := (tjcosets_iso n O).surjective g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, tjcosets_red_iso]
  have e1 : (tjcosets_iso n O h) • (QuotientGroup.mk (tjcosets_dG n j ϖ hϖ) : GL (Fin n) L ⧸ GLint (Fin n) O) =
      QuotientGroup.mk (bc O.subtype h * tjcosets_dG n j ϖ hϖ) := by
    show (QuotientGroup.mk (((tjcosets_iso n O h : GLint (Fin n) O) : GL (Fin n) L) * tjcosets_dG n j ϖ hϖ) :
      GL (Fin n) L ⧸ GLint (Fin n) O) = _
    rw [tjcosets_iso_coe]
  rw [e1, QuotientGroup.eq]
  have e2 : (bc O.subtype h * tjcosets_dG n j ϖ hϖ)⁻¹ * tjcosets_dG n j ϖ hϖ =
      (tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h⁻¹ * tjcosets_dG n j ϖ hϖ := by
    rw [map_inv]; group
  have e3 : ((tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h⁻¹ * tjcosets_dG n j ϖ hϖ)⁻¹ =
      (tjcosets_dG n j ϖ hϖ)⁻¹ * bc O.subtype h * tjcosets_dG n j ϖ hϖ := by
    rw [map_inv]; group
  rw [e2, tjcosets_mem_K_iff, e3]
  have E1 := tjcosets_entries n j ϖ hϖ hmax h⁻¹ hϖO
  have E2 := tjcosets_entries n j ϖ hϖ hmax h hϖO
  rw [map_inv, inv_mem_iff] at E1
  constructor
  · rintro ⟨_, h2⟩
    refine E2.1 (fun a b => ?_)
    have h3 := h2 a b
    rw [tjcosets_conj_apply, tjcosets_bc_apply] at h3
    exact h3
  · intro hp
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · have h3 := E1.2 hp a b
      rw [tjcosets_conj_apply, tjcosets_bc_apply]
      exact h3
    · have h3 := E2.2 hp a b
      rw [tjcosets_conj_apply, tjcosets_bc_apply]
      exact h3

theorem tjcosets_index (n j : ℕ) (ϖ : L) (hϖO : ϖ ∈ O) (hϖ : ϖ ≠ 0)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0)
    [Finite (IsLocalRing.ResidueField O)] :
    Nat.card {x : GL (Fin n) L ⧸ GLint (Fin n) O // ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
        x.out = a * tjcosets_dG n j ϖ hϖ * b} =
      (tjcosets_par (𝔽 := IsLocalRing.ResidueField O) n j).index := by
  rw [tjcosets_card_orbit, tjcosets_stab n j ϖ hϖO hϖ hmax]
  exact Subgroup.index_comap_of_surjective _ (tjcosets_red_surjective O n)

end Loc

end Formalism.UG.P
