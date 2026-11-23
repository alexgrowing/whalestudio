import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.SemisPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def img {A : Subalgebra C (Mat C N)} (I : Ideal A) : Submodule C (Fin N → C) :=
  Submodule.span C {w | ∃ x ∈ I, ∃ v, w = (x : Mat C N) *ᵥ v}

lemma img_step {A : Subalgebra C (Mat C N)} (J I : Ideal A) {x : A} (hx : x ∈ J) {u : Fin N → C}
    (hu : u ∈ img I) : (x : Mat C N) *ᵥ u ∈ img (J * I) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

lemma img_bot {A : Subalgebra C (Mat C N)} : img (⊥ : Ideal A) = ⊥ := by
  rw [img, Submodule.span_eq_bot]
  rintro w ⟨x, hx, v, rfl⟩
  rw [Submodule.mem_bot] at hx
  simp [hx]

lemma conj_pow (P B Q : Mat C N) (h : Q * P = 1) (n : ℕ) : (P * B * Q) ^ (n + 1) = P * B ^ (n + 1) * Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ B (n+1)]
    calc P * B ^ (n + 1) * Q * (P * B * Q) = P * B ^ (n + 1) * (Q * P) * B * Q := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring

lemma nil_conj (P B Q : Mat C N) (h : Q * P = 1) (hB : IsNilpotent B) : IsNilpotent (P * B * Q) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k + 1, ?_⟩
  rw [conj_pow P B Q h, pow_succ, hk]; simp

lemma inv_mul_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

lemma mul_inv_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem Semis_of : Semis := by
  intro Γ C _ _ N ρ A hss hn hk Y hYA hY

  let S : Set (Mat C N) := {Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}
  let U : Submodule C (Fin N → C) := Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}
  have hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨Z, ⟨hZA, hZ⟩, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩,
        (ρ g : Mat C N) *ᵥ v, ?_⟩
      · intro a ha
        have ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A := hn g⁻¹ a ha
        rw [inv_inv] at ha'
        have := nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z)
          (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')
        convert this using 1
        calc a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N))
            = ((ρ g : Mat C N) * (ρ g⁻¹ : Mat C N)) * a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N)) := by
              rw [mul_inv_rho]; simp
          _ = _ := by noncomm_ring
      · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨W, hcompl, hWst⟩ := hss U hUst
  have hWA := hk W hWst
  have hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0 := by
    intro Z hZ w hw
    have h1 : Z *ᵥ w ∈ U := Submodule.subset_span ⟨Z, hZ, w, rfl⟩
    have h2 : Z *ᵥ w ∈ W := hWA Z hZ.1 w hw
    have := hcompl.inf_eq_bot
    have h3 : Z *ᵥ w ∈ U ⊓ W := ⟨h1, h2⟩
    rw [this] at h3
    exact (Submodule.mem_bot C).1 h3
  have : IsArtinianRing A := IsArtinianRing.of_finite C A
  let J : Ideal A := Ideal.jacobson ⊥
  have hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J := by
    intro Z hZ
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A)) := by
      obtain ⟨k, hk'⟩ := hZ.2 y y.2
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk'
    have hu := hnil.isUnit_one_add
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [Ideal.mem_bot]
    have h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1 := hu.val_inv_mul
    calc (↑hu.unit⁻¹ : A) * y * (⟨Z, hZ.1⟩ : A) + ↑hu.unit⁻¹ - 1
        = (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) - 1 := by noncomm_ring
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have key : ∀ k : ℕ, U ≤ img (J ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [Submodule.pow_one]
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      exact Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩
    | succ k ih =>
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      have hv : v ∈ U ⊔ W := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))
      rw [Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]
      exact img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)
  have hU : U = ⊥ := by
    have h := key m
    have hb : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]
    rw [hb, img_bot] at h
    exact le_bot_iff.1 h
  ext i j
  have hv : Y *ᵥ Pi.single j 1 ∈ U := Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩
  rw [hU, Submodule.mem_bot] at hv
  simpa using congrFun hv i
end LateralTheory.DivDb.SemisPf
