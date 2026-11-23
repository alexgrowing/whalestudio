import Mathlib
import GroundTheory.AutomorphicForms.AdmissibleFiniteLength
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.LocalFields.LocalFourierChar
import GroundTheory.LocalFields.LocalZetaEpsilon
import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal ValuativeRel Topology Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def IsSchwartzBruhat (Φ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ

def absDet (g : GL (Fin n) F) : ℝ :=
  (LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) : ℝ)

def detPow (g : GL (Fin n) F) (s : ℂ) : ℂ :=
  (absDet g : ℂ) ^ s

variable (F) in

def qs (s : ℂ) : ℂ :=
  (LocalField.residueCard F : ℂ) ^ (-s)

def ordDet (g : GL (Fin n) F) : ℤ :=
  LocalField.ord ((g : Matrix (Fin n) (Fin n) F).det)

def IsLeviSchwartz {α : Type*} (β : Fin n → α) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  ∃ r A : ℕ,
    (∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X) ∧
    (∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])

theorem mem_valBall_iff_exists {r : ℕ} {y : F} :
    y ∈ LocalField.valBall F r ↔ ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hord : LocalField.ord (uniformizer F : F) = 1 :=
    LocalField.ord_uniformizer (irreducible_uniformizer F)
  have hϖr : (uniformizer F : F) ^ r ∈ LocalField.valBall F r := by
    rw [LocalField.mem_valBall_iff_le_ord (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    simp
  constructor
  · intro hy
    by_cases h0 : y = 0
    · exact ⟨0, zero_mem _, by rw [h0, mul_zero]⟩
    refine ⟨y / (uniformizer F : F) ^ r, ?_, by field_simp⟩
    have hne : y / (uniformizer F : F) ^ r ≠ 0 := div_ne_zero h0 (pow_ne_zero _ hϖ)
    rw [← LocalField.mem_valBall_zero_iff, LocalField.mem_valBall_iff_le_ord hne, div_eq_mul_inv,
      LocalField.ord_mul h0 (inv_ne_zero (pow_ne_zero _ hϖ)),
      LocalField.ord_inv (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    have := (LocalField.mem_valBall_iff_le_ord h0).1 hy
    linarith
  · rintro ⟨a, ha, rfl⟩
    have := LocalField.mul_mem_valBall hϖr (LocalField.mem_valBall_zero_iff.2 ha)
    simpa using this

theorem exists_valBall_subset {S : Set (Matrix (Fin n) (Fin n) F)}
    (hS : S ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F)) :
    ∃ r : ℕ, {Y : Matrix (Fin n) (Fin n) F | ∀ i j, Y i j ∈ LocalField.valBall F r} ⊆ S := by
  classical
  have hS' : S ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : Fin n → F) := by
    rw [← nhds_pi]; exact hS
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 hS'
  have ht' : ∀ i, t i ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : F) := fun i => by
    rw [← nhds_pi]; exact ht i
  choose J u hu hJu using fun i => Filter.mem_pi'.1 (ht' i)
  have hr : ∀ i j, ∃ r : ℤ, (LocalField.valBall F r : Set F) ⊆ u i j := fun i j => by
    obtain ⟨r, -, hr⟩ := LocalField.hasBasis_nhds_zero_valBall.mem_iff.1 (hu i j)
    exact ⟨r, hr⟩
  choose r hr using hr
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat, fun Y hY => hIt ?_⟩
  intro i _
  refine hJu i ?_
  intro j _
  refine hr i j (LocalField.valBall_antitone ?_ (hY i j))
  have : (r i j).toNat ≤ Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat :=
    Finset.le_sup (f := fun p : Fin n × Fin n => (r p.1 p.2).toNat) (Finset.mem_univ (i, j))
  omega

theorem exists_valBall_of_isCompact {K : Set (Matrix (Fin n) (Fin n) F)} (hK : IsCompact K) :
    ∃ A : ℕ, ∀ X ∈ K, ∀ i j, X i j ∈ LocalField.valBall F (-(A : ℤ)) := by
  classical
  let U : ℕ → Set (Matrix (Fin n) (Fin n) F) :=
    fun m => {X | ∀ i j, X i j ∈ LocalField.valBall F (-(m : ℤ))}
  have hU : ∀ m, IsOpen (U m) := fun m => by
    have : U m = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        (LocalField.valBall F (-(m : ℤ)) : Set F) := by
      ext X; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (LocalField.isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))
  have hcover : K ⊆ ⋃ m, U m := by
    intro X _
    choose m hm using fun p : Fin n × Fin n => LocalField.exists_mem_valBall_neg_nat (X p.1 p.2)
    refine Set.mem_iUnion.2 ⟨Finset.univ.sup m, fun i j => LocalField.valBall_antitone ?_ (hm (i, j))⟩
    have := Finset.le_sup (f := m) (Finset.mem_univ (i, j))
    omega
  have hdir : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨max a b, fun X hX i j => LocalField.valBall_antitone ?_ (hX i j),
      fun X hX i j => LocalField.valBall_antitone ?_ (hX i j)⟩ <;> omega
  obtain ⟨A, hA⟩ := hK.elim_directed_cover U hU hcover hdir
  exact ⟨A, fun X hX => hA hX⟩

theorem IsSchwartzBruhat.exists_invariant {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ r A : ℕ,
      (∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
        Φ (X + Y) = Φ X) ∧
      (∀ X : Matrix (Fin n) (Fin n) F, Φ X ≠ 0 → ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F]) := by
  classical
  obtain ⟨hlc, hcs⟩ := hΦ
  set K := tsupport Φ
  have hK : IsCompact K := hcs

  let L : ℕ → Set (Matrix (Fin n) (Fin n) F) :=
    fun r => {Y | ∀ i j, Y i j ∈ LocalField.valBall F r}
  have hLadd : ∀ r, ∀ Y ∈ L r, ∀ Z ∈ L r, Y + Z ∈ L r := fun r Y hY Z hZ i j =>
    add_mem (hY i j) (hZ i j)
  have hLneg : ∀ r, ∀ Y ∈ L r, -Y ∈ L r := fun r Y hY i j => by
    simpa using neg_mem (hY i j)
  have hLanti : ∀ {r r'}, r ≤ r' → L r' ⊆ L r := fun h Y hY i j =>
    LocalField.valBall_antitone (by exact_mod_cast h) (hY i j)
  have hLopen : ∀ r, IsOpen (L r) := fun r => by
    have : L r = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        (LocalField.valBall F (r : ℤ) : Set F) := by
      ext X; simp [L]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (LocalField.isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

  let Wr : ℕ → Set (Matrix (Fin n) (Fin n) F) := fun r => {X | ∀ Y ∈ L r, Φ (X + Y) = Φ X}
  have hWopen : ∀ r, IsOpen (Wr r) := by
    intro r
    rw [isOpen_iff_mem_nhds]
    intro X hX
    have hnhds : {Z | Z - X ∈ L r} ∈ 𝓝 X :=
      ((hLopen r).preimage (continuous_id.sub continuous_const)).mem_nhds (by
        show X - X ∈ L r
        rw [sub_self]
        exact fun i j => zero_mem (LocalField.valBall F (r : ℤ)))
    refine Filter.mem_of_superset hnhds fun Z hZ Y hY => ?_
    have h1 := hX (Z - X + Y) (hLadd r _ hZ _ hY)
    have h2 := hX (Z - X) hZ
    rw [show X + (Z - X + Y) = Z + Y by abel, show X + (Z - X) = Z by abel] at *
    rw [h1, h2]
  have hcover : K ⊆ ⋃ r, Wr r := by
    intro X _
    have hmem : (fun Y => X + Y) ⁻¹' (Φ ⁻¹' {Φ X}) ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F) := by
      refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
      show Φ ⁻¹' {Φ X} ∈ 𝓝 (X + 0)
      rw [add_zero]
      exact (hlc.isOpen_fiber (Φ X)).mem_nhds rfl
    obtain ⟨r, hr⟩ := exists_valBall_subset hmem
    exact Set.mem_iUnion.2 ⟨r, fun Y hY => hr hY⟩
  have hdir : Directed (· ⊆ ·) Wr := by
    intro a b
    refine ⟨max a b, fun X hX Y hY => hX Y (hLanti (le_max_left a b) hY),
      fun X hX Y hY => hX Y (hLanti (le_max_right a b) hY)⟩
  obtain ⟨r, hr⟩ := hK.elim_directed_cover Wr hWopen hcover hdir
  obtain ⟨A, hA⟩ := exists_valBall_of_isCompact hK
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  refine ⟨r, A, fun X Y hY => ?_, fun X hX i j => ?_⟩
  · have hYL : Y ∈ L r := fun i j => mem_valBall_iff_exists.2 (hY i j)
    by_cases hXK : X ∈ K
    · exact hr hXK Y hYL
    by_cases hXYK : X + Y ∈ K
    · have := hr hXYK (-Y) (hLneg r Y hYL)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hXK, image_eq_zero_of_notMem_tsupport hXYK]
  · have hXK : X ∈ K := subset_tsupport _ hX
    have h1 := hA X hXK i j
    have h2 : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) :=
      (mem_valBall_iff_exists (r := A)).2 ⟨1, one_mem _, by rw [mul_one]⟩
    have := LocalField.mul_mem_valBall h2 h1
    rw [add_neg_cancel] at this
    exact LocalField.mem_valBall_zero_iff.1 this

theorem detPow_eq_qs_zpow (g : GL (Fin n) F) (s : ℂ) : detPow g s = qs F s ^ ordDet g := by
  have hd : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [detPow, absDet, qs, ordDet, LocalField.modulus_cpow_eq_qcpow hd, LocalField.qcpow_zpow]
  congr 1
  ring

theorem qs_ne_zero (s : ℂ) : qs F s ≠ 0 := by
  rw [qs]
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero))

theorem norm_qs (s : ℂ) : ‖qs F s‖ = (LocalField.residueCard F : ℝ) ^ (-s.re) := by
  rw [qs, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero LocalField.residueCard_ne_zero)]
  simp

end GodementJacquet

end GroundTheory.Automorphic
