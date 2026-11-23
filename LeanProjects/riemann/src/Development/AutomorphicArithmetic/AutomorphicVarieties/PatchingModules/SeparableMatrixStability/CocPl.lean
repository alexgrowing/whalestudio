import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlSub

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Abs

variable {K M : Type} [Group K] [Ring M] (ρ z : K → M) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
  (hz : ∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹)

include h1 hz in
private theorem cocycle_apply_one_eq_zero : z 1 = 0 := by
  simpa [h1] using hz 1 1

include h1 hm in
private theorem cp_inv {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem cp_add {g : K} (hg : ρ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, hg, cp_inv ρ h1 hm hg, one_mul, mul_one]

include h1 hm hz in
private theorem cp_pow {g : K} (hg : ρ g = 1) (k : ℕ) : ρ (g ^ k) = 1 ∧ z (g ^ k) = k • z g := by
  induction k with
  | zero => exact ⟨by simpa using h1, by simpa using cocycle_apply_one_eq_zero ρ z h1 hz⟩
  | succ k ih =>
    refine ⟨by rw [pow_succ', hm, hg, ih.1, one_mul], ?_⟩
    rw [pow_succ', cp_add ρ z h1 hm hz hg, ih.2, succ_nsmul']

include h1 hm hz in
private theorem cp_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ z g = 0 := by
  have hinv : ∀ g, ρ g = 1 → z g = 0 → ρ g⁻¹ = 1 ∧ z g⁻¹ = 0 := by
    intro g hg hzg
    refine ⟨cp_inv ρ h1 hm hg, ?_⟩
    have := cp_add ρ z h1 hm hz hg g⁻¹
    rwa [mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz, hzg, zero_add, eq_comm] at this
  let S : Subgroup K :=
    { carrier := {g | ρ g = 1 ∧ z g = 0}
      mul_mem' := by
        rintro a b ⟨ha, hza⟩ ⟨hb, hzb⟩
        exact ⟨by rw [hm, ha, hb, one_mul], by rw [cp_add ρ z h1 hm hz ha, hza, hzb, zero_add]⟩
      one_mem' := ⟨h1, cocycle_apply_one_eq_zero ρ z h1 hz⟩
      inv_mem' := by
        rintro a ⟨ha, hza⟩
        exact hinv a ha hza }
  have hS : IsOpen (S : Set K) := (cρ.isOpen_fiber 1).inter (cz.isOpen_fiber 0)
  have hN : S.Normal := by
    constructor
    rintro a ⟨ha, hza⟩ k
    show ρ (k * a * k⁻¹) = 1 ∧ z (k * a * k⁻¹) = 0
    refine ⟨?_, ?_⟩
    · rw [hm, hm, ha, mul_one, ← hm, mul_inv_cancel, h1]
    · rw [mul_assoc, hz, cp_add ρ z h1 hm hz ha, hza, zero_add, ← hz, mul_inv_cancel, cocycle_apply_one_eq_zero ρ z h1 hz]
  exact ⟨{ toOpenSubgroup := ⟨S, hS⟩, isNormal' := hN }, fun g => Iff.rfl⟩

end Abs

private theorem cp_lc {K R : Type} [TopologicalSpace K] [CommRing R] {n : ℕ} (I : Ideal R)
    (f : K → Matrix (Fin n) (Fin n) R) (hf : ∀ i j, AdicCont I fun g => f g i j) (m : ℕ) :
    IsLocallyConstant fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g) := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro y
  have e : (fun g => (Ideal.Quotient.mk (I ^ m)).mapMatrix (f g)) ⁻¹' {y} =
      ⋂ i, ⋂ j, (fun g => Ideal.Quotient.mk (I ^ m) (f g i j)) ⁻¹' {y i j} := by
    ext g
    simp [← Matrix.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hf i j m).isOpen_fiber _

private theorem cp_zero {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 0 ↔ ∀ i j, A i j ∈ J := by
  rw [← Matrix.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

private theorem cp_one {R : Type} [CommRing R] {n : ℕ} (J : Ideal R) (A : Matrix (Fin n) (Fin n) R) :
    (Ideal.Quotient.mk J).mapMatrix A = 1 ↔ ∀ i j, (A - 1) i j ∈ J := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk J).mapMatrix, ← map_sub, cp_zero]

theorem UpperTheory.V.Pa.coc_pl :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G : Glob l L) (n : ℕ) (R : Type) [CommRing R] (I : Ideal R) (ρ z : G.G₀ → Matrix (Fin n) (Fin n) R) (H : Subgroup G.Γ) [H.Normal], IsOpen (H : Set G.Γ) → H ≤ G.η.ker → (l : R) = 0 → ρ 1 = 1 → (∀ g h, ρ (g * h) = ρ g * ρ h) → (∀ i j, AdicCont I fun g => ρ g i j) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m) → (∀ i j, AdicCont I fun g => z g i j) → (∀ g h, z (g * h) = z g + ρ g * z h * ρ g⁻¹) → (∀ (m : ℕ) (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j, (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧ ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ (m : ℕ) i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
  intro l _ L G n R _ I ρ z H _ hHo hHk hl h1 hm hρc hρH hzc hz
  have main : ∀ m : ℕ, (∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
      (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m) ∧
      ∀ k : G.G₀, (k : G.Γ) ∈ PL l H → ∀ i j, (ρ k - 1) i j ∈ I ^ m ∧ z k i j ∈ I ^ m := by
    intro m
    let ρ' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (ρ x)
    let z' := fun x => (Ideal.Quotient.mk (I ^ m)).mapMatrix (z x)
    have h1' : ρ' 1 = 1 := by simp [ρ', h1]
    have hm' : ∀ a b, ρ' (a * b) = ρ' a * ρ' b := by
      intro a b
      simp [ρ', hm]
    have hz' : ∀ a b, z' (a * b) = z' a + ρ' a * z' b * ρ' a⁻¹ := by
      intro a b
      simp only [z', ρ', hz, map_add, map_mul]
    have hlq : ((l : ℕ) : R ⧸ I ^ m) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (I ^ m)), hl, map_zero]
    have key : ∀ g : G.G₀, ρ' g = 1 → ρ' (g ^ l) = 1 ∧ z' (g ^ l) = 0 := by
      intro g hg
      obtain ⟨p1, p2⟩ := cp_pow ρ' z' h1' hm' hz' hg l
      refine ⟨p1, p2.trans ?_⟩
      ext i j
      simp [Matrix.smul_apply, nsmul_eq_mul, hlq]
    have P1 : ∀ (h : G.G₀), (h : G.Γ) ∈ H → ∃ e : ℕ, ∀ i j,
        (ρ (h ^ l ^ e) - 1) i j ∈ I ^ m ∧ z (h ^ l ^ e) i j ∈ I ^ m := by
      intro h hh
      obtain ⟨e, he⟩ := hρH m h hh
      refine ⟨e + 1, fun i j => ?_⟩
      rw [pow_succ l e, pow_mul]
      obtain ⟨q1, q2⟩ := key _ ((cp_one _ _).2 he)
      exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
    refine ⟨P1, ?_⟩
    obtain ⟨U, hU⟩ := cp_U ρ' z' h1' hm' hz' (cp_lc I ρ hρc m) (cp_lc I z hzc m)
    intro k hk i j
    have hkU : k ∈ U := by
      refine pl_sub l G.Γ H G.η.ker G.η_open hHk U ?_ k hk
      intro h hh
      obtain ⟨e, he⟩ := P1 h hh
      exact ⟨e, (hU _).2 ⟨(cp_one _ _).2 fun i j => (he i j).1, (cp_zero _ _).2 fun i j => (he i j).2⟩⟩
    obtain ⟨q1, q2⟩ := (hU k).1 hkU
    exact ⟨(cp_one _ _).1 q1 i j, (cp_zero _ _).1 q2 i j⟩
  exact ⟨fun m h hh => (main m).1 h hh, fun k hk m i j => (main m).2 k hk i j⟩
