import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.FixK
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.ColumnAlgebra.PiColElAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterAnnihilatorIntegerLatticeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacterStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.Form.LeviSmoothness.besselOf

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bessel_finite {V : Type} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB : IsPsd B)
    (u : ℕ → V) (v : V) (hself : ∀ i, B (u i) v = B (u i) (u i)) (horth : ∀ i j, i ≠ j → B (u i) (u j) = 0)
    (I : ℕ) : ∑ i ∈ Finset.range I, (B (u i) (u i)).re ≤ (B v v).re := by
  set S := ∑ i ∈ Finset.range I, u i with hS
  have h0 := hB.2 (v - S)
  have e1 : B (v - S) (v - S) = B v v - B v S - B S v + B S S := by
    simp only [map_sub, LinearMap.sub_apply]; ring
  have e2 : B S v = ∑ i ∈ Finset.range I, B (u i) (u i) := by
    rw [hS, map_sum, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hself i
  have e3 : B v S = ∑ i ∈ Finset.range I, starRingEnd ℂ (B (u i) (u i)) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB.1 (u i) v, hself i]
  have e4 : B S S = ∑ i ∈ Finset.range I, B (u i) (u i) := by
    rw [hS]
    simp only [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => horth j i hj) (fun h => absurd hi h)]
  rw [e1, e2, e3, e4] at h0
  simp only [Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.conj_re] at h0
  linarith

theorem isLat_sup {m : ℕ} {A A' : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) (hA' : IsLat A') : IsLat (A ⊔ A') := by
  refine ⟨?_, AddSubgroup.isOpen_mono le_sup_left hA.2⟩
  have hc : IsCompact ((A : Set (Fin (m + 1) → k)) + (A' : Set (Fin (m + 1) → k))) := hA.1.add hA'.1
  refine hc.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_mono le_sup_left hA.2)) ?_
  intro x hx
  obtain ⟨y, hy, w, hw, rfl⟩ := AddSubgroup.mem_sup.1 hx
  exact Set.add_mem_add hy hw

theorem val_lt_one_of_nabs {z : kˣ} (hz : nabs k z < 1) : valuation k (z : k) < 1 := by
  by_contra hc
  push Not at hc
  have h1 : valuation k ((1 : kˣ) : k) ≤ valuation k (z : k) := by simpa using hc
  have := (nabs_le_iff (1 : kˣ) z).2 h1
  rw [nabs_one] at this
  linarith

def Mz (ψ : AddChar k Circle) (m : ℕ) (b : k) : AddSubgroup (Fin (m + 1) → k) where
  carrier := {x | ∀ t : Fin (m + 1) → k, (∀ j, t j ∈ 𝒪[k]) → ψ (b * (t ⬝ᵥ x)) = 1}
  zero_mem' := by intro t _; simp
  add_mem' := by
    intro x y hx hy t ht
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, mul_add, AddChar.map_add_eq_mul, hx t ht, hy t ht, one_mul]
  neg_mem' := by
    intro x hx t ht
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_neg, mul_neg, AddChar.map_neg_eq_inv, hx t ht, inv_one]

theorem isLat_Mz {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (m : ℕ) {b : k} (hb : b ≠ 0) :
    IsLat (Mz ψ m b) :=
  GlobalTheory.T.character_annihilator_integer_lattice k ψ hψ hψ1 (m + 1) b hb

theorem smul_mem_Mz {ψ : AddChar k Circle} {m : ℕ} {b c : k} (hc : c ∈ 𝒪[k]) {x : Fin (m + 1) → k}
    (hx : x ∈ Mz ψ m b) : c • x ∈ Mz ψ m b := by
  intro t ht
  rw [dotProduct_smul, smul_eq_mul, ← smul_eq_mul c, ← smul_dotProduct]
  exact hx (c • t) fun j => by simpa using mul_mem hc (ht j)

theorem exists_sep {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (m : ℕ) {a : k}
    (ha : valuation k a < 1) :
    ∃ d : k, ψ d ≠ 1 ∧ ∀ c : k, c ∈ 𝒪[k] → Pi.single (Fin.last m) (c * d) ∈ Mz ψ m a := by
  obtain ⟨c₀, hc₀⟩ : ∃ c, ψ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hψ1 (DFunLike.ext _ _ (fun c => by rw [hcon c, AddChar.one_apply]))
  obtain ⟨d, hd, -, hd2⟩ := GlobalTheory.T.exists_scaled_nontrivial_character k ψ hψ a c₀ ha hc₀
  refine ⟨d, hd, fun c hc t ht => ?_⟩
  rw [dotProduct_single]
  have := hd2 (t (Fin.last m) * c) (mul_mem (ht _) hc)
  rw [← this]
  congr 1
  ring

section
variable {ψ : AddChar k Circle} {m N : ℕ} {h : m + 2 ≤ N} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ}

theorem B_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (α β : ℂ) (x y : W) :
    B (α • x) (β • y) = α * (starRingEnd ℂ β * B x y) := by
  rw [LinearMap.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul]

theorem nabs_pow (x : kˣ) (n : ℕ) : nabs k (x ^ n) = nabs k x ^ n := by
  induction n with
  | zero => simp [nabs_one]
  | succ n ih => rw [pow_succ, GlobalTheory.SmGL.nabs_mul' k, ih, pow_succ]

theorem B_colEl (hB : Lv ψ h π s B) (y : Fin (m + 1) → k) (a b : V) :
    B (π (colEl k m N h y) a) (π (colEl k m N h y) b) = B a b := by
  have hmem : unip k (m + 1) (Multiplicative.ofAdd y) ∈ Mir k (m + 1) := MirU_le_Mir k (m + 1) ⟨_, rfl⟩
  have e := hB.mir _ hmem a b
  rw [ColumnElementGluing.det_unip, nabs_one, Real.one_rpow, Complex.ofReal_one, one_mul] at e
  exact e

theorem B_scal (hB : Lv ψ h π s B) (z : kˣ) (i : ℕ) (a b : V) :
    B (π (scalAt k (m + 1) N (by omega) (z ^ i)) a) (π (scalAt k (m + 1) N (by omega) (z ^ i)) b) =
      ((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B a b := by
  set g : GL (Fin (m + 1)) k := Units.map (algebraMap k (Matrix (Fin (m + 1)) (Fin (m + 1)) k)).toMonoidHom (z ^ i)
    with hg
  have hmem : glEmb k (m + 1) g ∈ Mir k (m + 1) := glEmb_mem_Mir k (m + 1) g
  have e := hB.mir _ hmem a b
  rw [ColumnElementGluing.blkAt_glEmb h g, ColumnElementGluing.det_glEmb] at e
  have hdet : Matrix.GeneralLinearGroup.det g = (z ^ i) ^ (m + 1) := by
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, Units.coe_map]
    change (algebraMap k (Matrix (Fin (m + 1)) (Fin (m + 1)) k) ((z ^ i : kˣ) : k)).det = _
    rw [Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    push_cast
    rfl
  rw [hdet, nabs_pow, nabs_pow, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k z).le] at e
  show B (π (blkAt k (m + 1) N (by omega) g) a) (π (blkAt k (m + 1) N (by omega) g) b) = _
  rw [e]
  congr 3
  push_cast
  ring

theorem dens_bessel_of (hB : Lv ψ h π s B)
    (hstab : ∀ (K : Subgroup (GL (Fin (m + 1)) k)), IsOpen (K : Set (GL (Fin (m + 1)) k)) →
      ∀ {A₀ : AddSubgroup (Fin (m + 1) → k)}, IsLat A₀ →
      ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ ∀ v w, FixK (by omega) π K v → FixK (by omega) π K w → ∀ A, IsLat A → A₁ ≤ A →
        ((A₀.relIndex A : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A v) w =
          ((A₀.relIndex A₁ : ℕ) : ℂ) * B (avg ψ h π (xi0 k m) A₁ v) w) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀)
    {B' : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hD : IsDens ψ h π A₀ B B') (z : kˣ) (hz : nabs k z < 1) (v : V) :
    Summable fun i : ℕ => nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
      (B' (π (scalAt k (m + 1) N (by omega) (z ^ i)) v) (π (scalAt k (m + 1) N (by omega) (z ^ i)) v)).re := by
  have h1 : m + 1 ≤ N := by omega
  let S : Subgroup (GL (Fin N) k) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} (ha : π a v = v) (hb : π b v = v) =>
        show π (a * b) v = v by rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := show π 1 v = v by rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} (ha : π a v = v) => show π a⁻¹ v = v by
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let K : Subgroup (GL (Fin (m + 1)) k) := S.comap (blkAt k (m + 1) N h1)
  have hK : IsOpen (K : Set (GL (Fin (m + 1)) k)) := (hB.smooth v).preimage (ColumnElementGluing.continuous_blkAt (m + 1) N h1)
  have hvK : FixK h1 π K v := fun g hg => hg
  obtain ⟨A₁, hA₁, -, hst⟩ := hstab K hK hA₀
  have hzv : valuation k (z : k) < 1 := val_lt_one_of_nabs hz
  obtain ⟨d, hd, hdM⟩ := exists_sep hB.cont hB.ne m hzv
  have hM : IsLat (Mz ψ m (z : k)) := isLat_Mz hB.cont hB.ne m z.ne_zero
  let A : AddSubgroup (Fin (m + 1) → k) := A₁ ⊔ Mz ψ m (z : k)
  have hA : IsLat A := isLat_sup hA₁ hM
  have h1A : A₁ ≤ A := le_sup_left
  have hMA : Mz ψ m (z : k) ≤ A := le_sup_right
  have hzO : (z : k) ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 hzv.le
  let σ : ℕ → GL (Fin N) k := fun i => scalAt k (m + 1) N h1 (z ^ i)
  have hfix : ∀ i, FixK h1 π K (π (σ i) v) := by
    intro i g hg
    show π (blkAt k (m + 1) N h1 g) (π (scalAt k (m + 1) N h1 (z ^ i)) v) = π (scalAt k (m + 1) N h1 (z ^ i)) v
    rw [← Module.End.mul_apply, ← map_mul, ← ColumnElementGluing.scalAt_comm_blkAt h1 (z ^ i) g, map_mul, Module.End.mul_apply,
      hvK g hg]
  let a : ℕ → V := fun i => avg ψ h π (xi0 k m) A (π (σ i) v)
  have hval : ∀ i, B' (π (σ i) v) (π (σ i) v) = ((A₀.relIndex A : ℕ) : ℂ) * B (a i) (π (σ i) v) := by
    intro i
    obtain ⟨A₂, hA₂, -, hv2⟩ := hD (π (σ i) v) (π (σ i) v)
    have hA3 : IsLat (A ⊔ A₂) := isLat_sup hA hA₂
    rw [hv2 (A ⊔ A₂) hA3 le_sup_right, hst _ _ (hfix i) (hfix i) (A ⊔ A₂) hA3 (h1A.trans le_sup_left),
      ← hst _ _ (hfix i) (hfix i) A hA h1A]
  let u : ℕ → V := fun i => π (σ i)⁻¹ (a i)
  have hσu : ∀ i, π (σ i) (u i) = a i := fun i => by
    show π (σ i) (π (σ i)⁻¹ (a i)) = a i
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hsc : ∀ i (x y : V), B (π (σ i) x) (π (σ i) y) = ((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B x y :=
    fun i x y => B_scal hB z i x y
  have hcpos : ∀ i : ℕ, 0 < nabs k z ^ ((i : ℝ) * (m + 1) * s) := fun i => Real.rpow_pos_of_pos (nabs_pos' k z) _
  have hself : ∀ i, B (u i) v = B (u i) (u i) := by
    intro i
    have e : B (a i) (π (σ i) v) = B (a i) (avg ψ h π (xi0 k m) A (π (σ i) v)) :=
      alg.avg_selfadj hB (xi0 k m) hA (π (σ i) v) (π (σ i) v)
    change B (a i) (π (σ i) v) = B (a i) (a i) at e
    rw [← hσu i, hsc, hsc] at e
    exact mul_left_cancel₀ (by exact_mod_cast (hcpos i).ne') e
  have heig : ∀ i (y : Fin (m + 1) → k), ((z ^ i : kˣ) : k) • y ∈ A →
      π (colEl k m N h y) (u i) = ((ψ (xi0 k m ⬝ᵥ ((z ^ i : kˣ) : k) • y) : Circle) : ℂ) • u i := by
    intro i y hy
    show π (colEl k m N h y) (π (σ i)⁻¹ (a i)) = _ • π (σ i)⁻¹ (a i)
    have hc := ColumnElementGluing.scalAt_conj_colEl h (z ^ i) y
    have hc' : colEl k m N h y * (σ i)⁻¹ = (σ i)⁻¹ * colEl k m N h (((z ^ i : kˣ) : k) • y) := by
      show colEl k m N h y * (scalAt k (m + 1) N h1 (z ^ i))⁻¹ =
        (scalAt k (m + 1) N h1 (z ^ i))⁻¹ * colEl k m N h (((z ^ i : kˣ) : k) • y)
      rw [← hc]; group
    rw [← Module.End.mul_apply, ← map_mul, hc', map_mul, Module.End.mul_apply]
    have e := ColumnElementGluing.avg_eigen ψ h π hB.cont hB.smooth (xi0 k m) A hA (π (σ i) v) _ hy
    change π (colEl k m N h (((z ^ i : kˣ) : k) • y)) (a i) = _ at e
    rw [e, map_smul]
  have horth0 : ∀ i j, i < j → B (u i) (u j) = 0 := by
    intro i j hij
    obtain ⟨l, rfl⟩ : ∃ l, j = i + (l + 1) := ⟨j - i - 1, by omega⟩
    have hzl : valuation k ((z : k) ^ (l + 1)) < 1 := by
      rw [map_pow]; exact pow_lt_one₀ zero_le hzv (by omega)
    have h1z : valuation k (1 - (z : k) ^ (l + 1)) = 1 := Valuation.map_one_sub_of_lt _ hzl
    have h1z0 : (1 - (z : k) ^ (l + 1)) ≠ 0 := by
      intro e; rw [e, map_zero] at h1z; exact zero_ne_one h1z
    let c : k := (1 - (z : k) ^ (l + 1))⁻¹
    have hcO : c ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (by simp only [c, map_inv₀, h1z, inv_one]; exact le_rfl)
    let w : Fin (m + 1) → k := Pi.single (Fin.last m) (c * d)
    have hwM : w ∈ Mz ψ m (z : k) := hdM c hcO
    let y : Fin (m + 1) → k := (((z ^ i)⁻¹ : kˣ) : k) • w
    have hy1 : ((z ^ i : kˣ) : k) • y = w := by
      simp only [y, smul_smul, Units.mul_inv, one_smul]
    have hy2 : ((z ^ (i + (l + 1)) : kˣ) : k) • y = ((z : k) ^ (l + 1)) • w := by
      simp only [y, smul_smul]
      congr 1
      push_cast
      rw [pow_add, mul_assoc, mul_comm ((z : k) ^ (l + 1)), ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ z.ne_zero),
        one_mul]
    have e1 := heig i y (hy1 ▸ hMA hwM)
    have e2 := heig (i + (l + 1)) y (hy2 ▸ hMA (smul_mem_Mz (pow_mem hzO _) hwM))
    rw [hy1] at e1
    rw [hy2] at e2
    have hinv := B_colEl hB y (u i) (u (i + (l + 1)))
    rw [e1, e2, B_smul_smul] at hinv
    have hxw : xi0 k m ⬝ᵥ w = c * d := by simp [w, xi0]
    have hxw2 : xi0 k m ⬝ᵥ ((z : k) ^ (l + 1)) • w = (z : k) ^ (l + 1) * (c * d) := by
      rw [dotProduct_smul, hxw, smul_eq_mul]
    rw [hxw, hxw2] at hinv
    have hsplit : c * d = (z : k) ^ (l + 1) * (c * d) + d := by
      have : c * (1 - (z : k) ^ (l + 1)) = 1 := inv_mul_cancel₀ h1z0
      linear_combination d * this
    set β : Circle := ψ ((z : k) ^ (l + 1) * (c * d))
    have hα : ((ψ (c * d) : Circle) : ℂ) = (β : ℂ) * ((ψ d : Circle) : ℂ) := by
      rw [hsplit, AddChar.map_add_eq_mul]; push_cast; rfl
    rw [hα] at hinv
    have hb1 : starRingEnd ℂ (β : ℂ) * (β : ℂ) = 1 := ColumnElementGluing.conj_circle_mul_self β
    have hd1 : ((ψ d : Circle) : ℂ) ≠ 1 := fun e => hd (Subtype.ext (by simpa using e))
    have : ((ψ d : Circle) : ℂ) * B (u i) (u (i + (l + 1))) = B (u i) (u (i + (l + 1))) := by
      linear_combination hinv - (((ψ d : Circle) : ℂ) * B (u i) (u (i + (l + 1)))) * hb1
    have : (((ψ d : Circle) : ℂ) - 1) * B (u i) (u (i + (l + 1))) = 0 := by linear_combination this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hd1)
  have horth : ∀ i j, i ≠ j → B (u i) (u j) = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hl | hl
    · exact horth0 i j hl
    · rw [hB.psd.1 (u j) (u i), horth0 j i hl, map_zero]
  have hterm : ∀ i : ℕ, nabs k z ^ (-((i : ℝ) * (m + 1) * s)) * (B' (π (σ i) v) (π (σ i) v)).re =
      (A₀.relIndex A : ℝ) * (B (u i) (u i)).re := by
    intro i
    rw [hval i, ← hσu i, hsc i, hself i]
    rw [show ((A₀.relIndex A : ℕ) : ℂ) * (((nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B (u i) (u i)) =
      (((A₀.relIndex A : ℝ) * nabs k z ^ ((i : ℝ) * (m + 1) * s) : ℝ) : ℂ) * B (u i) (u i) by push_cast; ring]
    rw [Complex.re_ofReal_mul, Real.rpow_neg (nabs_pos' k z).le]
    have := (hcpos i).ne'
    field_simp
  refine summable_of_sum_range_le (c := (A₀.relIndex A : ℝ) * (B v v).re) (fun i => ?_) (fun I => ?_)
  · exact le_of_le_of_eq (mul_nonneg (Nat.cast_nonneg _) (hB.psd.2 _)) (hterm i).symm
  · calc ∑ i ∈ Finset.range I, nabs k z ^ (-((i : ℝ) * (m + 1) * s)) *
          (B' (π (σ i) v) (π (σ i) v)).re
        = ∑ i ∈ Finset.range I, (A₀.relIndex A : ℝ) * (B (u i) (u i)).re := Finset.sum_congr rfl fun i _ => hterm i
      _ = (A₀.relIndex A : ℝ) * ∑ i ∈ Finset.range I, (B (u i) (u i)).re := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (bessel_finite B hB.psd u v hself horth I) (Nat.cast_nonneg _)

end

end PositivityTheory.RgUd.Form.LeviSmoothness.besselOf
