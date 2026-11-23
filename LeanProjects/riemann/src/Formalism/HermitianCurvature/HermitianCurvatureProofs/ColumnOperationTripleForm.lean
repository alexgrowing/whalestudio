import Formalism.HermitianCurvature.BlockKernelPropertiesOfSteps
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MulInvBlockDiagApplySameBlock
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LowUniMulVecELast

open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix

namespace Formalism.FourierDecayAlt.P.A5x2

open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase

theorem blk_app (l : List ℕ) (s : ℕ) (hs : 1 ≤ s) : blk (l ++ [s]) l.sum = l.length := by
  induction l with
  | nil => simp [blk]; omega
  | cons a l ih => simp [blk, ih]; omega

theorem revIn_app (l : List ℕ) (s : ℕ) (hs : 1 ≤ s) :
    revIn (l ++ [s]) l.sum = l.sum + (s - 1) := by
  induction l with
  | nil => simp [revIn]; omega
  | cons a l ih => simp [revIn, ih]; omega

theorem inv_last {K : Type} [CommRing K] (S : List ℕ) (T : ℕ → Kˣ)
    (x y : Matrix (Fin S.sum) (Fin S.sum) K) (hx : IsLowUni x) (hy : IsUpUni y)
    (a b c : Fin S.sum) (hb : b.val + 1 = S.sum) (hc : revF S c = b) :
    (x * pt S T * y)⁻¹ a b = (((T (blk S c))⁻¹ : Kˣ) : K) * y⁻¹ a c := by
  have hinv : (x * pt S T * y)⁻¹ = y⁻¹ * ptI S T * x⁻¹ := by
    apply Matrix.inv_eq_right_inv
    calc x * pt S T * y * (y⁻¹ * ptI S T * x⁻¹)
        = x * (pt S T * ((y * y⁻¹) * ptI S T)) * x⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [mul_inv_one_up hy, Matrix.one_mul, pt_mul_ptI, Matrix.mul_one, mul_inv_one_low hx]
  have hxi := isLowUni_inv K hx
  have hbc : revF S b = c := by rw [← hc, revF_revF]
  rw [hinv, Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [hxi.2 b, mul_one, ptI, mul_mono, hbc, mul_comm]
  · intro k _ hk
    have : k < b := by
      rw [Fin.lt_def]
      have h1 := k.2
      have h2 : k.val ≠ b.val := fun h => hk (Fin.ext h)
      omega
    rw [low_zero hxi this, mul_zero]
  · simp

theorem char_mem_of_annihilator {C : Type} [AddCommGroup C] [Finite C]
    (H : AddSubgroup (AddChar C ℂ)) (χ : AddChar C ℂ)
    (h : ∀ c : C, (∀ η ∈ H, η c = 1) → χ c = 1) : χ ∈ H := by
  by_contra hχ
  have hne : (QuotientAddGroup.mk χ : AddChar C ℂ ⧸ H) ≠ 0 := by
    rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨Φ, hΦ⟩ := AddChar.exists_apply_ne_zero.2 hne
  let Ψ : AddChar (AddChar C ℂ) ℂ := Φ.compAddMonoidHom (QuotientAddGroup.mk' H)
  obtain ⟨c, hc⟩ := AddChar.doubleDualEmb_bijective.2 Ψ
  have hev : ∀ η : AddChar C ℂ, η c = Φ (QuotientAddGroup.mk η) := by
    intro η
    have := DFunLike.congr_fun hc η
    simpa [Ψ] using this
  apply hΦ
  rw [← hev]
  apply h
  intro η hη
  rw [hev, (QuotientAddGroup.eq_zero_iff η).2 hη, AddChar.map_zero_eq_one]

section

variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)

theorem psiKR_mk (hψ : ∀ r ∈ R, ψ r = 1) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a) = ψ a := by
  unfold psiKR
  have h1 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk a : KR R)) : KR R)
      = Submodule.Quotient.mk a := Quotient.out_eq _
  rw [Submodule.Quotient.eq] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 : Quotient.out (Submodule.Quotient.mk a : KR R) = a + (r : K) := by
    have : (r : K) = Quotient.out (Submodule.Quotient.mk a : KR R) - a := hr
    rw [this]; ring
  rw [h2, AddChar.map_add_eq_mul, hψ r r.2, mul_one]

noncomputable def psiB (hψ : ∀ r ∈ R, ψ r = 1) : AddChar (KR R) ℂ where
  toFun := psiKR R ψ
  map_zero_eq_one' := by
    have := psiKR_mk R ψ hψ 0
    rw [AddChar.map_zero_eq_one] at this
    exact this
  map_add_eq_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_add, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ,
      AddChar.map_add_eq_mul]

theorem psiB_sep (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (hψ : ∀ r ∈ R, ψ r = 1)
    (x : KR R) (hx : ∀ r : R, psiB R ψ hψ (r • x) = 1) : x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  have : a ∈ R := by
    rw [← hsd a]
    intro r hr
    have h1 := hx ⟨r, hr⟩
    rw [← Submodule.Quotient.mk_smul] at h1
    have h2 : psiKR R ψ (Submodule.Quotient.mk ((⟨r, hr⟩ : R) • a)) = 1 := h1
    rw [psiKR_mk R ψ hψ] at h2
    rw [mul_comm]
    exact h2
  exact ⟨⟨a, this⟩, rfl⟩

end

theorem dualSpan : DualSpan := by
  intro K _ R ψ hsd C _ _ _ ι _ lam μ hμ
  have hψ : ∀ r ∈ R, ψ r = 1 := fun r hr => by simpa using (hsd 1).2 R.one_mem r hr
  let χ : (C →ₗ[R] KR R) →+ AddChar C ℂ := AddMonoidHom.mk'
    (fun α => (psiB R ψ hψ).compAddMonoidHom α.toAddMonoidHom) (by
      intro α β
      ext c
      simp [AddChar.add_apply, AddChar.map_add_eq_mul])
  have hχ : ∀ α c, χ α c = psiB R ψ hψ (α c) := fun α c => rfl
  let S := Submodule.span R (Set.range lam)
  have hmem : χ μ ∈ S.toAddSubgroup.map χ := by
    apply char_mem_of_annihilator
    intro c hc
    have hz : ∀ α ∈ S, α c = 0 := by
      intro α hα
      apply psiB_sep R ψ hsd hψ
      intro r
      have := hc (χ (r • α)) ⟨r • α, S.smul_mem r hα, rfl⟩
      rwa [hχ] at this
    rw [hχ, hμ c (fun j => hz _ (Submodule.subset_span ⟨j, rfl⟩)), AddChar.map_zero_eq_one]
  obtain ⟨α, hα, hαμ⟩ := hmem
  have : α = μ := by
    ext c
    rw [← sub_eq_zero]
    apply psiB_sep R ψ hsd hψ
    intro r
    have h1 := DFunLike.congr_fun hαμ (r • c)
    rw [hχ, hχ] at h1
    rw [smul_sub, ← map_smul, ← map_smul, AddChar.map_sub_eq_div, h1, div_self]
    exact (AddChar.val_isUnit _ _).ne_zero
  rw [← this]; exact hα

section ColumnOp

variable {K : Type} [CommRing K] {n : ℕ}

theorem colOp_mul (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det) :
    Z * (1 + vecMulVec (Z⁻¹ *ᵥ m) (Pi.single c 1)) = Z + vecMulVec m (Pi.single c 1) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hZ, Matrix.one_mulVec]

theorem colOp_inv (ξ : Fin n → K) (c : Fin n) (hξ : ξ c = 0) :
    (1 + vecMulVec ξ (Pi.single c 1)) * (1 - vecMulVec ξ (Pi.single c 1)) = 1 := by
  have : vecMulVec ξ (Pi.single c (1:K)) * vecMulVec ξ (Pi.single c 1) = 0 := by
    ext a b
    simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, hξ]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, this]; simp

theorem colOp_row (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det)
    (hξ : (Z⁻¹ *ᵥ m) c = 0) (a b : Fin n) :
    (Z + vecMulVec m (Pi.single c 1))⁻¹ a b = Z⁻¹ a b - (Z⁻¹ *ᵥ m) a * Z⁻¹ c b := by
  rw [← colOp_mul Z m c hZ, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (colOp_inv _ c hξ),
    Matrix.sub_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, vecMulVec_apply, Pi.single_apply]

theorem colOp_det (Z : Matrix (Fin n) (Fin n) K) (m : Fin n → K) (c : Fin n) (hZ : IsUnit Z.det)
    (hξ : (Z⁻¹ *ᵥ m) c = 0) : IsUnit (Z + vecMulVec m (Pi.single c 1)).det := by
  rw [← colOp_mul Z m c hZ, Matrix.det_mul]
  exact hZ.mul (Matrix.isUnit_det_of_right_inverse (colOp_inv _ c hξ))

theorem add_single_mulVec (Z : Matrix (Fin n) (Fin n) K) (m y : Fin n → K) (c : Fin n) :
    (Z + vecMulVec m (Pi.single c 1)) *ᵥ y = Z *ᵥ y + y c • m := by
  rw [Matrix.add_mulVec]
  congr 1
  ext a
  simp [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.single_apply, mul_comm]

end ColumnOp

section Triple

variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}

theorem rowN_fin (a : Fin n) (x : Fin n → K) : rowN R a.val x = x a := by
  simp only [rowN, LinearMap.sum_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : ¬ (b.val = a.val) := fun h => hb (Fin.ext h)
    simp [this]
  · simp

theorem rowN_big (j : ℕ) (hj : n ≤ j) : (rowN R j : (Fin n → K) →ₗ[R] K) = 0 := by
  unfold rowN
  apply Finset.sum_eq_zero
  intro a _
  have : a.val ≠ j := by have := a.2; omega
  simp [this]

theorem lamTil_fin (Z : Matrix (Fin n) (Fin n) K) (a : Fin n) (v : Fin n → R) :
    lamTil R Z a.val v = (Z⁻¹ *ᵥ coeLin R v) a := rowN_fin R a _

theorem lamTil_big (Z : Matrix (Fin n) (Fin n) K) (j : ℕ) (hj : n ≤ j) : lamTil R Z j = 0 := by
  simp [lamTil, rowN_big R j hj]

theorem lamN_big (Z : Matrix (Fin n) (Fin n) K) (l : ℕ) (hl : n ≤ l) : lamN R Z l = 0 := by
  simp [lamN, lamTil_big R Z l hl]

theorem lamN_latZ (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (l : ℕ) :
    latZ R Z ≤ LinearMap.ker (lamN R Z l) := by
  intro v hv
  obtain ⟨y, hy⟩ := (mem_latZ R Z v).1 hv
  rw [LinearMap.mem_ker]
  by_cases hl : l < n
  · show Submodule.Quotient.mk (lamTil R Z (⟨l, hl⟩ : Fin n).val v) = 0
    rw [lamTil_fin, ← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hZ, Matrix.one_mulVec,
      Submodule.Quotient.mk_eq_zero, coeLin_apply]
    exact ⟨y ⟨l, hl⟩, rfl⟩
  · rw [lamN_big R Z l (by omega)]; rfl

theorem lamLin_eq (Z : Matrix (Fin n) (Fin n) K) (hn : 0 < n) : lamLin R Z = lamN R Z (n - 1) := by
  unfold lamN lamLin lamTil
  congr 2
  unfold rowN lastCoord
  refine Finset.sum_congr rfl fun a _ => ?_
  have : a.val + 1 = n ↔ a.val = n - 1 := by omega
  simp [this]

theorem smul_coe (r : R) (x : Fin n → K) : r • x = (r : K) • x := rfl

variable {R}

theorem liftRel_sub_smul {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' m m' : Fin n → R} (hv : LiftRel R k Z Z' φ v v') (hm : LiftRel R k Z Z' φ m m') (r : R) :
    LiftRel R k Z Z' φ (v - r • m) (v' - r • m') :=
  ⟨by rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, hv.1, hm.1,
      Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul],
    fun j hj => by rw [map_sub, map_smul, map_sub, map_smul, hv.2 j hj, hm.2 j hj]⟩

theorem liftRel_symm {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' : Fin n → R} (h : LiftRel R k Z Z' φ v v') : LiftRel R k Z' Z φ.symm v' v :=
  ⟨by rw [← h.1, φ.symm_apply_apply], fun j hj => (h.2 j hj).symm⟩

theorem liftRel_symm' {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    {v v' : Fin n → R} (h : LiftRel R k Z' Z φ.symm v' v) : LiftRel R k Z Z' φ v v' :=
  ⟨by rw [← h.1, φ.apply_symm_apply], fun j hj => (h.2 j hj).symm⟩

theorem inTTeq_symm {k : ℕ} {Z Z' : Matrix (Fin n) (Fin n) K} {φ : coker R Z ≃ₗ[R] coker R Z'}
    (h : InTTeq R k Z Z' φ) : InTTeq R k Z' Z φ.symm := by
  intro j hk hj v' v hv
  exact (h j hk hj v v' (by rw [← hv, φ.apply_symm_apply])).symm

variable (R)

def liftSub (k : ℕ) (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') :
    Submodule R ((Fin n → R) × (Fin n → R)) where
  carrier := {p | LiftRel R k Z Z' φ p.1 p.2}
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp only [Prod.fst_add, Prod.snd_add, Submodule.Quotient.mk_add, map_add, h1, h3],
      fun j hj => by simp only [Prod.fst_add, Prod.snd_add, map_add, h2 j hj, h4 j hj]⟩
  zero_mem' := ⟨by simp, fun j _ => by simp⟩
  smul_mem' := by
    rintro r p ⟨h1, h2⟩
    exact ⟨by simp only [Prod.smul_fst, Prod.smul_snd, Submodule.Quotient.mk_smul, map_smul, h1],
      fun j hj => by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, h2 j hj]⟩

theorem exists_lift (Z Z' : Matrix (Fin n) (Fin n) K) (hZ' : IsInt R Z') (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (k : ℕ) (hT : InTTeq R k Z Z' φ) (v : Fin n → R) :
    ∃ v', LiftRel R k Z Z' φ v v' := by
  obtain ⟨v0, hv0⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
  have h1 : ∀ a : Fin n, ∃ r : R, k ≤ a.val →
      (r : K) = lamTil R Z' a.val v0 - lamTil R Z a.val v := by
    intro a
    by_cases hk : k ≤ a.val
    · have := hT a.val hk a.2 v v0 hv0.symm
      simp only [lamN, LinearMap.comp_apply, Submodule.mkQ_apply] at this
      rw [Submodule.Quotient.eq] at this
      obtain ⟨r, hr⟩ := this
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose ρ hρ using h1
  let z : Fin n → R := liftR R Z' hZ' *ᵥ ρ
  have hz : coeLin R z = Z' *ᵥ coeLin R ρ := by rw [coeLin_mulVec, liftR_map]
  refine ⟨v0 - z, ?_, ?_⟩
  · rw [Submodule.Quotient.mk_sub, hv0]
    have : (Submodule.Quotient.mk z : coker R Z') = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, mem_latZ]; exact ⟨ρ, hz.symm⟩
    rw [this, sub_zero]
  · intro j hj
    by_cases hjn : j < n
    · have e := lamTil_fin R Z' ⟨j, hjn⟩ z
      rw [hz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd', Matrix.one_mulVec,
        coeLin_apply] at e
      have h2 := hρ ⟨j, hjn⟩ hj
      simp only at e h2
      rw [map_sub, e, h2]; ring
    · rw [lamTil_big R Z' j (by omega), lamTil_big R Z j (by omega)]; rfl

theorem lin_lift (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') (k : ℕ)
    (h : ∀ v, ∃ v', LiftRel R k Z Z' φ v v') :
    ∃ F : (Fin n → R) →ₗ[R] (Fin n → R), ∀ v, LiftRel R k Z Z' φ v (F v) := by
  let Γ := liftSub R k Z Z' φ
  let f : Γ →ₗ[R] (Fin n → R) := (LinearMap.fst R _ _).comp Γ.subtype
  have hf : Function.Surjective f := fun v => by
    obtain ⟨v', h'⟩ := h v
    exact ⟨⟨(v, v'), h'⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨(LinearMap.snd R _ _).comp (Γ.subtype.comp s), fun v => ?_⟩
  have h1 : ((s v : Γ) : (Fin n → R) × (Fin n → R)).1 = v := LinearMap.congr_fun hs v
  have h2 : LiftRel R k Z Z' φ ((s v : Γ) : (Fin n → R) × (Fin n → R)).1
      ((s v : Γ) : (Fin n → R) × (Fin n → R)).2 := (s v).2
  rw [h1] at h2
  exact h2

theorem lift_lat (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (hv : LiftRel R c.val Z Z' φ v v')
    (hl : v ∈ latZ R (Z + vecMulVec (coeLin R m) (Pi.single c 1))) :
    v' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by
  rw [mem_latZ] at hl ⊢
  obtain ⟨y, hy⟩ := hl
  rw [add_single_mulVec] at hy
  have hw := liftRel_sub_smul hv hm (y c)
  have e1 : coeLin R (v - y c • m) = Z *ᵥ coeLin R y := by
    rw [map_sub, map_smul, ← hy, smul_coe, coeLin_apply]; abel
  have hmk : (Submodule.Quotient.mk (v - y c • m) : coker R Z) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_latZ]; exact ⟨y, e1.symm⟩
  have h0 : (Submodule.Quotient.mk (v' - y c • m') : coker R Z') = 0 := by
    rw [← hw.1, hmk, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, mem_latZ] at h0
  obtain ⟨y', hy'⟩ := h0
  have e2 := hw.2 c.val le_rfl
  rw [lamTil_fin, lamTil_fin, e1, ← hy', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd',
    Matrix.one_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec] at e2
  refine ⟨y', ?_⟩
  rw [add_single_mulVec, hy', e2, map_sub, map_smul, smul_coe, coeLin_apply]; abel

theorem uniq_lat (Z Z' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (hd' : IsUnit Z'.det)
    (φ : coker R Z ≃ₗ[R] coker R Z') (c : Fin n) (m m' v v' v'' : Fin n → R)
    (hm : LiftRel R c.val Z Z' φ m m') (h1 : LiftRel R c.val Z Z' φ v v')
    (h2 : LiftRel R c.val Z Z' φ v v'') :
    v' - v'' ∈ latZ R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) := by
  have h := liftRel_sub_smul h1 h2 1
  rw [one_smul, one_smul, sub_self] at h
  exact lift_lat R Z Z' hd hd' φ c m m' 0 _ hm h (Submodule.zero_mem _)

theorem lamTil_colOp (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R) (c : Fin n)
    (hm : ∀ j, c.val ≤ j → lamTil R Z j m = 0) (j : ℕ) (hj : c.val ≤ j) :
    lamTil R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) j = lamTil R Z j := by
  by_cases hjn : j < n
  · apply LinearMap.ext
    intro v
    have hc : (Z⁻¹ *ᵥ coeLin R m) c = 0 := by rw [← lamTil_fin]; exact hm _ le_rfl
    have hjj : (Z⁻¹ *ᵥ coeLin R m) ⟨j, hjn⟩ = 0 := by rw [← lamTil_fin]; exact hm _ hj
    have e1 := lamTil_fin R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) ⟨j, hjn⟩ v
    have e2 := lamTil_fin R Z ⟨j, hjn⟩ v
    simp only at e1 e2
    rw [e1, e2]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [colOp_row Z _ c hd hc, hjj, zero_mul, sub_zero]
  · rw [lamTil_big R _ j (by omega), lamTil_big R _ j (by omega)]

end Triple

theorem lamTil_eLast {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) K) (a b : Fin n) (hb : b.val + 1 = n) :
    lamTil R Z a.val (eLast R) = Z⁻¹ a b := by
  rw [lamTil_fin]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single b]
  · simp [coeLin_apply, eLast, hb]
  · intro c _ hc
    have : ¬ (c.val + 1 = n) := fun h => hc (Fin.ext (by omega))
    simp [coeLin_apply, eLast, this]
  · simp

end Formalism.FourierDecayAlt.P.A5x2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase

theorem inverse_last_column_formula : Formalism.FourierDecayAlt.A5.InvLastCol := by
  intro K _ h s t hs x y hx hy a b c hb hc
  have hsum : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hrc : revF (addBlock h s t).1 c = b := by
    apply Fin.ext
    rw [revF_val, hc]
    show revIn (h.1 ++ [s]) h.1.sum = b.val
    rw [revIn_app _ _ hs]; omega
  have hblk : (addBlock h s t).2 (blk (addBlock h s t).1 c) = t := by
    rw [hc]
    show Function.update h.2 h.1.length t (blk (h.1 ++ [s]) h.1.sum) = t
    rw [blk_app _ _ hs, Function.update_self]
  have hyi := isUpUni_inv K hy
  have key : ∀ a', (x * pt (addBlock h s t).1 (addBlock h s t).2 * y)⁻¹ a' b
      = ((t⁻¹ : Kˣ) : K) * y⁻¹ a' c := by
    intro a'
    rw [inv_last _ _ x y hx hy a' b c hb hrc, hblk]
  refine ⟨key a, fun hca => ?_, ?_⟩
  · rw [key a, up_zero hyi hca, mul_zero]
  · rw [key c, hyi.2 c, mul_one]

theorem triple_form_end_identity : Formalism.FourierDecayAlt.A5.TTEnd := by
  have H := inverse_last_column_formula
  intro K _ R h h' s t t' hs h1 x y x' y' hx hy hx' hy' φ hφ hT
  have hn : (addBlock h s t).1.sum = h.1.sum + s := by simp [addBlock]
  have hn' : (addBlock h' s t').1.sum = h'.1.sum + s := by simp [addBlock]
  obtain ⟨a, ha⟩ := hT h.1.sum le_rfl (by omega)
  have e := ha (eLast R) (eLast R) hφ.1
  let c : Fin (addBlock h s t).1.sum := ⟨h.1.sum, by omega⟩
  let b : Fin (addBlock h s t).1.sum := ⟨h.1.sum + s - 1, by omega⟩
  let c' : Fin (addBlock h' s t').1.sum := ⟨h.1.sum, by omega⟩
  let b' : Fin (addBlock h' s t').1.sum := ⟨h.1.sum + s - 1, by omega⟩
  have hb : b.val + 1 = (addBlock h s t).1.sum := by simp only [b]; omega
  have hb' : b'.val + 1 = (addBlock h' s t').1.sum := by simp only [b']; omega
  have A := (H K h s t h1 x y hx hy c b c hb rfl).2.2
  have A' := (H K h' s t' h1 x' y' hx' hy' c' b' c' hb' hs).2.2
  have z : ∑ l ∈ Finset.Ioo h.1.sum (addBlock h s t).1.sum,
      a l • lamN R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) l (eLast R) = 0 := by
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_Ioo] at hl
    have B := (H K h s t h1 x y hx hy ⟨l, hl.2⟩ b c hb rfl).2.1
      (by simpa [c, Fin.lt_def] using hl.1)
    have := lamTil_eLast R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) ⟨l, hl.2⟩ b hb
    simp only [lamN, LinearMap.comp_apply]
    rw [this, B]; simp
  rw [z, add_zero] at e
  have E := lamTil_eLast R (x * pt (addBlock h s t).1 (addBlock h s t).2 * y) c b hb
  have E' := lamTil_eLast R (x' * pt (addBlock h' s t').1 (addBlock h' s t').2 * y') c' b' hb'
  simp only [lamN, LinearMap.comp_apply] at e
  rw [show h.1.sum = c.val from rfl, E, A] at e
  rw [show c.val = c'.val from rfl, E', A'] at e
  have := (Submodule.Quotient.eq _).1 e.symm
  obtain ⟨r, hr⟩ := this
  rw [← hr]; exact r.2

theorem column_operation_row_form : Formalism.FourierDecayAlt.A5.ColOpRow := by
  intro K _ n Z m c hZ hξ a b
  exact colOp_row Z m c hZ (hξ c le_rfl) a b

theorem column_operation_identity : Formalism.FourierDecayAlt.A5.ColOp := by
  intro K _ n Z u m c r hZ hu hrc hξ
  have hU := colOp_mul Z m c hZ
  set ξ := Z⁻¹ *ᵥ m with hξd
  refine ⟨⟨?_, ?_⟩, hU, ?_, ?_⟩
  · intro a b hab
    have hab' : b < a := hab
    by_cases hb : b = c
    · subst hb; simp [vecMulVec_apply, hξ a hab'.le, hab'.ne']
    · simp [vecMulVec_apply, hb, hab'.ne']
  · intro a
    by_cases ha : a = c
    · subst ha; simp [vecMulVec_apply, hξ a le_rfl]
    · simp [vecMulVec_apply, ha]
  · intro a b hca
    rw [colOp_row Z m c hZ (hξ c le_rfl), ← hξd, hξ a hca, zero_mul, sub_zero]
  · have e1 : u * (1 + vecMulVec ξ (Pi.single c 1)) = u + vecMulVec (u *ᵥ ξ) (Pi.single c 1) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec]
    have e2 : (u *ᵥ ξ) r = ξ r := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single r]
      · simp [hu.2 r]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have : u r b = 0 := hu.1 (by simpa using h)
          simp [this]
        · have : c ≤ b := by rw [Fin.le_def]; have := Fin.lt_def.1 h; omega
          simp [hξ b this]
      · simp
    rw [e1]
    unfold sUp
    have : ∀ j : Fin n, (if h : j.val + 1 < n then
        (u + vecMulVec (u *ᵥ ξ) (Pi.single c 1)) j ⟨j.val + 1, h⟩ else 0) =
        (if h : j.val + 1 < n then u j ⟨j.val + 1, h⟩ else 0) + (if j = r then ξ r else 0) := by
      intro j
      by_cases h : j.val + 1 < n
      · by_cases hj : j = r
        · subst hj
          have : (⟨j.val + 1, h⟩ : Fin n) = c := Fin.ext hrc
          simp [h, vecMulVec_apply, this, e2]
        · have : (⟨j.val + 1, h⟩ : Fin n) ≠ c := fun hh => hj (Fin.ext (by
            have := congrArg Fin.val hh; simp at this; omega))
          simp [h, vecMulVec_apply, this, hj]
      · have hj : j ≠ r := fun hh => h (by rw [hh, hrc]; exact c.2)
        simp [h, hj]
    simp only [this, Finset.sum_add_distrib]
    simp

theorem column_operation_triple_form : Formalism.FourierDecayAlt.A5.ColOpTriple := by
  intro K _ R n Z Z' hZ hZ' hd hd' φ hφ c hT he m m' hm hm0
  have hm0' : ∀ j, c.val ≤ j → lamTil R Z' j m' = 0 := fun j hj => by rw [hm.2 j hj, hm0 j hj]
  have hc : (Z⁻¹ *ᵥ coeLin R m) c = 0 := by rw [← lamTil_fin]; exact hm0 _ le_rfl
  have hc' : (Z'⁻¹ *ᵥ coeLin R m') c = 0 := by rw [← lamTil_fin]; exact hm0' _ le_rfl
  have hd1' := colOp_det Z' (coeLin R m') c hd' hc'
  obtain ⟨F, hF⟩ := lin_lift R Z Z' φ c.val (exists_lift R Z Z' hZ' hd' φ c.val hT)
  obtain ⟨G, hG⟩ := lin_lift R Z' Z φ.symm c.val
    (exists_lift R Z' Z hZ hd φ.symm c.val (inTTeq_symm hT))
  have hms := liftRel_symm hm
  let φn : coker R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) ≃ₗ[R]
      coker R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) :=
    LinearEquiv.ofLinearMap
      (Submodule.mapQ _ _ F (fun v hv => lift_lat R Z Z' hd hd' φ c m m' v (F v) hm (hF v) hv))
      (Submodule.mapQ _ _ G
        (fun v hv => lift_lat R Z' Z hd' hd φ.symm c m' m v (G v) hms (hG v) hv))
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show Submodule.Quotient.mk (F (G v)) = Submodule.Quotient.mk v
        rw [Submodule.Quotient.eq]
        exact uniq_lat R Z Z' hd hd' φ c m m' (G v) _ _ hm (hF _) (liftRel_symm' (hG v)))
      (by
        apply LinearMap.ext
        intro x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        show Submodule.Quotient.mk (G (F v)) = Submodule.Quotient.mk v
        rw [Submodule.Quotient.eq]
        exact uniq_lat R Z' Z hd' hd φ.symm c m' m (F v) _ _ hms (hG _) (liftRel_symm (hF v)))
  have hφn : ∀ v v', LiftRel R c.val Z Z' φ v v' →
      φn (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
    intro v v' h
    show Submodule.Quotient.mk (F v) = Submodule.Quotient.mk v'
    rw [Submodule.Quotient.eq]
    exact uniq_lat R Z Z' hd hd' φ c m m' v _ _ hm (hF v) h
  have hlam : ∀ j, c.val ≤ j → ∀ v v', φn (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
      lamN R (Z' + vecMulVec (coeLin R m') (Pi.single c 1)) j v' =
        lamN R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) j v := by
    intro j hj v v' h
    have h1 : (Submodule.Quotient.mk (F v) :
        coker R (Z' + vecMulVec (coeLin R m') (Pi.single c 1))) = Submodule.Quotient.mk v' := h
    rw [Submodule.Quotient.eq] at h1
    have h2 := lamN_latZ R _ hd1' j h1
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    rw [← h2]
    simp only [lamN, LinearMap.comp_apply]
    rw [lamTil_colOp R Z hd m c hm0 j hj, lamTil_colOp R Z' hd' m' c hm0' j hj, (hF v).2 j hj]
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) c.2
  refine ⟨φn, ⟨hφn _ _ he, fun v v' h => ?_⟩, fun j hj _ v v' h => hlam j hj v v' h, hφn⟩
  rw [lamLin_eq R _ hn, lamLin_eq R _ hn]
  exact hlam (n - 1) (by have := c.2; omega) v v' h

theorem triple_form_recursion : Formalism.FourierDecayAlt.A5.TTStep := by
  have hD := dualSpan
  intro K _ R ψ hsd n Z Z' hZ hZ' hfin φ k hk hT
  constructor
  · intro h v v' hv hker
    obtain ⟨a, ha⟩ := h k le_rfl hk
    rw [ha v v' hv]
    have : ∑ l ∈ Finset.Ioo k n, a l • lamN R Z l v = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      rw [hker l (Finset.mem_Ioo.1 hl).1, smul_zero]
    rw [this, add_zero]
  · intro h j hkj hjn
    by_cases hjk : j = k
    swap
    · exact hT j (by omega) hjn
    subst hjk
    let lamC : ℕ → coker R Z →ₗ[R] KR R :=
      fun l => (latZ R Z).liftQ (lamN R Z l) (lamN_latZ R Z hZ l)
    let lamC' : coker R Z' →ₗ[R] KR R := (latZ R Z').liftQ (lamN R Z' j) (lamN_latZ R Z' hZ' j)
    let μ : coker R Z →ₗ[R] KR R := lamC'.comp φ.toLinearMap - lamC j
    have hμ := hD K R ψ hsd (coker R Z) {l // l ∈ Finset.Ioo j n} (fun l => lamC l.1) μ (by
      intro c hc
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨v', hv'⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk v))
      have := h v v' hv'.symm (by
        intro l hl
        by_cases hln : l < n
        · exact hc ⟨l, Finset.mem_Ioo.2 ⟨hl, hln⟩⟩
        · rw [lamN_big R Z l (by omega)]; rfl)
      show lamC' (φ (Submodule.Quotient.mk v)) - lamC j (Submodule.Quotient.mk v) = 0
      rw [← hv']
      show lamN R Z' j v' - lamN R Z j v = 0
      rw [this, sub_self])
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hμ
    classical
    refine ⟨fun l => if hl : l ∈ Finset.Ioo j n then cf ⟨l, hl⟩ else 0, ?_⟩
    intro v v' hv
    have e1 := congrArg (fun f : coker R Z →ₗ[R] KR R => f (Submodule.Quotient.mk v)) hcf
    simp only [LinearMap.sum_apply, LinearMap.smul_apply] at e1
    have e2 : μ (Submodule.Quotient.mk v) = lamN R Z' j v' - lamN R Z j v := by
      show lamC' (φ (Submodule.Quotient.mk v)) - lamC j (Submodule.Quotient.mk v) = _
      rw [hv]; rfl
    rw [e2] at e1
    rw [← Finset.sum_attach]
    have e3 : ∑ x ∈ (Finset.Ioo j n).attach,
        (if hl : x.1 ∈ Finset.Ioo j n then cf ⟨x.1, hl⟩ else 0) • lamN R Z x.1 v =
        ∑ x : {l // l ∈ Finset.Ioo j n}, cf x • lamC x.1 (Submodule.Quotient.mk v) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [dif_pos x.2]; rfl
    rw [e3, e1]; abel

end Formalism.FourierDecayAlt.P
