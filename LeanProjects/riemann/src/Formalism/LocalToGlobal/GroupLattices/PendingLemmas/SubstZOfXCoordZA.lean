import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset
open scoped Kronecker Matrix

noncomputable section

namespace Formalism.L2.G.Pend

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem rank_eq (j : ℕ) : (X.Fl.Pj j).m + 1 = NN X.G.P.m X.Fl.t j := by
  cases j with
  | zero => simp [Fills.Pj, NN]
  | succ j => simp only [Fills.Pj, Places.withWt, NN]; omega

structure Frm (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) where
  g : ∀ v : X.Pl, GL (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)
  g' : ∀ v : X.Pl, GL (Fin ((X.Pj (j + 1)).m + 1)) (X.G.P.Qq v)
  hg : ∀ v, X.latAt v j La.2 = colSpan (X.G.P.W v) (g v : Matrix _ _ (X.G.P.Qq v))
  hg' : ∀ v, X.latAt v (j + 1) La'.2 = colSpan (X.G.P.W v) (g' v : Matrix _ _ (X.G.P.Qq v))

variable (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc]

def tw (v : X.Pl) (s : Fin (X.G.P.n' v)) : X.G.P.Qq v →+* Kc :=
  (algebraMap X.G.Kf Kc).comp ((X.G.P.ι v).comp (X.G.P.σ v ^ s.val : X.G.P.Qq v ≃+* X.G.P.Qq v).toRingHom)

def mAt (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (A : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  (A.map (tw X Kc v s)).submatrix (finCongr (rank_eq X j).symm) (finCongr (rank_eq X j).symm)

theorem mAt_mul (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v))
    (A B : Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v)) :
    mAt X Kc j v s A * mAt X Kc j v s B = mAt X Kc j v s (A * B) := by
  unfold mAt
  rw [Matrix.submatrix_mul_equiv, Matrix.map_mul]

theorem mAt_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) : mAt X Kc j v s 1 = 1 := by
  unfold mAt
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]

variable {X} {j : ℕ} {La : X.Lt j} {La' : X.Lt (j + 1)} (φ : Frm X j La La')

def Pf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  if IsOddPos s then mAt X Kc j v s ((φ.g v)⁻¹ : GL _ _) else (mAt X Kc j v s (φ.g v))ᵀ

def Pi (v : X.Pl) (s : Fin (X.G.P.n' v)) : Matrix (Fin (NN X.G.P.m X.t j)) (Fin (NN X.G.P.m X.t j)) Kc :=
  if IsOddPos s then mAt X Kc j v s (φ.g v) else (mAt X Kc j v s ((φ.g v)⁻¹ : GL _ _))ᵀ

def Qf (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then (mAt X Kc (j + 1) v s (φ.g' v))ᵀ else mAt X Kc (j + 1) v s ((φ.g' v)⁻¹ : GL _ _)

def Qi (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    Matrix (Fin (NN X.G.P.m X.t (j + 1))) (Fin (NN X.G.P.m X.t (j + 1))) Kc :=
  if IsOddPos s then (mAt X Kc (j + 1) v s ((φ.g' v)⁻¹ : GL _ _))ᵀ else mAt X Kc (j + 1) v s (φ.g' v)

def linF : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pf Kc φ v s ⊗ₖ Qf Kc φ v s) ab ab') * MvPowerSeries.X ⟨v, (s, ab')⟩

def linI : X.ZA j → MvPowerSeries (X.ZA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pi Kc φ v s ⊗ₖ Qi Kc φ v s) ab ab') * MvPowerSeries.X ⟨v, (s, ab')⟩

def bc (z z' : X.ZA j) : Kc := MvPowerSeries.coeff (Finsupp.single z' 1) (linF Kc φ z)

variable (X) in

def zOfX (j : ℕ) : X.ZA j → MvPowerSeries (X.EA j ⊕ X.EA j) Kc
  | ⟨v, (s, a, b)⟩ =>
    if IsOddPos s then ∑ r : Fin (X.G.P.n' v / 2),
      MvPowerSeries.C (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).omS r)))) *
        MvPowerSeries.X (Sum.inr ⟨v, (r, a, b)⟩)
    else ∑ r : Fin (X.G.P.n' v / 2),
      MvPowerSeries.C (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om r)))) *
        MvPowerSeries.X (Sum.inl ⟨v, (r, a, b)⟩)

def invF : X.ZA j → MvPowerSeries (X.EA j ⊕ X.EA j) Kc
  | ⟨v, (s, ab)⟩ => ∑ ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1)),
      MvPowerSeries.C ((Pi Kc φ v s ⊗ₖ Qi Kc φ v s) ab ab') * zOfX X Kc j ⟨v, (s, ab')⟩

def thA (F : MvPowerSeries (X.ZA j) Kc) : MvPowerSeries (X.EA j ⊕ X.EA j) Kc :=
  MvPowerSeries.subst (invF Kc φ) F

section Lin

variable {K : Type*} [Field K]

theorem sum_lin {ι M : Type*} [Fintype ι] [CommRing M] (c : K →+* M) (A B : Matrix ι ι K) (x : ι → M)
    (i : ι) : ∑ y, c (A i y) * ∑ w, c (B y w) * x w = ∑ w, c ((A * B) i w) * x w := by
  simp only [Finset.mul_sum, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sum_one {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommRing M] (c : K →+* M) (x : ι → M) (i : ι) :
    ∑ w, c ((1 : Matrix ι ι K) i w) * x w = x i := by
  simp [Matrix.one_apply, apply_ite c, ite_mul]

theorem lin_repr {σ ι : Type*} [Fintype σ] [Fintype ι] (k : ι → K) (e : ι → σ) :
    ∑ y, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single y 1)
        (∑ i, MvPowerSeries.C (k i) * MvPowerSeries.X (e i) : MvPowerSeries σ K)) * MvPowerSeries.X y =
      ∑ i, MvPowerSeries.C (k i) * MvPowerSeries.X (e i) := by
  classical
  simp only [map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro y _ hy
    simp [hy]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem subst_lin {σ τ ι : Type*} [Fintype ι] {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (k : ι → K) (f : ι → MvPowerSeries σ K) :
    MvPowerSeries.subst a (∑ i, MvPowerSeries.C (k i) * f i) =
      ∑ i, MvPowerSeries.C (k i) * MvPowerSeries.subst a (f i) := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

end Lin

section Dual

variable {n' : ℕ} (B : OmBasis p n')

theorem dual' (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  let A : Matrix (Fin (n' / 2)) (Fin (n' / 2)) (WW p) := fun r i => (sigW p)^[2 * i.val] (B.om r)
  let Bm : Matrix (Fin (n' / 2)) (Fin (n' / 2)) (WW p) := fun i r => (sigW p)^[2 * i.val] (B.omS r)
  have h1 : A * Bm = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    apply Finset.sum_congr rfl
    intro i _
    exact (iterate_map_mul (sigW p) _ _ _).symm
  have h2 : Bm * A = 1 := mul_eq_one_comm.1 h1
  have h3 := congrFun (congrFun h2 i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h3
  exact h3

theorem dualS (he : Even n') (s s' : Fin n') (hp : s.val % 2 = s'.val % 2) :
    ∑ r, (sigW p)^[s.val] (B.omS r) * (sigW p)^[s'.val] (B.om r) = if s = s' then 1 else 0 := by
  obtain ⟨h, rfl⟩ := he
  have hs := s.isLt
  have hs' := s'.isLt
  let i : Fin ((h + h) / 2) := ⟨s.val / 2, by omega⟩
  let i' : Fin ((h + h) / 2) := ⟨s'.val / 2, by omega⟩
  have e1 : s.val = s.val % 2 + 2 * i.val := by show s.val = s.val % 2 + 2 * (s.val / 2); omega
  have e2 : s'.val = s.val % 2 + 2 * i'.val := by show s'.val = s.val % 2 + 2 * (s'.val / 2); omega
  have h0 := congrArg ((sigW p)^[s.val % 2]) (dual' B i i')
  rw [← RingHom.coe_pow, map_sum] at h0
  simp only [map_mul] at h0
  rw [RingHom.coe_pow] at h0
  simp only [← Function.iterate_add_apply, ← e1, ← e2] at h0
  rw [h0, ← RingHom.coe_pow, apply_ite (⇑((sigW p) ^ (s.val % 2))), map_one, map_zero]
  have : (i = i') ↔ (s = s') := by
    rw [Fin.ext_iff, Fin.ext_iff]
    show s.val / 2 = s'.val / 2 ↔ _
    omega
  simp only [this]

theorem dualK (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (he : Even n') (s s' : Fin n')
    (hp : s.val % 2 = s'.val % 2) :
    ∑ r, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.omS r))) *
      algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s'.val] (B.om r))) = if s = s' then 1 else 0 := by
  simp only [← map_mul, ← map_sum]
  rw [dualS B he s s' hp]
  split_ifs <;> simp

end Dual

section Main

variable {X : Sys p} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ} {La : X.Lt j}
  {La' : X.Lt (j + 1)} (φ : Frm X j La La')

theorem Pi_mul_Pf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Pi Kc φ v s * Pf Kc φ v s = 1 := by
  unfold Pi Pf
  split_ifs
  · rw [mAt_mul, Units.mul_inv, mAt_one]
  · rw [← Matrix.transpose_mul, mAt_mul, Units.mul_inv, mAt_one, Matrix.transpose_one]

theorem Qi_mul_Qf (v : X.Pl) (s : Fin (X.G.P.n' v)) : Qi Kc φ v s * Qf Kc φ v s = 1 := by
  unfold Qi Qf
  split_ifs
  · rw [← Matrix.transpose_mul, mAt_mul, Units.mul_inv, mAt_one, Matrix.transpose_one]
  · rw [mAt_mul, Units.mul_inv, mAt_one]

theorem kron_inv (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (Pi Kc φ v s ⊗ₖ Qi Kc φ v s) * (Pf Kc φ v s ⊗ₖ Qf Kc φ v s) = 1 := by
  rw [← Matrix.mul_kronecker_mul, Pi_mul_Pf, Qi_mul_Qf, Matrix.one_kronecker_one]

theorem hasSubst_linF : MvPowerSeries.HasSubst (linF Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [linF]

theorem hasSubst_linI : MvPowerSeries.HasSubst (linI Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [linI]

theorem hasSubst_coordZA : MvPowerSeries.HasSubst (X.coordZA Kc j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun e => by
    rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA]

theorem constantCoeff_zOfX (z : X.ZA j) : MvPowerSeries.constantCoeff (zOfX X Kc j z) = 0 := by
  obtain ⟨v, s, a, b⟩ := z
  simp only [zOfX]
  split_ifs <;> simp

theorem hasSubst_invF : MvPowerSeries.HasSubst (invF Kc φ) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun ⟨v, (s, ab)⟩ => by simp [invF, constantCoeff_zOfX]

theorem bc_lin (z : X.ZA j) :
    ∑ y, MvPowerSeries.C (bc Kc φ z y) * MvPowerSeries.X y = linF Kc φ z := by
  obtain ⟨v, s, ab⟩ := z
  exact lin_repr _ _

theorem subst_linF_linI (z : X.ZA j) :
    MvPowerSeries.subst (linF Kc φ) (linI Kc φ z) = MvPowerSeries.X z := by
  obtain ⟨v, s, ab⟩ := z
  simp only [linI]
  rw [subst_lin (hasSubst_linF Kc φ)]
  simp only [MvPowerSeries.subst_X (hasSubst_linF Kc φ), linF]
  rw [sum_lin (MvPowerSeries.C) _ _ (fun ab' => (MvPowerSeries.X ⟨v, (s, ab')⟩ : MvPowerSeries (X.ZA j) Kc)), kron_inv,
    sum_one]

theorem subst_coordZA_zOfX (z : X.ZA j) :
    MvPowerSeries.subst (X.coordZA Kc j) (zOfX X Kc j z) = MvPowerSeries.X z := by
  obtain ⟨v, s, a, b⟩ := z
  have he : Even (X.G.P.n' v) := (X.G.P.setting v).even
  simp only [zOfX]
  split_ifs with h
  · rw [subst_lin (hasSubst_coordZA Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_coordZA Kc), Sys.coordZA, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single_of_mem s (by simp [h])]
    · simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      rw [dualK (X.om v) Kc he s s rfl]
      simp
    · intro s' hs' hne
      have hs'' : IsOddPos s' := (Finset.mem_filter.1 hs').2
      simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      rw [dualK (X.om v) Kc he s s' (by rw [show s.val % 2 = 1 from h, show s'.val % 2 = 1 from hs''])]
      simp [Ne.symm hne]
  · rw [subst_lin (hasSubst_coordZA Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_coordZA Kc), Sys.coordZA, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_eq_single_of_mem s (by simp [h])]
    · simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [mul_comm (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om _))))]
      rw [dualK (X.om v) Kc he s s rfl]
      simp
    · intro s' hs' hne
      have hs'' : ¬ IsOddPos s' := (Finset.mem_filter.1 hs').2
      have h1 : s.val % 2 = 0 := by have : ¬ s.val % 2 = 1 := h; omega
      have h2 : s'.val % 2 = 0 := by have : ¬ s'.val % 2 = 1 := hs''; omega
      simp only [← mul_assoc, ← map_mul MvPowerSeries.C, ← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [mul_comm (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om _))))]
      rw [dualK (X.om v) Kc he s' s (by rw [h1, h2])]
      simp [hne]

theorem subst_coordZA_invF (z : X.ZA j) :
    MvPowerSeries.subst (X.coordZA Kc j) (invF Kc φ z) = linI Kc φ z := by
  obtain ⟨v, s, ab⟩ := z
  simp only [invF, linI]
  rw [subst_lin (hasSubst_coordZA Kc)]
  simp only [subst_coordZA_zOfX]

theorem thF_frm (F : MvPowerSeries (X.ZA j) Kc) :
    F = linSub (bc Kc φ) (X.ThZA Kc j (thA Kc φ F)) := by
  unfold linSub Sys.ThZA thA
  simp only [bc_lin]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_invF Kc φ) (hasSubst_coordZA Kc)]
  simp only [subst_coordZA_invF]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_linI Kc φ) (hasSubst_linF Kc φ)]
  simp only [subst_linF_linI]
  exact (congrFun MvPowerSeries.subst_self F).symm

end Main

section Ex

variable (X : Sys p)

theorem latAt_isLattice (j : ℕ) (L : (X.Pj j).Tup) (hL : (X.Pj j).IsLatTup L) (v : X.Pl) :
    IsLattice (X.G.P.W v) (X.latAt v j L) := by
  cases j with
  | zero => exact hL v
  | succ j => exact hL v

theorem exists_frm (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (h : (X.Pj j).IsLatTup La.2)
    (h' : (X.Pj (j + 1)).IsLatTup La'.2) : Nonempty (Frm X j La La') := by
  choose g hg1 hg2 using latAt_isLattice X j La.2 h
  choose g' hg1' hg2' using latAt_isLattice X (j + 1) La'.2 h'
  exact ⟨⟨fun v => Matrix.nonsingInvUnit (g v) (hg1 v), fun v => Matrix.nonsingInvUnit (g' v) (hg1' v), hg2, hg2'⟩⟩

end Ex

section Uniq

theorem subst_linS {K σ τ ι : Type*} [Field K] {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (t : Finset ι) (k : ι → K) (f : ι → MvPowerSeries σ K) :
    MvPowerSeries.subst a (∑ i ∈ t, MvPowerSeries.C (k i) * f i) =
      ∑ i ∈ t, MvPowerSeries.C (k i) * MvPowerSeries.subst a (f i) := by
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

theorem sum_parity {M : Type*} [AddCommMonoid M] {n' : ℕ} (he : Even n') (ε : ℕ) (hε : ε < 2)
    (P : Fin n' → Prop) [DecidablePred P] (hP : ∀ s, P s ↔ s.val % 2 = ε) (f : ℕ → M) :
    ∑ s ∈ univ.filter P, f s.val = ∑ i : Fin (n' / 2), f (ε + 2 * i.val) := by
  obtain ⟨h, rfl⟩ := he
  refine Finset.sum_bij' (fun s _ => (⟨s.val / 2, by have := s.isLt; omega⟩ : Fin ((h + h) / 2)))
    (fun i _ => (⟨ε + 2 * i.val, by have := i.isLt; omega⟩ : Fin (h + h))) ?_ ?_ ?_ ?_ ?_
  · intro s _
    exact Finset.mem_univ _
  · intro i _
    rw [Finset.mem_filter, hP]
    exact ⟨Finset.mem_univ _, by show (ε + 2 * i.val) % 2 = ε; omega⟩
  · intro s hs
    have := (hP s).1 (Finset.mem_filter.1 hs).2
    apply Fin.ext
    show ε + 2 * (s.val / 2) = s.val
    omega
  · intro i _
    apply Fin.ext
    show (ε + 2 * i.val) / 2 = i.val
    omega
  · intro s hs
    have := (hP s).1 (Finset.mem_filter.1 hs).2
    congr 1
    show s.val = ε + 2 * (s.val / 2)
    omega

theorem dualT {n' : ℕ} (B : OmBasis p n') (he : Even n') (ε : ℕ) (hε : ε < 2) (P : Fin n' → Prop) [DecidablePred P]
    (hP : ∀ s, P s ↔ s.val % 2 = ε) (r r' : Fin (n' / 2)) :
    ∑ s ∈ univ.filter P, (sigW p)^[s.val] (B.om r) * (sigW p)^[s.val] (B.omS r') = if r = r' then 1 else 0 := by
  rw [sum_parity he ε hε P hP (fun n => (sigW p)^[n] (B.om r) * (sigW p)^[n] (B.omS r'))]
  have h0 := congrArg ((sigW p)^[ε]) (B.dual r r')
  rw [← RingHom.coe_pow, map_sum] at h0
  rw [apply_ite (⇑((sigW p) ^ ε)), map_one, map_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.coe_pow, ← Function.iterate_add_apply, iterate_map_mul]

theorem dualTK {n' : ℕ} (B : OmBasis p n') (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (he : Even n') (ε : ℕ)
    (hε : ε < 2) (P : Fin n' → Prop) [DecidablePred P] (hP : ∀ s, P s ↔ s.val % 2 = ε) (r r' : Fin (n' / 2)) :
    ∑ s ∈ univ.filter P, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.om r))) *
      algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] (B.omS r'))) = if r = r' then 1 else 0 := by
  simp only [← map_mul, ← map_sum]
  rw [dualT B he ε hε P hP r r']
  split_ifs <;> simp

variable {X : Sys p} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] [Algebra X.G.Kf Kc] {j : ℕ} {La : X.Lt j}
  {La' : X.Lt (j + 1)} (φ : Frm X j La La')

theorem kron_inv' (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (Pf Kc φ v s ⊗ₖ Qf Kc φ v s) * (Pi Kc φ v s ⊗ₖ Qi Kc φ v s) = 1 :=
  mul_eq_one_comm.1 (kron_inv Kc φ v s)

theorem hasSubst_zOfX : MvPowerSeries.HasSubst (zOfX X Kc j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_zOfX Kc)

theorem subst_invF_linF (z : X.ZA j) :
    MvPowerSeries.subst (invF Kc φ) (linF Kc φ z) = zOfX X Kc j z := by
  obtain ⟨v, s, ab⟩ := z
  simp only [linF]
  rw [subst_lin (hasSubst_invF Kc φ)]
  simp only [MvPowerSeries.subst_X (hasSubst_invF Kc φ), invF]
  rw [sum_lin (MvPowerSeries.C) _ _ (fun ab' => zOfX X Kc j ⟨v, (s, ab')⟩), kron_inv', sum_one]

theorem subst_zOfX_coordZA (e : X.EA j ⊕ X.EA j) :
    MvPowerSeries.subst (zOfX X Kc j) (X.coordZA Kc j e) = MvPowerSeries.X e := by
  rcases e with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  · have he : Even (X.G.P.n' v) := (X.G.P.setting v).even
    simp only [Sys.coordZA]
    rw [subst_linS (hasSubst_zOfX Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_zOfX Kc)]
    rw [Finset.sum_congr rfl (g := fun s => ∑ r' : Fin (X.G.P.n' v / 2), MvPowerSeries.C
      (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om r'))) *
        algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).omS r)))) *
        (MvPowerSeries.X (Sum.inl ⟨v, (r', a, b)⟩) : MvPowerSeries (X.EA j ⊕ X.EA j) Kc))]
    · rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [dualTK (X.om v) Kc he 0 (by norm_num) (fun s => ¬ IsOddPos s)
        (fun s => by show ¬ (s.val % 2 = 1) ↔ _; omega)]
      simp [apply_ite MvPowerSeries.C, ite_mul]
    · intro s hs
      have hs' : ¬ IsOddPos s := (Finset.mem_filter.1 hs).2
      simp only [zOfX, if_neg hs', Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [map_mul]
      ring
  · have he : Even (X.G.P.n' v) := (X.G.P.setting v).even
    simp only [Sys.coordZA]
    rw [subst_linS (hasSubst_zOfX Kc)]
    simp only [MvPowerSeries.subst_X (hasSubst_zOfX Kc)]
    rw [Finset.sum_congr rfl (g := fun s => ∑ r' : Fin (X.G.P.n' v / 2), MvPowerSeries.C
      (algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).om r))) *
        algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) ((sigW p)^[s.val] ((X.om v).omS r')))) *
        (MvPowerSeries.X (Sum.inr ⟨v, (r', a, b)⟩) : MvPowerSeries (X.EA j ⊕ X.EA j) Kc))]
    · rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← map_sum MvPowerSeries.C]
      simp only [dualTK (X.om v) Kc he 1 (by norm_num) (fun s => IsOddPos s) (fun s => Iff.rfl)]
      simp [apply_ite MvPowerSeries.C, ite_mul]
    · intro s hs
      have hs' : IsOddPos s := (Finset.mem_filter.1 hs).2
      simp only [zOfX, if_pos hs', Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [map_mul]
      ring

theorem thA_unique (F : MvPowerSeries (X.ZA j) Kc) (G : MvPowerSeries (X.EA j ⊕ X.EA j) Kc)
    (h : F = linSub (bc Kc φ) (X.ThZA Kc j G)) : G = thA Kc φ F := by
  subst h
  unfold linSub Sys.ThZA thA
  simp only [bc_lin]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_linF Kc φ) (hasSubst_invF Kc φ)]
  simp only [subst_invF_linF]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_coordZA Kc) (hasSubst_zOfX Kc)]
  simp only [subst_zOfX_coordZA]
  exact (congrFun MvPowerSeries.subst_self G).symm

theorem bc_same (v : X.Pl) (s : Fin (X.G.P.n' v)) (ab ab' : Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t (j + 1))) :
    bc Kc φ ⟨v, (s, ab)⟩ ⟨v, (s, ab')⟩ = Pf Kc φ v s ab.1 ab'.1 * Qf Kc φ v s ab.2 ab'.2 := by
  classical
  simp only [bc, linF, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
    Finsupp.single_left_inj one_ne_zero]
  rw [Finset.sum_eq_single ab']
  · simp [Matrix.kroneckerMap_apply]
  · intro y _ hy
    have : ¬ ((⟨v, (s, ab')⟩ : X.ZA j) = ⟨v, (s, y)⟩) := by
      intro h
      simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
      exact hy h.symm
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem bc_ne (z z' : X.ZA j) (h : (⟨z.1, z.2.1⟩ : Σ v : X.Pl, Fin (X.G.P.n' v)) ≠ ⟨z'.1, z'.2.1⟩) :
    bc Kc φ z z' = 0 := by
  classical
  obtain ⟨v, s, ab⟩ := z
  simp only [bc, linF, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
    Finsupp.single_left_inj one_ne_zero]
  refine Finset.sum_eq_zero fun y _ => ?_
  have : ¬ (z' = (⟨v, (s, y)⟩ : X.ZA j)) := by
    rintro rfl
    exact h rfl
  simp [this]

end Uniq

end Formalism.L2.G.Pend
