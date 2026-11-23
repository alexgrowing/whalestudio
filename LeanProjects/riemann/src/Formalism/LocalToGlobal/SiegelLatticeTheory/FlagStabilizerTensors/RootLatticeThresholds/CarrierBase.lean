import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.CarrierBase

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting
open Formalism.L2.SG.RealObj.InfCut

section Frame

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ}

def scaleZ (F : PtRepPf.Fr ε r k) (T' : ℝ) (hT' : 0 < T') : PtRepPf.Fr ε r k where
  e := F.e
  fd := F.fd
  z := ((√(T' / F.T) : ℝ) : ℂ) • F.z
  wb := F.wb
  T := T'
  T_pos := hT'
  card := F.card
  ee := F.ee
  ff := F.ff
  ef := F.ef
  ez a := by rw [PtRepPf.hJ_smul_right, F.ez, mul_zero]
  fz a := by rw [PtRepPf.hJ_smul_right, F.fz, mul_zero]
  zz := by
    rw [PtRepPf.hJ_smul_right, PtRepPf.hJ_smul_left, F.zz, Complex.star_def, Complex.conj_ofReal]
    have hT := F.T_pos
    have hs : (√(T' / F.T)) ^ 2 = T' / F.T := Real.sq_sqrt (div_nonneg hT'.le hT.le)
    have hcc : ((√(T' / F.T) : ℝ) : ℂ) * ((√(T' / F.T) : ℝ) : ℂ) = ((T' / F.T : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← sq, hs]
    have hT0 : (F.T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    calc ((√(T' / F.T) : ℝ) : ℂ) * (((√(T' / F.T) : ℝ) : ℂ) * -(F.T : ℂ))
        = -(((√(T' / F.T) : ℝ) : ℂ) * ((√(T' / F.T) : ℝ) : ℂ)) * (F.T : ℂ) := by ring
      _ = -(T' : ℂ) := by
        rw [hcc]
        push_cast
        field_simp
  ww := F.ww
  ew := F.ew
  fw := F.fw
  zw i := by rw [PtRepPf.hJ_smul_left, F.zw, mul_zero]

theorem gram_eq (F G : PtRepPf.Fr ε r k) (hT : F.T = G.T) (i j : PtRepPf.Fr.Ix r k) :
    hJ ε (G.bv i) (G.bv j) = hJ ε (F.bv i) (F.bv j) := by
  rcases i with (a | a) | (_ | a) <;> rcases j with (b | b) | (_ | b) <;>
    simp only [PtRepPf.Fr.bv, Sum.elim_inl, Sum.elim_inr] <;>
    first
      | (simp [F.ee, G.ee, F.ff, G.ff, F.ef, G.ef, F.ez, G.ez, F.fz, G.fz, F.zz, G.zz, hT, F.ww, G.ww,
          F.ew, G.ew, F.fw, G.fw, F.zw, G.zw]; done)
      | (conv_lhs => rw [← PtRepPf.hJ_conj]
         conv_rhs => rw [← PtRepPf.hJ_conj]
         simp [F.ee, G.ee, F.ff, G.ff, F.ef, G.ef, F.ez, G.ez, F.fz, G.fz, F.zz, G.zz, hT, F.ww, G.ww,
          F.ew, G.ew, F.fw, G.fw, F.zw, G.zw])

def trL (F G : PtRepPf.Fr ε r k) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun y := ∑ i, hJ ε (F.dv i) y • G.bv i
  map_add' y y' := by simp only [PtRepPf.hJ_add_right, add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp only [PtRepPf.hJ_smul_right, mul_smul, Finset.smul_sum, RingHom.id_apply]

def trM (F G : PtRepPf.Fr ε r k) : Matrix (Fin n) (Fin n) ℂ := LinearMap.toMatrix' (trL F G)

theorem trM_mulVec (F G : PtRepPf.Fr ε r k) (y : Fin n → ℂ) :
    trM F G *ᵥ y = ∑ i, hJ ε (F.dv i) y • G.bv i := by
  rw [trM, LinearMap.toMatrix'_mulVec]
  rfl

theorem trM_bv (F G : PtRepPf.Fr ε r k) (j : PtRepPf.Fr.Ix r k) : trM F G *ᵥ F.bv j = G.bv j := by
  rw [trM_mulVec]
  simp [F.dual]

private theorem hJ_finset_sum_right {κ : Type} (s : Finset κ) (x : Fin n → ℂ) (w : κ → Fin n → ℂ) :
    hJ ε x (∑ j ∈ s, w j) = ∑ j ∈ s, hJ ε x (w j) := by
  induction s using Finset.cons_induction with
  | empty => unfold hJ; simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, PtRepPf.hJ_add_right, ih]

private theorem hJ_finset_sum_left {κ : Type} (s : Finset κ) (u : κ → Fin n → ℂ) (y : Fin n → ℂ) :
    hJ ε (∑ i ∈ s, u i) y = ∑ i ∈ s, hJ ε (u i) y := by
  rw [← PtRepPf.hJ_conj, hJ_finset_sum_right, star_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [PtRepPf.hJ_conj]

private theorem hJ_sum_smul_sum_smul {κ : Type} [Fintype κ] (c d : κ → ℂ) (u w : κ → Fin n → ℂ) :
    hJ ε (∑ i, c i • u i) (∑ j, d j • w j) = ∑ i, ∑ j, star (c i) * d j * hJ ε (u i) (w j) := by
  rw [hJ_finset_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PtRepPf.hJ_smul_left, hJ_finset_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PtRepPf.hJ_smul_right]
  ring

theorem trM_isom (F G : PtRepPf.Fr ε r k) (hT : F.T = G.T) (x y : Fin n → ℂ) :
    hJ ε (trM F G *ᵥ x) (trM F G *ᵥ y) = hJ ε x y := by
  classical
  have hli : LinearIndependent ℂ F.bv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (hJ ε (F.dv j)) hg
    simp only [hJ_finset_sum_right, PtRepPf.hJ_smul_right, F.dual] at h1
    unfold hJ at h1
    simpa using h1
  have hspan : Submodule.span ℂ (Set.range F.bv) = ⊤ := by
    have hcard : Fintype.card (PtRepPf.Fr.Ix r k) = Module.finrank ℂ (Fin n → ℂ) := by
      rw [Module.finrank_fin_fun, F.card]
      simp [PtRepPf.Fr.Ix]
    first
      | exact hli.span_eq_top_of_card_eq_finrank hcard
      | exact span_eq_top_of_linearIndependent_of_card_eq_finrank hli hcard
      | exact hli.span_eq_top_of_card_eq_finrank' hcard
  have hmem : ∀ z : Fin n → ℂ, ∃ c : PtRepPf.Fr.Ix r k → ℂ, ∑ i, c i • F.bv i = z := fun z =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (by rw [hspan]; exact Submodule.mem_top)
  have hM : ∀ c : PtRepPf.Fr.Ix r k → ℂ, trM F G *ᵥ ∑ i, c i • F.bv i = ∑ i, c i • G.bv i := by
    intro c
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, trM_bv]
  obtain ⟨c, rfl⟩ := hmem x
  obtain ⟨d, rfl⟩ := hmem y
  rw [hM, hM, hJ_sum_smul_sum_smul, hJ_sum_smul_sum_smul]
  simp only [gram_eq F G hT]

theorem single_dot (A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    star (Pi.single p (1 : ℂ) : Fin n → ℂ) ⬝ᵥ (A *ᵥ (Pi.single q (1 : ℂ) : Fin n → ℂ)) = A p q := by
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul, Matrix.mulVec_single_one]
  rfl

theorem trM_unitary (F G : PtRepPf.Fr ε r k) (hT : F.T = G.T) :
    (trM F G)ᴴ * Formalism.REAL.Jm ε * trM F G = Formalism.REAL.Jm ε := by
  ext p q
  have h := trM_isom F G hT (Pi.single p 1) (Pi.single q 1)
  unfold hJ at h
  rw [← single_dot ((trM F G)ᴴ * Formalism.REAL.Jm ε * trM F G) p q, ← single_dot (Formalism.REAL.Jm ε) p q, ← h,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

end Frame

section Words

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def m0X (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ :=
  trM (PtRepPf.frU X u' v) (scaleZ (PtRepPf.frU X u v) (PtRepPf.frU X u' v).T (PtRepPf.frU X u' v).T_pos)

variable (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem transport_matrix_fix_isotropic_e (a : Fin D.R.rS) : m0X X u u' v *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
  trM_bv _ _ (Sum.inl (Sum.inl a))

theorem transport_matrix_fix_isotropic_f (a : Fin D.R.rS) : m0X X u u' v *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a) :=
  trM_bv _ _ (Sum.inl (Sum.inr a))

theorem transport_matrix_apply_anisotropic : m0X X u u' v *ᵥ rv X.B.I v (X.zR u') =
    ((√(Tw (D := D) u' / Tw (D := D) u) : ℝ) : ℂ) • rv X.B.I v (X.zR u) :=
  trM_bv _ _ (Sum.inr (Sum.inl ⟨⟩))

theorem transport_matrix_apply_frame (i : Fin D.R.k) : m0X X u u' v *ᵥ X.wfr u' v i = X.wfr u v i :=
  trM_bv _ _ (Sum.inr (Sum.inr i))

theorem transportMatrix_unitary_hermitian : (m0X X u u' v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * m0X X u u' v = Formalism.REAL.Jm (X.B.I.ε v) :=
  trM_unitary _ _ rfl

end Words

section Transport

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F)
  {g : ℝ} {k r : ℕ} {Qm : Matrix (Fin X.B.I.n) (Fin (2 * r + k + 1)) ℂ}
  {Qim : Matrix (Fin (2 * r + k + 1)) (Fin X.B.I.n) ℂ}

theorem herm_Qi (hQ : IsTransp X v g k r Qm Qim) (x y : Fin X.B.I.n → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Qim *ᵥ x) (Qim *ᵥ y) = hJ (X.B.I.ε v) y x := by
  unfold Formalism.QuantumDeterminants.herm
  rw [← hQ.2.2.1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.mulVec_mulVec _ Qm Qim, Matrix.mulVec_mulVec _ Qm Qim, hQ.2.1, Matrix.one_mulVec, Matrix.one_mulVec]
  rfl

theorem hpk_row_esI (a : Fin r) (b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) b = if b = Formalism.QuantumDeterminants.eI k r a then 1 else 0 := by
  simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff]
  have ha := a.2
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_row_eI (a : Fin r) (b : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) b = if b = Formalism.QuantumDeterminants.esI k r a then 1 else 0 := by
  simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff]
  have ha := a.2
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec (y : Fin (2 * r + k + 1) → ℂ) (j : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) y (Formalism.QuantumDeterminants.bvec j) = (Formalism.QuantumDeterminants.Hpk k r *ᵥ y) j := by
  unfold Formalism.QuantumDeterminants.herm Formalism.QuantumDeterminants.bvec
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul]

theorem hpk_mulVec_esI (y : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ y) (Formalism.QuantumDeterminants.esI k r a) = y (Formalism.QuantumDeterminants.eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row_esI]

theorem hpk_mulVec_eI (y : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ y) (Formalism.QuantumDeterminants.eI k r a) = y (Formalism.QuantumDeterminants.esI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row_eI]

theorem inWb_Qi (hr : r = D.R.rS) (hQ : IsTransp X v g k r Qm Qim) (w : Fin X.B.I.n → ℂ)
    (hwe : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) w = 0) (hwf : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) w = 0) :
    Formalism.QuantumDeterminants.inWb k r (Qim *ᵥ w) := by
  have hbv : ∀ j, Formalism.QuantumDeterminants.bvec j = Qim *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := fun j => by
    rw [Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
  intro i hi
  rcases hi with hi | hi
  · let a : Fin r := ⟨i.val, hi⟩
    have hia : i = Formalism.QuantumDeterminants.eI k r a := Fin.ext rfl
    have h1 : (Qim *ᵥ w) i = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Qim *ᵥ w) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a)) := by
      rw [herm_bvec, hpk_mulVec_esI, hia]
    rw [h1, hbv, herm_Qi X v hQ]
    have hq := (hQ.2.2.2 a (Fin.cast hr a) rfl).2
    unfold Formalism.QuantumDeterminants.bvec
    rw [hq, PtRepPf.hJ_smul_left, hwf, mul_zero]
  · have hi2 := i.2
    let a : Fin r := ⟨2 * r + k - i.val, by omega⟩
    have hia : i = Formalism.QuantumDeterminants.esI k r a := Fin.ext (by simp only [Formalism.QuantumDeterminants.esI, a]; omega)
    have h1 : (Qim *ᵥ w) i = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Qim *ᵥ w) (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
      rw [herm_bvec, hpk_mulVec_eI, hia]
    rw [h1, hbv, herm_Qi X v hQ]
    have hq := (hQ.2.2.2 a (Fin.cast hr a) rfl).1
    unfold Formalism.QuantumDeterminants.bvec
    rw [hq, PtRepPf.hJ_smul_left, hwe, mul_zero]

def m0Of (Qm : Matrix (Fin X.B.I.n) (Fin (2 * r + k + 1)) ℂ) (Qim : Matrix (Fin (2 * r + k + 1)) (Fin X.B.I.n) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Qim * m0X X u u' v * Qm

theorem transportMatrix_unitary_form (hQ : IsTransp X v g k r Qm Qim) :
    (m0Of X u u' v Qm Qim)ᴴ * Formalism.QuantumDeterminants.Hpk k r * m0Of X u u' v Qm Qim = Formalism.QuantumDeterminants.Hpk k r := by
  have h1 : Qm * Qim = 1 := hQ.2.1
  have h2 : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have hU := transportMatrix_unitary_hermitian X u u' v
  unfold m0Of
  rw [← hQ.2.2.1]
  calc (Qim * m0X X u u' v * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Qm) * (Qim * m0X X u u' v * Qm)
      = Qmᴴ * ((m0X X u u' v)ᴴ * ((Qimᴴ * Qmᴴ) * (Formalism.REAL.Jm (X.B.I.ε v) * ((Qm * Qim) *
          (m0X X u u' v * Qm))))) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Qmᴴ * (((m0X X u u' v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * m0X X u u' v) * Qm) := by
        rw [h1, h2]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
    _ = Qmᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Qm := by
        rw [hU, Matrix.mul_assoc]

theorem transportMatrix_fixes_isotropic (hr : r = D.R.rS) (hQ : IsTransp X v g k r Qm Qim) (a : Fin r) :
    m0Of X u u' v Qm Qim *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a) ∧
    m0Of X u u' v Qm Qim *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.esI k r a) := by
  have hq := hQ.2.2.2 a (Fin.cast hr a) rfl
  unfold m0Of Formalism.QuantumDeterminants.bvec
  constructor
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hq.1, Matrix.mulVec_smul, transport_matrix_fix_isotropic_e, ← hq.1,
      Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hq.2, Matrix.mulVec_smul, transport_matrix_fix_isotropic_f, ← hq.2,
      Matrix.mulVec_mulVec, hQ.1, Matrix.one_mulVec]

theorem tz_Qi (hQ : IsTransp X v g k r Qm Qim) (w : D.what₂.Word) :
    Formalism.QuantumDeterminants.Tz k r (Qim *ᵥ rv X.B.I v (X.zR w)) = Tw (D := D) w := by
  unfold Formalism.QuantumDeterminants.Tz
  rw [herm_Qi X v hQ]
  have := (PtRepPf.frU X w v).zz
  change hJ (X.B.I.ε v) (rv X.B.I v (X.zR w)) (rv X.B.I v (X.zR w)) = -((Tw (D := D) w : ℝ) : ℂ) at this
  rw [this]
  simp

theorem isBaseFrame_of (hr : r = D.R.rS) (hQ : IsTransp X v g k r Qm Qim) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bs : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (hz : Bs.z = Qim *ᵥ rv X.B.I v (X.zR u))
    (hz' : Bs.z' = Qim *ᵥ rv X.B.I v (X.zR u')) (i : Fin D.R.k) :
    Formalism.FourierDecayAlt.D.IsBaseFrame Bs (Qim *ᵥ X.wfr u' v i) (m0Of X u u' v Qm Qim) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inWb_Qi X v hr hQ _ (fun a => (PtRepPf.frU X u' v).ew a i) (fun a => (PtRepPf.frU X u' v).fw a i)
  · rw [hz', herm_Qi X v hQ]
    exact (PtRepPf.frU X u' v).zw i
  · rw [herm_Qi X v hQ]
    have := (PtRepPf.frU X u' v).ww i i
    rw [if_pos rfl] at this
    exact this
  · exact ⟨transportMatrix_unitary_form X u u' v hQ, fun a _ => transportMatrix_fixes_isotropic X u u' v hr hQ a⟩
  · rw [hz, hz', tz_Qi X v hQ, tz_Qi X v hQ]
    unfold m0Of
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec _ Qm Qim, hQ.2.1, Matrix.one_mulVec,
      transport_matrix_apply_anisotropic, Matrix.mulVec_smul]

theorem baseFromX_of [IsCMField D.host.E] {Wp Wq : InfinitePlace D.host.E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (τ : Fin S.f ≃ InfinitePlace X.B.I.F)
    (Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * S.G.r + S.G.k + 1)) ℂ)
    (Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin X.B.I.n) ℂ)
    (hQ : ∀ v, Q v * Qi v = 1) (hi : ∀ v, i0 v = i0' v) :
    BaseFromX X S u u' i0 i0' τ Q Qi (fun j => Qi (τ j) *ᵥ X.wfr u' (τ j) (i0' (τ j)))
      (fun j => m0Of X u u' (τ j) (Q (τ j)) (Qi (τ j))) := by
  intro w
  refine ⟨hi w, by simp, fun i => ?_⟩
  simp only [Equiv.apply_symm_apply, m0Of]
  have : Q w * (Qi w * m0X X u u' w * Q w) * Qi w = m0X X u u' w := by
    calc Q w * (Qi w * m0X X u u' w * Q w) * Qi w = (Q w * Qi w) * m0X X u u' w * (Q w * Qi w) := by
          simp only [Matrix.mul_assoc]
      _ = m0X X u u' w := by rw [hQ w, Matrix.one_mul, Matrix.mul_one]
  rw [this, transport_matrix_apply_frame]

end Transport

end Formalism.L2.SG.Pf.CarrierBase
