import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsPretransitiveActO

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem cj_mulM (g : GL (Fin N) k) (a b : Matrix (Fin N) (Fin N) k) : cj g (a * b) = cj g a * cj g b := by
  have h1 : g⁻¹.val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [cj]
  rw [show g.val * a * g⁻¹.val * (g.val * b * g⁻¹.val) = g.val * a * (g⁻¹.val * g.val) * b * g⁻¹.val by
    simp only [mul_assoc], h1, mul_one]
  simp only [mul_assoc]

theorem cj_inv_cj (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g⁻¹ (cj g x) = x := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_cj_inv (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : cj g (cj g⁻¹ x) = x := by
  rw [← cj_mul, mul_inv_cancel, cj_one]

theorem cj_sum {ι : Type*} (g : GL (Fin N) k) (T : Finset ι) (f : ι → Matrix (Fin N) (Fin N) k) :
    cj g (∑ i ∈ T, f i) = ∑ i ∈ T, cj g (f i) := by
  simp only [cj, Finset.mul_sum, Finset.sum_mul]

theorem cj_smul (g : GL (Fin N) k) (c : k) (x : Matrix (Fin N) (Fin N) k) : cj g (c • x) = c • cj g x := by
  simp only [cj, mul_smul_comm, smul_mul_assoc]

theorem cj_pow (g : GL (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (n : ℕ) : cj g (x ^ n) = cj g x ^ n :=
  (Units.conj_pow g x n).symm

theorem rank_cj (g : GL (Fin N) k) (e : Matrix (Fin N) (Fin N) k) : (cj g e).rank = e.rank := rank_conj g e

theorem eq_zero_of_rank {A : Matrix (Fin N) (Fin N) k} (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
  ext i j
  have := congrArg (fun f => f (Pi.single j 1) i) h
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single] using this

theorem ne_zero_iff_rank {A : Matrix (Fin N) (Fin N) k} : A ≠ 0 ↔ A.rank ≠ 0 :=
  ⟨fun h h0 => h (eq_zero_of_rank h0), fun h h0 => h (by rw [h0, Matrix.rank_zero])⟩

def lin {a0 : ℕ} (c : Fin a0 → k) (w : Fin a0 → Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  ∑ i, c i • w i

theorem lin_cj {a0 : ℕ} (c : Fin a0 → k) (w : Fin a0 → Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    lin c (fun i => cj g (w i)) = cj g (lin c w) := by
  simp only [lin, cj_sum, cj_smul]

theorem continuous_lin {a0 : ℕ} (c : Fin a0 → k) : Continuous (lin (N := N) c) := by
  unfold lin
  exact continuous_finset_sum _ fun i _ => by fun_prop

theorem pe_cj {d : ℕ} (c : Fin d → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    pe (fun l => cj g (c l)) (cj g x) = cj g (pe c x) := by
  simp only [pe, cj_sum, cj_mulM, cj_pow]

theorem continuous_re {d r : ℕ} (γ : Fin d → Fin r → k) (s : Fin r → Matrix (Fin N) (Fin N) k) :
    Continuous (re γ s) := by
  unfold re
  exact continuous_finset_sum _ fun l _ => continuous_finset_sum _ fun j _ => by fun_prop

variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)

theorem z_mem (i : Fin D.a0) : D.z i ∈ Z := by
  show D.z i ∈ Z.toSubmodule
  rw [D.hz]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem exists_coef {a : Matrix (Fin N) (Fin N) k} (ha : a ∈ Z) : ∃ c : Fin D.a0 → k, lin c D.z = a := by
  have : a ∈ Submodule.span k (Set.range D.z) := by rw [← D.hz]; exact ha
  exact (Submodule.mem_span_range_iff_exists_fun k).1 this

def al (j : Fin D.r) (l : Fin D.d) : Fin D.a0 → k := (exists_coef D (D.ha j l)).choose

def bl (l : Fin D.d) : Fin D.a0 → k := (exists_coef D (D.hb l)).choose

theorem lin_al (j : Fin D.r) (l : Fin D.d) : lin (al D j l) D.z = D.a j l := (exists_coef D (D.ha j l)).choose_spec

theorem lin_bl (l : Fin D.d) : lin (bl D l) D.z = D.b l := (exists_coef D (D.hb l)).choose_spec

def sw (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : Fin D.r → Matrix (Fin N) (Fin N) k :=
  fun j => pe (fun l => lin (al D j l) w) x

def ew (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k :=
  pe (fun l => lin (bl D l) w) x

def et (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (t : Fin D.m) :
    Matrix (Fin N) (Fin N) k :=
  ∑ j, D.κ t j • sw D w x j

theorem weight_map_at_base (x : Matrix (Fin N) (Fin N) k) : sw D D.z x = fun j => pe (D.a j) x := by
  funext j; simp only [sw, lin_al]

theorem eigenvalue_map_at_base (x : Matrix (Fin N) (Fin N) k) : ew D D.z x = pe D.b x := by
  simp only [ew, lin_bl]

theorem sw_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    sw D (fun i => cj g (w i)) (cj g x) = fun j => cj g (sw D w x j) := by
  funext j; simp only [sw, lin_cj, pe_cj]

theorem ew_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) :
    ew D (fun i => cj g (w i)) (cj g x) = cj g (ew D w x) := by
  simp only [ew, lin_cj, pe_cj]

theorem et_cj (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) (t : Fin D.m) :
    et D (fun i => cj g (w i)) (cj g x) t = cj g (et D w x t) := by
  simp only [et, sw_cj, cj_sum, cj_smul]

theorem continuous_sw (j : Fin D.r) :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => sw D p.1 p.2 j := by
  unfold sw pe
  exact continuous_finset_sum _ fun l _ => ((continuous_lin _).comp continuous_fst).mul ((continuous_pow _).comp continuous_snd)

theorem continuous_ew :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => ew D p.1 p.2 := by
  unfold ew pe
  exact continuous_finset_sum _ fun l _ => ((continuous_lin _).comp continuous_fst).mul ((continuous_pow _).comp continuous_snd)

theorem continuous_et (t : Fin D.m) :
    Continuous fun p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Matrix (Fin N) (Fin N) k => et D p.1 p.2 t := by
  unfold et
  exact continuous_finset_sum _ fun j _ => (continuous_sw D j).const_smul (D.κ t j)

def Ys (τ : Fin D.m → ℕ) : Set ((Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
  {p | ∃ g : GL (Fin N) k, (∀ i, p.1 i = cj g (D.z i)) ∧ cj g⁻¹ p.2.1 ∈ piece D τ}

theorem mem_Ys_cj {τ : Fin D.m → ℕ} {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ)
    (g : GL (Fin N) k) : ((fun i => cj g (p.1 i)), act g p.2) ∈ Ys D τ := by
  obtain ⟨h, hh, hx⟩ := hp
  refine ⟨g * h, fun i => by show cj g (p.1 i) = _; rw [hh, cj_mul], ?_⟩
  show cj (g * h)⁻¹ (cj g p.2.1) ∈ piece D τ
  rw [_root_.mul_inv_rev, cj_mul, cj_inv_cj]
  exact hx

def F0 : Set ((Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
  {p | p.1 ∈ Orb D.z ∧ (∀ i, p.1 i * p.2.1 = p.2.1 * p.1 i) ∧ aeval p.2.1 χ = 0}

theorem mem_orbit_base_iff {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ F0 D) :
    ∃ g : GL (Fin N) k, (∀ i, p.1 i = cj g (D.z i)) ∧ cj g⁻¹ p.2.1 ∈ Bz Z ∧ aeval (cj g⁻¹ p.2.1) χ = 0 := by
  obtain ⟨⟨g, hg⟩, hc, hχ⟩ := hp
  refine ⟨g, hg, (comm_span_iff D.hz _).2 fun i => ?_, ?_⟩
  · have e : D.z i = cj g⁻¹ (p.1 i) := by rw [hg, cj_inv_cj]
    rw [e, ← cj_mulM, ← cj_mulM, hc]
  · rw [cj, PTop.aeval_conj, hχ, mul_zero, zero_mul]

theorem orbit_base_idempotent_rank {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ F0 D) (t : Fin D.m) :
    IsIdempotentElem (et D p.1 p.2.1 t) ∧ (et D p.1 p.2.1 t).rank = typ D (cj (Classical.choose (mem_orbit_base_iff D hp))⁻¹ p.2.1) t := by
  obtain ⟨hg, hB, hχ⟩ := Classical.choose_spec (mem_orbit_base_iff D hp)
  set g := Classical.choose (mem_orbit_base_iff D hp)
  have e1 : p.1 = fun i => cj g (D.z i) := funext hg
  have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
  have e3 : et D p.1 p.2.1 t = cj g (∑ j, D.κ t j • pe (D.a j) (cj g⁻¹ p.2.1)) := by
    conv_lhs => rw [e1, e2]
    rw [et_cj, et, weight_map_at_base]
  rw [e3]
  refine ⟨?_, rank_conj g _⟩
  show cj g _ * cj g _ = cj g _
  rw [← cj_mulM, ((D.spec _ hB hχ).2.2.2.2.2.2.2.2.1 t).eq]

theorem Ys_eq (τ : Fin D.m → ℕ) (hP : ∀ g ∈ Gz Z, ∀ x ∈ piece D τ, g.val * x * g⁻¹.val ∈ piece D τ) :
    Ys D τ = F0 D ∩ ⋂ t, {p | p ∈ F0 D ∧ (et D p.1 p.2.1 t).rank = τ t} := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hg, hx, hχ, hτ⟩
    have e1 : p.1 = fun i => cj g (D.z i) := funext hg
    have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
    have hF : p ∈ F0 D := by
      refine ⟨⟨g, hg⟩, fun i => ?_, ?_⟩
      · rw [hg, e2, ← cj_mulM, ← cj_mulM, hx _ (z_mem D i)]
      · rw [e2, cj, PTop.aeval_conj, hχ, mul_zero, zero_mul]
    refine ⟨hF, fun t => ⟨hF, ?_⟩⟩
    rw [e1, e2, et_cj, rank_cj, et, weight_map_at_base]
    exact congrFun hτ t
  · rintro ⟨hF, ht⟩
    obtain ⟨g, hg, hB, hχ⟩ := mem_orbit_base_iff D hF
    refine ⟨g, hg, hB, hχ, funext fun t => ?_⟩
    have e1 : p.1 = fun i => cj g (D.z i) := funext hg
    have e2 : p.2.1 = cj g (cj g⁻¹ p.2.1) := (cj_cj_inv g _).symm
    have := (ht t).2
    rw [e1, e2, et_cj, rank_cj, et, weight_map_at_base] at this
    exact this

theorem isClosed_orbit_base (hO : OrbClosed k) (hZ : CR Z) : IsClosed (F0 D) := by
  haveI : T2Space k := t2k
  have e : F0 D = (Prod.fst ⁻¹' Orb D.z) ∩ ((⋂ i, {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N |
      p.1 i * p.2.1 = p.2.1 * p.1 i}) ∩ {p | aeval p.2.1 χ = 0}) := by
    ext p; simp only [F0, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
  rw [e]
  refine ((isClosed_orb hO hZ D.hz).preimage continuous_fst).inter (IsClosed.inter ?_ ?_)
  · exact isClosed_iInter fun i => isClosed_eq (((continuous_apply i).comp continuous_fst).mul
      (continuous_fst.comp continuous_snd)) ((continuous_fst.comp continuous_snd).mul ((continuous_apply i).comp continuous_fst))
  · exact isClosed_eq ((continuous_aevalM χ).comp (continuous_fst.comp continuous_snd)) continuous_const

theorem isClosed_Ys (hO : OrbClosed k) (hZ : CR Z) (τ : Fin D.m → ℕ)
    (hP : ∀ g ∈ Gz Z, ∀ x ∈ piece D τ, g.val * x * g⁻¹.val ∈ piece D τ) : IsClosed (Ys D τ) := by
  rw [Ys_eq D τ hP]
  have hF := isClosed_orbit_base D hO hZ
  exact hF.inter (isClosed_iInter fun t => isClosed_rank hF ((continuous_et D t).comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))) (fun p hp => (orbit_base_idempotent_rank D hp t).1) _)

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
