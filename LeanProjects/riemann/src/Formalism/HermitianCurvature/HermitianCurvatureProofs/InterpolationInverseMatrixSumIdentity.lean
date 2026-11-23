import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerLevelsSameScalar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute

noncomputable section

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.NFx3

open Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.P

theorem poly_pad {A : Type} [Ring A] [Algebra ℂ A] (m n : ℕ) (hmn : m < n) (t : A) (a : ℕ → A) (Y : ℂ) :
    ∑ j ∈ range n, Y ^ j • (if j < m then a j else if j = m then t else 0) = Y ^ m • t + ∑ j ∈ range m, Y ^ j • a j := by
  have h1 : ∑ j ∈ range n, Y ^ j • (if j < m then a j else if j = m then t else 0) =
      ∑ j ∈ range (m + 1), Y ^ j • (if j < m then a j else if j = m then t else 0) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [mem_range] at hj ⊢
      omega
    · intro j hj hj'
      simp only [mem_range] at hj hj'
      rw [if_neg (by omega), if_neg (by omega), smul_zero]
  rw [h1, Finset.sum_range_succ, if_neg (lt_irrefl m), if_pos rfl, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos (mem_range.mp hj)]

theorem modelSHyp : ModelSHyp := by
  intro P L hP hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -, -, hT⟩ := hL
  obtain ⟨hs, hsz, -, hsG, -, -⟩ := star_generators P
  have hH := transfer_hermitian P hP
  have hE : ∀ Y a b, star (QQr P Y a b) = QQr P (star Y) b a := fun Y a b => by
    rw [← hH Y]; rfl
  have hszb : star (zbA P) = zA P := by rw [← hsz, star_star]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show star L.ζ = L.ζb
    rw [hz, hzb, hsz]
  · show star L.TT = L.TT
    rw [hT]; simp
  · intro l
    show star (L.c l) = L.cb l ∧ star (L.ci l) = L.cbi l ∧ star (L.p l) = -L.pb l
    rw [hc, hcb, hci, hcbi, hp, hpb]; exact hs l
  · exact ⟨fun Y hY => by rw [hH Y, hY], transfer_rtt P hP, transfer_determinant P hP, Mx8.qC_real P⟩
  · intro Y Y'; exact lower_left_commute_model P hP Y Y'
  · intro Y
    show t22 P Y = L.GG * NF.xA (kap P) Y
    rw [hG]; rfl
  · exact fun f => Mx7.star_kap P f
  · intro f g hg
    have : ∃ w, g = sc P w := by
      simp only [PreLevel.ops, PreLevel.fns, PreLevel.ofLevel, hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi,
        Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl)) | ⟨l, rfl⟩) | ⟨l, rfl⟩ <;>
        exact ⟨_, rfl⟩
    obtain ⟨w, rfl⟩ := this
    exact Mx7.kap_comm_sc P f w
  · obtain ⟨a11, a12, a21, a22, h⟩ := transfer_leading P hP
    refine ⟨P.k + 2, fun a b j => !![if j < P.k + 1 then a11 j else if j = P.k + 1 then 1 else 0,
      if j < P.k then a12 j else if j = P.k then -zA P else 0;
      if j < P.k then a21 j else if j = P.k then -zbA P else 0,
      if j < P.k - 1 then a22 j else if j = P.k - 1 then ggA P else 0] a b, ?_, ?_⟩
    · intro Y a b
      obtain ⟨h1, h2, h3, h4⟩ := h Y
      fin_cases a <;> fin_cases b
      · exact h1.trans (poly_pad (P.k + 1) (P.k + 2) (by omega) _ a11 Y).symm
      · refine h2.trans ?_
        rw [← smul_neg]; exact (poly_pad P.k (P.k + 2) (by omega) _ a12 Y).symm
      · refine h3.trans ?_
        rw [← smul_neg]; exact (poly_pad P.k (P.k + 2) (by omega) _ a21 Y).symm
      · exact h4.trans (poly_pad (P.k - 1) (P.k + 2) (by omega) _ a22 Y).symm
    · intro Y
      show t21 P Y = -(Y ^ P.k • L.ζb) + _
      rw [(h Y).2.2.1, hzb]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      show _ = Y ^ j • (if j < P.k then a21 j else _)
      rw [if_pos (Finset.mem_range.1 hj)]
  · intro Y
    obtain ⟨z1, -, z3, z4⟩ := transfer_zeta P Y
    obtain ⟨w1, -, w3, w4⟩ := transfer_zeta P (star Y)
    have e21 : star (t21 P (star Y)) = t12 P Y := by have := hE (star Y) 1 0; rwa [star_star] at this
    have e12 : star (t12 P (star Y)) = t21 P Y := by have := hE (star Y) 0 1; rwa [star_star] at this
    have e22 : star (t22 P (star Y)) = t22 P Y := by have := hE (star Y) 1 1; rwa [star_star] at this
    have s1 := congrArg star w1
    have s3 := congrArg star w3.eq
    have s4 := congrArg star w4.eq
    simp only [star_sub, star_mul, star_neg, e21, e12, e22, hsz] at s1 s3 s4
    show t21 P Y * L.ζ = L.ζ * t21 P Y - t22 P Y ∧ t22 P Y * L.ζ = L.ζ * t22 P Y ∧ t12 P Y * L.ζ = L.ζ * t12 P Y ∧
      t12 P Y * L.ζb = L.ζb * t12 P Y + t22 P Y ∧ t21 P Y * L.ζb = L.ζb * t21 P Y ∧ t22 P Y * L.ζb = L.ζb * t22 P Y
    rw [hz, hzb]
    refine ⟨?_, z4.eq, z3.eq, ?_, s3.symm, s4.symm⟩
    · rw [sub_eq_iff_eq_add] at z1; rw [z1]; abel
    · rw [sub_eq_iff_eq_add] at s1; rw [s1]; abel
  · intro Y a b g hg
    have key : ∀ l, ∀ x ∈ Wd.ops (siteA P l), Commute (QQr P Y a b) x := fun l =>
      Mx8.commutes_of_ent P l _ (Mx8.QQr_ent P l) Y a b
    simp only [PreLevel.crdOps, PreLevel.ofLevel, hp, hpb, hc, hci, hcb, hcbi, Set.mem_union, Set.mem_range] at hg
    rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · exact key l _ (Or.inl (by simp [Wd.hol, siteA]))
    · exact key l _ (Or.inl (by simp [Wd.hol, siteA]))
    · exact key l _ (Or.inr (by rw [← (hs l).1, star_star]; simp [Wd.hol, siteA]))
    · exact key l _ (Or.inr (by rw [← (hs l).2.1, star_star]; simp [Wd.hol, siteA]))
    · exact key l _ (Or.inl (by simp [Wd.hol, siteA]))
    · have h := key l (-pbA P l) (Or.inr (by rw [← (hs l).2.2, star_star]; simp [Wd.hol, siteA]))
      simpa using h.neg_right

theorem relIsCoreNorm : RelIsCoreNorm := by
  intro P A _ _ _ d
  unfold Q.NFData.Rel RelCore RelNorm
  tauto

theorem thmSOfSteps : ThmSOfSteps := by
  intro h1 h2 h3 h4 h5 h6 hB hC hN hR P A _ _ _ L0 QQ κ hP hS
  obtain ⟨b, SS, hF, hRa, hCo⟩ := hB h1 h2 h3 P A L0 QQ κ hP hS
  obtain ⟨L, hE, hn, hns, hst, hcore, hent⟩ := hC P A L0 QQ κ b SS hP hS hF hRa hCo
  obtain ⟨hnorm, h11⟩ := hN h1 h2 h3 h4 h5 h6 P A L0 QQ κ b SS L hP hS hF hRa hCo hE hn hns hst hcore
    (fun Y => ⟨(hent Y).1, (hent Y).2.1⟩)
  refine ⟨⟨L, κ, SS⟩, hE, rfl, hst, (hR P A _).2 ⟨hcore, hnorm⟩, fun Y => ?_⟩
  ext a b
  fin_cases a <;> fin_cases b
  · exact h11 Y
  · exact (hent Y).2.1
  · exact (hent Y).1
  · exact (hent Y).2.2

theorem normalFormOfS : NormalFormOfS := by
  intro hT hPre hH Wp Wq _ _ _ _ _ _ P z z' π π' hpl X
  obtain ⟨L0, hL0⟩ := hPre Wp Wq P z z' π π' hpl X
  obtain ⟨κ, hS⟩ := hH Wp Wq P z z' π π' hpl X L0 hL0
  obtain ⟨d, hE, -, hst, hrel, hq⟩ := hT P _ L0 X.QQ κ hpl.1 hS
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13⟩ := hE
  refine ⟨d, ?_, hst, hrel, hq⟩
  unfold Q.IsActualLevel
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
  exact hL0

theorem normalFormFromModuleOfParts : NormalFormFromModuleOfParts :=
  fun hT hPre hP hC hTy hS hZ hL h22 _ => normalFormOfS hT hPre (hP hS hZ hL h22 hC hTy)

end Formalism.FourierDecayAlt.P.NFx3

open Matrix Finset Polynomial

namespace Formalism.FourierDecayAlt.P.NFx3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

theorem rho_sep (P : M.Par) (hP : P.OK) (π σ : M.Ty P) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hij : i < j) : M.rho P π j < M.rho P σ i := by
  have hIπ := Mx3.tyInterlaces P hP π
  have hIσ := Mx3.tyInterlaces P hP σ
  have o := (Mx3.ord P.k P.u P.u' (M.rho P π) hIπ i hi).2.2.2 j hj hij
  have b := hIσ i hi
  linarith [o.1, b.2.2.1]

def xPoly (P : M.Par) (ρ : M.Ty P) : ℂ[X] := ∏ i ∈ Icc 1 (P.k - 1), (X + C (M.rho P ρ i : ℂ))

theorem eval_xPoly (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (xPoly P ρ).eval Y = M.xC P ρ Y := by
  simp [xPoly, M.xC, Polynomial.eval_prod]

theorem xPoly_inj (P : M.Par) (hP : P.OK) (hTy : M.TyComplete) {ρ σ : M.Ty P} (h : xPoly P ρ = xPoly P σ) :
    ρ = σ := by
  apply (hTy P hP).2
  intro i hi
  have h0 : (xPoly P σ).eval (-(M.rho P σ i : ℂ)) = 0 := by
    rw [eval_xPoly]
    unfold M.xC
    exact Finset.prod_eq_zero hi (by ring)
  rw [← h, eval_xPoly] at h0
  unfold M.xC at h0
  obtain ⟨j, hj, hz⟩ := Finset.prod_eq_zero_iff.1 h0
  have hr : M.rho P ρ j = M.rho P σ i := by
    have : ((M.rho P ρ j : ℝ) : ℂ) = (M.rho P σ i : ℂ) := by linear_combination hz
    exact_mod_cast this
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd hr (rho_sep P hP ρ σ hi hj hlt).ne
  · subst heq
    exact hr
  · exact absurd hr.symm (rho_sep P hP σ ρ hj hi hgt).ne

theorem exists_sep (P : M.Par) (hP : P.OK) (hTy : M.TyComplete) :
    ∃ Y0 : ℂ, ∀ ρ σ : M.Ty P, ρ ≠ σ → M.xC P ρ Y0 ≠ M.xC P σ Y0 := by
  classical
  obtain ⟨Y0, hY0⟩ := Infinite.exists_notMem_finset
    ((Finset.univ : Finset (M.Ty P × M.Ty P)).biUnion fun pr => (xPoly P pr.1 - xPoly P pr.2).roots.toFinset)
  refine ⟨Y0, fun ρ σ hne heq => hY0 ?_⟩
  have hp : xPoly P ρ - xPoly P σ ≠ 0 := fun h0 => hne (xPoly_inj P hP hTy (sub_eq_zero.1 h0))
  refine Finset.mem_biUnion.2 ⟨(ρ, σ), Finset.mem_univ _, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, IsRoot.def, eval_sub, eval_xPoly, eval_xPoly, heq, sub_self]

def lag {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (ρ : ι) : ℂ[X] :=
  ∏ σ ∈ Finset.univ.erase ρ, (C (x ρ - x σ)⁻¹ * (X - C (x σ)))

theorem eval_lag {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ) (hx : ∀ ρ σ, ρ ≠ σ → x ρ ≠ x σ) (ρ σ : ι) :
    (lag x ρ).eval (x σ) = if σ = ρ then 1 else 0 := by
  simp only [lag, Polynomial.eval_prod, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  split_ifs with h
  · subst h
    apply Finset.prod_eq_one
    intro τ hτ
    have hne : x σ - x τ ≠ 0 := sub_ne_zero.mpr (hx σ τ (Finset.ne_of_mem_erase hτ).symm)
    exact inv_mul_cancel₀ hne
  · apply Finset.prod_eq_zero (i := σ) (Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩)
    simp

theorem aeval_commute {A : Type*} [Ring A] [Algebra ℂ A] {T y : A} (h : Commute T y) (p : ℂ[X]) :
    Commute (aeval T p) y := by
  refine Polynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add]
    exact hp.add_left hq
  · rw [Polynomial.aeval_monomial]
    exact Commute.mul_left (Algebra.commutes a y) (h.pow_left n)

section Lin

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

theorem smooth_fsum {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → Mx k r → E)
    (hf : ∀ σ, SmoothLev k r i D (f σ)) : SmoothLev k r i D (fun y => ∑ σ ∈ s, a σ • f σ y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Qx2.smooth_zero : SmoothLev k r i D (fun _ => (0 : E)))
  | insert σ s hσ ih =>
    have := Qx2.smooth_add (Qx2.smooth_smul (hf σ) (a σ)) ih
    simpa only [Finset.sum_insert hσ] using this

theorem ll_zero_val {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.LL k r i D T) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) : T (fun _ => 0) g = 0 := by
  have h := hT.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g hg
  simp only [smul_zero, add_zero, one_smul] at h
  simpa using h

theorem ll_fsum {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.LL k r i D T) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (f : ι → Mx k r → E) (hf : ∀ σ, SmoothLev k r i D (f σ)) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    T (fun y => ∑ σ ∈ s, a σ • f σ y) g = ∑ σ ∈ s, a σ • T (f σ) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ll_zero_val hT hg
  | insert σ s hσ ih =>
    have e : (fun y => ∑ τ ∈ insert σ s, a τ • f τ y) = fun y => (∑ τ ∈ s, a τ • f τ y) + a σ • f σ y := by
      funext y
      rw [Finset.sum_insert hσ, add_comm]
    rw [e, hT.lin _ _ _ (smooth_fsum s a f hf) (hf σ) g hg, ih, Finset.sum_insert hσ, add_comm]

end Lin

section Slices

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem end_ext_dom {A B : Module.End ℂ (RadSp k r z z' π π')}
    (h : ∀ Φ : RadSp k r z z' π π', ∀ c ∈ OmX r, ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z',
      ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = (B Φ : Fn k r (Wq →L[ℂ] Wp)) c g) : A = B := by
  refine NFx1.APL.end_ext fun Φ => ?_
  funext c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · exact h Φ c hx.1 g ⟨hx.2.1, hx.2.2⟩
  · rw [(A Φ).2.1 (c, g) hx, (B Φ).2.1 (c, g) hx]

theorem coe_fsum {ι : Type*} (s : Finset ι) (A : ι → Module.End ℂ (RadSp k r z z' π π'))
    (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    (((∑ ρ ∈ s, A ρ) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      ∑ ρ ∈ s, ((A ρ Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g := by
  simp [LinearMap.sum_apply, Finset.sum_apply]

theorem coe_smulEnd (s : ℂ) (A : Module.End ℂ (RadSp k r z z' π π')) (Φ : RadSp k r z z' π π')
    (c : Fin r → ℂ) (g : Mx k r) :
    (((s • A) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      s • ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g := rfl

variable (Xo : ActualOps k r z z' π π')

theorem T_slice (Y0 : ℂ) {ι : Type*} [Fintype ι] (x : ι → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (dec : ι → Mx k r → (Wq →L[ℂ] Wp))
    (hsm : ∀ σ, SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') (dec σ))
    (hev : ∀ σ, ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z',
      tL k r z z' (Fin.last r) Y0 1 1 (dec σ) g = ((GGl k r z z' g : ℂ) * x σ) • dec σ g)
    (Ψ : RadSp k r z z' π π') (a : ι → ℂ)
    (hΨ : ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = ∑ σ, a σ • dec σ g)
    {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    (((Xo.fn 5 * Xo.t Y0 1 1) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      ∑ σ, (x σ * a σ) • dec σ g := by
  have hG : ((GGl k r z z' g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hg.2.ne'
  rw [Module.End.mul_apply, NFx1.APL.fn_coe]
  show fnVal k r z z' 5 g • ((Xo.t Y0 1 1 Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g = _
  rw [Xo.t_apply Y0 1 1 Ψ (c, g) ⟨hc, hg.1, hg.2⟩]
  have hll := Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := Fin.last r) (Qx5.Dp_open k r z z') z z' Y0 1 1
  rw [hll.loc _ (fun y => ∑ σ, a σ • dec σ y) (fun y hy => hΨ y hy) g hg, ll_fsum hll _ a dec hsm hg]
  simp only [hev _ g hg, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [show fnVal k r z z' 5 g = ((GGl k r z z' g : ℂ))⁻¹ from rfl]
  field_simp

theorem ks (Y0 : ℂ) {ι : Type*} [Fintype ι] (x : ι → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (dec : ι → Mx k r → (Wq →L[ℂ] Wp))
    (hsm : ∀ σ, SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') (dec σ))
    (hev : ∀ σ, ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z',
      tL k r z z' (Fin.last r) Y0 1 1 (dec σ) g = ((GGl k r z z' g : ℂ) * x σ) • dec σ g) (p : ℂ[X]) :
    ∀ (Ψ : RadSp k r z z' π π') (a : ι → ℂ),
      (∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = ∑ σ, a σ • dec σ g) →
      ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z',
        ((aeval (Xo.fn 5 * Xo.t Y0 1 1) p Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
          ∑ σ, (p.eval (x σ) * a σ) • dec σ g := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro b Ψ a hΨ g hg
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, coe_smulEnd]
    simp only [Module.End.one_apply, hΨ g hg, Finset.smul_sum, smul_smul, Polynomial.eval_C]
  · intro p q hp hq Ψ a hΨ g hg
    rw [map_add]
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, hp Ψ a hΨ g hg, hq Ψ a hΨ g hg,
      Polynomial.eval_add, add_mul, add_smul, Finset.sum_add_distrib]
  · intro n b ih Ψ a hΨ g hg
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply,
      ih _ (fun σ => x σ * a σ) (fun g' hg' => T_slice Xo Y0 x hc dec hsm hev Ψ a hΨ hg') g hg]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    ring

theorem lag_slice (Y0 : ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℂ)
    (hx : ∀ ρ σ, ρ ≠ σ → x ρ ≠ x σ) {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (dec : ι → Mx k r → (Wq →L[ℂ] Wp))
    (hsm : ∀ σ, SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') (dec σ))
    (hev : ∀ σ, ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z',
      tL k r z z' (Fin.last r) Y0 1 1 (dec σ) g = ((GGl k r z z' g : ℂ) * x σ) • dec σ g)
    (Ψ : RadSp k r z z' π π') (a : ι → ℂ)
    (hΨ : ∀ g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z', (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = ∑ σ, a σ • dec σ g)
    (ρ : ι) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    ((aeval (Xo.fn 5 * Xo.t Y0 1 1) (lag x ρ) Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      a ρ • dec ρ g := by
  rw [ks Xo Y0 x hc dec hsm hev (lag x ρ) Ψ a hΨ g hg]
  simp only [eval_lag x hx]
  simp [ite_smul, Finset.sum_ite_eq']

end Slices

section Main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
  {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem dec_of (hT22 : RadialDecompositionSpectral) (hpl : IsPlace P z z' π π') (Φ : RadSp P.k P.r z z' π π')
    {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r) :
    ∃ dec : M.Ty P → Mx P.k P.r → (Wq →L[ℂ] Wp),
      (∀ σ, SmoothLev P.k P.r (Fin.last P.r) (Qx5.Dp P.k P.r z z') (dec σ)) ∧
      (∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z',
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = ∑ σ, (1 : ℂ) • dec σ g) ∧
      ∀ (σ : M.Ty P) (Y : ℂ), ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z',
        tL P.k P.r z z' (Fin.last P.r) Y 1 1 (dec σ) g = ((GGl P.k P.r z z' g : ℂ) * M.xC P σ Y) • dec σ g := by
  obtain ⟨dec, hmem, hsum, hev⟩ := hT22 Wp Wq P z z' π π' (Qx5.Dp P.k P.r z z') hpl (Qx5.Dp_dom _ _ _ _)
    (fun g hg => hg.ne') _ (Qx5.slice_FF hpl.2.1 hpl.2.2.1 Φ.2 hc)
  exact ⟨dec, fun σ => (hmem σ).1, fun g hg => by simp [hsum g hg], hev⟩

theorem spectral (hT22 : RadialDecompositionSpectral) (hTy : M.TyComplete) (hpl : IsPlace P z z' π π')
    (Xo : ActualOps P.k P.r z z' π π')
    (hop : ∀ Y l i, Commute (Xo.t Y 1 1) (Xo.op l i)) (hfn : ∀ Y j, Commute (Xo.t Y 1 1) (Xo.fn j)) :
    ∃ Pj : M.Ty P → Module.End ℂ (RadSp P.k P.r z z' π π'),
      (∑ ρ, Pj ρ = 1) ∧ (∀ ρ σ, Pj ρ * Pj σ = if ρ = σ then Pj ρ else 0) ∧
      (∀ Y, Xo.t Y 1 1 = Xo.fn 4 * ∑ ρ, M.xC P ρ Y • Pj ρ) ∧
      (∀ ρ l i, Commute (Pj ρ) (Xo.op l i)) ∧ (∀ ρ j, Commute (Pj ρ) (Xo.fn j)) := by
  classical
  obtain ⟨Y0, hY0⟩ := exists_sep P hpl.1 hTy
  let x : M.Ty P → ℂ := fun ρ => M.xC P ρ Y0
  have hx : ∀ ρ σ, ρ ≠ σ → x ρ ≠ x σ := hY0
  have hsl1 : ∀ (Φ : RadSp P.k P.r z z' π π') (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r)
      (dec : M.Ty P → Mx P.k P.r → (Wq →L[ℂ] Wp))
      (hsm : ∀ σ, SmoothLev P.k P.r (Fin.last P.r) (Qx5.Dp P.k P.r z z') (dec σ))
      (hJ : ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z',
        (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g = ∑ σ, (1 : ℂ) • dec σ g)
      (hev : ∀ (σ : M.Ty P) (Y : ℂ), ∀ g ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z',
        tL P.k P.r z z' (Fin.last P.r) Y 1 1 (dec σ) g = ((GGl P.k P.r z z' g : ℂ) * M.xC P σ Y) • dec σ g)
      (ρ : M.Ty P) (g : Mx P.k P.r) (hg : g ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z'),
      ((aeval (Xo.fn 5 * Xo.t Y0 1 1) (lag x ρ) Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        dec ρ g := by
    intro Φ c hc dec hsm hJ hev ρ g hg
    rw [lag_slice Xo Y0 x hx hc dec hsm (fun σ => hev σ Y0) Φ (fun _ => 1) hJ ρ hg, one_smul]
  refine ⟨fun ρ => aeval (Xo.fn 5 * Xo.t Y0 1 1) (lag x ρ), ?_, ?_, ?_, ?_, ?_⟩
  · refine end_ext_dom fun Φ c hc g hg => ?_
    obtain ⟨dec, hsm, hJ, hev⟩ := dec_of hT22 hpl Φ hc
    rw [coe_fsum, Module.End.one_apply, hJ g hg]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hsl1 Φ c hc dec hsm hJ hev ρ g hg, one_smul]
  · intro ρ σ
    refine end_ext_dom fun Φ c hc g hg => ?_
    obtain ⟨dec, hsm, hJ, hev⟩ := dec_of hT22 hpl Φ hc
    have hΨ : ∀ g' ∈ Glev P.k P.r (Fin.last P.r) ∩ Qx5.Dp P.k P.r z z',
        ((aeval (Xo.fn 5 * Xo.t Y0 1 1) (lag x σ) Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) c g' =
          ∑ τ, (if τ = σ then (1 : ℂ) else 0) • dec τ g' := by
      intro g' hg'
      rw [hsl1 Φ c hc dec hsm hJ hev σ g' hg']
      simp [ite_smul]
    rw [Module.End.mul_apply, lag_slice Xo Y0 x hx hc dec hsm (fun τ => hev τ Y0) _ _ hΨ ρ hg]
    split_ifs with h
    · subst h
      rw [hsl1 Φ c hc dec hsm hJ hev ρ g hg, one_smul]
    · simp
  · intro Y
    refine end_ext_dom fun Φ c hc g hg => ?_
    obtain ⟨dec, hsm, hJ, hev⟩ := dec_of hT22 hpl Φ hc
    have hll := Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := Fin.last P.r) (Qx5.Dp_open P.k P.r z z') z z' Y 1 1
    rw [Xo.t_apply Y 1 1 Φ (c, g) ⟨hc, hg.1, hg.2⟩,
      hll.loc _ (fun y => ∑ σ, (1 : ℂ) • dec σ y) (fun y hy => hJ y hy) g hg,
      ll_fsum hll _ _ dec hsm hg, Module.End.mul_apply, NFx1.APL.fn_coe]
    show _ = fnVal P.k P.r z z' 4 g • ((∑ ρ, M.xC P ρ Y • aeval (Xo.fn 5 * Xo.t Y0 1 1) (lag x ρ)) Φ :
      Fn P.k P.r (Wq →L[ℂ] Wp)) c g
    rw [coe_fsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [coe_smulEnd, hsl1 Φ c hc dec hsm hJ hev ρ g hg, hev ρ Y g hg, one_smul, smul_smul,
      show fnVal P.k P.r z z' 4 g = ((GGl P.k P.r z z' g : ℝ) : ℂ) from rfl]
  · intro ρ l i
    refine aeval_commute ?_ _
    exact (show Commute (Xo.op l i) (Xo.fn 5) from NFx1.APL.op_fn Xo l i 5).symm.mul_left (hop Y0 l i)
  · intro ρ j
    refine aeval_commute ?_ _
    exact (show Commute (Xo.fn 5) (Xo.fn j) from
      (NFx1.APL.mul_fn Xo 5).comm (NFx1.APL.mul_fn Xo j)).mul_left (hfn Y0 j)

end Main

end Formalism.FourierDecayAlt.P.NFx3

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.NFx3

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF Formalism.FourierDecayAlt.P.NFx1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem interpolation_inverse_matrix_sum_identity {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (e : M →ₗ[ℂ] N) (he : Function.Injective e) (F : ℂ → Module.End ℂ M) (m : ℕ) (c : ℕ → M → N)
    (h : ∀ Y v, e (F Y v) = ∑ j ∈ Finset.range m, Y ^ j • c j v)
    (v : Fin m → ℂ) (W : Matrix (Fin m) (Fin m) ℂ) (hWV : W * Matrix.vandermonde v = 1) :
    ∃ C : ℕ → Module.End ℂ M, ∀ Y, F Y = ∑ j ∈ Finset.range m, Y ^ j • C j := by
  classical
  have key : ∀ (j : ℕ) (hj : j < m) (x : M),
      e ((∑ i : Fin m, W ⟨j, hj⟩ i • F (v i)) x) = c j x := by
    intro j hj x
    have e1 : e ((∑ i : Fin m, W ⟨j, hj⟩ i • F (v i)) x) =
        ∑ i : Fin m, W ⟨j, hj⟩ i • ∑ l : Fin m, (v i) ^ (l : ℕ) • c l x := by
      rw [LinearMap.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, map_smul, h]
      simp only [Finset.sum_range]
    rw [e1]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have e2 : ∀ l : Fin m, (∑ i : Fin m, W ⟨j, hj⟩ i * v i ^ (l : ℕ)) = (W * Matrix.vandermonde v) ⟨j, hj⟩ l := by
      intro l
      simp only [Matrix.mul_apply, Matrix.vandermonde_apply]
    simp_rw [e2, hWV, Matrix.one_apply]
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin m)]
    · simp
    · intro b _ hb
      rw [if_neg (fun h' => hb h'.symm), zero_smul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  refine ⟨fun j => if hj : j < m then ∑ i : Fin m, W ⟨j, hj⟩ i • F (v i) else 0, fun Y => ?_⟩
  refine LinearMap.ext fun x => he ?_
  rw [h, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  rw [LinearMap.smul_apply, map_smul]
  dsimp only
  rw [dif_pos hj', key j hj' x]

theorem interp {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (e : M →ₗ[ℂ] N) (he : Function.Injective e) (F : ℂ → Module.End ℂ M) (m : ℕ) (c : ℕ → M → N)
    (h : ∀ Y v, e (F Y v) = ∑ j ∈ Finset.range m, Y ^ j • c j v) :
    ∃ C : ℕ → Module.End ℂ M, ∀ Y, F Y = ∑ j ∈ Finset.range m, Y ^ j • C j := by
  refine interpolation_inverse_matrix_sum_identity e he F m c h (fun i : Fin m => ((i : ℕ) : ℂ)) _ (Matrix.nonsing_inv_mul _ ?_)
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  exact Fin.ext (by simpa using hij)

theorem smul_mkPair {V : Type*} [AddCommGroup V] [Module ℂ V] (s : ℂ) (a b : Module.End ℂ V) :
    s • Q.mkP a b = Q.mkP (s • a) ((starRingEnd ℂ) s • b) := by
  rw [Algebra.smul_def, APL.algebraMap_Pr]
  simp only [Q.mkP, Algebra.algebraMap_eq_smul_one]
  refine Prod.ext ?_ ?_
  · show s • (1 : Module.End ℂ V) * a = s • a
    rw [smul_mul_assoc, one_mul]
  · show (starRingEnd ℂ) s • (1 : (Module.End ℂ V)ᵐᵒᵖ) * MulOpposite.op b = (starRingEnd ℂ) s • MulOpposite.op b
    apply MulOpposite.unop_injective
    simp [mul_smul_comm]

theorem sum_mkPair {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} (t : Finset ι) (a b : ι → Module.End ℂ V) :
    ∑ i ∈ t, Q.mkP (a i) (b i) = Q.mkP (∑ i ∈ t, a i) (∑ i ∈ t, b i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty]
    rfl
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi, ih]
    rfl

section Pair

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem neg_mkPair (a b : Module.End ℂ V) : -Q.mkP a b = Q.mkP (-a) (-b) := rfl

theorem star_mkP (a b : Module.End ℂ V) : star (Q.mkP a b) = Q.mkP b a := rfl

theorem mkPair_commute {a b c d : Module.End ℂ V} (h1 : Commute a c) (h2 : Commute b d) :
    Commute (Q.mkP a b) (Q.mkP c d) := by
  simp only [Q.mkP, Commute, SemiconjBy]
  refine Prod.ext ?_ ?_
  · show a * c = c * a
    exact h1.eq
  · show MulOpposite.op b * MulOpposite.op d = MulOpposite.op d * MulOpposite.op b
    rw [← MulOpposite.op_mul, ← MulOpposite.op_mul, h2.eq]

theorem comm_inv {t u v : Module.End ℂ V} (h : Commute t u) (huv : u * v = 1) (hvu : v * u = 1) : Commute t v := by
  show t * v = v * t
  calc t * v = v * u * (t * v) := by rw [hvu, one_mul]
    _ = v * (u * t) * v := by simp only [mul_assoc]
    _ = v * (t * u) * v := by rw [h.eq]
    _ = v * t * (u * v) := by simp only [mul_assoc]
    _ = v * t := by rw [huv, mul_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_mul_sum (Pj : ι → Module.End ℂ V) (ho : ∀ i j, Pj i * Pj j = if i = j then Pj i else 0) (a b : ι → ℂ) :
    (∑ i, a i • Pj i) * (∑ j, b j • Pj j) = ∑ i, (a i * b i) • Pj i := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ho, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def kapOf (Pj : ι → Module.End ℂ V) (hs : ∑ i, Pj i = 1) (ho : ∀ i j, Pj i * Pj j = if i = j then Pj i else 0) :
    (ι → ℂ) →ₐ[ℂ] Q.Pr V where
  toFun f := Q.mkP (∑ i, f i • Pj i) (∑ i, star (f i) • Pj i)
  map_one' := by
    simp only [Pi.one_apply, one_smul, star_one, hs]
    rfl
  map_mul' f g := by
    simp only [Pi.mul_apply]
    rw [APL.mkPair_mul_mkPair, sum_mul_sum Pj ho, sum_mul_sum Pj ho]
    simp only [star_mul]
  map_zero' := by
    simp only [Pi.zero_apply, zero_smul, star_zero, Finset.sum_const_zero]
    rfl
  map_add' f g := by
    simp only [Pi.add_apply, add_smul, star_add, Finset.sum_add_distrib]
    rfl
  commutes' s := by
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Finset.smul_sum, ← Finset.smul_sum, hs, APL.algebraMap_Pr, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    rfl

theorem kapOf_apply (Pj : ι → Module.End ℂ V) (hs : ∑ i, Pj i = 1)
    (ho : ∀ i j, Pj i * Pj j = if i = j then Pj i else 0) (f : ι → ℂ) :
    kapOf Pj hs ho f = Q.mkP (∑ i, f i • Pj i) (∑ i, star (f i) • Pj i) := rfl

theorem sum_comm_of (Pj : ι → Module.End ℂ V) (f : ι → ℂ) {A : Module.End ℂ V} (h : ∀ i, Commute (Pj i) A) :
    Commute (∑ i, f i • Pj i) A := by
  exact Commute.sum_left _ _ _ fun i _ => (h i).smul_left (f i)

end Pair

section Ops

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem op_zeta (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) (j : Fin 6) (s : ℂ)
    (hpt : ∀ (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r), (c, g) ∈ DomR k r z z' →
      tL k r z z' (Fin.last r) Y a b (fun x => fnVal k r z z' j x • (Φ : Fn k r (Wq →L[ℂ] Wp)) c x) g =
        fnVal k r z z' j g • tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g +
          s • tL k r z z' (Fin.last r) Y 1 1 ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g) :
    X.t Y a b * X.fn j = X.fn j * X.t Y a b + s • X.t Y 1 1 := by
  refine APL.end_ext fun Φ => ?_
  funext c g
  show ((X.t Y a b (X.fn j Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
    ((X.fn j (X.t Y a b Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g +
      s • ((X.t Y 1 1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · have e1 : ((X.t Y a b (X.fn j Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        tL k r z z' (Fin.last r) Y a b (((X.fn j Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c) g :=
      X.t_apply Y a b _ (c, g) hx
    have e2 : ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g := X.t_apply Y a b Φ (c, g) hx
    have e3 : ((X.t Y 1 1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        tL k r z z' (Fin.last r) Y 1 1 ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g := X.t_apply Y 1 1 Φ (c, g) hx
    rw [e1]
    simp only [APL.fn_coe]
    rw [e2, e3]
    exact hpt Φ c g hx
  · rw [(X.t Y a b (X.fn j Φ)).2.1 (c, g) hx, (X.fn j (X.t Y a b Φ)).2.1 (c, g) hx,
      (X.t Y 1 1 Φ).2.1 (c, g) hx, smul_zero, add_zero]

theorem fnVal_zero (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    fnVal k r z z' 0 g = zetaL k r z z' (Fin.last r) g := rfl

theorem fnVal_two (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    fnVal k r z z' 2 g = star (zetaL k r z z' (Fin.last r) g) := rfl

theorem zeta_ids (hZ : Q.ZetaComm) (hz : inWb k r z) (hz' : inWb k r z') (X : ActualOps k r z z' π π') (Y : ℂ) :
    X.t Y 1 0 * X.fn 0 = X.fn 0 * X.t Y 1 0 - X.t Y 1 1 ∧ X.t Y 1 1 * X.fn 0 = X.fn 0 * X.t Y 1 1 ∧
    X.t Y 0 1 * X.fn 0 = X.fn 0 * X.t Y 0 1 ∧ X.t Y 0 1 * X.fn 2 = X.fn 2 * X.t Y 0 1 + X.t Y 1 1 ∧
    X.t Y 1 0 * X.fn 2 = X.fn 2 * X.t Y 1 0 ∧ X.t Y 1 1 * X.fn 2 = X.fn 2 * X.t Y 1 1 := by
  have H : ∀ (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r), (c, g) ∈ DomR k r z z' →
      let f : Mx k r → (Wq →L[ℂ] Wp) := (Φ : Fn k r (Wq →L[ℂ] Wp)) c
      let ζ : Mx k r → ℂ := zetaL k r z z' (Fin.last r)
      tL k r z z' (Fin.last r) Y 1 0 (fun x => ζ x • f x) g =
          ζ g • tL k r z z' (Fin.last r) Y 1 0 f g - tL k r z z' (Fin.last r) Y 1 1 f g ∧
        tL k r z z' (Fin.last r) Y 1 1 (fun x => ζ x • f x) g = ζ g • tL k r z z' (Fin.last r) Y 1 1 f g ∧
        tL k r z z' (Fin.last r) Y 0 1 (fun x => ζ x • f x) g = ζ g • tL k r z z' (Fin.last r) Y 0 1 f g ∧
        tL k r z z' (Fin.last r) Y 0 1 (fun x => star (ζ x) • f x) g =
          star (ζ g) • tL k r z z' (Fin.last r) Y 0 1 f g + tL k r z z' (Fin.last r) Y 1 1 f g ∧
        tL k r z z' (Fin.last r) Y 1 0 (fun x => star (ζ x) • f x) g = star (ζ g) • tL k r z z' (Fin.last r) Y 1 0 f g ∧
        tL k r z z' (Fin.last r) Y 1 1 (fun x => star (ζ x) • f x) g = star (ζ g) • tL k r z z' (Fin.last r) Y 1 1 f g :=
    fun Φ c g hx => hZ (Wq →L[ℂ] Wp) k r z z' (Qx5.Dp k r z z') ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) hz hz'
      (Qx5.Dp_open k r z z') (Qx5.slice_smooth Φ.2 hx.1) g ⟨hx.2.1, hx.2.2⟩ Y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := op_zeta X Y 1 0 0 (-1) fun Φ c g hx => by
      simp only [fnVal_zero]; rw [(H Φ c g hx).1, neg_one_smul]; abel
    rw [this, neg_one_smul, ← sub_eq_add_neg]
  · have := op_zeta X Y 1 1 0 0 fun Φ c g hx => by
      simp only [fnVal_zero]; rw [(H Φ c g hx).2.1, zero_smul, add_zero]
    rw [this, zero_smul, add_zero]
  · have := op_zeta X Y 0 1 0 0 fun Φ c g hx => by
      simp only [fnVal_zero]; rw [(H Φ c g hx).2.2.1, zero_smul, add_zero]
    rw [this, zero_smul, add_zero]
  · have := op_zeta X Y 0 1 2 1 fun Φ c g hx => by
      simp only [fnVal_two]; rw [(H Φ c g hx).2.2.2.1, one_smul]
    rw [this, one_smul]
  · have := op_zeta X Y 1 0 2 0 fun Φ c g hx => by
      simp only [fnVal_two]; rw [(H Φ c g hx).2.2.2.2.1, zero_smul, add_zero]
    rw [this, zero_smul, add_zero]
  · have := op_zeta X Y 1 1 2 0 fun Φ c g hx => by
      simp only [fnVal_two]; rw [(H Φ c g hx).2.2.2.2.2, zero_smul, add_zero]
    rw [this, zero_smul, add_zero]

theorem rep_of (X : ActualOps k r z z' π π') (a b : Fin 2) (m : ℕ) (ℓ : Module.End ℂ (RadSp k r z z' π π'))
    (A' : ℕ → (Mx k r → (Wq →L[ℂ] Wp)) → Mx k r → (Wq →L[ℂ] Wp))
    (hpt : ∀ (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r), (c, g) ∈ DomR k r z z' → ∀ Y : ℂ,
      tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g =
        Y ^ m • ((ℓ Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g +
          ∑ j ∈ Finset.range m, Y ^ j • A' j ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g) :
    ∃ C : ℕ → Module.End ℂ (RadSp k r z z' π π'),
      ∀ Y, X.t Y a b = Y ^ m • ℓ + ∑ j ∈ Finset.range m, Y ^ j • C j := by
  classical
  have hpw : ∀ (Y : ℂ) (Φ : RadSp k r z z' π π'),
      (RadSp k r z z' π π').subtype ((X.t Y a b - Y ^ m • ℓ) Φ) = ∑ j ∈ Finset.range m, Y ^ j •
        (fun c g => if (c, g) ∈ DomR k r z z' then A' j ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g else 0 :
          Fn k r (Wq →L[ℂ] Wp)) := by
    intro Y Φ
    funext c g
    simp only [Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply, Submodule.coe_sub,
      Submodule.coe_smul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]
    by_cases hx : (c, g) ∈ DomR k r z z'
    · have e : ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
          tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g := X.t_apply Y a b Φ (c, g) hx
      simp only [if_pos hx]
      rw [e, hpt Φ c g hx Y]
      abel
    · simp only [if_neg hx, smul_zero, Finset.sum_const_zero]
      rw [(X.t Y a b Φ).2.1 (c, g) hx, (ℓ Φ).2.1 (c, g) hx, smul_zero, sub_zero]
  obtain ⟨C, hC⟩ := interp (RadSp k r z z' π π').subtype Subtype.val_injective (fun Y => X.t Y a b - Y ^ m • ℓ) m
    (fun j Φ => fun c g => if (c, g) ∈ DomR k r z z' then A' j ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) g else 0) hpw
  refine ⟨C, fun Y => ?_⟩
  rw [← hC Y]
  abel

end Ops

theorem mdim_last (k r : ℕ) : Q.mdim k r (Fin.last r) = k + 1 := by
  simp [Q.mdim]

section Main

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem QQ_apply (X : ActualOps k r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b = Q.mkP (X.t Y a b) (X.t (star Y) b a) := rfl

theorem neg_fn_pt (X : ActualOps k r z z' π π') (j : Fin 6) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) (g : Mx k r) :
    (((-X.fn j) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
      -(fnVal k r z z' j g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  rw [LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, Pi.neg_apply, APL.fn_coe]

theorem comm_ops_of (X : ActualOps k r z z' π π') (L0 : PreLevel (Q.Pr (RadSp k r z z' π π')) r)
    (hL0 : IsActualPre X L0) {x y : Module.End ℂ (RadSp k r z z' π π')}
    (hx1 : ∀ l i, Commute x (X.op l i)) (hy1 : ∀ l i, Commute y (X.op l i)) :
    (∀ g ∈ L0.crdOps, Commute (Q.mkP x y) g) ∧
      ((∀ j, Commute x (X.fn j)) → (∀ j, Commute y (X.fn j)) → ∀ g ∈ L0.ops, Commute (Q.mkP x y) g) := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hL0
  refine ⟨fun g hg => ?_, fun hx2 hy2 g hg => ?_⟩
  · simp only [PreLevel.crdOps, Set.mem_union, Set.mem_range] at hg
    rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · rw [hc l]; exact mkPair_commute (hx1 l 1) (hy1 l 4)
    · rw [hci l]; exact mkPair_commute (hx1 l 2) (hy1 l 5)
    · rw [hcb l]; exact mkPair_commute (hx1 l 4) (hy1 l 1)
    · rw [hcbi l]; exact mkPair_commute (hx1 l 5) (hy1 l 2)
    · rw [hp l]; exact mkPair_commute (hx1 l 0) (hy1 l 3).neg_right
    · rw [hpb l]; exact mkPair_commute (hx1 l 3) (hy1 l 0).neg_right
  · simp only [PreLevel.ops, PreLevel.fns, Set.mem_union, Set.mem_range, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    rcases hg with (((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl)) |
      ⟨l, rfl⟩) | ⟨l, rfl⟩
    · rw [hc l]; exact mkPair_commute (hx1 l 1) (hy1 l 4)
    · rw [hci l]; exact mkPair_commute (hx1 l 2) (hy1 l 5)
    · rw [hcb l]; exact mkPair_commute (hx1 l 4) (hy1 l 1)
    · rw [hcbi l]; exact mkPair_commute (hx1 l 5) (hy1 l 2)
    · rw [hz]; exact mkPair_commute (hx2 0) (hy2 2)
    · rw [hzi]; exact mkPair_commute (hx2 1) (hy2 3)
    · rw [hzb]; exact mkPair_commute (hx2 2) (hy2 0)
    · rw [hzbi]; exact mkPair_commute (hx2 3) (hy2 1)
    · rw [hG]; exact mkPair_commute (hx2 4) (hy2 4)
    · rw [hGi]; exact mkPair_commute (hx2 5) (hy2 5)
    · rw [hp l]; exact mkPair_commute (hx1 l 0) (hy1 l 3).neg_right
    · rw [hpb l]; exact mkPair_commute (hx1 l 3) (hy1 l 0).neg_right

end Main

def padC {R : Type*} [Zero R] (m : ℕ) (ℓ : R) (C : ℕ → R) (j : ℕ) : R :=
  if j < m then C j else if j = m then ℓ else 0

def sel {R : Type*} (x00 x01 x10 x11 : R) (a b : Fin 2) : R :=
  if a = 0 then (if b = 0 then x00 else x01) else (if b = 0 then x10 else x11)

theorem star_xC (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : star (M.xC P ρ Y) = M.xC P ρ (star Y) := by
  simp [M.xC]

theorem actualSHypOfParts : ActualSHypOfParts := by
  intro hSt hZ hL h22 hTC hTy Wp Wq _ _ _ _ _ _ P z z' π π' hpl X L0 hL0
  have hz : inWb P.k P.r z := hpl.2.1
  have hz' : inWb P.k P.r z' := hpl.2.2.1
  have hTT := Qx5.place_alt_alt hpl
  have Z := zeta_ids hZ hz hz' X
  have hop : ∀ Y (a b : Fin 2) l i, Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => (hTC Wp Wq P z z' π π' hpl X l i).1 Y a b
  obtain ⟨f01, f10, f23, f32, f45, f54⟩ := APL.fn_inv X hTT
  have hfn : ∀ Y j, Commute (X.t Y 1 1) (X.fn j) := by
    intro Y j
    have c0 : Commute (X.t Y 1 1) (X.fn 0) := (Z Y).2.1
    have c2 : Commute (X.t Y 1 1) (X.fn 2) := (Z Y).2.2.2.2.2
    have c4 : Commute (X.t Y 1 1) (X.fn 4) := by
      rw [APL.fn_GG X]
      exact (c0.mul_right c2).sub_right (Algebra.commute_algebraMap_right _ _)
    fin_cases j
    · exact c0
    · exact comm_inv c0 f01 f10
    · exact c2
    · exact comm_inv c2 f23 f32
    · exact c4
    · exact comm_inv c4 f45 f54
  obtain ⟨Pj, hsum, horth, h22', hPop, hPfn⟩ := spectral h22 hTy hpl X (fun Y l i => hop Y 1 1 l i) hfn
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hζ, hζi, hζb, hζbi, hG, hGi, hT⟩ := id hL0
  obtain ⟨A, hA⟩ := hL (Wq →L[ℂ] Wp) P.k P.r z z' (Fin.last P.r) hz hz'
  have hmd := mdim_last P.k P.r
  obtain ⟨C00, h00⟩ := rep_of X 0 0 (P.k + 1) 1 (A 0 0) fun Φ c g hx Y => by
    obtain ⟨h1, -, -, -⟩ := hA _ _ (Qx5.Dp_open _ _ _ _) (Qx5.slice_smooth Φ.2 hx.1) g ⟨hx.2.1, hx.2.2⟩ Y
    rw [hmd] at h1
    rw [h1]
    rfl
  obtain ⟨C01, h01⟩ := rep_of X 0 1 P.k (-X.fn 0) (A 0 1) fun Φ c g hx Y => by
    obtain ⟨-, h2, -, -⟩ := hA _ _ (Qx5.Dp_open _ _ _ _) (Qx5.slice_smooth Φ.2 hx.1) g ⟨hx.2.1, hx.2.2⟩ Y
    rw [hmd, Nat.add_sub_cancel] at h2
    rw [h2, neg_fn_pt, fnVal_zero, smul_neg, smul_smul, mul_comm]
  obtain ⟨crystallineComparison, h10⟩ := rep_of X 1 0 P.k (-X.fn 2) (A 1 0) fun Φ c g hx Y => by
    obtain ⟨-, -, h3, -⟩ := hA _ _ (Qx5.Dp_open _ _ _ _) (Qx5.slice_smooth Φ.2 hx.1) g ⟨hx.2.1, hx.2.2⟩ Y
    rw [hmd, Nat.add_sub_cancel] at h3
    rw [h3, neg_fn_pt, fnVal_two, smul_neg, smul_smul, mul_comm]
  obtain ⟨C11, h11⟩ := rep_of X 1 1 P.k 0 (A 1 1) fun Φ c g hx Y => by
    obtain ⟨-, -, -, h4⟩ := hA _ _ (Qx5.Dp_open _ _ _ _) (Qx5.slice_smooth Φ.2 hx.1) g ⟨hx.2.1, hx.2.2⟩ Y
    rw [hmd, Nat.add_sub_cancel] at h4
    rw [h4]
    simp
  have pad : ∀ (a b : Fin 2) (m : ℕ) (ℓ : Module.End ℂ (RadSp P.k P.r z z' π π')) (C : ℕ → Module.End ℂ (RadSp P.k P.r z z' π π')),
      m < P.k + 2 → (∀ Y, X.t Y a b = Y ^ m • ℓ + ∑ j ∈ Finset.range m, Y ^ j • C j) →
      ∀ Y, X.t Y a b = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • padC m ℓ C j :=
    fun a b m ℓ C hm h Y => by rw [h Y]; exact (poly_pad m (P.k + 2) hm ℓ C Y).symm
  set S := sel (padC (P.k + 1) 1 C00) (padC P.k (-X.fn 0) C01) (padC P.k (-X.fn 2) crystallineComparison) (padC P.k 0 C11) with hS
  have hDD : ∀ Y (a b : Fin 2), X.t Y a b = ∑ j ∈ Finset.range (P.k + 2), Y ^ j • S a b j := by
    intro Y a b
    fin_cases a <;> fin_cases b
    · exact pad 0 0 (P.k + 1) 1 C00 (by omega) h00 Y
    · exact pad 0 1 P.k (-X.fn 0) C01 (by omega) h01 Y
    · exact pad 1 0 P.k (-X.fn 2) crystallineComparison (by omega) h10 Y
    · exact pad 1 1 P.k 0 C11 (by omega) h11 Y
  refine ⟨kapOf Pj hsum horth, ?_, ?_, ?_, (hSt Wp Wq P z z' π π' hpl X).1, (hSt Wp Wq P z z' π π' hpl X).2,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hζ, hζb]; rfl
  · rw [hT, Complex.star_def, Complex.conj_ofReal]
  · intro l
    rw [hc, hcb, hci, hcbi, hp, hpb, neg_mkPair, neg_neg]
    exact ⟨rfl, rfl, rfl⟩
  · intro Y
    rw [hG, QQ_apply]
    unfold NF.xA
    rw [kapOf_apply, APL.mkPair_mul_mkPair, APL.mkPair_inj]
    refine ⟨h22' Y, ?_⟩
    rw [h22' (star Y)]
    simp only [star_xC]
    exact (sum_comm_of Pj _ fun ρ => hPfn ρ 4).eq.symm
  · intro f
    rw [kapOf_apply, kapOf_apply, star_mkP]
    simp only [star_star]
  · intro f g hg
    rw [kapOf_apply]
    exact (comm_ops_of X L0 hL0 (fun l i => sum_comm_of Pj _ fun ρ => hPop ρ l i)
      (fun l i => sum_comm_of Pj _ fun ρ => hPop ρ l i)).2 (fun j => sum_comm_of Pj _ fun ρ => hPfn ρ j)
      (fun j => sum_comm_of Pj _ fun ρ => hPfn ρ j) g hg
  · refine ⟨P.k + 2, fun a b j => Q.mkP (S a b j) (S b a j), fun Y a b => ?_, fun Y => ?_⟩
    · rw [QQ_apply, hDD Y a b, hDD (star Y) b a]
      simp only [smul_mkPair, map_pow, starRingEnd_apply]
      rw [sum_mkPair]
    · rw [QQ_apply, hζb, h10 Y, h01 (star Y)]
      simp only [smul_mkPair, map_pow, starRingEnd_apply]
      rw [sum_mkPair, neg_mkPair, APL.mkPair_add_mkPair, APL.mkPair_inj]
      constructor
      · rw [smul_neg]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [hS, sel, padC, Finset.mem_range.1 hj]
      · rw [smul_neg]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        simp [hS, sel, padC, Finset.mem_range.1 hj]
  · intro Y
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := Z Y
    obtain ⟨w1, w2, w3, w4, w5, w6⟩ := Z (star Y)
    rw [hζ, hζb]
    simp only [QQ_apply]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_sub_mkPair, APL.mkPair_inj]
      exact ⟨z1, by rw [w4]; abel⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_inj]
      exact ⟨z2, w6.symm⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_inj]
      exact ⟨z3, w5.symm⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_add_mkPair, APL.mkPair_inj]
      exact ⟨z4, by rw [w1]; abel⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_inj]
      exact ⟨z5, w3.symm⟩
    · rw [APL.mkPair_mul_mkPair, APL.mkPair_mul_mkPair, APL.mkPair_inj]
      exact ⟨z6, w2.symm⟩
  · intro Y a b g hg
    rw [QQ_apply]
    exact (comm_ops_of X L0 hL0 (fun l i => hop Y a b l i) (fun l i => hop (star Y) b a l i)).1 g hg

end Formalism.FourierDecayAlt.P.NFx3

namespace Formalism.FourierDecayAlt.P

theorem model_hypotheses : Formalism.FourierDecayAlt.NF.ModelSHyp := by
  exact NFx3.modelSHyp
theorem theorem_S_of_steps : Formalism.FourierDecayAlt.NF.ThmSOfSteps := by
  exact NFx3.thmSOfSteps
theorem normal_form_of_S : Formalism.FourierDecayAlt.NF.NormalFormOfS := by
  exact NFx3.normalFormOfS
theorem normal_form_from_module : Formalism.FourierDecayAlt.NF.NormalFormFromModuleOfParts := by
  exact NFx3.normalFormFromModuleOfParts

theorem actual_hypotheses_of_parts : Formalism.FourierDecayAlt.NF.ActualSHypOfParts := by
  exact NFx3.actualSHypOfParts

end Formalism.FourierDecayAlt.P
