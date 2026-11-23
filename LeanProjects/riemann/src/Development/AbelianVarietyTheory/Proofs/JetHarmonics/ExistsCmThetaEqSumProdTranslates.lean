import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.StatementB
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OpUConstMul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoords
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.ThetaDecomp

def okGroup (d : ℕ) : AddSubgroup ℂ where
  carrier := {z | InOK d z}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
    exact ⟨u + u', v + v', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨u, v, rfl⟩
    exact ⟨-u, -v, by push_cast; ring⟩

theorem inOK_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : InOK d z) : InOK d ((n : ℂ) * z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem wK_re (d : ℕ) : (wK d).re = 1 / 2 := by simp [wK]

theorem wK_im (d : ℕ) : (wK d).im = Real.sqrt d / 2 := by simp [wK]

theorem cmLatticeHermitianForm_im_int_of_mem_order {d : ℕ} (hd : 0 < d) {x y : ℂ} (hx : InOK d x) (hy : InOK d y) : ∃ k : ℤ, (h1 d x y).im = k := by
  obtain ⟨u, v, rfl⟩ := hx
  obtain ⟨u', v', rfl⟩ := hy
  have hs : Real.sqrt d ≠ 0 := by positivity
  refine ⟨v * u' - u * v', ?_⟩
  rw [h1, Complex.im_ofReal_mul]
  simp [wK_re, wK_im]
  field_simp
  ring

theorem inOK_of_im {d : ℕ} (hd : 0 < d) {z : ℂ} {k l : ℤ} (h : (h1 d z 1).im = k) (h' : (h1 d z (wK d)).im = l) :
    InOK d z := by
  have hs : Real.sqrt d ≠ 0 := by positivity
  rw [h1, Complex.im_ofReal_mul] at h h'
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, wK_re, wK_im, map_one, Complex.one_re,
    Complex.one_im] at h h'
  have e : Real.sqrt d * (2 / Real.sqrt d) = 2 := by field_simp
  refine ⟨-l, k, Complex.ext ?_ ?_⟩
  · simp [wK_re, wK_im]
    linear_combination (-1) * h' + (1 / 2) * h - z.re / 2 * e
  · simp [wK_re, wK_im]
    linear_combination (Real.sqrt d / 2) * h - z.im / 2 * e

theorem exp_rat_mem (r : ℚ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  refine IsAlgebraic.of_pow (n := 2 * r.den) (by have := r.den_pos; omega) ?_
  have : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) ^ (2 * r.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have : (r.num : ℂ) = r * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
    rw [this]; push_cast; ring
  rw [this]; exact isAlgebraic_one

theorem kap_eq_one_iff {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    kap Hm x y = 1 ↔ ∃ k : ℤ, (hf Hm x y).im = k := by
  rw [kap, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have h2 : (((hf Hm x y).im : ℝ) : ℂ) = ((-n : ℤ) : ℝ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      push_cast
      linear_combination -hn
    exact_mod_cast h2
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [hk]; push_cast; ring⟩

noncomputable def betaL {g : ℕ} (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun v := beta d Hm v y
  map_add' v w := by simp only [beta, hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c v := by
    simp only [beta, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem natCast_mul_im (n : ℕ) (z : ℂ) : ((n : ℂ) * z).im = n * z.im := by simp

theorem cmLatticeHermitianForm_natCast_mul_right (d n : ℕ) (z w : ℂ) : h1 d z ((n : ℂ) * w) = n * h1 d z w := by
  simp only [h1, map_mul, map_natCast]; ring

theorem isTheta_sum {g : ℕ} (S : Setup g) (hS : S.Ok) (A : AddSubgroup S.La) [Fintype (S.La ⧸ A)]
    (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (hA : ∀ l ∈ A, opW S.d S.Hm l G = G) :
    S.IsTheta (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) G z) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hS.1.pos hS.2.2.1.1
  have hW : ∀ (l l' : S.La) F, opW S.d S.Hm l (opW S.d S.Hm l' F) = opW S.d S.Hm (l + l' : S.La) F :=
    fun l l' F => (h1 l l' F).2.2 (hS.2.2.2.2.2.2.1 l l.2 l' l'.2)
  have hq : ∀ l l' : S.La, (l : S.La ⧸ A) = l' → opW S.d S.Hm l G = opW S.d S.Hm l' G := by
    intro l l' h
    have := hW l (-l + l') G
    rw [hA _ (QuotientAddGroup.eq.1 h), add_neg_cancel_left] at this
    exact this
  refine ⟨ContDiff.sum fun c _ => (h3 _ G hG).2, fun y hy => ?_⟩
  funext z
  rw [← Equiv.sum_comp (Equiv.addLeft ((⟨y, hy⟩ : S.La) : S.La ⧸ A))]
  have : opW S.d S.Hm y (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) G z) z =
      ∑ c : S.La ⧸ A, opW S.d S.Hm y (opW S.d S.Hm (c.out : S.La) G) z := by
    simp only [opW.eq_1 S.d S.Hm y, opU.eq_1 S.Hm y, Finset.mul_sum, Finset.sum_mul]
  rw [this]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hW ⟨y, hy⟩, hq]
  simp

end GlobalTheory.MomOne.ThetaDecomp

namespace GlobalTheory.MomOne
open ThetaDecomp

theorem exists_theta_eq_sum_prod : ∀ (q : ℕ) (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ) (θ : ℂ → ℂ), q.Prime → S.Ok → (∀ i, x i ∈ S.La) → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i ∧ Nat.Coprime (a i) q) → IsTh S.d θ → ∃ (m : ℕ) (r : Fin m → ℂ) (t : Fin m → Fin g → ℂ) (Θ : (Fin g → ℂ) → ℂ), S.IsTheta Θ ∧ Θ ≠ 0 ∧ (∀ j, r j ∈ Qbar) ∧ (∀ j i, PrimeTo S.d q (t j i)) ∧ ∀ z : Fin g → ℂ, Θ (∑ i, z i • x i) = ∑ j, r j * ∏ i, U1 S.d (t j i) θ (z i) ^ a i := by
  classical
  intro q g S x a θ _ hS hx hβ ha hθ
  have hd : 0 < S.d := hS.1.pos
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.MomOne.Frame.coord g S x a hd hβ fun i => (ha i).1
  obtain ⟨e1, -, e3, -, -, e6⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd hS.2.2.1.1
  have ha0 : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).1.ne'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v i, ψ v i = beta S.d S.Hm v (x i) / (a i : ℂ) :=
    ⟨LinearMap.pi fun i => (a i : ℂ)⁻¹ • betaL S.d S.Hm (x i), fun v i => by
      rw [div_eq_inv_mul]; rfl⟩
  have hφψ : ∀ v, ∑ i, ψ v i • x i = v := fun v => by simp only [hψ]; exact (c1 v).symm
  have hψφ : ∀ z : Fin g → ℂ, ψ (∑ i, z i • x i) = z := fun z => by
    funext i
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul]
    simp only [Pi.smul_apply, hψ, hβ, smul_eq_mul]
    rw [Finset.sum_eq_single i (fun j _ h => by simp [h]) (by simp)]
    simp [ha0 i]
  have hH : ∀ v w, (hf S.Hm v w).im = ∑ i, (a i : ℝ) * (h1 S.d (ψ v i) (ψ w i)).im := fun v w => by
    have := c2 (ψ v) (ψ w)
    rw [hφψ, hφψ] at this
    rw [this, Complex.im_sum]
    simp
  obtain ⟨F, hFd⟩ : ∃ F : (Fin g → ℂ) → ℂ, F = fun v => ∏ i, θ (ψ v i) ^ a i := ⟨_, rfl⟩
  have hF : ∀ z : Fin g → ℂ, F (∑ i, z i • x i) = ∑ _j : Fin 1, 1 * ∏ i, θ (z i) ^ a i := fun z => by
    simp [hFd, hψφ]
  have hFc : ContDiff ℂ ⊤ F := by
    rw [hFd]
    refine contDiff_prod fun i _ => ContDiff.pow (hθ.1.contDiff.comp ?_) _
    exact (LinearMap.toContinuousLinearMap ((LinearMap.proj i).comp ψ)).contDiff
  have hF0 : F 0 = 1 := by simp [hFd, hθ.2.1]
  have hU : ∀ v z : Fin g → ℂ, opU S.Hm v F (∑ i, z i • x i) = ∏ i, U1 S.d (ψ v i) θ (z i) ^ a i := fun v z => by
    have := (c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) z).1
    rw [hφψ] at this
    simpa using this
  have hW : ∀ v : Fin g → ℂ, (∀ i, InOK S.d (ψ v i)) → opW S.d S.Hm v F = F := fun v hv => by
    funext w
    have := (c3 1 (fun _ => 1) (fun _ _ => θ) F hF (ψ v) (ψ w)).2
    rw [hφψ, hφψ] at this
    rw [this]
    simp [hFd, hθ.2.2.2.1 _ (hv _)]
  obtain ⟨D, hD⟩ : ∃ D : AddSubgroup (Fin g → ℂ), ∀ v, v ∈ D ↔ ∀ i, InOK S.d ((a i : ℂ) * ψ v i) :=
    ⟨⨅ i, (okGroup S.d).comap ((betaL S.d S.Hm (x i)).toAddMonoidHom), fun v => by
      simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap, hψ, mul_div_cancel₀ _ (ha0 _)]
      rfl⟩
  have hLD : ∀ l ∈ S.La, l ∈ D := fun l hl => (hD l).2 fun i => by
    rw [hψ, mul_div_cancel₀ _ (ha0 _)]
    exact hS.2.2.2.2.2.2.1 l hl _ (hx i)
  obtain ⟨A, hA⟩ : ∃ A : AddSubgroup S.La, ∀ l : S.La, l ∈ A ↔ ∀ i, InOK S.d (ψ l i) :=
    ⟨⨅ i, (okGroup S.d).comap
      (((LinearMap.proj i).comp ψ : (Fin g → ℂ) →ₗ[ℂ] ℂ).toAddMonoidHom.comp S.La.subtype.toAddMonoidHom), fun l => by
      simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
      rfl⟩
  have hN : ∀ v ∈ D, ∀ i, InOK S.d (ψ ((∏ j, a j) • v) i) := fun v hv i => by
    have := inOK_natCast_mul (∏ j ∈ Finset.univ.erase i, a j) ((hD v).1 hv i)
    rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at this
    rwa [map_nsmul, Pi.smul_apply, nsmul_eq_mul]
  have hN0 : ∏ j, a j ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => (ha i).1.ne'
  have hint : ∀ v, (∀ i, InOK S.d (ψ v i)) → ∀ w ∈ D, ∃ k : ℤ, (hf S.Hm v w).im = k := fun v hv w hw => by
    choose k hk using fun i => cmLatticeHermitianForm_im_int_of_mem_order hd (hv i) ((hD w).1 hw i)
    refine ⟨∑ i, k i, ?_⟩
    rw [hH]; push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hk, cmLatticeHermitianForm_natCast_mul_right]; simp
  have hrat : ∀ v ∈ D, ∀ w ∈ D, ∃ r : ℚ, (hf S.Hm v w).im = r := fun v hv w hw => by
    obtain ⟨k, hk⟩ := hint _ (hN v hv) w hw
    refine ⟨k / (∏ j, a j : ℕ), ?_⟩
    have h0 : ((∏ j, a j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN0
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, eq_div_iff h0, ← hk, hH, hH, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, nsmul_eq_mul, Basic.cmLatticeHermitianForm_mul_left, natCast_mul_im]
    ring
  have := hS.2.2.2.1
  have : Module.Finite ℤ S.La := inferInstance
  have : AddGroup.FG S.La := Module.Finite.iff_addGroup_fg.1 inferInstance
  have := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg S.La hN0
  have : A.FiniteIndex := AddSubgroup.finiteIndex_of_le (H := (nsmulAddMonoidHom (∏ j, a j)).range) (by
    rintro _ ⟨l, rfl⟩
    exact (hA _).2 (hN l (hLD l l.2)))
  have : Fintype (S.La ⧸ A) := Fintype.ofFinite _
  have hcomm : ∀ (l w : Fin g → ℂ) z, opW S.d S.Hm l (opU S.Hm w F) z = kap S.Hm l w * opU S.Hm w (opW S.d S.Hm l F) z := by
    intro l w z
    rw [opW, (e1 l w F).2.1]
    simp only [opU.eq_1 S.Hm w, opW]
    ring
  have hk0 : ∀ l w : Fin g → ℂ, kap S.Hm l w ≠ 0 := fun l w => Complex.exp_ne_zero _
  obtain ⟨χ, hχd⟩ : ∃ χ : S.La ⧸ A → Multiplicative D →* ℂ, ∀ c w hw,
      χ c (Multiplicative.ofAdd ⟨w, hw⟩) = kap S.Hm (c.out : S.La) w :=
    ⟨fun c =>
      { toFun := fun w => kap S.Hm (c.out : S.La) (Multiplicative.toAdd w : D)
        map_one' := by simp [kap, hf]
        map_mul' := fun w w' => (e6 _ _ _).1 }, fun _ _ _ => rfl⟩
  have hχ : Function.Injective χ := by
    intro c c' h
    rw [← c.out_eq, ← c'.out_eq]
    refine QuotientAddGroup.eq.2 ((hA _).2 fun i => ?_)
    have key : ∀ s, InOK S.d s → ∃ k : ℤ, (h1 S.d (ψ (-c.out + c'.out : S.La) i) s).im = k := by
      intro s hs
      obtain ⟨w, hψs⟩ : ∃ w, ψ w = Pi.single i (s / a i) := ⟨_, hψφ _⟩
      have hw : w ∈ D := (hD w).2 fun j => by
        rw [hψs]
        by_cases hj : j = i
        · subst hj; simpa [mul_div_cancel₀ _ (ha0 _)] using hs
        · exact ⟨0, 0, by simp [hj]⟩
      have h1' : kap S.Hm (c.out : S.La) w = kap S.Hm (c'.out : S.La) w := by
        rw [← hχd c w hw, ← hχd c' w hw, h]
      have h2 := (e6 (c.out : S.La) (-c.out + c'.out : S.La) w).2
      rw [← Submodule.coe_add, add_neg_cancel_left, ← h1'] at h2
      obtain ⟨k, hk⟩ := (kap_eq_one_iff _ _ _).1 ((mul_eq_left₀ (hk0 _ _)).1 h2.symm)
      refine ⟨k, ?_⟩
      rw [← hk, hH, hψs, Finset.sum_eq_single i (fun j _ h => by simp [h, h1]) (by simp), ← natCast_mul_im,
        ← cmLatticeHermitianForm_natCast_mul_right]
      simp [mul_div_cancel₀ _ (ha0 _)]
    obtain ⟨k, hk⟩ := key 1 ⟨1, 0, by simp⟩
    obtain ⟨l, hl⟩ := key (wK S.d) ⟨0, 1, by simp⟩
    exact inOK_of_im hd hk hl
  have hli := (linearIndependent_monoidHom (Multiplicative D) ℂ).comp χ hχ
  obtain ⟨σ, hσ, hne⟩ : ∃ σ ∈ D, (fun z => ∑ c : S.La ⧸ A, opW S.d S.Hm (c.out : S.La) (opU S.Hm σ F) z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h := Fintype.linearIndependent_iff.1 hli (fun c => opW S.d S.Hm (c.out : S.La) F 0) (by
      funext w
      rw [Finset.sum_apply, Pi.zero_apply]
      obtain ⟨σ, hσ⟩ := w
      have h := congrFun (hcon σ hσ) (-σ)
      simp only [hcomm, opU.eq_1 S.Hm σ, neg_add_cancel, ← mul_assoc, ← Finset.sum_mul, Pi.zero_apply] at h
      have h := (mul_eq_zero.1 h).resolve_right (Complex.exp_ne_zero _)
      rw [← h]
      exact Finset.sum_congr rfl fun c _ => by rw [← hχd c σ hσ]; exact mul_comm _ _) 0
    have h0 : (0 : S.La ⧸ A).out ∈ A := (QuotientAddGroup.eq_zero_iff _).1 (Quotient.out_eq _)
    simp only [hW _ ((hA _).1 h0), hF0] at h
    exact one_ne_zero h
  clear c1 c2 c3
  have hth := isTheta_sum S hS A (opU S.Hm σ F) (e3 σ F hFc).1 fun l hl => by
    funext z
    rw [hcomm, hW _ ((hA l).1 hl), (kap_eq_one_iff _ _ _).2 (hint _ ((hA l).1 hl) σ hσ), one_mul]
  let e := (Fintype.equivFin (S.La ⧸ A)).symm
  refine ⟨_, fun j => Complex.exp ((Real.pi : ℂ) * Complex.I *
      ((beta S.d S.Hm ((e j).out : S.La) ((e j).out : S.La)).re : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (((hf S.Hm ((e j).out : S.La) σ).im : ℝ) : ℂ)),
    fun j => ψ (((e j).out : S.La) + σ), _, hth, hne, fun j => mul_mem ?_ ?_, fun j i => ?_, fun z => ?_⟩
  · obtain ⟨u, v, h⟩ := hS.2.2.2.2.2.2.1 _ (e j).out.2 _ (e j).out.2
    have h' : (w0 S.d).re = 1 / 2 := wK_re S.d
    convert exp_rat_mem (u + v / 2) using 3
    rw [h]; simp [h']; ring
  · obtain ⟨r, hr⟩ := hrat _ (hLD _ (e j).out.2) σ hσ
    convert exp_rat_mem (-r) using 2
    rw [hr]; push_cast; ring
  · exact ⟨a i, (ha i).1, (ha i).2, (hD _).1 (D.add_mem (hLD _ (e j).out.2) hσ) i⟩
  · rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [opW, (e1 _ σ F).1, ← hU]
    exact (mul_assoc _ _ _).symm

end GlobalTheory.MomOne
