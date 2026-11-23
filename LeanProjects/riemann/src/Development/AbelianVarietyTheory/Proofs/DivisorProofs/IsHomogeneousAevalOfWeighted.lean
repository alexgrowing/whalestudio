import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbCompEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbeddingStatement

noncomputable section

open MvPolynomial Finset Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer

open Formalism.BasicNotions.DivX (md)

namespace GlobalTheory.HodgeTateGlobal

section General

theorem isHomogeneous_aeval_of_weighted {σ τ : Type} (w : σ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ v, (f v).IsHomogeneous (w v)) {m : ℕ} {G : MvPolynomial σ ℚ} (hG : G.IsWeightedHomogeneous w m) :
    (aeval f G).IsHomogeneous m := by
  induction hG using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isHomogeneous_zero _ _ _
  | add p q _ _ hp hq => rw [map_add]; exact hp.add hq
  | monomial d r hr =>
    rw [aeval_monomial, ← hr, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, algebraMap_eq]
    refine IsHomogeneous.C_mul ?_ r
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    simpa [mul_comm] using (hf i).pow (d i)

theorem real_of_rat {σ ι : Type} [Finite ι] (w : σ → ℕ) (m : ℕ) (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ)
    (U : ι → MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (s : ℕ → ι) (i₀ : ι) (c l e : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (h : ∀ G : MvPolynomial σ ℚ, G.IsWeightedHomogeneous w m →
      L (toR G) = l * ((∑' n : ℕ, c ^ (n + 1) * U (s n) (toR G)) - U i₀ (toR G) / e))
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsWeightedHomogeneous w m) :
    L Q = l * ((∑' n : ℕ, c ^ (n + 1) * U (s n) Q) - U i₀ Q / e) := by
  have hs : ∀ P, Summable fun n : ℕ => c ^ (n + 1) * U (s n) P := fun P => by
    obtain ⟨B, hB⟩ := (Set.finite_range fun i => |U i P|).bddAbove
    refine Summable.of_norm_bounded (g := fun n : ℕ => c ^ n * (c * B))
      ((summable_geometric_of_lt_one hc0 hc1).mul_right _) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), pow_succ, mul_assoc]
    have := hB ⟨s n, rfl⟩
    gcongr
  induction hQ using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq =>
    simp only [map_add, mul_add]
    rw [(hs p).tsum_add (hs q), hp, hq]
    ring
  | monomial d r hr =>
    have e1 : (monomial d r : MvPolynomial σ ℝ) = r • toR (monomial d (1 : ℚ)) := by
      simp [toR, smul_monomial]
    rw [e1]
    simp only [map_smul, smul_eq_mul]
    rw [h _ (isWeightedHomogeneous_monomial w d 1 hr)]
    simp only [mul_left_comm _ r, tsum_mul_left]
    ring

theorem sum_low {A : Type*} [AddCommMonoid A] {N r j : ℕ} (hr : r = j) (hj : j ≤ N) (f : Fin r → A) (g : Fin N → A)
    (h : ∀ (l : Fin r) (i : Fin N), (i : ℕ) = l → f l = g i) :
    ∑ l, f l = ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < j), g i := by
  subst hr
  refine Finset.sum_bij (fun l _ => Fin.castLE hj l) (fun l _ => by simp) (fun a _ b _ e => Fin.castLE_injective hj e)
    (fun i hi => ⟨⟨i, by simpa using hi⟩, mem_univ _, rfl⟩) fun l _ => h _ _ rfl

theorem sum_high {A : Type*} [AddCommMonoid A] {N r j : ℕ} (hr : r = N - j) (f : Fin r → A) (g : Fin N → A)
    (h : ∀ (l : Fin r) (i : Fin N), (i : ℕ) = j + l → f l = g i) :
    ∑ l, f l = ∑ i ∈ univ.filter (fun i : Fin N => j ≤ (i : ℕ)), g i := by
  subst hr
  refine Finset.sum_bij (fun l _ => ⟨j + l, by omega⟩) (fun l _ => by simp)
    (fun a _ b _ e => Fin.ext (by simpa using e))
    (fun i hi => ?_) fun l _ => h _ _ rfl
  have : j ≤ (i : ℕ) := by simpa using hi
  exact ⟨⟨i - j, by omega⟩, mem_univ _, Fin.ext (by simp only; omega)⟩

theorem sum_split {A : Type*} [AddCommMonoid A] {N : ℕ} (j : ℕ) (g : Fin N → A) :
    ∑ i, g i = ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < j), g i +
      ∑ i ∈ univ.filter (fun i : Fin N => j ≤ (i : ℕ)), g i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i : Fin N => (i : ℕ) < j)]
  simp only [not_lt]

theorem capDeg_divP_pow {Z : ITh}
    (hc : ∀ (E E' : Z.VDiv) (a : Z.Ch), Z.capDeg E (Z.cD E' * a) = Z.capDeg E' (Z.cD E * a))
    (a : Z.Ch) (V : Z.VDiv) (n : ℕ) (Q : Z.Ch) :
    Z.capDeg Z.divP ((a + Z.cD V) ^ n * Q) = Z.capDeg Z.divP (a ^ n * Q) := by
  obtain ⟨b, hb⟩ := sub_dvd_pow_sub_pow (a + Z.cD V) a n
  have : (a + Z.cD V) ^ n * Q = a ^ n * Q + Z.cD V * (b * Q) := by linear_combination Q * hb
  rw [this, map_add, hc, Z.cD_divP, zero_mul, map_zero, add_zero]

end General

section Poly

variable {D : D7} {N : ℕ}

def liePow (j k : ℕ) : EmbC D → MvPolynomial (Vm D.what₂.Tau N) ℚ
  | Sum.inl τ => ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < j), X (Sum.inl (false, (τ, i))) ^ k
  | Sum.inr τ => ∑ i ∈ univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-X (Sum.inl (false, (τ, i)))) ^ k

def divDiff (k : ℕ) (r : Rt D.what₂.Tau N) : MvPolynomial (Vm D.what₂.Tau N) ℚ :=
  ∑ a ∈ range k, X (Sum.inl (false, r)) ^ a * X (Sum.inl (true, r)) ^ (k - 1 - a)

theorem homog_X_pow (v : Bool × Rt D.what₂.Tau N) (k : ℕ) :
    (X (Sum.inl v) ^ k : MvPolynomial (Vm D.what₂.Tau N) ℚ).IsWeightedHomogeneous (wt D.what₂.Tau N) k := by
  simpa [wt] using (isWeightedHomogeneous_X ℚ (wt D.what₂.Tau N) (Sum.inl v)).pow k

theorem homog_liePow (j k : ℕ) (σ : EmbC D) :
    (liePow (N := N) j k σ).IsWeightedHomogeneous (wt D.what₂.Tau N) k := by
  rcases σ with τ | τ
  · exact IsWeightedHomogeneous.sum _ _ _ fun i _ => homog_X_pow _ _
  · refine IsWeightedHomogeneous.sum _ _ _ fun i _ => ?_
    have := (isWeightedHomogeneous_C (wt D.what₂.Tau N) ((-1 : ℚ) ^ k)).mul (homog_X_pow (false, (τ, i)) k)
    rw [neg_pow]
    simpa using this

theorem homog_divDiff (k : ℕ) (r : Rt D.what₂.Tau N) :
    (divDiff k r).IsWeightedHomogeneous (wt D.what₂.Tau N) (k - 1) := by
  refine IsWeightedHomogeneous.sum _ _ _ fun a ha => ?_
  have := (homog_X_pow (false, r) a).mul (homog_X_pow (true, r) (k - 1 - a))
  rwa [show a + (k - 1 - a) = k - 1 by have := mem_range.1 ha; omega] at this

theorem chLie_eq (j k : ℕ) (σ : EmbC D) :
    chLie j k σ = C ((Nat.factorial k : ℝ)⁻¹) * collapse D N (toR (liePow j k σ)) := by
  rcases σ with τ | τ <;> simp [chLie, liePow, toR, collapse]

theorem tag_sub (τ : D.what₂.Tau) (k : ℕ) (G : MvPolynomial (Vm D.what₂.Tau N) ℚ) :
    (tagDR D.what₂.Tau N (C ((Nat.factorial k : ℝ)⁻¹) * pk D N τ k) -
      tagHT D.what₂.Tau N (C ((Nat.factorial k : ℝ)⁻¹) * pk D N τ k)) * toR G =
    (Nat.factorial k : ℝ)⁻¹ • ∑ i, dRt D.what₂.Tau N (τ, i) * toR (divDiff k (τ, i) * G) := by
  have h : ∀ i, dRt D.what₂.Tau N (τ, i) * toR (divDiff k (τ, i) * G) =
      (X (Sum.inl (false, (τ, i))) ^ k - X (Sum.inl (true, (τ, i))) ^ k) * toR G := fun i => by
    rw [← geom_sum₂_mul]
    simp only [dRt, divDiff, toR, map_mul, map_sum, map_pow, map_X]
    ring
  simp only [h, tagDR, tagHT, pk, map_mul, map_sum, map_pow, rename_X, rename_C, smul_eq_C_mul]
  rw [← mul_sub, ← Finset.sum_sub_distrib, mul_assoc, Finset.sum_mul]

variable {p : ℕ} [Fact p.Prime] {rk : Emb D p → ℕ} (M : Mdl D p N rk) (rt : Bool × Rt D.what₂.Tau N → M.Z.LB)

theorem homog_evV {m : ℕ} {G : MvPolynomial (Vm D.what₂.Tau N) ℚ} (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau N) m) :
    (evV M rt G).IsHomogeneous m := by
  refine isHomogeneous_aeval_of_weighted _ _ ?_ hG
  rintro (r | ⟨_ | _, k⟩)
  · exact isHomogeneous_X _ _
  all_goals
    exact IsHomogeneous.C_mul ((IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_X_pow _ _).add
      (IsHomogeneous.sum _ _ _ fun l _ => isHomogeneous_X_pow _ _)) _

theorem evC_mul (G H : MvPolynomial (Vm D.what₂.Tau N) ℚ) : evC M rt (G * H) = evC M rt G * evC M rt H := by
  simp [evC, evQ]

theorem evC_divDiff (k : ℕ) (r : Rt D.what₂.Tau N) :
    evC M rt (divDiff k r) = Gk M.Z k (M.Z.c1 (rt (false, r))) (M.Z.c1 (rt (true, r))) := by
  simp [evC, evQ, evV, divDiff, Gk]

theorem evC_liePow_inl (j k : ℕ) (τ : D.what₂.Tau) : evC M rt (liePow j k (Sum.inl τ)) =
    ∑ i ∈ univ.filter (fun i : Fin N => (i : ℕ) < j), M.Z.c1 (rt (false, (τ, i))) ^ k := by
  simp [evC, evQ, evV, liePow]

theorem evC_liePow_inr (j k : ℕ) (τ : D.what₂.Tau) : evC M rt (liePow j k (Sum.inr τ)) =
    ∑ i ∈ univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-M.Z.c1 (rt (false, (τ, i)))) ^ k := by
  simp [evC, evQ, evV, liePow]

end Poly

section Galois

variable {D : D7}

theorem toGG_ofGG (g : D.R.GG) : toGG D (ofGG D g) = g := by
  have hcc : D.R.cc * D.R.cc = 1 := D.R.toFrame.cc_mul_cc
  unfold ofGG
  split_ifs with h h'
  · simp [toGG]
  · simp [toGG, mul_assoc, hcc]
  · exact absurd h' (not_not.2 (by
      by_contra h''
      exact h ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h'')))

variable {p : ℕ} [Fact p.Prime]

theorem comp_phiPow (hp : UnramE D p) (jc : KW p →+* ℂ) (τ : Emb D p) (g : D.R.GG)
    (h : jc.comp τ = D.host.emb g) (n : ℕ) : jc.comp (phiPow D n τ) = D.host.emb (g * frobG D p ^ n) := by
  induction n with
  | zero => rw [pow_zero, mul_one, ← h]; rfl
  | succ n ih =>
    have e : phiPow D (n + 1) τ = phiPow D 1 (phiPow D n τ) := by
      unfold phiPow
      rw [pow_succ', pow_one]; rfl
    have e2 : D.host.sigmaOf (g * frobG D p ^ n * frobG D p) =
        D.host.sigmaOf (g * frobG D p ^ n) * D.host.sigmaOf (frobG D p) :=
      map_mul (D.host.gal).symm _ _
    rw [e, GlobalTheory.T.frobenius_power_embedding D p hp, ← RingHom.comp_assoc, ih, pow_succ (frobG D p), ← mul_assoc]
    unfold Host.emb
    rw [e2]; rfl

theorem exists_cEmb (jc : KW p →+* ℂ) (τ : Emb D p) (τ₀ : D.what₂.Tau)
    (h : jc.comp τ = D.host.emb (toGG D (Sum.inr τ₀))) :
    ∃ τ' : Emb D p, jc.comp τ' = tauEmb D τ₀ ∧ τ = cEmb D τ' := by
  have hcc : D.R.cc * D.R.cc = 1 := D.R.toFrame.cc_mul_cc
  have hc : ∀ (a : Emb D p) g, jc.comp a = D.host.emb g →
      jc.comp (cEmb D a) = D.host.emb (g * D.R.cc) := fun a g e => by
    rw [Formalism.L2.Geo.emb_mul_cc_comp, ← e]; rfl
  have h1 := hc _ _ h
  simp only [toGG, mul_assoc, hcc, mul_one] at h1
  refine ⟨cEmb D τ, h1, RingHom.ext fun x => jc.injective ?_⟩
  exact RingHom.congr_fun (h.trans (hc _ _ h1).symm) x

theorem rkOf_eq (jc : KW p →+* ℂ) (τ : Emb D p) (τ₀ : D.what₂.Tau) (h : jc.comp τ = tauEmb D τ₀) (N j : ℕ) :
    rkOf (PsiOf D jc) N j τ = j := by
  unfold rkOf
  exact if_pos ⟨τ₀, h⟩

end Galois

section Model

variable {D : D7} {XD : DivX D} (T : Loc D XD) {S : letI := D.host.cmStar; HSpace D.host.E} {κ : XD.Lev}
  (hS : HidaSetting D XD S κ) {p : ℕ} [Fact p.Prime] (la : XD.PlP p) (z : XD.Mp S κ p la)

include hS

theorem lie_pow_eq (τ : Emb D p) (σ : EmbC D) (h : (XD.jC p la).comp τ = D.host.emb (toGG D σ)) (k : ℕ) :
    ∑ l, (md XD S κ p la z).Z.c1 (((md XD S κ p la z).lie τ).x l) ^ k =
      evC (md XD S κ p la z) (T.rt S κ p la z) (liePow (XD.shv S κ).j k σ) := by
  rcases σ with τ₀ | τ₀
  · rw [evC_liePow_inl]
    refine sum_low (rkOf_eq _ τ τ₀ h _ _) (XD.shv S κ).j_lt.le _ _ fun l i hi => ?_
    rw [(T.rt_lie S κ hS p la z τ₀ τ h l i hi).1]
  · obtain ⟨τ', h', rfl⟩ := exists_cEmb _ τ τ₀ h
    obtain ⟨e, he⟩ := (md XD S κ p la z).om_dual τ'
    rw [evC_liePow_inr, ← e.sum_comp]
    refine sum_high (by rw [rkOf_eq _ τ' τ₀ h']) _ _ fun l i hi => ?_
    rw [(T.rt_om S κ hS p la z τ₀ τ' h' l i hi).1, he, neg_neg]

omit hS in

theorem chDiv_eq_chern (h5 : adm5 D XD T S κ) {r : ℕ} (x : Fin r → (md XD S κ p la z).Z.LB) {k m : ℕ}
    (hm : k + m = dimFl D.what₂.Tau (XD.shv S κ).N) {H G : MvPolynomial (Vm D.what₂.Tau (XD.shv S κ).N) ℚ}
    (hH : H.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) k)
    (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau (XD.shv S κ).N) m)
    (h : ∀ Q, (md XD S κ p la z).Z.capDeg (md XD S κ p la z).Z.divP
        ((∑ l, (md XD S κ p la z).Z.c1 (x l) ^ k) * Q) =
      (md XD S κ p la z).Z.capDeg (md XD S κ p la z).Z.divP (evC (md XD S κ p la z) (T.rt S κ p la z) H * Q)) :
    chDiv x k (evC (md XD S κ p la z) (T.rt S κ p la z) G) / ((md XD S κ p la z).cov : ℝ) =
      (XD.shv S κ).chern (C ((Nat.factorial k : ℝ)⁻¹) * collapse D _ (toR H) * collapse D _ (toR G)) := by
  have := h5 p la z (H * G) (hm ▸ hH.mul hG)
  rw [chDiv, h, ← evC_mul, div_right_comm, this, mul_assoc, ← smul_eq_C_mul, map_smul, ← map_mul, smul_eq_mul,
    div_eq_inv_mul]
  simp only [toR, map_mul]

end Model

theorem tsum_div_sub (a b : ℕ → ℝ) (u v c e : ℝ) (p k : ℕ) (h : ∀ n, a n / c = b n) (h' : u / c = v) :
    ((∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ * a n) - u / e) / c =
      (∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * b n) - v / e := by
  rw [sub_div, ← tsum_div_const, div_right_comm, h']
  congr 1
  refine tsum_congr fun n => ?_
  rw [mul_div_assoc, h, mul_comm (n + 1), pow_mul, inv_pow]

theorem inv_pow_lt_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) : ((p : ℝ) ^ k)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega))

variable {D : D7} {XD : DivX D} {P : Formalism.MainNotions.DIV.Align.PrinLev XD} {T : Loc D XD}

end GlobalTheory.HodgeTateGlobal

end
