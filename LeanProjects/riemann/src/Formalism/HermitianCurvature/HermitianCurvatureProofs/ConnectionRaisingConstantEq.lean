import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuasiDeterminantFromEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsPFSum

open Matrix Finset Polynomial

namespace Formalism.FourierDecayAlt.P.NFx2

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF

noncomputable section

section Proj

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)

theorem pj_mul (ρ σ : M.Ty P) : proj κ ρ * proj κ σ = if ρ = σ then proj κ ρ else 0 := by
  unfold proj
  rw [← map_mul]
  split_ifs with h
  · subst h; congr 1; funext x; by_cases hx : x = ρ <;> simp [hx]
  · rw [← map_zero κ]; congr 1; funext x; by_cases hx : x = ρ <;> by_cases hy : x = σ <;> simp_all

theorem pj_idem (ρ : M.Ty P) : proj κ ρ * proj κ ρ = proj κ ρ := by simp [pj_mul]

theorem pj_orth {ρ σ : M.Ty P} (h : ρ ≠ σ) : proj κ ρ * proj κ σ = 0 := by simp [pj_mul, h]

theorem sum_pj : ∑ ρ, proj κ ρ = 1 := by
  unfold proj
  rw [← map_sum, ← map_one κ]; congr 1; funext x; simp

theorem kap_eq (f : M.Ty P → ℂ) : κ f = ∑ ρ, f ρ • proj κ ρ := by
  unfold proj
  simp_rw [← map_smul, ← map_sum]; congr 1; funext x; simp

theorem kap_mul_pj (f : M.Ty P → ℂ) (ρ : M.Ty P) : κ f * proj κ ρ = f ρ • proj κ ρ := by
  unfold proj
  rw [← map_mul, ← map_smul]; congr 1; funext x; by_cases hx : x = ρ <;> simp [hx]

theorem pj_mul_kap (f : M.Ty P → ℂ) (ρ : M.Ty P) : proj κ ρ * κ f = f ρ • proj κ ρ := by
  unfold proj
  rw [← map_mul, ← map_smul]; congr 1; funext x; by_cases hx : x = ρ <;> simp [hx]

theorem kap_comm (f g : M.Ty P → ℂ) : κ f * κ g = κ g * κ f := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem decomp (X : A) : X = ∑ σ, ∑ τ, proj κ σ * X * proj κ τ := by
  calc X = (∑ σ, proj κ σ) * X * (∑ τ, proj κ τ) := by rw [sum_pj, one_mul, mul_one]
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; simp_rw [Finset.mul_sum]

theorem eq_of_blocks {X Y : A} (h : ∀ σ τ, proj κ σ * X * proj κ τ = proj κ σ * Y * proj κ τ) : X = Y := by
  rw [decomp κ X, decomp κ Y]; simp_rw [h]

theorem eq_of_rblocks {X Y : A} (h : ∀ τ, X * proj κ τ = Y * proj κ τ) : X = Y := by
  rw [← mul_one X, ← mul_one Y, ← sum_pj κ, Finset.mul_sum, Finset.mul_sum]; simp_rw [h]

theorem xA_xiA {Y : ℂ} (h : Reg P Y) : xA κ Y * xiA κ Y = 1 := by
  unfold xA xiA; rw [← map_mul, ← map_one κ]; congr 1; funext ρ; simp [h ρ]

theorem xiA_xA {Y : ℂ} (h : Reg P Y) : xiA κ Y * xA κ Y = 1 := by
  unfold xA xiA; rw [← map_mul, ← map_one κ]; congr 1; funext ρ; simp [h ρ]

end Proj

section PF

variable {A : Type} [Ring A] [Algebra ℂ A]

def ev (p : A[X]) (Y : ℂ) : A := p.eval₂ (RingHom.id A) (algebraMap ℂ A Y)

def IsPF (f : ℂ → A) : Prop := ∃ p : A[X], ∀ Y, f Y = ev p Y

theorem isPF_const (a : A) : IsPF fun _ : ℂ => a := ⟨C a, fun Y => by simp [ev]⟩

theorem isPF_add {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) : IsPF fun Y => f Y + g Y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun Y => by simp [ev, hp, hq]⟩

theorem isPF_neg {f : ℂ → A} (hf : IsPF f) : IsPF fun Y => -f Y := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun Y => by simp [ev, hp]⟩

theorem isPF_sub {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) : IsPF fun Y => f Y - g Y := by
  simpa [sub_eq_add_neg] using isPF_add hf (isPF_neg hg)

theorem isPF_mul {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) : IsPF fun Y => f Y * g Y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun Y => ?_⟩
  show f Y * g Y = _
  rw [hp, hq, ev, ev, ev, eval₂_mul_noncomm]
  intro k; exact (Algebra.commutes Y _).symm

theorem isPF_sum {ι : Type} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i ∈ s, IsPF (f i)) :
    IsPF fun Y => ∑ i ∈ s, f i Y :=
  _root_.UpperTheory.Reformulated.B.IsPFSum.isPF_sum s hf

theorem isPF_cpoly (Q : ℂ[X]) (a : A) : IsPF fun Y => Q.eval Y • a := by
  refine ⟨Q.map (algebraMap ℂ A) * C a, fun Y => ?_⟩
  rw [ev, eval₂_mul_noncomm, eval₂_map, eval₂_C]
  · simp only [RingHom.id_comp, Algebra.smul_def]
    congr 1
    rw [← Polynomial.eval₂_at_apply]
  · intro k; exact (Algebra.commutes Y _).symm

theorem isPF_smul_fun {f : ℂ → A} (Q : ℂ[X]) (hf : IsPF f) : IsPF fun Y => Q.eval Y • f Y := by
  have := isPF_mul (isPF_cpoly Q (1 : A)) hf
  simpa [smul_mul_assoc] using this

theorem isPF_id_smul (a : A) : IsPF fun Y => Y • a := by simpa using isPF_cpoly (X : ℂ[X]) a

theorem isPF_algebraMap (Q : ℂ[X]) : IsPF fun Y => algebraMap ℂ A (Q.eval Y) := by
  simpa [Algebra.algebraMap_eq_smul_one] using isPF_cpoly Q (1 : A)

theorem isPF_zero {f : ℂ → A} (hf : IsPF f) {S : Set ℂ} (hS : S.Infinite) (h0 : ∀ Y ∈ S, f Y = 0) :
    ∀ Y, f Y = 0 := by
  obtain ⟨p, hp⟩ := hf
  intro Y
  rw [hp, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  let q : ℂ[X] := p.sum fun n a => monomial n (φ a)
  have hq : ∀ Z, q.eval Z = φ (ev p Z) := by
    intro Z
    simp only [q, ev, eval₂_eq_sum, Polynomial.sum, eval_finsetSum, eval_monomial, map_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have : q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine hS.mono fun Z hZ => ?_
    simp only [Set.mem_ofPred_eq, IsRoot, hq, ← hp, h0 Z hZ, map_zero]
  rw [← hq, this, eval_zero]

theorem isPF_eq {f g : ℂ → A} (hf : IsPF f) (hg : IsPF g) {S : Set ℂ} (hS : S.Infinite)
    (h0 : ∀ Y ∈ S, f Y = g Y) : ∀ Y, f Y = g Y := by
  have := isPF_zero (isPF_sub hf hg) hS (fun Y hY => by simp [h0 Y hY])
  intro Y; exact sub_eq_zero.mp (this Y)

theorem cofinite_infinite {S : Set ℂ} (h : Sᶜ.Finite) : S.Infinite := by
  have := h.infinite_compl; simpa using this

theorem real_infinite : {Y : ℂ | star Y = Y}.Infinite := by
  have : Set.range (fun x : ℝ => (x : ℂ)) ⊆ {Y : ℂ | star Y = Y} := by
    rintro _ ⟨x, rfl⟩; simp [Complex.conj_ofReal]
  exact (Set.infinite_range_of_injective Complex.ofReal_injective).mono this

end PF

section Types

open Formalism.FourierDecayAlt.M

theorem rho_succ (P : M.Par) (π : M.Ty P) (i : Fin (P.k - 1)) :
    M.rho P π ((i : ℕ) + 1) = P.lo ((i : ℕ) + 1) + (((π i : Fin _) : ℕ) : ℝ) := by
  rw [Mx3.rho_eq P π _ ⟨by omega, by omega⟩]; congr 3

theorem idx_eq (P : M.Par) (hP : P.OK) (π π' : M.Ty P) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (h : M.rho P π i = M.rho P π' j) : i = j := by
  have hI := Mx3.tyInterlaces P hP π
  have hI' := Mx3.tyInterlaces P hP π'
  rcases lt_trichotomy i j with hij | hij | hij
  · have o := (Mx3.ord P.k P.u P.u' (M.rho P π') hI' i hi).2.2.2 j hj hij
    have b := hI i hi
    linarith [o.1, b.2.2.1]
  · exact hij
  · have o := (Mx3.ord P.k P.u P.u' (M.rho P π) hI j hj).2.2.2 i hi hij
    have b := hI' j hj
    linarith [o.1, b.2.2.1]

theorem ty_ext (P : M.Par) {π π' : M.Ty P} (h : ∀ i ∈ Icc 1 (P.k - 1), M.rho P π i = M.rho P π' i) : π = π' := by
  funext i; apply Fin.ext
  have := h ((i : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rw [rho_succ, rho_succ] at this
  exact_mod_cast add_left_cancel this

theorem up_of_rho (P : M.Par) {l : ℕ} {π π' : M.Ty P}
    (h : ∀ i ∈ Icc 1 (P.k - 1), M.rho P π' i = M.rho P π i + if i = l then 1 else 0) : M.Up P l π π' := by
  intro i
  have := h ((i : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rw [rho_succ, rho_succ] at this
  split_ifs at this with hl
  · simp only [hl, if_true]; exact_mod_cast (by linarith : ((((π' i : Fin _) : ℕ) : ℝ)) = (((π i : Fin _) : ℕ) : ℝ) + 1)
  · simp only [hl, if_false, add_zero]; exact_mod_cast (by linarith : ((((π' i : Fin _) : ℕ) : ℝ)) = (((π i : Fin _) : ℕ) : ℝ))

theorem up_rho (P : M.Par) {l : ℕ} {π π' : M.Ty P} (h : M.Up P l π π') (i : ℕ) (hi : i ∈ Icc 1 (P.k - 1)) :
    M.rho P π' i = M.rho P π i + if i = l then 1 else 0 := Mx3.rhoUp P l π π' h i hi

theorem up_ne (P : M.Par) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {π π' : M.Ty P} (h : M.Up P l π π') : π ≠ π' := by
  rintro rfl
  have := h ⟨l - 1, by have := Finset.mem_Icc.1 hl; omega⟩
  have _hl' := Finset.mem_Icc.1 hl
  simp only at this; split_ifs at this with h' <;> omega

theorem up_right (P : M.Par) {l : ℕ} {π σ σ' : M.Ty P} (h : M.Up P l π σ) (h' : M.Up P l π σ') : σ = σ' := by
  funext i; apply Fin.ext; rw [h i, h' i]

theorem up_left (P : M.Par) {l : ℕ} {π π' σ : M.Ty P} (h : M.Up P l π σ) (h' : M.Up P l π' σ) : π = π' := by
  funext i; apply Fin.ext; have := h i; have := h' i; omega

theorem up_idx (P : M.Par) {l l' : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hl' : l' ∈ Icc 1 (P.k - 1)) {π σ : M.Ty P}
    (h : M.Up P l π σ) (h' : M.Up P l' π σ) : l = l' := by
  by_contra hne
  have a := Finset.mem_Icc.1 hl
  have e1 := h ⟨l - 1, by omega⟩
  have e2 := h' ⟨l - 1, by omega⟩
  simp only at e1 e2
  split_ifs at e1 e2 <;> omega

theorem not_up_up (P : M.Par) {i j l : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hl : l ∈ Icc 1 (P.k - 1)) {τ μ σ : M.Ty P} (h1 : M.Up P i τ μ) (h2 : M.Up P j μ σ) (h3 : M.Up P l τ σ) : False := by
  have a := Finset.mem_Icc.1 hi; have b := Finset.mem_Icc.1 hj; have c := Finset.mem_Icc.1 hl
  have e1 := h1 ⟨l - 1, by omega⟩; have e2 := h2 ⟨l - 1, by omega⟩; have e3 := h3 ⟨l - 1, by omega⟩
  have f1 := h1 ⟨i - 1, by omega⟩; have f2 := h2 ⟨i - 1, by omega⟩; have f3 := h3 ⟨i - 1, by omega⟩
  have g1 := h1 ⟨j - 1, by omega⟩; have g2 := h2 ⟨j - 1, by omega⟩; have g3 := h3 ⟨j - 1, by omega⟩
  simp only at e1 e2 e3 f1 f2 f3 g1 g2 g3
  split_ifs at e1 e2 e3 f1 f2 f3 g1 g2 g3 <;> omega

theorem not_up_down (P : M.Par) {i j l : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hl : l ∈ Icc 1 (P.k - 1)) {τ μ σ : M.Ty P} (h1 : M.Up P i τ μ) (h2 : M.Up P j σ μ) (h3 : M.Up P l τ σ) : False := by
  have a := Finset.mem_Icc.1 hi; have b := Finset.mem_Icc.1 hj; have c := Finset.mem_Icc.1 hl
  have e1 := h1 ⟨l - 1, by omega⟩; have e2 := h2 ⟨l - 1, by omega⟩; have e3 := h3 ⟨l - 1, by omega⟩
  have f1 := h1 ⟨i - 1, by omega⟩; have f2 := h2 ⟨i - 1, by omega⟩; have f3 := h3 ⟨i - 1, by omega⟩
  have g1 := h1 ⟨j - 1, by omega⟩; have g2 := h2 ⟨j - 1, by omega⟩; have g3 := h3 ⟨j - 1, by omega⟩
  simp only at e1 e2 e3 f1 f2 f3 g1 g2 g3
  split_ifs at e1 e2 e3 f1 f2 f3 g1 g2 g3 <;> omega

theorem not_down_up (P : M.Par) {i j l : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1))
    (hl : l ∈ Icc 1 (P.k - 1)) {τ μ σ : M.Ty P} (h1 : M.Up P i μ τ) (h2 : M.Up P j μ σ) (h3 : M.Up P l τ σ) : False := by
  have a := Finset.mem_Icc.1 hi; have b := Finset.mem_Icc.1 hj; have c := Finset.mem_Icc.1 hl
  have e1 := h1 ⟨l - 1, by omega⟩; have e2 := h2 ⟨l - 1, by omega⟩; have e3 := h3 ⟨l - 1, by omega⟩
  have f1 := h1 ⟨i - 1, by omega⟩; have f2 := h2 ⟨i - 1, by omega⟩; have f3 := h3 ⟨i - 1, by omega⟩
  have g1 := h1 ⟨j - 1, by omega⟩; have g2 := h2 ⟨j - 1, by omega⟩; have g3 := h3 ⟨j - 1, by omega⟩
  simp only at e1 e2 e3 f1 f2 f3 g1 g2 g3
  split_ifs at e1 e2 e3 f1 f2 f3 g1 g2 g3 <;> omega

end Types

section Hyp

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem H_kstar (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) : star (κ f) = κ fun ρ => star (f ρ) :=
  h.2.2.2.2.2.2.1 f

theorem H_kops (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) : ∀ g ∈ L0.ops, Commute (κ f) g :=
  h.2.2.2.2.2.2.2.1 f

theorem H_start (h : SHyp P L0 QQ κ) : Wd.IsStart QQ (M.qC P) := h.2.2.2.1

theorem diagonal_entry_hypothesis (h : SHyp P L0 QQ κ) (Y : ℂ) : QQ Y 1 1 = L0.GG * xA κ Y := h.2.2.2.2.2.1 Y

theorem lower_left_commute_self (h : SHyp P L0 QQ κ) (Y Y' : ℂ) : Commute (QQ Y 1 0) (QQ Y' 1 0) := h.2.2.2.2.1 Y Y'

theorem levelSubgroupAtPlace (h : SHyp P L0 QQ κ) (Y : ℂ) :
    QQ Y 1 0 * L0.ζ = L0.ζ * QQ Y 1 0 - QQ Y 1 1 ∧ QQ Y 1 1 * L0.ζ = L0.ζ * QQ Y 1 1 ∧
    QQ Y 0 1 * L0.ζ = L0.ζ * QQ Y 0 1 ∧ QQ Y 0 1 * L0.ζb = L0.ζb * QQ Y 0 1 + QQ Y 1 1 ∧
    QQ Y 1 0 * L0.ζb = L0.ζb * QQ Y 1 0 ∧ QQ Y 1 1 * L0.ζb = L0.ζb * QQ Y 1 1 :=
  h.2.2.2.2.2.2.2.2.2.1 Y

theorem H_crd (h : SHyp P L0 QQ κ) (Y : ℂ) (a b : Fin 2) : ∀ g ∈ L0.crdOps, Commute (QQ Y a b) g :=
  h.2.2.2.2.2.2.2.2.2.2 Y a b

theorem H_poly (h : SHyp P L0 QQ κ) (a b : Fin 2) : IsPF fun Y => QQ Y a b := by
  obtain ⟨n, C, hC, -⟩ := h.2.2.2.2.2.2.2.2.1
  refine ⟨∑ j ∈ Finset.range n, Polynomial.monomial j (C a b j), fun Y => ?_⟩
  show QQ Y a b = _
  rw [hC, ev, Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval₂_monomial, RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]

theorem H_alg_star (h : SHyp P L0 QQ κ) (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (star z) := by
  have e : ∀ w : ℂ, algebraMap ℂ A w = κ (algebraMap ℂ (M.Ty P → ℂ) w) := fun w => (κ.commutes w).symm
  rw [e, e, H_kstar h]; rfl

theorem H_smul_star (h : SHyp P L0 QQ κ) (z : ℂ) (a : A) : star (z • a) = star z • star a := by
  rw [Algebra.smul_def, star_mul, H_alg_star h, ← Algebra.commutes, ← Algebra.smul_def]

theorem H_pj_star (h : SHyp P L0 QQ κ) (ρ : M.Ty P) : star (proj κ ρ) = proj κ ρ := by
  unfold proj; rw [H_kstar h]; congr 1; funext x; split_ifs <;> simp

theorem H_herm (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : star Y = Y) (a b : Fin 2) : star (QQ Y a b) = QQ Y b a := by
  have := congrFun (congrFun ((H_start h).herm Y hY) b) a
  simpa [Matrix.conjTranspose_apply] using this

theorem H_rtt (h : SHyp P L0 QQ κ) (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (QQ u i j * QQ v k l - QQ v k l * QQ u i j) = QQ u k j * QQ v i l - QQ v k j * QQ u i l :=
  Formalism.FourierDecayAlt.P.rtt_relation_entries ℂ A QQ v u ((H_start h).rtt v u) i j k l

theorem quantum_determinant_relation (h : SHyp P L0 QQ κ) (Y : ℂ) :
    QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y) := by
  have := congrFun (congrFun ((H_start h).det Y).2 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] at this
  rw [← this]; noncomm_ring

theorem lower_diagonal_shift_relation (h : SHyp P L0 QQ κ) (Y : ℂ) : QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0 := by
  have := congrFun (congrFun ((H_start h).det Y).2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Formalism.YangianSpanCharacter.T.J] at this
  exact sub_eq_zero.mp (by rw [← this]; noncomm_ring)

end Hyp

section GlobalTheory

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)

def GlobalTheory (R : M.Ty P → M.Ty P → Prop) (X : A) : Prop := ∀ σ τ, ¬ R τ σ → proj κ σ * X * proj κ τ = 0

theorem blk_expand (X Y : A) (σ τ : M.Ty P) :
    proj κ σ * (X * Y) * proj κ τ = ∑ μ, (proj κ σ * X * proj κ μ) * (proj κ μ * Y * proj κ τ) := by
  have : X * Y = X * (∑ μ, proj κ μ) * Y := by rw [sum_pj, mul_one]
  rw [this, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have e : proj κ μ = proj κ μ * proj κ μ := (pj_idem κ μ).symm
  conv_lhs => rw [e]
  noncomm_ring

theorem blk_mul {R S : M.Ty P → M.Ty P → Prop} {X Y : A} (hX : GlobalTheory κ R X) (hY : GlobalTheory κ S Y) :
    GlobalTheory κ (fun τ σ => ∃ μ, S τ μ ∧ R μ σ) (X * Y) := by
  intro σ τ h
  rw [blk_expand]
  refine Finset.sum_eq_zero fun μ _ => ?_
  by_cases h1 : S τ μ
  · have h2 : ¬ R μ σ := fun h2 => h ⟨μ, h1, h2⟩
    rw [hX σ μ h2, zero_mul]
  · rw [hY μ τ h1, mul_zero]

theorem blk_mono {R S : M.Ty P → M.Ty P → Prop} {X : A} (hX : GlobalTheory κ R X) (hRS : ∀ τ σ, R τ σ → S τ σ) :
    GlobalTheory κ S X := fun σ τ h => hX σ τ fun h' => h (hRS τ σ h')

theorem blk_add {R : M.Ty P → M.Ty P → Prop} {X Y : A} (hX : GlobalTheory κ R X) (hY : GlobalTheory κ R Y) : GlobalTheory κ R (X + Y) := by
  intro σ τ h; rw [mul_add, add_mul, hX σ τ h, hY σ τ h, add_zero]

theorem blk_sum {R : M.Ty P → M.Ty P → Prop} {ι : Type} (s : Finset ι) {X : ι → A} (hX : ∀ i ∈ s, GlobalTheory κ R (X i)) :
    GlobalTheory κ R (∑ i ∈ s, X i) := by
  intro σ τ h; rw [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun i hi => hX i hi σ τ h

theorem blk_zero (R : M.Ty P → M.Ty P → Prop) : GlobalTheory κ R (0 : A) := by intro σ τ _; simp

theorem blk_diag {X : A} (hX : ∀ ρ, Commute (proj κ ρ) X) : GlobalTheory κ (fun τ σ => τ = σ) X := by
  intro σ τ h
  rw [(hX σ).eq, mul_assoc, pj_orth κ (Ne.symm h), mul_zero]

theorem blk_star {R : M.Ty P → M.Ty P → Prop} {X : A} (hs : ∀ ρ, star (proj κ ρ) = proj κ ρ) (hX : GlobalTheory κ R X) :
    GlobalTheory κ (fun τ σ => R σ τ) (star X) := by
  intro σ τ h
  have := hX τ σ h
  have e := congrArg star this
  rw [star_mul, star_mul, hs, hs, star_zero, ← mul_assoc] at e
  exact e

theorem ss_pj_none {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ : M.Ty P} (h : ¬ ∃ ρ', M.Up P l ρ ρ') :
    SS l * proj κ ρ = 0 := by
  have := hR l (fun x => if x = ρ then 1 else 0) 0 (by
    intro a b hab
    simp only [Pi.zero_apply]
    split_ifs with hh
    · subst hh; exact absurd ⟨b, hab⟩ h
    · rfl)
  rw [map_zero, zero_mul] at this
  exact this.symm

theorem ss_pj_up {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    proj κ ρ' * SS l = SS l * proj κ ρ := by
  refine hR l _ _ fun a b hab => ?_
  by_cases ha : a = ρ
  · subst ha; have := up_right P hab h; subst this; simp
  · have hb : b ≠ ρ' := fun hb => ha (up_left P hab (hb ▸ h))
    simp [ha, hb]

theorem pj_ss_pj {SS : ℕ → A} (hR : Raises κ SS) {l : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    proj κ ρ' * SS l * proj κ ρ = SS l * proj κ ρ := by
  rw [ss_pj_up κ hR h, mul_assoc, pj_idem]

theorem blk_ss {SS : ℕ → A} (hR : Raises κ SS) (l : ℕ) : GlobalTheory κ (M.Up P l) (SS l) := by
  intro σ τ h
  by_cases hτ : ∃ τ', M.Up P l τ τ'
  · obtain ⟨τ', hτ'⟩ := hτ
    have hne : σ ≠ τ' := fun e => h (e ▸ hτ')
    rw [mul_assoc, ← ss_pj_up κ hR hτ', ← mul_assoc, pj_orth κ hne, zero_mul]
  · rw [mul_assoc, ss_pj_none κ hR hτ, mul_zero]

theorem blk_kap (f : M.Ty P → ℂ) : GlobalTheory κ (fun τ σ => τ = σ) (κ f) :=
  blk_diag κ fun ρ => by unfold proj; exact kap_comm κ _ _

end GlobalTheory

section Regular

theorem xC_ne_of_im (P : M.Par) (ρ : M.Ty P) {Y : ℂ} (h : Y.im ≠ 0) : M.xC P ρ Y ≠ 0 := by
  unfold M.xC
  rw [Finset.prod_ne_zero_iff]
  intro i _ h0
  apply h
  have := congrArg Complex.im h0
  simpa using this

theorem reg_of_im (P : M.Par) {Y : ℂ} (h : Y.im ≠ 0) : Reg P Y := fun ρ => xC_ne_of_im P ρ h

theorem nreg_finite (P : M.Par) : {Y : ℂ | ¬ Reg P Y}.Finite := by
  have : {Y : ℂ | ¬ Reg P Y} ⊆ ⋃ ρ : M.Ty P, ⋃ i ∈ Icc 1 (P.k - 1), {-((M.rho P ρ i : ℝ) : ℂ)} := by
    intro Y hY
    simp only [Reg, not_forall, not_not, Set.mem_setOf_eq] at hY
    obtain ⟨ρ, hρ⟩ := hY
    unfold M.xC at hρ
    obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.1 hρ
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨ρ, i, hi, by linear_combination h0⟩
  refine Set.Finite.subset ?_ this
  exact Set.finite_iUnion fun ρ => Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => Set.finite_singleton _

theorem reg_infinite (P : M.Par) : {Y : ℂ | Reg P Y}.Infinite := by
  apply cofinite_infinite
  simpa [Set.compl_setOf] using nreg_finite P

theorem regular_pairs_infinite (P : M.Par) : {Y : ℂ | Reg P Y ∧ Reg P (Y + 1)}.Infinite := by
  apply cofinite_infinite
  have h2 : {Y : ℂ | ¬ Reg P (Y + 1)}.Finite := by
    have := (nreg_finite P).preimage (f := fun Y : ℂ => Y + 1) (add_left_injective 1).injOn
    simpa using this
  refine ((nreg_finite P).union h2).subset ?_
  intro Y hY
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hY
  rcases hY with h | h
  · exact Or.inl h
  · exact Or.inr h

end Regular

section SB

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem sb_mem_GG : L0.GG ∈ L0.ops := by simp [PreLevel.ops, PreLevel.fns]
theorem sb_mem_GGi : L0.GGi ∈ L0.ops := by simp [PreLevel.ops, PreLevel.fns]
theorem sb_mem_ζ : L0.ζ ∈ L0.ops := by simp [PreLevel.ops, PreLevel.fns]
theorem sb_mem_ζb : L0.ζb ∈ L0.ops := by simp [PreLevel.ops, PreLevel.fns]

theorem sb_pj_GG (h : SHyp P L0 QQ κ) (ρ : M.Ty P) : proj κ ρ * L0.GG = L0.GG * proj κ ρ :=
  (H_kops h _ _ sb_mem_GG).eq

theorem sb_pj_GGi (h : SHyp P L0 QQ κ) (ρ : M.Ty P) : proj κ ρ * L0.GGi = L0.GGi * proj κ ρ :=
  (H_kops h _ _ sb_mem_GGi).eq

theorem sb_pj_ζb (h : SHyp P L0 QQ κ) (ρ : M.Ty P) : proj κ ρ * L0.ζb = L0.ζb * proj κ ρ :=
  (H_kops h _ _ sb_mem_ζb).eq

theorem sb_x_ζb (h : SHyp P L0 QQ κ) (v : ℂ) : xA κ v * L0.ζb = L0.ζb * xA κ v :=
  (H_kops h _ _ sb_mem_ζb).eq

theorem sb_GG_ζb : L0.GG * L0.ζb = L0.ζb * L0.GG :=
  L0.fns_comm _ (by simp) _ (by simp)

theorem sb_GGi_ζb : L0.GGi * L0.ζb = L0.ζb * L0.GGi :=
  L0.fns_comm _ (by simp) _ (by simp)

theorem lower_left_gamma_commutator (h : SHyp P L0 QQ κ) (v : ℂ) :
    QQ v 1 0 * L0.GG = L0.GG * QQ v 1 0 - QQ v 1 1 * L0.ζb := by
  obtain ⟨e1, -, -, -, e5, -⟩ := levelSubgroupAtPlace h v
  have e2 : QQ v 1 0 * algebraMap ℂ A L0.TT = algebraMap ℂ A L0.TT * QQ v 1 0 := (Algebra.commutes _ _).symm
  rw [L0.GG_def, mul_sub, sub_mul, e2, ← mul_assoc, e1, sub_mul, mul_assoc, e5]
  noncomm_ring

def lowerBlockAlt (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (σ ρ : M.Ty P) (v : ℂ) : A :=
  proj κ σ * QQ v 1 0 * proj κ ρ

theorem projection_mul_coordinate (σ : M.Ty P) (u : ℂ) : proj κ σ * xA κ u = M.xC P σ u • proj κ σ :=
  pj_mul_kap κ (fun ρ => M.xC P ρ u) σ

theorem sb_x_pj (σ : M.Ty P) (u : ℂ) : xA κ u * proj κ σ = M.xC P σ u • proj κ σ :=
  kap_mul_pj κ (fun ρ => M.xC P ρ u) σ

theorem sb_sand1 (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (u v : ℂ) :
    proj κ σ * (QQ u 1 1 * QQ v 1 0) * proj κ ρ = L0.GG * (M.xC P σ u • lowerBlockAlt κ QQ σ ρ v) := by
  rw [diagonal_entry_hypothesis h, lowerBlockAlt]
  calc proj κ σ * (L0.GG * xA κ u * QQ v 1 0) * proj κ ρ
      = (proj κ σ * L0.GG) * xA κ u * QQ v 1 0 * proj κ ρ := by noncomm_ring
    _ = L0.GG * (proj κ σ * xA κ u) * QQ v 1 0 * proj κ ρ := by rw [sb_pj_GG h]; noncomm_ring
    _ = _ := by rw [projection_mul_coordinate]; simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]

theorem sb_sand2 (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (u v : ℂ) :
    proj κ σ * (QQ v 1 0 * QQ u 1 1) * proj κ ρ =
      L0.GG * (M.xC P ρ u • lowerBlockAlt κ QQ σ ρ v - (M.xC P σ v * M.xC P ρ u) • (L0.ζb * (proj κ σ * proj κ ρ))) := by
  rw [diagonal_entry_hypothesis h, lowerBlockAlt]
  have e := lower_left_gamma_commutator h v
  rw [diagonal_entry_hypothesis h] at e
  calc proj κ σ * (QQ v 1 0 * (L0.GG * xA κ u)) * proj κ ρ
      = proj κ σ * (QQ v 1 0 * L0.GG) * (xA κ u * proj κ ρ) := by noncomm_ring
    _ = proj κ σ * (L0.GG * QQ v 1 0 - L0.GG * xA κ v * L0.ζb) * (M.xC P ρ u • proj κ ρ) := by rw [e, sb_x_pj]
    _ = M.xC P ρ u • ((proj κ σ * L0.GG) * QQ v 1 0 * proj κ ρ) -
          M.xC P ρ u • ((proj κ σ * L0.GG) * (xA κ v * L0.ζb) * proj κ ρ) := by
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_sub, mul_assoc]
    _ = M.xC P ρ u • (L0.GG * (proj κ σ * QQ v 1 0 * proj κ ρ)) -
          M.xC P ρ u • (L0.GG * ((proj κ σ * xA κ v) * L0.ζb * proj κ ρ)) := by
        rw [sb_pj_GG h]; simp only [mul_assoc]
    _ = _ := by
        rw [projection_mul_coordinate, smul_mul_assoc, smul_mul_assoc, sb_pj_ζb h]
        simp only [mul_sub, mul_smul_comm, smul_smul, mul_assoc]
        congr 1; rw [mul_comm (M.xC P σ v)]

theorem sb_feq (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (u v : ℂ) :
    (u - v) • (M.xC P σ u • lowerBlockAlt κ QQ σ ρ v -
      (M.xC P ρ u • lowerBlockAlt κ QQ σ ρ v - (M.xC P σ v * M.xC P ρ u) • (L0.ζb * (proj κ σ * proj κ ρ)))) =
      M.xC P σ u • lowerBlockAlt κ QQ σ ρ v - M.xC P σ v • lowerBlockAlt κ QQ σ ρ u := by
  have r := H_rtt h u v 1 1 1 0
  have r2 := congrArg (fun Z => L0.GGi * (proj κ σ * Z * proj κ ρ)) r
  simp only [smul_sub, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc] at r2
  rw [sb_sand1 h, sb_sand2 h, sb_sand1 h] at r2
  have cancel : ∀ Z : A, L0.GGi * (L0.GG * Z) = Z := fun Z => by rw [← mul_assoc, L0.GGi_GG, one_mul]
  simp only [cancel] at r2
  rw [smul_sub]
  exact r2

theorem sb_T_pj (σ ρ : M.Ty P) (v : ℂ) : lowerBlockAlt κ QQ σ ρ v * proj κ ρ = lowerBlockAlt κ QQ σ ρ v := by
  rw [lowerBlockAlt, mul_assoc, pj_idem]

theorem sb_diag (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {u v : ℂ} (hu : M.xC P ρ u ≠ 0) (hv : M.xC P ρ v ≠ 0) :
    (M.xC P ρ u)⁻¹ • lowerBlockAlt κ QQ ρ ρ u + u • (L0.ζb * proj κ ρ) =
      (M.xC P ρ v)⁻¹ • lowerBlockAlt κ QQ ρ ρ v + v • (L0.ζb * proj κ ρ) := by
  have e := sb_feq h ρ ρ u v
  rw [pj_idem] at e
  have key : (M.xC P ρ u * M.xC P ρ v) • ((M.xC P ρ u)⁻¹ • lowerBlockAlt κ QQ ρ ρ u + u • (L0.ζb * proj κ ρ)) =
      (M.xC P ρ u * M.xC P ρ v) • ((M.xC P ρ v)⁻¹ • lowerBlockAlt κ QQ ρ ρ v + v • (L0.ζb * proj κ ρ)) := by
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    rw [show M.xC P ρ u * M.xC P ρ v * (M.xC P ρ u)⁻¹ = M.xC P ρ v by field_simp,
      show M.xC P ρ u * M.xC P ρ v * (M.xC P ρ v)⁻¹ = M.xC P ρ u by field_simp]
    linear_combination (norm := module) e
  exact smul_right_injective A (mul_ne_zero hu hv) key

theorem sb_xC_zero {π : M.Ty P} {Y : ℂ} (h : M.xC P π Y = 0) :
    ∃ i ∈ Icc 1 (P.k - 1), Y = -((M.rho P π i : ℝ) : ℂ) := by
  unfold M.xC at h
  obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.1 h
  exact ⟨i, hi, by linear_combination h0⟩

theorem sb_xC_root (π : M.Ty P) {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) : M.xC P π (-((M.rho P π i : ℝ) : ℂ)) = 0 := by
  unfold M.xC
  exact Finset.prod_eq_zero hi (by ring)

theorem type_eq_of_coordinate (hP : P.OK) {σ ρ : M.Ty P} (hx : ∀ u, M.xC P σ u = M.xC P ρ u) : σ = ρ := by
  apply ty_ext P
  intro i hi
  have h0 : M.xC P σ (-((M.rho P ρ i : ℝ) : ℂ)) = 0 := by rw [hx]; exact sb_xC_root ρ hi
  obtain ⟨j, hj, e⟩ := sb_xC_zero h0
  have e' : M.rho P ρ i = M.rho P σ j := by exact_mod_cast neg_injective e
  have := idx_eq P hP ρ σ hi hj e'
  subst this; exact e'.symm

theorem sb_roots (hP : P.OK) {σ ρ : M.Ty P} (hne : σ ≠ ρ) {c : ℂ}
    (hc : ∀ u, M.xC P σ u * (u + c - 1) = M.xC P ρ u * (u + c)) :
    ∃ m ∈ Icc 1 (P.k - 1), M.Up P m ρ σ ∧ c = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by
  have ha := hc (1 - c)
  have hxa : M.xC P ρ (1 - c) = 0 := by
    rw [show (1 - c + c - 1 : ℂ) = 0 by ring, show (1 - c + c : ℂ) = 1 by ring, mul_zero, mul_one] at ha
    exact ha.symm
  obtain ⟨m, hm, em⟩ := sb_xC_zero hxa
  have hcm : c = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by linear_combination -em

  have hb : ∀ i ∈ Icc 1 (P.k - 1), i ≠ m → M.rho P σ i = M.rho P ρ i := by
    intro i hi him
    have e := hc (-((M.rho P ρ i : ℝ) : ℂ))
    rw [sb_xC_root ρ hi, zero_mul, mul_eq_zero] at e
    rcases e with e | e
    · obtain ⟨j, hj, ej⟩ := sb_xC_zero e
      have ej' : M.rho P ρ i = M.rho P σ j := by exact_mod_cast neg_injective ej
      have := idx_eq P hP ρ σ hi hj ej'
      subst this; exact ej'.symm
    · exfalso; apply him
      have : M.rho P ρ i = M.rho P ρ m := by
        have : ((M.rho P ρ i : ℝ) : ℂ) = ((M.rho P ρ m : ℝ) : ℂ) := by linear_combination -e + hcm
        exact_mod_cast this
      exact idx_eq P hP ρ ρ hi hm this
  have hmm : M.rho P σ m = M.rho P ρ m + 1 := by
    have e := hc (-((M.rho P σ m : ℝ) : ℂ))
    rw [sb_xC_root σ hm, zero_mul] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exfalso; apply hne
      obtain ⟨j, hj, ej⟩ := sb_xC_zero e
      have ej' : M.rho P σ m = M.rho P ρ j := by exact_mod_cast neg_injective ej
      have := idx_eq P hP σ ρ hm hj ej'
      subst this
      apply ty_ext P
      intro i hi
      by_cases him : i = m
      · subst him; exact ej'
      · exact hb i hi him
    · have : ((M.rho P σ m : ℝ) : ℂ) = ((M.rho P ρ m : ℝ) : ℂ) + 1 := by linear_combination -e + hcm
      exact_mod_cast this
  refine ⟨m, hm, up_of_rho P fun i hi => ?_, hcm⟩
  by_cases him : i = m
  · subst him; simp [hmm]
  · simp [him, hb i hi him]

theorem sb_off (h : SHyp P L0 QQ κ) (hP : P.OK) {σ ρ : M.Ty P} (hne : σ ≠ ρ) :
    (∀ v, lowerBlockAlt κ QQ σ ρ v = 0) ∨ ∃ m ∈ Icc 1 (P.k - 1), M.Up P m ρ σ ∧
      ∃ K : A, ∀ v, (v + ((M.rho P ρ m : ℝ) : ℂ) + 1) • lowerBlockAlt κ QQ σ ρ v = M.xC P σ v • K := by
  set T := lowerBlockAlt κ QQ σ ρ with hTdef
  set xs := M.xC P σ
  set xr := M.xC P ρ
  have O : ∀ u v, (u - v) • (xs u • T v - xr u • T v) = xs u • T v - xs v • T u := by
    intro u v
    have e := sb_feq h σ ρ u v
    rw [pj_orth κ hne, mul_zero, smul_zero, sub_zero] at e
    exact e
  have S : ∀ u v, (xs u - xr u) • T v = (xs v - xr v) • T u := by
    intro u v
    by_cases huv : u = v
    · subst huv; rfl
    · have e1 := O u v
      have e2 := O v u
      have : (u - v) • ((xs u - xr u) • T v - (xs v - xr v) • T u) = 0 := by
        linear_combination (norm := module) e1 + e2
      rcases smul_eq_zero.1 this with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) huv
      · exact sub_eq_zero.1 h0
  by_cases hD : ∀ u, xs u - xr u = 0
  · exact absurd (type_eq_of_coordinate hP fun u => sub_eq_zero.1 (hD u)) hne
  push Not at hD
  obtain ⟨u0, hu0⟩ := hD
  set K := (xs u0 - xr u0)⁻¹ • T u0
  have hT : ∀ v, T v = (xs v - xr v) • K := by
    intro v
    have e := S u0 v
    have : T v = (xs u0 - xr u0)⁻¹ • ((xs u0 - xr u0) • T v) := by rw [smul_smul, inv_mul_cancel₀ hu0, one_smul]
    rw [this, e, smul_smul, smul_smul, mul_comm]
  by_cases hK : K = 0
  · left; intro v; rw [hT v, hK, smul_zero]
  right
  have hsc : ∀ u v, ((u - v) * (xs u - xr u) - xs u) * (xs v - xr v) + xs v * (xs u - xr u) = 0 := by
    intro u v
    have e := O u v
    rw [hT u, hT v] at e
    have : (((u - v) * (xs u - xr u) - xs u) * (xs v - xr v) + xs v * (xs u - xr u)) • K = 0 := by
      linear_combination (norm := module) e
    exact (smul_eq_zero.1 this).resolve_right hK
  set c0 := xs u0 / (xs u0 - xr u0) - u0
  have hxs : ∀ u, xs u = (xs u - xr u) * (u + c0) := by
    intro u
    have e := hsc u u0
    apply mul_right_cancel₀ hu0
    have hdc : xs u0 / (xs u0 - xr u0) * (xs u0 - xr u0) = xs u0 := div_mul_cancel₀ _ hu0
    simp only [c0]
    linear_combination -e - (xs u - xr u) * hdc
  have hc : ∀ u, xs u * (u + c0 - 1) = xr u * (u + c0) := by
    intro u
    have e := hxs u
    linear_combination (-1 : ℂ) * e
  obtain ⟨m, hm, hup, hcm⟩ := sb_roots hP hne hc
  refine ⟨m, hm, hup, K, fun v => ?_⟩
  rw [hT v, smul_smul]
  congr 1
  have e := hxs v
  rw [hcm] at e
  linear_combination (-1 : ℂ) * e

def regular_base_point : ℂ := Complex.I

theorem regular_base_point_reg : Reg P regular_base_point := reg_of_im P (by simp [regular_base_point])

def sb_K (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (l : ℕ) (ρ σ : M.Ty P) : A :=
  ((regular_base_point + ((M.rho P ρ l : ℝ) : ℂ) + 1) / M.xC P σ regular_base_point) • lowerBlockAlt κ QQ σ ρ regular_base_point

def sb_SS (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (l : ℕ) : A :=
  ∑ ρ : M.Ty P, ∑ σ : M.Ty P, if l ∈ Icc 1 (P.k - 1) ∧ M.Up P l ρ σ then sb_K κ QQ l ρ σ else 0

def sb_b (L0 : PreLevel A P.r) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (ρ : M.Ty P) : A :=
  L0.GGi * ((M.xC P ρ regular_base_point)⁻¹ • lowerBlockAlt κ QQ ρ ρ regular_base_point + regular_base_point • (L0.ζb * proj κ ρ))

theorem sb_T_pj' (σ ρ' ρ : M.Ty P) (v : ℂ) :
    lowerBlockAlt κ QQ σ ρ' v * proj κ ρ = if ρ' = ρ then lowerBlockAlt κ QQ σ ρ v else 0 := by
  rw [lowerBlockAlt, mul_assoc, pj_mul]
  split_ifs with h
  · subst h; rfl
  · rw [mul_zero]

theorem sb_K_pj (l : ℕ) (ρ' σ ρ : M.Ty P) :
    sb_K κ QQ l ρ' σ * proj κ ρ = if ρ' = ρ then sb_K κ QQ l ρ σ else 0 := by
  rw [sb_K, smul_mul_assoc, sb_T_pj']
  split_ifs with h
  · subst h; rfl
  · rw [smul_zero]

theorem sb_SS_pj {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P} (hup : M.Up P l ρ σ) :
    sb_SS κ QQ l * proj κ ρ = sb_K κ QQ l ρ σ := by
  rw [sb_SS, Finset.sum_mul, Finset.sum_eq_single ρ]
  · rw [Finset.sum_mul, Finset.sum_eq_single σ]
    · rw [if_pos ⟨hl, hup⟩, sb_K_pj, if_pos rfl]
    · intro σ' _ hσ'
      rw [if_neg]; · rw [zero_mul]
      rintro ⟨-, hup'⟩; exact hσ' (up_right P hup' hup)
    · simp
  · intro ρ' _ hρ'
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun σ' _ => ?_
    split_ifs
    · rw [sb_K_pj, if_neg hρ']
    · rw [zero_mul]
  · simp

theorem sb_up_factor {σ : M.Ty P} {Y : ℂ} (hY : M.xC P σ Y ≠ 0) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    Y + ((M.rho P σ l : ℝ) : ℂ) ≠ 0 := by
  unfold M.xC at hY
  exact (Finset.prod_ne_zero_iff.1 hY) l hl

theorem sb_K_eval (h : SHyp P L0 QQ κ) (hP : P.OK) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ σ : M.Ty P}
    (hup : M.Up P l ρ σ) {Y : ℂ} (hY : Reg P Y) :
    (Y + ((M.rho P ρ l : ℝ) : ℂ) + 1)⁻¹ • sb_K κ QQ l ρ σ = (M.xC P σ Y)⁻¹ • lowerBlockAlt κ QQ σ ρ Y := by
  have hne : σ ≠ ρ := fun e => up_ne P hl hup e.symm
  have hσl : M.rho P σ l = M.rho P ρ l + 1 := by
    have := up_rho P hup l hl; simpa using this
  have hfac : ∀ Z : ℂ, Reg P Z → Z + ((M.rho P ρ l : ℝ) : ℂ) + 1 ≠ 0 := by
    intro Z hZ
    have := sb_up_factor (hZ σ) hl
    rw [hσl] at this; push_cast at this; rwa [← add_assoc] at this
  rcases sb_off h hP hne with h0 | ⟨m, hm, hupm, K, hK⟩
  · simp [sb_K, h0]
  · have hml : m = l := up_idx P hm hl hupm hup
    subst hml
    have h0 := regular_base_point_reg (P := P)
    have hKK : sb_K κ QQ m ρ σ = K := by
      rw [sb_K, div_eq_mul_inv, mul_comm, ← smul_smul, hK regular_base_point, smul_smul, inv_mul_cancel₀ (h0 σ), one_smul]
    have hTY : lowerBlockAlt κ QQ σ ρ Y = ((Y + ((M.rho P ρ m : ℝ) : ℂ) + 1)⁻¹ * M.xC P σ Y) • K := by
      rw [← smul_smul, ← hK Y, smul_smul, inv_mul_cancel₀ (hfac Y hY), one_smul]
    rw [hKK, hTY, smul_smul]
    congr 1
    field_simp [hY σ]

theorem sb_lA_blk (h : SHyp P L0 QQ κ) (σ ρ : M.Ty P) (Y : ℂ) :
    proj κ σ * lA L0 QQ κ Y * proj κ ρ = (M.xC P σ Y)⁻¹ • (L0.GGi * lowerBlockAlt κ QQ σ ρ Y) := by
  unfold lA xiA
  rw [← mul_assoc, ← mul_assoc, pj_mul_kap, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, sb_pj_GGi h, lowerBlockAlt]
  simp only [mul_assoc]

theorem sb_diag_form (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {Y : ℂ} (hY : Reg P Y) :
    (sb_b L0 κ QQ ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ = (M.xC P ρ Y)⁻¹ • (L0.GGi * lowerBlockAlt κ QQ ρ ρ Y) := by
  have e := sb_diag h ρ (regular_base_point_reg ρ) (hY ρ)
  have e1 : sb_b L0 κ QQ ρ * proj κ ρ = L0.GGi * ((M.xC P ρ regular_base_point)⁻¹ • lowerBlockAlt κ QQ ρ ρ regular_base_point + regular_base_point • (L0.ζb * proj κ ρ)) := by
    rw [sb_b, mul_assoc, add_mul, smul_mul_assoc, smul_mul_assoc, sb_T_pj, mul_assoc, pj_idem]
  rw [sub_mul, e1, e, smul_mul_assoc, mul_assoc,
    show L0.ζb * (L0.GGi * proj κ ρ) = L0.GGi * (L0.ζb * proj κ ρ) by rw [← mul_assoc, ← sb_GGi_ζb, mul_assoc],
    mul_add, mul_smul_comm, mul_smul_comm]
  abel

theorem sb_form (h : SHyp P L0 QQ κ) (hP : P.OK) : SForm P L0 QQ κ (sb_b L0 κ QQ) (sb_SS κ QQ) := by
  intro Y hY ρ ρ'
  rw [sb_lA_blk h]
  by_cases hρ : ρ' = ρ
  · subst hρ
    rw [if_pos rfl, Finset.sum_eq_zero (fun l hl => if_neg (fun hu => up_ne P hl hu rfl)), add_zero,
      sb_diag_form h ρ' hY]
  · rw [if_neg hρ, zero_add]
    by_cases hex : ∃ l ∈ Icc 1 (P.k - 1), M.Up P l ρ ρ'
    · obtain ⟨l, hl, hup⟩ := hex
      rw [Finset.sum_eq_single l]
      · rw [if_pos hup, mul_assoc, sb_SS_pj hl hup, ← mul_smul_comm (Y + ((M.rho P ρ l : ℝ) : ℂ) + 1)⁻¹,
          sb_K_eval h hP hl hup hY, mul_smul_comm]
      · intro l' hl' hne
        rw [if_neg]; intro hup'; exact hne (up_idx P hl' hl hup' hup)
      · intro hl'; exact absurd hl hl'
    · rw [Finset.sum_eq_zero]
      · rcases sb_off h hP hρ with h0 | ⟨m, hm, hup, -⟩
        · rw [h0]; simp
        · exact absurd ⟨m, hm, hup⟩ hex
      · intro l hl; rw [if_neg]; intro hup; exact hex ⟨l, hl, hup⟩

theorem sb_raises : Raises κ (sb_SS κ QQ) := by
  intro l f g hfg
  unfold sb_SS
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with hc
  · have e1 : κ g * lowerBlockAlt κ QQ σ ρ regular_base_point = g σ • lowerBlockAlt κ QQ σ ρ regular_base_point := by
      rw [lowerBlockAlt, ← mul_assoc, ← mul_assoc, kap_mul_pj, smul_mul_assoc, smul_mul_assoc]
    have e2 : lowerBlockAlt κ QQ σ ρ regular_base_point * κ f = f ρ • lowerBlockAlt κ QQ σ ρ regular_base_point := by
      rw [lowerBlockAlt, mul_assoc, pj_mul_kap, mul_smul_comm]
    rw [sb_K, mul_smul_comm, smul_mul_assoc, e1, e2, hfg ρ σ hc.2]
  · rw [mul_zero, zero_mul]

theorem sb_comm_inv {X a ai : A} (h : Commute X a) (h1 : a * ai = 1) (h2 : ai * a = 1) : Commute X ai := by
  show X * ai = ai * X
  calc X * ai = (ai * a) * X * ai := by rw [h2, one_mul]
    _ = ai * (a * X) * ai := by noncomm_ring
    _ = ai * (X * a) * ai := by rw [h.eq]
    _ = ai * X * (a * ai) := by noncomm_ring
    _ = ai * X := by rw [h1, mul_one]

theorem sb_comm_ops {X : A} (hz : Commute X L0.ζ) (hzb : Commute X L0.ζb) (hc : ∀ g ∈ L0.crdOps, Commute X g) :
    ∀ g ∈ L0.ops, Commute X g := by
  have hGG : Commute X L0.GG := by
    rw [L0.GG_def]; exact (hz.mul_right hzb).sub_right (Algebra.commutes _ X).symm
  intro g hg
  simp only [PreLevel.ops, PreLevel.fns, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range] at hg
  rcases hg with (((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl)) | ⟨i, rfl⟩) |
      ⟨i, rfl⟩
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hz
  · exact sb_comm_inv hz L0.ζ_ζi L0.ζi_ζ
  · exact hzb
  · exact sb_comm_inv hzb L0.ζb_ζbi L0.ζbi_ζb
  · exact hGG
  · exact sb_comm_inv hGG L0.GG_GGi L0.GGi_GG
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])

theorem sb_crd_sub_ops {g : A} (hg : g ∈ L0.crdOps) : g ∈ L0.ops := by
  simp only [PreLevel.crdOps, PreLevel.ops, PreLevel.fns, Set.mem_union] at hg ⊢
  tauto

theorem sb_T_comm (h : SHyp P L0 QQ κ) {σ ρ : M.Ty P} (hne : σ ≠ ρ) (v : ℂ) :
    ∀ g ∈ L0.ops, Commute (lowerBlockAlt κ QQ σ ρ v) g := by
  obtain ⟨e1, -, -, -, e5, -⟩ := levelSubgroupAtPlace h v
  have hPz : ∀ τ, Commute (proj κ τ) L0.ζ := fun τ => H_kops h _ _ sb_mem_ζ
  have hPzb : ∀ τ, Commute (proj κ τ) L0.ζb := fun τ => H_kops h _ _ sb_mem_ζb
  have h22 : proj κ σ * QQ v 1 1 * proj κ ρ = 0 := by
    rw [diagonal_entry_hypothesis h, ← mul_assoc, sb_pj_GG h, mul_assoc, mul_assoc, sb_x_pj, mul_smul_comm,
      pj_orth κ hne, smul_zero, mul_zero]
  apply sb_comm_ops
  · show lowerBlockAlt κ QQ σ ρ v * L0.ζ = L0.ζ * lowerBlockAlt κ QQ σ ρ v
    rw [lowerBlockAlt, mul_assoc, (hPz ρ).eq, ← mul_assoc, mul_assoc (proj κ σ), e1, mul_sub, sub_mul, h22, sub_zero,
      ← mul_assoc, (hPz σ).eq]
    simp only [mul_assoc]
  · show lowerBlockAlt κ QQ σ ρ v * L0.ζb = L0.ζb * lowerBlockAlt κ QQ σ ρ v
    rw [lowerBlockAlt, mul_assoc, (hPzb ρ).eq, ← mul_assoc, mul_assoc (proj κ σ), e5, ← mul_assoc, (hPzb σ).eq]
    simp only [mul_assoc]
  · intro g hg
    have hp : ∀ τ, Commute (proj κ τ) g := fun τ => H_kops h _ _ (sb_crd_sub_ops hg)
    exact ((hp σ).mul_left (H_crd h v 1 0 g hg)).mul_left (hp ρ)

theorem sb_SS_comm (h : SHyp P L0 QQ κ) (l : ℕ) : ∀ g ∈ L0.ops, Commute (sb_SS κ QQ l) g := by
  intro g hg
  unfold sb_SS
  refine Commute.sum_left _ _ _ fun ρ _ => Commute.sum_left _ _ _ fun σ _ => ?_
  split_ifs with hc
  · have hne : σ ≠ ρ := fun e => up_ne P hc.1 hc.2 e.symm
    exact (sb_T_comm h hne regular_base_point g hg).smul_left _
  · exact Commute.zero_left g

theorem sb_main : SBlock := by
  intro _ _ _ P A _ _ _ L0 QQ κ hP h
  exact ⟨sb_b L0 κ QQ, sb_SS κ QQ, sb_form h hP, sb_raises, fun l => sb_SS_comm h l⟩

end SB

section SN

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem sn_kc (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) :
    ∀ g ∈ L.fns ∪ {L.nab, L.nabs}, Commute (κ f) g := hc.2.1 f

theorem sn_kG (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) : Commute (κ f) L.GG :=
  sn_kc hc f _ (by simp [R.LevelData.fns])

theorem sn_kGi (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) : Commute (κ f) L.GGi :=
  sn_kc hc f _ (by simp [R.LevelData.fns])

theorem sn_kz (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) : Commute (κ f) L.ζ :=
  sn_kc hc f _ (by simp [R.LevelData.fns])

theorem sn_knabs (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) : Commute (κ f) L.nabs :=
  sn_kc hc f _ (by simp)

theorem sn_kalg (f : M.Ty P → ℂ) (z : ℂ) : Commute (κ f) (algebraMap ℂ A z) := (Algebra.commutes z _).symm

theorem kappa_commute_raising (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (f : M.Ty P → ℂ) (Y : ℂ) : Commute (κ f) (L.m0 Y) := by
  unfold R.LevelData.m0
  exact ((sn_knabs hc f).neg_right).sub_right ((sn_kalg f _).mul_right ((sn_kz hc f).mul_right (sn_kGi hc f)))

theorem sn_sGi (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (l : ℕ) : Commute (SS l) L.GGi :=
  hc.2.2.1 l _ (by simp [R.LevelData.fns])

theorem sn_raises (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) : Raises κ SS := hc.2.2.2.1

theorem sn_alg_star (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (z : ℂ) :
    star (algebraMap ℂ A z) = algebraMap ℂ A (star z) := by
  have e : ∀ w : ℂ, algebraMap ℂ A w = κ (algebraMap ℂ (M.Ty P → ℂ) w) := fun w => (κ.commutes w).symm
  rw [e, e]; exact hc.1 _

theorem sn_G_star (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) : star L.GG = L.GG := by
  have hz : star L.ζb = L.ζ := by rw [← hs.1, star_star]
  rw [L.GG_def, star_sub, star_mul, hz, hs.1, sn_alg_star hc, hs.2.2]

theorem sn_Gi_star (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) : star L.GGi = L.GGi := by
  have h1 : star L.GGi * L.GG = 1 := by
    rw [← sn_G_star hc hs, ← star_mul, L.GG_GGi, star_one]
  calc star L.GGi = star L.GGi * (L.GG * L.GGi) := by rw [L.GG_GGi, mul_one]
    _ = L.GGi := by rw [← mul_assoc, h1, one_mul]

theorem sn_ssGi (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) (l : ℕ) :
    Commute (star (SS l)) L.GGi := by
  have := (sn_sGi hc l).star_star
  rwa [sn_Gi_star hc hs] at this

end SN

section KatoClassHeckeEulerFactorRelation

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

def sn_hsh (P : M.Par) (l j : ℕ) (ρ : M.Ty P) (Y : ℂ) : ℂ :=
  ∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + ((M.rho P ρ i : ℂ) + if i = j then 1 else 0))

theorem sn_x_up {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (h : M.Up P j ρ ρ') (Y : ℂ) :
    M.xC P ρ' Y = (Y + M.rho P ρ j + 1) * M.xEx P {j} ρ Y := by
  unfold M.xC M.xEx
  rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hj h)]
  congr 1
  · rw [up_rho P h j hj]; simp; ring
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_sdiff.1 hi
    rw [up_rho P h i hi'.1]
    have : i ≠ j := fun e => hi'.2 (by simp [e])
    simp [this]

theorem sn_xEx_up {j : ℕ} {ρ ρ' : M.Ty P} (h : M.Up P j ρ ρ') (l : ℕ) (Y : ℂ) :
    M.xEx P {l} ρ' Y = sn_hsh P l j ρ Y := by
  unfold M.xEx sn_hsh
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [up_rho P h i (Finset.mem_sdiff.1 hi).1]
  split_ifs <;> simp

theorem sn_hsh_same (j : ℕ) (ρ : M.Ty P) (Y : ℂ) : sn_hsh P j j ρ Y = M.xEx P {j} ρ Y := by
  unfold M.xEx sn_hsh
  refine Finset.prod_congr rfl fun i hi => ?_
  have : i ≠ j := fun e => (Finset.mem_sdiff.1 hi).2 (by simp [e])
  simp [this]

theorem sn_hsh_diff {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : l ≠ j) (ρ : M.Ty P) (Y : ℂ) :
    sn_hsh P l j ρ Y = (Y + M.rho P ρ j + 1) * M.xEx P {l, j} ρ Y := by
  unfold M.xEx sn_hsh
  have hjm : j ∈ Icc 1 (P.k - 1) \ {l} := Finset.mem_sdiff.2 ⟨hj, by simpa using hlj.symm⟩
  rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hjm h)]
  congr 1
  · simp; ring
  · have e : (Icc 1 (P.k - 1) \ {l}) \ {j} = Icc 1 (P.k - 1) \ {l, j} := by
      ext i; simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_insert]; tauto
    rw [e]
    refine Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ j := fun e' => (Finset.mem_sdiff.1 hi).2 (by simp [e'])
    simp [this]

theorem sn_kxi_ss (hR : Raises κ SS) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (Y : ℂ) :
    xiA κ Y * SS j = SS j * κ (fun ρ => ((Y + M.rho P ρ j + 1) * M.xEx P {j} ρ Y)⁻¹) :=
  hR j _ _ fun ρ ρ' h => by rw [sn_x_up hj h]

theorem sn_kxl_ss (hR : Raises κ SS) (j l : ℕ) (Y : ℂ) :
    κ (fun ρ => M.xEx P {l} ρ Y) * SS j = SS j * κ (fun ρ => sn_hsh P l j ρ Y) :=
  hR j _ _ fun ρ ρ' h => by rw [sn_xEx_up h]

theorem sn_kxl_sss (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (l : ℕ) (Y : ℂ) :
    κ (fun ρ => M.xEx P {l} ρ Y) * star (SS l) = star (SS l) * κ (fun ρ => M.xEx P {l} ρ Y) := by
  have h := sn_raises hc l (fun ρ => star (M.xEx P {l} ρ Y)) (fun ρ => star (M.xEx P {l} ρ Y))
    (fun ρ ρ' h => by rw [sn_xEx_up h, sn_hsh_same])
  have h2 := congrArg star h
  rw [star_mul, star_mul, show star (κ _) = _ from hc.1 _] at h2
  simp only [star_star] at h2
  exact h2.symm

theorem upper_left_from_determinant {t11 t12 t21 t21' τ τ' τi τi' q : A} (hD3 : t11 * τ' - t12 * t21' = q)
    (hD4 : t21 * τ' = τ * t21') (h1 : τ' * τi' = 1) (h2 : τi * τ = 1) : t11 = q * τi' + t12 * τi * t21 := by
  calc t11 = t11 * τ' * τi' := by rw [mul_assoc, h1, mul_one]
    _ = (q + t12 * t21') * τi' := by rw [← hD3]; noncomm_ring
    _ = q * τi' + t12 * (τi * τ) * t21' * τi' := by rw [h2]; noncomm_ring
    _ = q * τi' + t12 * τi * (τ * t21') * τi' := by noncomm_ring
    _ = q * τi' + t12 * τi * t21 * (τ' * τi') := by rw [← hD4]; noncomm_ring
    _ = q * τi' + t12 * τi * t21 := by rw [h1, mul_one]

theorem sn_expand {G Gi x xi m l S12 weightedSumBis : A} (hGG : Gi * G = 1) (hx : x * xi = 1) (hxi : xi * x = 1)
    (hmx : m * x = x * m) (hxGi : x * Gi = Gi * x) (hxiG : xi * G = G * xi) :
    (G * x * m + S12) * (Gi * xi) * (G * x * l + weightedSumBis) =
      G * x * m * l + G * m * Gi * weightedSumBis + S12 * l + S12 * (Gi * xi) * weightedSumBis := by
  have k1 : G * x * m * (Gi * xi) = G * m * Gi := by
    calc G * x * m * (Gi * xi) = G * (m * x) * Gi * xi := by rw [hmx]; noncomm_ring
      _ = G * m * (x * Gi) * xi := by noncomm_ring
      _ = G * m * Gi * (x * xi) := by rw [hxGi]; noncomm_ring
      _ = G * m * Gi := by rw [hx, mul_one]
  have k2 : Gi * xi * (G * x * l) = l := by
    calc Gi * xi * (G * x * l) = Gi * (xi * G) * x * l := by noncomm_ring
      _ = (Gi * G) * (xi * x) * l := by rw [hxiG]; noncomm_ring
      _ = l := by rw [hGG, hxi, one_mul, one_mul]
  have k3 : G * m * Gi * (G * x * l) = G * x * m * l := by
    calc G * m * Gi * (G * x * l) = G * m * (Gi * G) * x * l := by noncomm_ring
      _ = G * (m * x) * l := by rw [hGG]; noncomm_ring
      _ = G * x * m * l := by rw [hmx]; noncomm_ring
  calc (G * x * m + S12) * (Gi * xi) * (G * x * l + weightedSumBis)
      = (G * x * m * (Gi * xi)) * (G * x * l) + (G * x * m * (Gi * xi)) * weightedSumBis + S12 * (Gi * xi * (G * x * l)) +
          S12 * (Gi * xi) * weightedSumBis := by noncomm_ring
    _ = _ := by rw [k1, k2, k3]

end KatoClassHeckeEulerFactorRelation

section UnipotentMoveNumericalInequalities

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem sn_sum_swap (s : Finset ℕ) (F : ℕ → ℕ → A) :
    ∑ j ∈ s, ∑ l ∈ s.erase j, F l j = ∑ l ∈ s, ∑ j ∈ s.erase l, F l j := by
  have h1 : ∀ j, ∑ l ∈ s.erase j, F l j = ∑ l ∈ s, if l ≠ j then F l j else 0 := fun j => by
    rw [← Finset.sum_filter, Finset.filter_ne']
  have h2 : ∀ l, ∑ j ∈ s.erase l, F l j = ∑ j ∈ s, if j ≠ l then F l j else 0 := fun l => by
    rw [← Finset.sum_filter, Finset.filter_ne']
  simp_rw [h1, h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  simp [ne_comm]

theorem lower_sum_mul_projection (τ : M.Ty P) (Y : ℂ) :
    Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ =
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y • (SS j * proj κ τ) := by
  unfold Q.NFData.weightedSumBis
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only
  rw [mul_assoc, kap_mul_pj, mul_smul_comm]

theorem sn_stepB (hR : Raises κ SS) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) (Y : ℂ) :
    (L.GGi * xiA κ Y) * (SS j * proj κ τ) =
      ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ • (L.GGi * (SS j * proj κ τ)) := by
  rw [mul_assoc, ← mul_assoc (xiA κ Y), sn_kxi_ss hR hj, mul_assoc, kap_mul_pj, mul_smul_comm, mul_smul_comm]

theorem sn_stepC (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) (j : ℕ) (τ : M.Ty P) (Y : ℂ) :
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * (SS j * proj κ τ)) =
      L.GGi * ∑ l ∈ Icc 1 (P.k - 1), sn_hsh P l j τ Y • (star (SS l) * SS j * proj κ τ) := by
  unfold Q.NFData.S12
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only
  have e1 : (κ fun ρ => M.xEx P {l} ρ Y) * star (SS l) * (L.GGi * (SS j * proj κ τ)) =
      L.GGi * (star (SS l) * ((κ fun ρ => M.xEx P {l} ρ Y) * SS j) * proj κ τ) := by
    rw [sn_kxl_sss hc l Y]
    have a := (sn_ssGi hc hs l).eq
    have b := (sn_kGi hc (fun ρ => M.xEx P {l} ρ Y)).eq
    calc star (SS l) * (κ fun ρ => M.xEx P {l} ρ Y) * (L.GGi * (SS j * proj κ τ))
        = star (SS l) * ((κ fun ρ => M.xEx P {l} ρ Y) * L.GGi) * SS j * proj κ τ := by noncomm_ring
      _ = (star (SS l) * L.GGi) * (κ fun ρ => M.xEx P {l} ρ Y) * SS j * proj κ τ := by rw [b]; noncomm_ring
      _ = _ := by rw [a]; noncomm_ring
  rw [e1, sn_kxl_ss (sn_raises hc) j l Y]
  rw [show star (SS l) * (SS j * κ fun ρ => sn_hsh P l j ρ Y) * proj κ τ =
      star (SS l) * SS j * ((κ fun ρ => sn_hsh P l j ρ Y) * proj κ τ) by noncomm_ring, kap_mul_pj,
    mul_smul_comm]

theorem sn_stepE (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) {Y : ℂ} (hY : Reg P Y) {j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    ∑ l ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y * ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ * sn_hsh P l j τ Y) •
        (star (SS l) * SS j * proj κ τ) =
      (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ) +
        ∑ l ∈ (Icc 1 (P.k - 1)).erase j, M.xEx P {l, j} τ Y • (star (SS l) * SS j * proj κ τ) := by
  by_cases hτ : ∃ τ', M.Up P j τ τ'
  · obtain ⟨τ', hU⟩ := hτ
    have hx := hY τ'
    rw [sn_x_up hj hU] at hx
    have ha : (Y + M.rho P τ j + 1) ≠ 0 := left_ne_zero_of_mul hx
    have hb : M.xEx P {j} τ Y ≠ 0 := right_ne_zero_of_mul hx
    rw [← Finset.add_sum_erase _ _ hj]
    congr 1
    · rw [sn_hsh_same]; congr 1; field_simp
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hlj : l ≠ j := Finset.ne_of_mem_erase hl
      rw [sn_hsh_diff hj hlj]; congr 1; field_simp
  · have h0 := ss_pj_none κ (sn_raises hc) hτ
    have z : ∀ l, star (SS l) * SS j * proj κ τ = 0 := fun l => by rw [mul_assoc, h0, mul_zero]
    simp [z]

theorem upper_left_tail_projection (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {Y : ℂ} (hY : Reg P Y)
    (τ : M.Ty P) :
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y) * Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y *
        proj κ τ =
      L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ) := by
  rw [mul_assoc, mul_assoc, lower_sum_mul_projection, Finset.mul_sum, Finset.mul_sum]
  have e : ∀ j ∈ Icc 1 (P.k - 1),
      Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y * (M.xEx P {j} τ Y • (SS j * proj κ τ))) =
        L.GGi * ∑ l ∈ Icc 1 (P.k - 1),
          (M.xEx P {j} τ Y * ((Y + M.rho P τ j + 1) * M.xEx P {j} τ Y)⁻¹ * sn_hsh P l j τ Y) •
            (star (SS l) * SS j * proj κ τ) := by
    intro j hj
    rw [mul_smul_comm, sn_stepB (sn_raises hc) hj, smul_smul, mul_smul_comm, sn_stepC hc hs, ← mul_smul_comm,
      Finset.smul_sum]
    congr 1; refine Finset.sum_congr rfl fun l _ => ?_; rw [smul_smul]
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← mul_add]
  congr 1
  rw [Finset.sum_congr rfl fun j hj => sn_stepE hc hY hj τ, Finset.sum_add_distrib, sn_sum_swap]
  congr 1
  unfold Q.NFData.S4
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only
  rw [mul_assoc _ (κ _), kap_mul_pj, mul_smul_comm, mul_assoc]

end UnipotentMoveNumericalInequalities

section EpsilonZeroPos

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem sn_prod_eval (s : Finset ℕ) (c : ℕ → ℂ) (Y : ℂ) :
    (∏ i ∈ s, (X + C (c i))).eval Y = ∏ i ∈ s, (Y + c i) := by
  simp [Polynomial.eval_prod]

theorem sn_isPF_prod_smul (s : Finset ℕ) (c : ℕ → ℂ) {f : ℂ → A} (hf : IsPF f) :
    IsPF fun Y => (∏ i ∈ s, (Y + c i)) • f Y := by
  have e : (fun Y => (∏ i ∈ s, (Y + c i)) • f Y) = fun Y => (∏ i ∈ s, (X + C (c i))).eval Y • f Y :=
    funext fun Y => by rw [sn_prod_eval]
  rw [e]; exact isPF_smul_fun _ hf

theorem sn_isPF_kprod (s : Finset ℕ) (c : M.Ty P → ℕ → ℂ) :
    IsPF fun Y => κ (fun ρ => ∏ i ∈ s, (Y + c ρ i)) := by
  have e : (fun Y => κ (fun ρ => ∏ i ∈ s, (Y + c ρ i))) = fun Y => ∑ ρ, (∏ i ∈ s, (Y + c ρ i)) • proj κ ρ :=
    funext fun Y => kap_eq κ _
  rw [e]
  exact isPF_sum _ fun ρ _ => sn_isPF_prod_smul s (c ρ) (isPF_const _)

theorem polynomial_coordinate : IsPF fun Y => xA κ Y := sn_isPF_kprod (Icc 1 (P.k - 1)) fun ρ i => (M.rho P ρ i : ℂ)

theorem sn_isPF_xEx (s : Finset ℕ) : IsPF fun Y => κ (fun ρ => M.xEx P s ρ Y) :=
  sn_isPF_kprod (Icc 1 (P.k - 1) \ s) fun ρ i => (M.rho P ρ i : ℂ)

theorem polynomial_raising : IsPF fun Y => L.m0 Y := by
  have e : (fun Y => L.m0 Y) = fun Y => -L.nabs - algebraMap ℂ A ((X - C (1 / 2 : ℂ)).eval Y) * (L.ζ * L.GGi) := by
    funext Y; simp [R.LevelData.m0]
  rw [e]; exact isPF_sub (isPF_const _) (isPF_mul (isPF_algebraMap _) (isPF_const _))

theorem polynomial_lowering : IsPF fun Y => L.l0 Y := by
  have e : (fun Y => L.l0 Y) = fun Y => -L.nab - algebraMap ℂ A ((X + C (1 / 2 : ℂ)).eval Y) * (L.ζb * L.GGi) := by
    funext Y; simp [R.LevelData.l0]
  rw [e]; exact isPF_sub (isPF_const _) (isPF_mul (isPF_algebraMap _) (isPF_const _))

theorem polynomial_lower_sum : IsPF fun Y => Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
  unfold Q.NFData.weightedSumBis
  exact isPF_sum _ fun l _ => isPF_mul (isPF_const _) (sn_isPF_xEx _)

theorem polynomial_upper_sum : IsPF fun Y => Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
  unfold Q.NFData.S12
  exact isPF_sum _ fun l _ => isPF_mul (sn_isPF_xEx _) (isPF_const _)

theorem polynomial_quartic_sum : IsPF fun Y => Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
  unfold Q.NFData.S4
  exact isPF_sum _ fun l _ => isPF_sum _ fun j _ => isPF_mul (isPF_const _) (sn_isPF_xEx _)

theorem sn_isPF_w : IsPF fun Y => κ (fun ρ => M.wC P ρ Y) := by
  have e : (fun Y => κ (fun ρ => M.wC P ρ Y)) = fun Y => ∑ ρ, (M.wNum P ρ /ₘ M.coordinatePolynomial P ρ).eval Y • proj κ ρ :=
    funext fun Y => kap_eq κ _
  rw [e]
  exact isPF_sum _ fun ρ _ => isPF_cpoly _ _

def upperLeftTail (L : R.LevelData A P.r) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (SS : ℕ → A) (Y : ℂ) : A :=
  L.GG * xA κ Y * L.m0 Y * L.l0 Y + L.GG * L.m0 Y * L.GGi * Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y +
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * L.l0 Y

theorem polynomial_upper_left_tail : IsPF fun Y => upperLeftTail L κ SS Y := by
  unfold upperLeftTail
  exact isPF_add (isPF_add (isPF_mul (isPF_mul (isPF_mul (isPF_const _) polynomial_coordinate) polynomial_raising) polynomial_lowering)
    (isPF_mul (isPF_mul (isPF_mul (isPF_const _) polynomial_raising) (isPF_const _)) polynomial_lower_sum))
    (isPF_mul polynomial_upper_sum polynomial_lowering)

theorem upper_left_decomposition (Y : ℂ) : (Q.NFData.QQ (⟨L, κ, SS⟩ : Q.NFData P A) Y) 0 0 =
    L.GGi * κ (fun ρ => M.wC P ρ Y) + upperLeftTail L κ SS Y + L.GGi * Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
  simp only [Q.NFData.QQ, upperLeftTail, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Q.NFData.x, xA]
  noncomm_ring

theorem polynomial_upper_left : IsPF fun Y => (Q.NFData.QQ (⟨L, κ, SS⟩ : Q.NFData P A) Y) 0 0 := by
  simp_rw [upper_left_decomposition]
  exact isPF_add (isPF_add (isPF_mul (isPF_const _) sn_isPF_w) polynomial_upper_left_tail) (isPF_mul (isPF_const _) polynomial_quartic_sum)

end EpsilonZeroPos

section SN5

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem sn_core (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0)
    {Y : ℂ} (hY : Reg P Y) (hY1 : Reg P (Y + 1)) (τ : M.Ty P) :
    QQ Y 0 0 * proj κ τ = (M.qC P Y / M.xC P τ (Y + 1)) • (L.GGi * proj κ τ) + upperLeftTail L κ SS Y * proj κ τ +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Y / (Y + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ)) +
        L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ)) := by
  have cG : ∀ Z, xA κ Z * L.GGi = L.GGi * xA κ Z := fun Z => (sn_kGi hc _).eq
  have cG' : ∀ Z, xiA κ Z * L.GG = L.GG * xiA κ Z := fun Z => (sn_kG hc _).eq
  have h1 : L.GG * xA κ (Y + 1) * (L.GGi * xiA κ (Y + 1)) = 1 := by
    calc L.GG * xA κ (Y + 1) * (L.GGi * xiA κ (Y + 1)) = L.GG * (xA κ (Y + 1) * L.GGi) * xiA κ (Y + 1) := by
          noncomm_ring
      _ = (L.GG * L.GGi) * (xA κ (Y + 1) * xiA κ (Y + 1)) := by rw [cG]; noncomm_ring
      _ = 1 := by rw [L.GG_GGi, xA_xiA κ hY1, one_mul]
  have h2 : L.GGi * xiA κ Y * (L.GG * xA κ Y) = 1 := by
    calc L.GGi * xiA κ Y * (L.GG * xA κ Y) = L.GGi * (xiA κ Y * L.GG) * xA κ Y := by noncomm_ring
      _ = (L.GGi * L.GG) * (xiA κ Y * xA κ Y) := by rw [cG']; noncomm_ring
      _ = 1 := by rw [L.GGi_GG, xiA_xA κ hY, one_mul]
  have d3 : QQ Y 0 0 * (L.GG * xA κ (Y + 1)) - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y) := by
    rw [← h22]; exact hD3 Y
  have d4 : QQ Y 1 0 * (L.GG * xA κ (Y + 1)) = (L.GG * xA κ Y) * QQ (Y + 1) 1 0 := by
    rw [← h22, ← h22]; exact hD4 Y
  have a3 := upper_left_from_determinant d3 d4 h1 h2
  have ex : QQ Y 0 1 * (L.GGi * xiA κ Y) * QQ Y 1 0 =
      upperLeftTail L κ SS Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * xiA κ Y) *
        Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y := by
    rw [h12, h21, sn_expand L.GGi_GG (xA_xiA κ hY) (xiA_xA κ hY) (kappa_commute_raising hc _ Y).eq.symm (cG Y) (cG' Y)]
    unfold upperLeftTail; noncomm_ring
  have hq : algebraMap ℂ A (M.qC P Y) * (L.GGi * xiA κ (Y + 1)) * proj κ τ =
      (M.qC P Y / M.xC P τ (Y + 1)) • (L.GGi * proj κ τ) := by
    have e : xiA κ (Y + 1) * proj κ τ = (M.xC P τ (Y + 1))⁻¹ • proj κ τ := kap_mul_pj κ _ τ
    rw [mul_assoc, mul_assoc, e, mul_smul_comm, mul_smul_comm, ← Algebra.smul_def, smul_smul, div_eq_mul_inv,
      mul_comm (M.qC P Y)]
  rw [a3, ex, add_mul, add_mul, hq, upper_left_tail_projection hc hs hY τ]
  noncomm_ring

end SN5

section SN6

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem coordinate_shift_product (τ : M.Ty P) (Y : ℂ) : M.xC P τ (Y + 1) = ∏ i ∈ Icc 1 (P.k - 1), (Y + (1 + (M.rho P τ i : ℂ))) := by
  unfold M.xC; exact Finset.prod_congr rfl fun i _ => by ring

theorem sn_qeval (Y : ℂ) : (M.qP P).eval Y = M.qC P Y := by
  simp only [M.qP, M.qC, eval_mul, eval_C, eval_prod, eval_add, eval_X]
  congr 1; exact Finset.prod_congr rfl fun i _ => by ring

def sn_e (P : M.Par) (τ : M.Ty P) (j : ℕ) (Y : ℂ) : ℂ :=
  (∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (M.rho P τ i : ℂ))) * ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ)))

theorem coordinate_shift_split {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) (Y : ℂ) :
    M.xC P τ (Y + 1) = (Y + M.rho P τ j + 1) * ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ))) := by
  rw [coordinate_shift_product, Finset.prod_eq_mul_prod_sdiff_singleton j _ (fun h => absurd hj h)]; ring

theorem sn_res (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    (τ : M.Ty P) (Y : ℂ) :
    M.xC P τ (Y + 1) • (QQ Y 0 0 * proj κ τ) = M.qC P Y • (L.GGi * proj κ τ) +
      M.xC P τ (Y + 1) • (upperLeftTail L κ SS Y * proj κ τ) +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), sn_e P τ j Y • (star (SS j) * SS j * proj κ τ)) +
        M.xC P τ (Y + 1) • (L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Y * proj κ τ))) := by
  have pfx : ∀ {f : ℂ → A}, IsPF f → IsPF fun Y => M.xC P τ (Y + 1) • f Y := fun {f} hf => by
    simp_rw [coordinate_shift_product]; exact sn_isPF_prod_smul _ _ hf
  refine isPF_eq (f := fun Z => M.xC P τ (Z + 1) • (QQ Z 0 0 * proj κ τ))
    (g := fun Z => M.qC P Z • (L.GGi * proj κ τ) + M.xC P τ (Z + 1) • (upperLeftTail L κ SS Z * proj κ τ) +
      (L.GGi * (∑ j ∈ Icc 1 (P.k - 1), sn_e P τ j Z • (star (SS j) * SS j * proj κ τ)) +
        M.xC P τ (Z + 1) • (L.GGi * (Q.NFData.S4 (⟨L, κ, SS⟩ : Q.NFData P A) Z * proj κ τ))))
    (pfx (isPF_mul hpoly (isPF_const _))) ?_ (regular_pairs_infinite P) ?_ Y
  · refine isPF_add (isPF_add ?_ (pfx (isPF_mul polynomial_upper_left_tail (isPF_const _)))) (isPF_add ?_ ?_)
    · simp_rw [← sn_qeval]; exact isPF_cpoly _ _
    · refine isPF_mul (isPF_const _) (isPF_sum _ fun j _ => ?_)
      unfold sn_e; simp_rw [mul_smul]
      exact sn_isPF_prod_smul _ _ (sn_isPF_prod_smul _ _ (isPF_const _))
    · exact pfx (isPF_mul (isPF_const _) (isPF_mul polynomial_quartic_sum (isPF_const _)))
  · rintro Z ⟨hZ, hZ1⟩
    have hx : M.xC P τ (Z + 1) ≠ 0 := hZ1 τ
    rw [sn_core hc hs h22 h21 h12 hD3 hD4 hZ hZ1 τ, smul_add, smul_add, smul_smul, mul_div_cancel₀ _ hx,
      smul_add]
    congr 2
    rw [← mul_smul_comm, Finset.smul_sum]; congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [smul_smul]; congr 1
    have hx' := hx
    rw [coordinate_shift_split hj] at hx'
    have ha : Z + M.rho P τ j + 1 ≠ 0 := left_ne_zero_of_mul hx'
    rw [coordinate_shift_split hj, sn_e]; unfold M.xEx; field_simp

end SN6

section SN7

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}

theorem sn_e_other {j l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (τ : M.Ty P) :
    sn_e P τ j ((-(M.rho P τ l) - 1 : ℝ) : ℂ) = 0 := by
  unfold sn_e
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (i := l)
  · exact Finset.mem_sdiff.2 ⟨hl, by simpa using hjl.symm⟩
  · push_cast; ring

theorem sn_e_self (l : ℕ) (τ : M.Ty P) :
    sn_e P τ l ((-(M.rho P τ l) - 1 : ℝ) : ℂ) =
      (((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l - 1) : ℝ) : ℂ) := by
  unfold sn_e
  rw [Finset.sdiff_singleton_eq_erase, mul_comm]
  push_cast
  congr 1 <;> exact Finset.prod_congr rfl fun i _ => by ring

theorem sn_norm_eq (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L)
    {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    M.qC P ((-(M.rho P τ l) - 1 : ℝ) : ℂ) • proj κ τ +
      sn_e P τ l ((-(M.rho P τ l) - 1 : ℝ) : ℂ) • (star (SS l) * SS l * proj κ τ) = 0 := by
  have r := sn_res hc hs h22 h21 h12 hD3 hD4 hpoly τ ((-(M.rho P τ l) - 1 : ℝ) : ℂ)
  have hx : M.xC P τ (((-(M.rho P τ l) - 1 : ℝ) : ℂ) + 1) = 0 := by
    rw [coordinate_shift_split hl]; apply mul_eq_zero_of_left; push_cast; ring
  rw [hx, zero_smul, zero_smul, zero_smul, add_zero, add_zero,
    Finset.sum_eq_single l (fun j hj hjl => by rw [sn_e_other hl hjl, zero_smul]) (fun h => absurd hl h),
    ← mul_smul_comm, ← mul_add] at r
  have := congrArg (L.GG * ·) r
  simp only [mul_zero, ← mul_assoc, L.GG_GGi, one_mul] at this
  rw [← this]

theorem sn_norm_blk (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) (hP : P.OK)
    (hNF : M.NrmFacts) (hRP : M.RealPoints)
    {QQ : ℂ → Matrix (Fin 2) (Fin 2) A}
    (h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y)
    (h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y)
    (hD3 : ∀ Y, QQ Y 0 0 * QQ (Y + 1) 1 1 - QQ Y 0 1 * QQ (Y + 1) 1 0 = algebraMap ℂ A (M.qC P Y))
    (hD4 : ∀ Y, QQ Y 1 0 * QQ (Y + 1) 1 1 = QQ Y 1 1 * QQ (Y + 1) 1 0) (hpoly : IsPF fun Y => QQ Y 0 0)
    {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) :
    star (SS l) * SS l * proj κ τ = ((M.Nrm P l τ : ℝ) : ℂ) • proj κ τ := by
  by_cases hτ : ∃ τ', M.Up P l τ τ'
  · obtain ⟨τ', hU⟩ := hτ
    have hpos := ((hNF P hP l hl τ).1 τ' hU).1
    set den : ℝ := (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (M.rho P τ j - M.rho P τ l - 1) with hden
    have hd : den ≠ 0 := by
      intro h0; unfold M.Nrm at hpos; rw [← hden, h0, div_zero] at hpos; exact lt_irrefl _ hpos
    have key := Mx3.nrm_key P hP l hl τ
    rw [← hden] at key
    have e := sn_norm_eq hc hs h22 h21 h12 hD3 hD4 hpoly hl τ
    rw [sn_e_self, ← hden, (hRP P τ _).2,
      show I.qpoly P.k P.T P.T' P.u P.u' (-M.rho P τ l - 1) = -(M.Nrm P l τ * den) by linarith] at e
    have hdC : ((den : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
    have e3 : ((den : ℝ) : ℂ) • (star (SS l) * SS l * proj κ τ) =
        ((den : ℝ) : ℂ) • (((M.Nrm P l τ : ℝ) : ℂ) • proj κ τ) := by
      rw [eq_neg_of_add_eq_zero_right e, smul_smul]; push_cast; rw [neg_smul, neg_neg, mul_comm]
    exact smul_right_injective A hdC e3
  · rw [mul_assoc, ss_pj_none κ (sn_raises hc) hτ, mul_zero, (hNF P hP l hl τ).2.1 hτ]; simp

end SN7

section SN8

theorem sn_wC {P : M.Par} (hWE : M.WExact) (hP : P.OK) (τ : M.Ty P) {Y : ℂ} (hY1 : M.xC P τ (Y + 1) ≠ 0) :
    M.wC P τ Y = M.qC P Y / M.xC P τ (Y + 1) +
      ∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Y / (Y + M.rho P τ j + 1) * ((M.Nrm P j τ : ℝ) : ℂ) := by
  have hx1 : (M.coordinatePolynomial P τ).eval Y = M.xC P τ (Y + 1) := by
    rw [coordinate_shift_product]; simp only [M.coordinatePolynomial, eval_prod, eval_add, eval_X, eval_C]
    exact Finset.prod_congr rfl fun i _ => by ring
  have hw := congrArg (Polynomial.eval Y) (hWE P hP τ)
  rw [eval_mul, hx1] at hw
  have hwc : M.wC P τ Y = (M.wNum P τ).eval Y / M.xC P τ (Y + 1) := by
    rw [hw, M.wC]; field_simp
  rw [hwc]
  simp only [M.wNum, eval_add, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_X, sn_qeval]
  rw [add_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hsplit := coordinate_shift_split hj τ Y
  have hne := hY1
  rw [hsplit] at hne
  have hB := right_ne_zero_of_mul hne
  have ha := left_ne_zero_of_mul hne
  have e1 : ∏ i ∈ (Icc 1 (P.k - 1)).erase j, (Y + ((M.rho P τ i : ℂ) + 1)) =
      ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ))) := by
    rw [Finset.sdiff_singleton_eq_erase]; exact Finset.prod_congr rfl fun i _ => by ring
  have e2 : ∏ i ∈ (Icc 1 (P.k - 1)).erase j, (Y + (M.rho P τ i : ℂ)) = M.xEx P {j} τ Y := by
    unfold M.xEx; rw [Finset.sdiff_singleton_eq_erase]
  rw [hsplit, e1, e2]
  field_simp

theorem sn_main : Formalism.FourierDecayAlt.NF.SNorm := by
  intro _ _ _ hNF hRP hWE P A _ _ _ L0 QQ κ b SS L hP hS _ _ _ hExt _ _ hst hc hQ
  have hGG : L.GG = L0.GG := hExt.2.2.2.2.2.2.2.2.2.2.1
  have h22 : ∀ Y, QQ Y 1 1 = L.GG * xA κ Y := fun Y => by rw [diagonal_entry_hypothesis hS, hGG]
  have h21 : ∀ Y, QQ Y 1 0 = L.GG * xA κ Y * L.l0 Y + Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y := fun Y => by
    rw [(hQ Y).1]; simp [Q.NFData.QQ, Q.NFData.x, xA]
  have h12 : ∀ Y, QQ Y 0 1 = L.GG * xA κ Y * L.m0 Y + Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y := fun Y => by
    rw [(hQ Y).2]; simp [Q.NFData.QQ, Q.NFData.x, xA]
  have hD3 := quantum_determinant_relation hS
  have hD4 := lower_diagonal_shift_relation hS
  have hpoly := H_poly hS 0 0
  refine ⟨fun l hl => ?_, fun Y => ?_⟩
  · show star (SS l) * SS l = κ fun ρ => ((M.Nrm P l ρ : ℝ) : ℂ)
    exact eq_of_rblocks κ fun τ => by
      rw [sn_norm_blk hc hst hP hNF hRP h22 h21 h12 hD3 hD4 hpoly hl τ, kap_mul_pj]
  · refine isPF_eq hpoly polynomial_upper_left (regular_pairs_infinite P) ?_ Y
    rintro Z ⟨hZ, hZ1⟩
    refine eq_of_rblocks κ fun τ => ?_
    have hsum : ∑ j ∈ Icc 1 (P.k - 1), (M.xEx P {j} τ Z / (Z + M.rho P τ j + 1)) • (star (SS j) * SS j * proj κ τ) =
        (∑ j ∈ Icc 1 (P.k - 1), M.xEx P {j} τ Z / (Z + M.rho P τ j + 1) * ((M.Nrm P j τ : ℝ) : ℂ)) • proj κ τ := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [sn_norm_blk hc hst hP hNF hRP h22 h21 h12 hD3 hD4 hpoly hj τ, smul_smul]
    rw [sn_core hc hst h22 h21 h12 hD3 hD4 hZ hZ1 τ, upper_left_decomposition, hsum, add_mul, add_mul, mul_assoc L.GGi (κ _),
      kap_mul_pj, sn_wC hWE hP τ (hZ1 τ), add_smul, mul_add, mul_smul_comm, mul_assoc L.GGi]
    noncomm_ring

end SN8

section SC

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem sc_fc (L0 : PreLevel A P.r) {x y : A} (hx : x ∈ L0.fns) (hy : y ∈ L0.fns) : x * y = y * x :=
  L0.fns_comm x hx y hy

section Mem
variable (L0 : PreLevel A P.r)
theorem sc_mζ : L0.ζ ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mζi : L0.ζi ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mζb : L0.ζb ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mζbi : L0.ζbi ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mGG : L0.GG ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mGGi : L0.GGi ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mc (l) : L0.c l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mci (l) : L0.ci l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mcb (l) : L0.cb l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mcbi (l) : L0.cbi l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_ops_of_fns {x : A} (hx : x ∈ L0.fns) : x ∈ L0.ops := by
  unfold PreLevel.ops; exact Or.inl (Or.inl hx)
theorem sc_mp (l) : L0.p l ∈ L0.ops := by unfold PreLevel.ops; exact Or.inl (Or.inr ⟨l, rfl⟩)
theorem sc_mpb (l) : L0.pb l ∈ L0.ops := by unfold PreLevel.ops; exact Or.inr ⟨l, rfl⟩
theorem sc_crd_c (l) : L0.c l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_ci (l) : L0.ci l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_cb (l) : L0.cb l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_cbi (l) : L0.cbi l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_p (l) : L0.p l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_pb (l) : L0.pb l ∈ L0.crdOps := by simp [PreLevel.crdOps]
end Mem

section Core

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem sc_kc (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) {g : A} (hg : g ∈ L0.fns) : κ f * g = g * κ f :=
  (H_kops h f g (sc_ops_of_fns L0 hg)).eq

theorem sc_kops (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) {g : A} (hg : g ∈ L0.ops) : κ f * g = g * κ f :=
  (H_kops h f g hg).eq

theorem sc_pc (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {g : A} (hg : g ∈ L0.ops) : proj κ ρ * g = g * proj κ ρ :=
  sc_kops h _ hg

theorem sc_pf (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {g : A} (hg : g ∈ L0.fns) : proj κ ρ * g = g * proj κ ρ :=
  sc_kc h _ hg

theorem sc_crd_ops {g : A} (hg : g ∈ L0.crdOps) : g ∈ L0.ops ∧ L0.GGi * g = g * L0.GGi := by
  unfold PreLevel.crdOps at hg
  rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mc L0 l), sc_fc L0 (sc_mGGi L0) (sc_mc L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mci L0 l), sc_fc L0 (sc_mGGi L0) (sc_mci L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mcb L0 l), sc_fc L0 (sc_mGGi L0) (sc_mcb L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mcbi L0 l), sc_fc L0 (sc_mGGi L0) (sc_mcbi L0 l)⟩
  · exact ⟨sc_mp L0 l, (L0.p_GGi l).symm⟩
  · exact ⟨sc_mpb L0 l, (L0.pb_GGi l).symm⟩

theorem sc_lreg (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : Reg P Y) : QQ Y 1 0 = L0.GG * xA κ Y * lA L0 QQ κ Y := by
  unfold lA
  have e : L0.GG * xA κ Y * (xiA κ Y * L0.GGi * QQ Y 1 0) = L0.GG * (xA κ Y * xiA κ Y) * L0.GGi * QQ Y 1 0 := by
    noncomm_ring
  rw [e, xA_xiA κ hY, mul_one, L0.GG_GGi, one_mul]

theorem sc_ldiag {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y) (ρ : M.Ty P) :
    proj κ ρ * lA L0 QQ κ Y * proj κ ρ = (b ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ := by
  have := hF Y hY ρ ρ
  rw [if_pos rfl, Finset.sum_eq_zero, add_zero] at this
  · exact this
  · intro l hl; rw [if_neg (fun hu => up_ne P hl hu rfl)]

theorem sc_lup {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') :
    proj κ ρ' * lA L0 QQ κ Y * proj κ ρ = (Y + (M.rho P ρ l : ℂ) + 1)⁻¹ • (L0.GGi * SS l * proj κ ρ) := by
  have := hF Y hY ρ ρ'
  rw [if_neg (fun e => up_ne P hl hu e.symm), zero_add, Finset.sum_eq_single l] at this
  · rw [this, if_pos hu]
  · intro j hj hjl; rw [if_neg (fun hu' => hjl (up_idx P hj hl hu' hu))]
  · intro h; exact absurd hl h

theorem sc_lzero {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y)
    {ρ ρ' : M.Ty P} (hne : ρ' ≠ ρ) (hn : ∀ l ∈ Icc 1 (P.k - 1), ¬ M.Up P l ρ ρ') :
    proj κ ρ' * lA L0 QQ κ Y * proj κ ρ = 0 := by
  have := hF Y hY ρ ρ'
  rw [if_neg hne, zero_add, Finset.sum_eq_zero] at this
  · exact this
  · intro l hl; rw [if_neg (hn l hl)]

theorem sc_Zp (h : SHyp P L0 QQ κ) (ρ : M.Ty P) :
    proj κ ρ * (L0.ζb * L0.GGi) = (L0.ζb * L0.GGi) * proj κ ρ := by
  rw [← mul_assoc, sc_pf h ρ (sc_mζb L0), mul_assoc, sc_pf h ρ (sc_mGGi L0), mul_assoc]

theorem sc_exreg (P : M.Par) : ∃ Y, Reg P Y := (reg_infinite P).nonempty

theorem sc_pbp (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) (ρ : M.Ty P) :
    proj κ ρ * b ρ * proj κ ρ = b ρ * proj κ ρ := by
  obtain ⟨Y, hY⟩ := sc_exreg P
  have e := sc_ldiag hF hY ρ
  have e2 : proj κ ρ * (proj κ ρ * lA L0 QQ κ Y * proj κ ρ) = proj κ ρ * lA L0 QQ κ Y * proj κ ρ := by
    rw [← mul_assoc, ← mul_assoc, pj_idem]
  rw [e] at e2
  have hZ := sc_Zp h ρ
  have e3a : proj κ ρ * (b ρ * proj κ ρ) = proj κ ρ * b ρ * proj κ ρ := (mul_assoc _ _ _).symm
  have e3b : proj κ ρ * ((L0.ζb * L0.GGi) * proj κ ρ) = (L0.ζb * L0.GGi) * proj κ ρ := by
    rw [← mul_assoc, hZ, mul_assoc, pj_idem]
  have e3 : proj κ ρ * ((b ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ) =
      proj κ ρ * b ρ * proj κ ρ - Y • ((L0.ζb * L0.GGi) * proj κ ρ) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, e3a, e3b]
  rw [e3, sub_mul, smul_mul_assoc] at e2
  exact sub_left_inj.mp e2

def sc_B (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) : A := ∑ ρ, proj κ ρ * b ρ * proj κ ρ

def sc_D (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (X : A) : A := ∑ ρ, proj κ ρ * X * proj κ ρ

theorem sc_B_eq (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ}
    (hY : Reg P Y) : sc_B κ b = sc_D κ (lA L0 QQ κ Y) + Y • (L0.ζb * L0.GGi) := by
  unfold sc_B sc_D
  have : ∀ ρ, proj κ ρ * b ρ * proj κ ρ = proj κ ρ * lA L0 QQ κ Y * proj κ ρ + Y • ((L0.ζb * L0.GGi) * proj κ ρ) := by
    intro ρ; rw [sc_pbp h hF ρ, sc_ldiag hF hY ρ, sub_mul, smul_mul_assoc]; abel
  simp_rw [this, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.mul_sum, sum_pj, mul_one]

theorem sc_D_comm {g : A} (hg : ∀ ρ, proj κ ρ * g = g * proj κ ρ) (X : A) :
    sc_D κ X * g = sc_D κ (X * g) ∧ g * sc_D κ X = sc_D κ (g * X) := by
  unfold sc_D
  constructor
  · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun ρ _ => ?_; rw [mul_assoc, hg ρ]; noncomm_ring
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ρ _ => ?_; rw [← mul_assoc, ← mul_assoc, ← hg ρ]; noncomm_ring

theorem sc_lζ (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : Reg P Y) : lA L0 QQ κ Y * L0.ζ = L0.ζ * lA L0 QQ κ Y - 1 := by
  unfold lA
  have h1 := (levelSubgroupAtPlace h Y).1
  have hx : xiA κ Y * L0.ζ = L0.ζ * xiA κ Y := sc_kc h _ (sc_mζ L0)
  have hg : L0.GGi * L0.ζ = L0.ζ * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζ L0)
  have hgx : L0.GGi * L0.GG = 1 := L0.GGi_GG
  calc xiA κ Y * L0.GGi * QQ Y 1 0 * L0.ζ = xiA κ Y * L0.GGi * (QQ Y 1 0 * L0.ζ) := by noncomm_ring
    _ = xiA κ Y * L0.GGi * (L0.ζ * QQ Y 1 0 - L0.GG * xA κ Y) := by rw [h1, diagonal_entry_hypothesis h]
    _ = (xiA κ Y * L0.GGi * L0.ζ) * QQ Y 1 0 - xiA κ Y * (L0.GGi * L0.GG) * xA κ Y := by noncomm_ring
    _ = L0.ζ * (xiA κ Y * L0.GGi * QQ Y 1 0) - 1 := by
        have key : xiA κ Y * L0.GGi * L0.ζ = L0.ζ * (xiA κ Y * L0.GGi) := by
          rw [mul_assoc, hg, ← mul_assoc, hx, mul_assoc]
        rw [hgx, mul_one, xiA_xA κ hY, key]; noncomm_ring

theorem sc_lζb (h : SHyp P L0 QQ κ) (Y : ℂ) : lA L0 QQ κ Y * L0.ζb = L0.ζb * lA L0 QQ κ Y := by
  unfold lA
  have h1 := (levelSubgroupAtPlace h Y).2.2.2.2.1
  have hx : xiA κ Y * L0.ζb = L0.ζb * xiA κ Y := sc_kc h _ (sc_mζb L0)
  have hg : L0.GGi * L0.ζb = L0.ζb * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζb L0)
  rw [mul_assoc, h1, ← mul_assoc, mul_assoc (xiA κ Y), hg, ← mul_assoc, hx, mul_assoc, mul_assoc, mul_assoc]

theorem sc_lcrd (h : SHyp P L0 QQ κ) (Y : ℂ) {g : A} (hg : g ∈ L0.crdOps) : lA L0 QQ κ Y * g = g * lA L0 QQ κ Y := by
  unfold lA
  obtain ⟨ho, hgi⟩ := sc_crd_ops hg
  have h1 := (H_crd h Y 1 0 g hg).eq
  have hx : xiA κ Y * g = g * xiA κ Y := sc_kops h _ ho
  rw [mul_assoc, h1, ← mul_assoc, mul_assoc (xiA κ Y), hgi, ← mul_assoc, hx, mul_assoc, mul_assoc, mul_assoc]

end Core

section Conn

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem coordinate_commute_zeta {g : A} (hg : g ∈ L0.crdOps) : L0.ζb * g = g * L0.ζb ∧ L0.ζ * g = g * L0.ζ := by
  unfold PreLevel.crdOps at hg
  rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mc L0 l), sc_fc L0 (sc_mζ L0) (sc_mc L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mci L0 l), sc_fc L0 (sc_mζ L0) (sc_mci L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mcb L0 l), sc_fc L0 (sc_mζ L0) (sc_mcb L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mcbi L0 l), sc_fc L0 (sc_mζ L0) (sc_mcbi L0 l)⟩
  · exact ⟨(L0.p_ζb l).symm, (L0.p_ζ l).symm⟩
  · exact ⟨(L0.pb_ζb l).symm, (L0.pb_ζ l).symm⟩

theorem sc_Zc {g : A} (hb : L0.ζb * g = g * L0.ζb) (hi : L0.GGi * g = g * L0.GGi) :
    (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi) := by
  rw [mul_assoc, hi, ← mul_assoc, hb, mul_assoc]

theorem sc_B_rel (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g c : A}
    (hg : g ∈ L0.ops) (hZ : (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi))
    (hl : ∀ Y, Reg P Y → lA L0 QQ κ Y * g = g * lA L0 QQ κ Y + c) (hD : sc_D κ c = c) :
    sc_B κ b * g = g * sc_B κ b + c := by
  obtain ⟨Y, hY⟩ := sc_exreg P
  obtain ⟨c1, c2⟩ := sc_D_comm (κ := κ) (fun ρ => sc_pc h ρ hg) (lA L0 QQ κ Y)
  have hsum : sc_D κ (g * lA L0 QQ κ Y + c) = sc_D κ (g * lA L0 QQ κ Y) + sc_D κ c := by
    unfold sc_D; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun ρ _ => ?_; noncomm_ring
  rw [sc_B_eq h hF hY, add_mul, c1, hl Y hY, hsum, hD, ← c2, smul_mul_assoc, hZ, mul_add, mul_smul_comm]
  abel

theorem sc_D_zero : sc_D κ (0 : A) = 0 := by unfold sc_D; simp

theorem sc_D_neg_one : sc_D κ (-1 : A) = -1 := by
  unfold sc_D; simp_rw [mul_neg, neg_mul, mul_one, pj_idem]; rw [Finset.sum_neg_distrib, sum_pj]

theorem sc_Bζ (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    sc_B κ b * L0.ζ = L0.ζ * sc_B κ b + (-1) :=
  sc_B_rel h hF (sc_ops_of_fns L0 (sc_mζ L0))
    (sc_Zc (sc_fc L0 (sc_mζb L0) (sc_mζ L0)) (sc_fc L0 (sc_mGGi L0) (sc_mζ L0)))
    (fun Y hY => by rw [sc_lζ h hY]; abel) sc_D_neg_one

theorem sc_Bζb (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    sc_B κ b * L0.ζb = L0.ζb * sc_B κ b + 0 :=
  sc_B_rel h hF (sc_ops_of_fns L0 (sc_mζb L0))
    (sc_Zc rfl (sc_fc L0 (sc_mGGi L0) (sc_mζb L0)))
    (fun Y _ => by rw [sc_lζb h Y, add_zero]) sc_D_zero

theorem sc_Bcrd (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g : A}
    (hg : g ∈ L0.crdOps) : sc_B κ b * g = g * sc_B κ b + 0 :=
  sc_B_rel h hF (sc_crd_ops hg).1 (sc_Zc (coordinate_commute_zeta hg).1 (sc_crd_ops hg).2)
    (fun Y _ => by rw [sc_lcrd h Y hg, add_zero]) sc_D_zero

theorem sc_Bkap (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) (f : M.Ty P → ℂ) :
    κ f * sc_B κ b = sc_B κ b * κ f := by
  unfold sc_B
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  calc κ f * (proj κ ρ * b ρ * proj κ ρ) = (κ f * proj κ ρ) * b ρ * proj κ ρ := by noncomm_ring
    _ = f ρ • (proj κ ρ * b ρ * proj κ ρ) := by rw [kap_mul_pj, smul_mul_assoc, smul_mul_assoc]
    _ = proj κ ρ * b ρ * (proj κ ρ * κ f) := by rw [pj_mul_kap, mul_smul_comm]
    _ = _ := by noncomm_ring

end Conn

section Nab

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}

theorem sc_inv_rel {X a ai c : A} (h : X * a = a * X + c) (h1 : a * ai = 1) (h2 : ai * a = 1) :
    X * ai = ai * X - ai * c * ai := by
  calc X * ai = ai * a * X * ai := by rw [h2, one_mul]
    _ = ai * (X * a - c) * ai := by rw [h]; noncomm_ring
    _ = ai * X * (a * ai) - ai * c * ai := by noncomm_ring
    _ = _ := by rw [h1, mul_one]

theorem sc_N_eq (b : M.Ty P → A) :
    nabDef L0 κ b = -sc_B κ b - (1 / 2 : ℂ) • (L0.ζb * L0.GGi) := rfl

theorem sc_N_rel {b : M.Ty P → A} {g c : A} (hB : sc_B κ b * g = g * sc_B κ b + c)
    (hZ : (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi)) : nabDef L0 κ b * g = g * nabDef L0 κ b - c := by
  rw [sc_N_eq, sub_mul, neg_mul, hB, smul_mul_assoc, hZ, mul_sub, mul_neg, mul_smul_comm]; abel

theorem sc_Nζ (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζ = L0.ζ * nabDef L0 κ b + 1 := by
  rw [sc_N_rel (sc_Bζ h hF) (sc_Zc (sc_fc L0 (sc_mζb L0) (sc_mζ L0)) (sc_fc L0 (sc_mGGi L0) (sc_mζ L0)))]; abel

theorem sc_Nζb (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζb = L0.ζb * nabDef L0 κ b := by
  rw [sc_N_rel (sc_Bζb h hF) (sc_Zc rfl (sc_fc L0 (sc_mGGi L0) (sc_mζb L0)))]; abel

theorem sc_Ncrd (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g : A}
    (hg : g ∈ L0.crdOps) : nabDef L0 κ b * g = g * nabDef L0 κ b := by
  rw [sc_N_rel (sc_Bcrd h hF hg) (sc_Zc (coordinate_commute_zeta hg).1 (sc_crd_ops hg).2)]; abel

theorem sc_Nkap (h : SHyp P L0 QQ κ) (b : M.Ty P → A) (f : M.Ty P → ℂ) :
    κ f * nabDef L0 κ b = nabDef L0 κ b * κ f := by
  have hZ : κ f * (L0.ζb * L0.GGi) = (L0.ζb * L0.GGi) * κ f := by
    rw [← mul_assoc, sc_kc h f (sc_mζb L0), mul_assoc, sc_kc h f (sc_mGGi L0), mul_assoc]
  rw [sc_N_eq, mul_sub, sub_mul, mul_neg, neg_mul, sc_Bkap, mul_smul_comm, smul_mul_assoc, hZ]

theorem sc_NGG (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.GG = L0.GG * nabDef L0 κ b + L0.ζb := by
  have e1 := sc_Nζ h hF
  have e2 := sc_Nζb h hF
  have e3 : nabDef L0 κ b * algebraMap ℂ A L0.TT = algebraMap ℂ A L0.TT * nabDef L0 κ b := (Algebra.commutes _ _).symm
  rw [L0.GG_def]
  calc nabDef L0 κ b * (L0.ζ * L0.ζb - algebraMap ℂ A L0.TT)
      = (nabDef L0 κ b * L0.ζ) * L0.ζb - nabDef L0 κ b * algebraMap ℂ A L0.TT := by noncomm_ring
    _ = L0.ζ * (nabDef L0 κ b * L0.ζb) + L0.ζb - algebraMap ℂ A L0.TT * nabDef L0 κ b := by
        rw [e1, e3]; noncomm_ring
    _ = _ := by rw [e2]; noncomm_ring

theorem sc_NGGi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.GGi = L0.GGi * nabDef L0 κ b - L0.ζb * L0.GGi * L0.GGi := by
  rw [sc_inv_rel (sc_NGG h hF) L0.GG_GGi L0.GGi_GG, sc_fc L0 (sc_mGGi L0) (sc_mζb L0)]

theorem sc_Nζi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζi = L0.ζi * nabDef L0 κ b - L0.ζi * L0.ζi := by
  rw [sc_inv_rel (sc_Nζ h hF) L0.ζ_ζi L0.ζi_ζ, mul_one]

theorem sc_Nζbi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζbi = L0.ζbi * nabDef L0 κ b := by
  rw [sc_inv_rel (a := L0.ζb) (c := 0) (by rw [sc_Nζb h hF, add_zero]) L0.ζb_ζbi L0.ζbi_ζb]; simp

theorem sc_inv_uniq {a b b' : A} (h1 : b * a = 1) (h2 : a * b' = 1) : b = b' := by
  calc b = b * (a * b') := by rw [h2, mul_one]
    _ = (b * a) * b' := by noncomm_ring
    _ = b' := by rw [h1, one_mul]

theorem sc_sζ (h : SHyp P L0 QQ κ) : star L0.ζ = L0.ζb := h.1
theorem sc_sζb (h : SHyp P L0 QQ κ) : star L0.ζb = L0.ζ := by rw [← sc_sζ h, star_star]
theorem sc_sζi (h : SHyp P L0 QQ κ) : star L0.ζi = L0.ζbi :=
  sc_inv_uniq (a := L0.ζb) (by rw [← sc_sζ h, ← star_mul, L0.ζ_ζi, star_one]) L0.ζb_ζbi
theorem sc_sζbi (h : SHyp P L0 QQ κ) : star L0.ζbi = L0.ζi := by rw [← sc_sζi h, star_star]
theorem sc_sGG (h : SHyp P L0 QQ κ) : star L0.GG = L0.GG := by
  rw [L0.GG_def, star_sub, star_mul, sc_sζ h, sc_sζb h, H_alg_star h, h.2.1]
theorem sc_sGGi (h : SHyp P L0 QQ κ) : star L0.GGi = L0.GGi :=
  sc_inv_uniq (a := L0.GG) (by rw [← sc_sGG h, ← star_mul, L0.GG_GGi, star_one]) L0.GG_GGi
theorem sc_sc (h : SHyp P L0 QQ κ) (l) : star (L0.c l) = L0.cb l := (h.2.2.1 l).1
theorem sc_sci (h : SHyp P L0 QQ κ) (l) : star (L0.ci l) = L0.cbi l := (h.2.2.1 l).2.1
theorem sc_sp (h : SHyp P L0 QQ κ) (l) : star (L0.p l) = -L0.pb l := (h.2.2.1 l).2.2
theorem sc_scb (h : SHyp P L0 QQ κ) (l) : star (L0.cb l) = L0.c l := by rw [← sc_sc h, star_star]
theorem sc_scbi (h : SHyp P L0 QQ κ) (l) : star (L0.cbi l) = L0.ci l := by rw [← sc_sci h, star_star]
theorem sc_spb (h : SHyp P L0 QQ κ) (l) : star (L0.pb l) = -L0.p l := by
  rw [← neg_neg (L0.pb l), ← sc_sp h, star_neg, star_star]

end Nab

section Nabs

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem sc_Nsζb (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζb = L0.ζb * star (nabDef L0 κ b) - 1 := by
  have e := congrArg star (sc_Nζ h hF)
  rw [star_mul, star_add, star_mul, star_one, sc_sζ h] at e
  rw [e]; abel

theorem sc_Nsζbi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζbi = L0.ζbi * star (nabDef L0 κ b) + L0.ζbi * L0.ζbi := by
  have e := congrArg star (sc_Nζi h hF)
  rw [star_mul, star_sub, star_mul, star_mul, sc_sζi h] at e
  rw [e]; abel

theorem sc_Nsζ (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζ = L0.ζ * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Nζb h hF)
  rw [star_mul, star_mul, sc_sζb h] at e
  exact e.symm

theorem sc_Nsζi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζi = L0.ζi * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Nζbi h hF)
  rw [star_mul, star_mul, sc_sζbi h] at e
  exact e.symm

theorem sc_NsGG (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.GG = L0.GG * star (nabDef L0 κ b) - L0.ζ := by
  have e := congrArg star (sc_NGG h hF)
  rw [star_mul, star_add, star_mul, sc_sGG h, sc_sζb h] at e
  rw [e]; abel

theorem sc_NsGGi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.GGi = L0.GGi * star (nabDef L0 κ b) + L0.ζ * L0.GGi * L0.GGi := by
  have e := congrArg star (sc_NGGi h hF)
  rw [star_mul, star_sub, star_mul, star_mul, star_mul, sc_sGGi h, sc_sζb h] at e
  have c1 : L0.GGi * L0.ζ = L0.ζ * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζ L0)
  have c : L0.GGi * (L0.GGi * L0.ζ) = L0.ζ * L0.GGi * L0.GGi := by
    calc L0.GGi * (L0.GGi * L0.ζ) = L0.GGi * (L0.ζ * L0.GGi) := by rw [c1]
      _ = (L0.GGi * L0.ζ) * L0.GGi := by noncomm_ring
      _ = _ := by rw [c1]
  rw [e, c]; abel

theorem sc_Ns_of {g g' : A} (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hg : g ∈ L0.crdOps)
    (hs : star g = g') : star (nabDef L0 κ b) * g' = g' * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Ncrd h hF hg)
  rw [star_mul, star_mul, hs] at e
  exact e.symm

theorem sc_Nskap (h : SHyp P L0 QQ κ) (b : M.Ty P → A) (f : M.Ty P → ℂ) :
    κ f * star (nabDef L0 κ b) = star (nabDef L0 κ b) * κ f := by
  have e := congrArg star (sc_Nkap h b (fun ρ => star (f ρ)))
  rw [star_mul, star_mul, H_kstar h] at e
  simp only [star_star] at e
  exact e.symm

def sc_L {r : ℕ} (L0 : PreLevel A r) (N Ns : A)
    (p_nab : ∀ l, L0.p l * N = N * L0.p l) (pb_nab : ∀ l, L0.pb l * N = N * L0.pb l)
    (p_nabs : ∀ l, L0.p l * Ns = Ns * L0.p l) (pb_nabs : ∀ l, L0.pb l * Ns = Ns * L0.pb l)
    (nab_ζ : N * L0.ζ = L0.ζ * N + 1) (nab_ζi : N * L0.ζi = L0.ζi * N - L0.ζi * L0.ζi)
    (nab_ζb : N * L0.ζb = L0.ζb * N) (nab_ζbi : N * L0.ζbi = L0.ζbi * N)
    (nab_GG : N * L0.GG = L0.GG * N + L0.ζb) (nab_GGi : N * L0.GGi = L0.GGi * N - L0.ζb * L0.GGi * L0.GGi)
    (nab_c : ∀ l, N * L0.c l = L0.c l * N) (nab_ci : ∀ l, N * L0.ci l = L0.ci l * N)
    (nab_cb : ∀ l, N * L0.cb l = L0.cb l * N) (nab_cbi : ∀ l, N * L0.cbi l = L0.cbi l * N)
    (nabs_ζb : Ns * L0.ζb = L0.ζb * Ns - 1) (nabs_ζbi : Ns * L0.ζbi = L0.ζbi * Ns + L0.ζbi * L0.ζbi)
    (nabs_ζ : Ns * L0.ζ = L0.ζ * Ns) (nabs_ζi : Ns * L0.ζi = L0.ζi * Ns)
    (nabs_GG : Ns * L0.GG = L0.GG * Ns - L0.ζ) (nabs_GGi : Ns * L0.GGi = L0.GGi * Ns + L0.ζ * L0.GGi * L0.GGi)
    (nabs_c : ∀ l, Ns * L0.c l = L0.c l * Ns) (nabs_ci : ∀ l, Ns * L0.ci l = L0.ci l * Ns)
    (nabs_cb : ∀ l, Ns * L0.cb l = L0.cb l * Ns) (nabs_cbi : ∀ l, Ns * L0.cbi l = L0.cbi l * Ns) :
    R.LevelData A r where
  p := L0.p
  pb := L0.pb
  c := L0.c
  ci := L0.ci
  cb := L0.cb
  cbi := L0.cbi
  ζ := L0.ζ
  ζi := L0.ζi
  ζb := L0.ζb
  ζbi := L0.ζbi
  GG := L0.GG
  GGi := L0.GGi
  nab := N
  nabs := Ns
  TT := L0.TT
  fns_comm := L0.fns_comm
  c_ci := L0.c_ci
  ci_c := L0.ci_c
  cb_cbi := L0.cb_cbi
  cbi_cb := L0.cbi_cb
  ζ_ζi := L0.ζ_ζi
  ζi_ζ := L0.ζi_ζ
  ζb_ζbi := L0.ζb_ζbi
  ζbi_ζb := L0.ζbi_ζb
  GG_GGi := L0.GG_GGi
  GGi_GG := L0.GGi_GG
  GG_def := L0.GG_def
  p_c := L0.p_c
  p_ci := L0.p_ci
  p_cb := L0.p_cb
  p_cbi := L0.p_cbi
  p_ζ := L0.p_ζ
  p_ζi := L0.p_ζi
  p_ζb := L0.p_ζb
  p_ζbi := L0.p_ζbi
  p_GG := L0.p_GG
  p_GGi := L0.p_GGi
  pb_cb := L0.pb_cb
  pb_cbi := L0.pb_cbi
  pb_c := L0.pb_c
  pb_ci := L0.pb_ci
  pb_ζ := L0.pb_ζ
  pb_ζi := L0.pb_ζi
  pb_ζb := L0.pb_ζb
  pb_ζbi := L0.pb_ζbi
  pb_GG := L0.pb_GG
  pb_GGi := L0.pb_GGi
  p_p := L0.p_p
  p_pb := L0.p_pb
  pb_pb := L0.pb_pb
  p_nab := p_nab
  pb_nab := pb_nab
  p_nabs := p_nabs
  pb_nabs := pb_nabs
  nab_ζ := nab_ζ
  nab_ζi := nab_ζi
  nab_ζb := nab_ζb
  nab_ζbi := nab_ζbi
  nab_GG := nab_GG
  nab_GGi := nab_GGi
  nab_c := nab_c
  nab_ci := nab_ci
  nab_cb := nab_cb
  nab_cbi := nab_cbi
  nabs_ζb := nabs_ζb
  nabs_ζbi := nabs_ζbi
  nabs_ζ := nabs_ζ
  nabs_ζi := nabs_ζi
  nabs_GG := nabs_GG
  nabs_GGi := nabs_GGi
  nabs_c := nabs_c
  nabs_ci := nabs_ci
  nabs_cb := nabs_cb
  nabs_cbi := nabs_cbi

def sc_LL (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) : R.LevelData A P.r :=
  sc_L L0 (nabDef L0 κ b) (star (nabDef L0 κ b))
    (fun l => (sc_Ncrd h hF (sc_crd_p L0 l)).symm) (fun l => (sc_Ncrd h hF (sc_crd_pb L0 l)).symm)
    (fun l => by
      have := sc_Ns_of h hF (sc_crd_pb L0 l) (sc_spb h l)
      rw [neg_mul, mul_neg] at this; exact (neg_inj.mp this).symm)
    (fun l => by
      have := sc_Ns_of h hF (sc_crd_p L0 l) (sc_sp h l)
      rw [neg_mul, mul_neg] at this; exact (neg_inj.mp this).symm)
    (sc_Nζ h hF) (sc_Nζi h hF) (sc_Nζb h hF) (sc_Nζbi h hF) (sc_NGG h hF) (sc_NGGi h hF)
    (fun l => sc_Ncrd h hF (sc_crd_c L0 l)) (fun l => sc_Ncrd h hF (sc_crd_ci L0 l))
    (fun l => sc_Ncrd h hF (sc_crd_cb L0 l)) (fun l => sc_Ncrd h hF (sc_crd_cbi L0 l))
    (sc_Nsζb h hF) (sc_Nsζbi h hF) (sc_Nsζ h hF) (sc_Nsζi h hF) (sc_NsGG h hF) (sc_NsGGi h hF)
    (fun l => sc_Ns_of h hF (sc_crd_cb L0 l) (sc_scb h l)) (fun l => sc_Ns_of h hF (sc_crd_cbi L0 l) (sc_scbi h l))
    (fun l => sc_Ns_of h hF (sc_crd_c L0 l) (sc_sc h l)) (fun l => sc_Ns_of h hF (sc_crd_ci L0 l) (sc_sci h l))

end Nabs

section T21

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem sc_isPF_kap (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (g : M.Ty P → ℕ → ℂ) (s : M.Ty P → Finset ℕ) :
    IsPF fun Y => κ (fun ρ => ∏ i ∈ s ρ, (Y + g ρ i)) := by
  have e : ∀ Y, κ (fun ρ => ∏ i ∈ s ρ, (Y + g ρ i)) =
      ∑ ρ, (∏ i ∈ s ρ, (Polynomial.X + Polynomial.C (g ρ i))).eval Y • proj κ ρ := by
    intro Y; rw [kap_eq]; refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Polynomial.eval_prod]; simp
  simp_rw [e]
  exact isPF_sum _ fun ρ _ => isPF_cpoly _ _

theorem sc_isPF_xA (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : IsPF fun Y => xA κ Y :=
  sc_isPF_kap κ (fun ρ i => (M.rho P ρ i : ℂ)) (fun _ => Icc 1 (P.k - 1))

theorem sc_isPF_xEx (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (ex : Finset ℕ) : IsPF fun Y => κ (fun ρ => M.xEx P ex ρ Y) :=
  sc_isPF_kap κ (fun ρ i => (M.rho P ρ i : ℂ)) (fun _ => Icc 1 (P.k - 1) \ ex)

theorem sc_x_up {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {τ σ : M.Ty P} (hu : M.Up P l τ σ) (Y : ℂ) :
    M.xC P σ Y = (Y + (M.rho P τ l : ℂ) + 1) * M.xEx P {l} τ Y := by
  unfold M.xC M.xEx
  rw [← Finset.mul_prod_erase _ _ hl, Finset.sdiff_singleton_eq_erase]
  congr 1
  · rw [up_rho P hu l hl, if_pos rfl]; push_cast; ring
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [up_rho P hu i (Finset.mem_of_mem_erase hi), if_neg (Finset.ne_of_mem_erase hi), add_zero]

theorem sc_x_self {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) (τ : M.Ty P) (Y : ℂ) :
    M.xC P τ Y = (Y + (M.rho P τ l : ℂ)) * M.xEx P {l} τ Y := by
  unfold M.xC M.xEx
  rw [← Finset.mul_prod_erase _ _ hl, Finset.sdiff_singleton_eq_erase]

theorem sc_pGx (h : SHyp P L0 QQ κ) (σ : M.Ty P) (Y : ℂ) (X : A) :
    proj κ σ * (L0.GG * xA κ Y * X) = M.xC P σ Y • (L0.GG * (proj κ σ * X)) := by
  rw [← mul_assoc, ← mul_assoc, sc_pf h σ (sc_mGG L0), mul_assoc L0.GG, xA, pj_mul_kap, mul_smul_comm,
    smul_mul_assoc, mul_assoc]

theorem projection_gamma_coordinate (h : SHyp P L0 QQ κ) (σ τ : M.Ty P) (Y : ℂ) (X : A) :
    proj κ σ * (L0.GG * xA κ Y * X) * proj κ τ = M.xC P σ Y • (L0.GG * (proj κ σ * X * proj κ τ)) := by
  rw [sc_pGx h, smul_mul_assoc, mul_assoc, mul_assoc]

theorem sc_B_pj (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (σ : M.Ty P) :
    sc_B κ b * proj κ σ = b σ * proj κ σ := by
  unfold sc_B
  rw [Finset.sum_mul, Finset.sum_eq_single σ]
  · rw [mul_assoc, pj_idem, sc_pbp h hF]
  · intro ρ _ hρ; rw [mul_assoc, pj_orth κ hρ, mul_zero]
  · simp

theorem sc_B_pc (b : M.Ty P → A) (σ : M.Ty P) : proj κ σ * sc_B κ b = sc_B κ b * proj κ σ := by
  unfold proj; exact sc_Bkap κ b _

theorem connection_lowering_eq (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (sc_LL h hF).l0 Y = sc_B κ b - Y • (L0.ζb * L0.GGi) := by
  show -(nabDef L0 κ b) - algebraMap ℂ A (Y + 1 / 2) * (L0.ζb * L0.GGi) = _
  rw [sc_N_eq, ← Algebra.smul_def, add_smul]; abel

theorem connection_lowering_projection (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ : M.Ty P) :
    proj κ σ * (sc_LL h hF).l0 Y = (sc_LL h hF).l0 Y * proj κ σ := by
  rw [connection_lowering_eq, mul_sub, sub_mul, sc_B_pc, mul_smul_comm, smul_mul_assoc, sc_Zp h]

theorem connection_lowering_block (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ τ : M.Ty P) :
    proj κ σ * (sc_LL h hF).l0 Y * proj κ τ = if σ = τ then (b σ - Y • (L0.ζb * L0.GGi)) * proj κ σ else 0 := by
  rw [connection_lowering_projection, mul_assoc]
  split_ifs with hst
  · subst hst; rw [pj_idem, connection_lowering_eq, sub_mul, sc_B_pj h hF, smul_mul_assoc, sub_mul, smul_mul_assoc]
  · rw [pj_orth κ hst, mul_zero]

theorem lower_sum_block_entry (hR : Raises κ SS) (Y : ℂ) (σ τ : M.Ty P) :
    proj κ σ * (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) * proj κ τ =
      ∑ l ∈ Icc 1 (P.k - 1), M.xEx P {l} τ Y • (proj κ σ * SS l * proj κ τ) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, mul_assoc, kap_mul_pj, mul_smul_comm, mul_smul_comm, ← mul_assoc]

theorem connection_lower_left_entry (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 =
      L0.GG * xA κ Y * (sc_LL h hF).l0 Y + ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y) := rfl

theorem connection_lower_left_regular (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {Y : ℂ} (hY : Reg P Y) :
    QQ Y 1 0 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 := by
  rw [connection_lower_left_entry]
  apply eq_of_blocks κ
  intro σ τ
  rw [sc_lreg h hY, mul_add, add_mul, lower_sum_block_entry hR, projection_gamma_coordinate h, projection_gamma_coordinate h, connection_lowering_block h hF]
  by_cases hst : σ = τ
  · subst hst
    rw [sc_ldiag hF hY, if_pos rfl, Finset.sum_eq_zero, add_zero]
    intro l hl
    rw [blk_ss κ hR l σ σ (fun hu => up_ne P hl hu rfl), smul_zero]
  · rw [if_neg hst, mul_zero, smul_zero, zero_add]
    by_cases hex : ∃ l ∈ Icc 1 (P.k - 1), M.Up P l τ σ
    · obtain ⟨l, hl, hu⟩ := hex
      rw [sc_lup hF hY hl hu, Finset.sum_eq_single l, pj_ss_pj κ hR hu, mul_smul_comm, ← mul_assoc, ← mul_assoc,
        L0.GG_GGi, one_mul, smul_smul]
      · congr 1
        have hx := sc_x_up hl hu Y
        have hne : (Y + (M.rho P τ l : ℂ) + 1) ≠ 0 := by
          intro h0; apply hY σ; rw [hx, h0, zero_mul]
        rw [hx]; field_simp
      · intro j hj hjl; rw [blk_ss κ hR j σ τ (fun hu' => hjl (up_idx P hj hl hu' hu)), smul_zero]
      · intro hn; exact absurd hl hn
    · push_neg at hex
      rw [sc_lzero hF hY hst (fun l hl => hex l hl), mul_zero, smul_zero, Finset.sum_eq_zero]
      intro l hl; rw [blk_ss κ hR l σ τ (hex l hl), smul_zero]

theorem connection_lower_left_eq (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) (Y : ℂ) :
    QQ Y 1 0 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 := by
  have hpf : IsPF fun Y => (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 1 0 := by
    simp_rw [connection_lower_left_entry, connection_lowering_eq]
    refine isPF_add (isPF_mul (isPF_mul (isPF_const _) (sc_isPF_xA κ)) (isPF_sub (isPF_const _) (isPF_id_smul _)))
      (isPF_sum _ fun l _ => isPF_mul (isPF_const _) (sc_isPF_xEx κ {l}))
  exact isPF_eq (H_poly h 1 0) hpf (reg_infinite P) (fun Y hY => connection_lower_left_regular h hF hR hY) Y

end T21

section T12

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem sc_star_prod {Y : ℂ} (hY : star Y = Y) (s : Finset ℕ) (g : ℕ → ℝ) :
    star (∏ i ∈ s, (Y + (g i : ℂ))) = ∏ i ∈ s, (Y + (g i : ℂ)) := by
  rw [show star (∏ i ∈ s, (Y + (g i : ℂ))) = starRingEnd ℂ (∏ i ∈ s, (Y + (g i : ℂ))) from rfl, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_add, Complex.conj_ofReal]
  congr 1

theorem sc_star_xA (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : star Y = Y) : star (xA κ Y) = xA κ Y := by
  unfold xA; rw [H_kstar h]; congr 1; funext ρ; unfold M.xC; exact sc_star_prod hY _ _

theorem sc_star_kx (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : star Y = Y) (ex : Finset ℕ) :
    star (κ fun ρ => M.xEx P ex ρ Y) = κ fun ρ => M.xEx P ex ρ Y := by
  rw [H_kstar h]; congr 1; funext ρ; unfold M.xEx; exact sc_star_prod hY _ _

theorem connection_upper_right_entry (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 =
      L0.GG * xA κ Y * (sc_LL h hF).m0 Y + ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ Y) * star (SS l) := rfl

theorem connection_raising_constant_eq (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (sc_LL h hF).m0 Y = -star (nabDef L0 κ b) - (Y - 1 / 2) • (L0.ζ * L0.GGi) := by
  show -star (nabDef L0 κ b) - algebraMap ℂ A (Y - 1 / 2) * (L0.ζ * L0.GGi) = _
  rw [← Algebra.smul_def]

theorem connection_lowering_eq_nabla (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    (sc_LL h hF).l0 Y = -nabDef L0 κ b - (Y + 1 / 2) • (L0.ζb * L0.GGi) := by
  show -(nabDef L0 κ b) - algebraMap ℂ A (Y + 1 / 2) * (L0.ζb * L0.GGi) = _
  rw [← Algebra.smul_def]

theorem sc_GGζGGi (L0 : PreLevel A P.r) : L0.GG * (L0.ζ * L0.GGi) = L0.ζ := by
  rw [← mul_assoc, sc_fc L0 (sc_mGG L0) (sc_mζ L0), mul_assoc, L0.GG_GGi, mul_one]

theorem connection_star_lowering (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : star Y = Y) :
    star ((sc_LL h hF).l0 Y) = L0.GG * (sc_LL h hF).m0 Y * L0.GGi := by
  have hc : star (Y + 1 / 2 : ℂ) = Y + 1 / 2 := by simp [hY]
  rw [connection_lowering_eq_nabla, connection_raising_constant_eq, star_sub, star_neg, H_smul_star h, star_mul, sc_sGGi h, sc_sζb h, hc,
    mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc]
  have e1b : L0.GG * (L0.ζ * L0.GGi * L0.GGi) = L0.ζ * L0.GGi := by
    calc L0.GG * (L0.ζ * L0.GGi * L0.GGi) = (L0.GG * L0.ζ) * L0.GGi * L0.GGi := by noncomm_ring
      _ = (L0.ζ * L0.GG) * L0.GGi * L0.GGi := by rw [sc_fc L0 (sc_mGG L0) (sc_mζ L0)]
      _ = L0.ζ * (L0.GG * L0.GGi) * L0.GGi := by noncomm_ring
      _ = L0.ζ * L0.GGi := by rw [L0.GG_GGi, mul_one]
  have e1 : L0.GG * star (nabDef L0 κ b) * L0.GGi = star (nabDef L0 κ b) + L0.ζ * L0.GGi := by
    rw [mul_assoc, sc_NsGGi h hF, mul_add, ← mul_assoc, L0.GG_GGi, one_mul, e1b]
  have e2 : L0.GG * (L0.ζ * L0.GGi) * L0.GGi = L0.ζ * L0.GGi := by rw [sc_GGζGGi]
  have e3 : L0.GGi * L0.ζ = L0.ζ * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζ L0)
  rw [e1, e2, e3, show (Y + 1 / 2 : ℂ) = (Y - 1 / 2) + 1 by ring, add_smul, one_smul]
  abel

theorem connection_coordinate_commute (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    xA κ Y * (sc_LL h hF).m0 Y = (sc_LL h hF).m0 Y * xA κ Y := by
  unfold xA
  rw [connection_raising_constant_eq, mul_sub, sub_mul, mul_neg, neg_mul, sc_Nskap h, mul_smul_comm, smul_mul_assoc, ← mul_assoc,
    sc_kc h _ (sc_mζ L0), mul_assoc, sc_kc h _ (sc_mGGi L0), mul_assoc]

theorem connection_upper_right_real (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {Y : ℂ} (hY : star Y = Y) :
    QQ Y 0 1 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
  rw [← H_herm h hY 1 0, connection_lower_left_eq h hF hR Y, connection_lower_left_entry, connection_upper_right_entry, star_add, star_sum]
  congr 1
  · rw [star_mul, star_mul, sc_star_xA h hY, sc_sGG h, connection_star_lowering h hF hY]
    have hx : L0.GGi * xA κ Y * L0.GG = xA κ Y := by
      show L0.GGi * κ (fun ρ => M.xC P ρ Y) * L0.GG = κ (fun ρ => M.xC P ρ Y)
      rw [← sc_kc h _ (sc_mGGi L0), mul_assoc, L0.GGi_GG, mul_one]
    calc L0.GG * (sc_LL h hF).m0 Y * L0.GGi * (xA κ Y * L0.GG)
        = L0.GG * (sc_LL h hF).m0 Y * (L0.GGi * xA κ Y * L0.GG) := by noncomm_ring
      _ = L0.GG * xA κ Y * (sc_LL h hF).m0 Y := by rw [hx, mul_assoc, ← connection_coordinate_commute h hF, ← mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [star_mul, sc_star_kx h hY]

theorem connection_upper_right_eq (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) (Y : ℂ) :
    QQ Y 0 1 = (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
  have hpf : IsPF fun Y => (Q.NFData.QQ (⟨sc_LL h hF, κ, SS⟩ : Q.NFData P A) Y) 0 1 := by
    simp_rw [connection_upper_right_entry, connection_raising_constant_eq]
    refine isPF_add (isPF_mul (isPF_mul (isPF_const _) (sc_isPF_xA κ))
      (isPF_sub (isPF_const _) ?_)) (isPF_sum _ fun l _ => isPF_mul (sc_isPF_xEx κ {l}) (isPF_const _))
    have := isPF_cpoly (A := A) (Polynomial.X - Polynomial.C (1 / 2)) (L0.ζ * L0.GGi)
    simpa using this
  exact isPF_eq (H_poly h 0 1) hpf real_infinite (fun Y hY => connection_upper_right_real h hF hR hY) Y

end T12

section NabSS

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem sc_xEx_ne (P : M.Par) (ρ : M.Ty P) (ex : Finset ℕ) {Y : ℂ} (h : Y.im ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff]
  intro i _ h0
  apply h
  have := congrArg Complex.im h0
  simpa using this

theorem sc_x_of_P {σ : M.Ty P} {W : A} (hW : proj κ σ * W = W) (Y : ℂ) : xA κ Y * W = M.xC P σ Y • W := by
  conv_lhs => rw [← hW]
  rw [← mul_assoc, xA, kap_mul_pj, smul_mul_assoc, hW]

theorem sc_G_pc (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ : M.Ty P) :
    proj κ σ * (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) = (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) * proj κ σ := by
  have c1 : proj κ σ * xA κ Y = xA κ Y * proj κ σ := by unfold proj xA; exact kap_comm κ _ _
  rw [← mul_assoc, ← mul_assoc, sc_pf h σ (sc_mGG L0), mul_assoc L0.GG, c1, ← mul_assoc, mul_assoc _ (proj κ σ),
    connection_lowering_projection h hF, ← mul_assoc]

theorem lower_sum_block_structure (hR : Raises κ SS) (Y : ℂ) :
    GlobalTheory κ (fun τ σ => ∃ j ∈ Icc 1 (P.k - 1), M.Up P j τ σ)
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) := by
  refine blk_sum κ _ fun j hj => ?_
  refine blk_mono κ (blk_mul κ (blk_ss κ hR j) (blk_kap κ _)) ?_
  rintro τ σ ⟨μ, rfl, hμ⟩; exact ⟨j, hj, hμ⟩

theorem lower_sum_raising_block (hR : Raises κ SS) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (Y : ℂ) :
    proj κ ρ' * (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y)) * proj κ ρ =
      M.xEx P {l} ρ Y • (SS l * proj κ ρ) := by
  rw [lower_sum_block_entry hR, Finset.sum_eq_single l, pj_ss_pj κ hR hu]
  · intro j hj hjl; rw [blk_ss κ hR j ρ' ρ (fun hu' => hjl (up_idx P hj hl hu' hu)), smul_zero]
  · intro hn; exact absurd hl hn

theorem lower_sum_square_raising_zero (hR : Raises κ SS) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ')
    (u v : ℂ) :
    proj κ ρ' * ((∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ u)) *
      (∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ v))) * proj κ ρ = 0 := by
  refine blk_mul κ (lower_sum_block_structure hR u) (lower_sum_block_structure hR v) ρ' ρ ?_
  rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
  exact not_up_up P hi hj hl h1 h2 hu

theorem sc_K_comm (h : SHyp P L0 QQ κ) (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) (l : ℕ) (ρ : M.Ty P)
    {g : A} (hg : g ∈ L0.fns) : (SS l * proj κ ρ) * g = g * (SS l * proj κ ρ) := by
  rw [mul_assoc, sc_pf h ρ hg, ← mul_assoc, (hSS l g (sc_ops_of_fns L0 hg)).eq, mul_assoc]

theorem sc_keyN (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hu : M.Up P l ρ ρ') :
    (SS l * proj κ ρ) * nabDef L0 κ b - nabDef L0 κ b * (SS l * proj κ ρ) -
      (L0.ζb * L0.GGi) * (SS l * proj κ ρ) = 0 := by
  set K := SS l * proj κ ρ with hK
  set N := nabDef L0 κ b with hN
  set Z := L0.ζb * L0.GGi with hZ
  set G := fun Y => L0.GG * xA κ Y * (sc_LL h hF).l0 Y with hGdef
  set S := fun Y => ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ Y) with hSdef
  set e := fun Y => M.xEx P {l} ρ Y with he
  have hne : ρ ≠ ρ' := up_ne P hl hu
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGG : K * L0.GG = L0.GG * K := sc_K_comm h hSS l ρ (sc_mGG L0)
  have hKZ : K * Z = Z * K := by
    have c1 : K * L0.ζb = L0.ζb * K := sc_K_comm h hSS l ρ (sc_mζb L0)
    have c2 : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)
    rw [hZ, ← mul_assoc, c1, mul_assoc, c2, mul_assoc]
  have hKx : ∀ Y, K * xA κ Y = M.xC P ρ Y • K := by
    intro Y; rw [hK, mul_assoc, xA, pj_mul_kap, mul_smul_comm]
  have hG : ∀ Y, G Y * K - K * G Y =
      L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).l0 Y * K) - M.xC P ρ Y • (K * (sc_LL h hF).l0 Y)) := by
    intro Y
    have hPl : proj κ ρ' * ((sc_LL h hF).l0 Y * K) = (sc_LL h hF).l0 Y * K := by
      rw [← mul_assoc, connection_lowering_projection h hF, mul_assoc, hPK]
    have a1 : G Y * K = L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).l0 Y * K)) := by
      simp only [hGdef]; rw [mul_assoc, mul_assoc, sc_x_of_P hPl]
    have a2 : K * G Y = L0.GG * (M.xC P ρ Y • (K * (sc_LL h hF).l0 Y)) := by
      simp only [hGdef]
      calc K * (L0.GG * xA κ Y * (sc_LL h hF).l0 Y) = (K * L0.GG) * xA κ Y * (sc_LL h hF).l0 Y := by noncomm_ring
        _ = L0.GG * (K * xA κ Y) * (sc_LL h hF).l0 Y := by rw [hKGG]; noncomm_ring
        _ = _ := by rw [hKx, mul_assoc, smul_mul_assoc]
    rw [a1, a2, mul_sub]
  have hGP : ∀ Y σ, proj κ σ * G Y = G Y * proj κ σ := fun Y σ => sc_G_pc h hF Y σ
  have hT : ∀ u v, proj κ ρ' * (QQ u 1 0 * QQ v 1 0) * proj κ ρ = e v • (G u * K) + e u • (K * G v) := by
    intro u v
    rw [connection_lower_left_eq h hF hR u, connection_lower_left_eq h hF hR v, connection_lower_left_entry, connection_lower_left_entry]
    have p1 : proj κ ρ' * (G u * G v) * proj κ ρ = 0 := by
      refine blk_diag κ (X := G u * G v) (fun σ => ?_) ρ' ρ hne
      show proj κ σ * (G u * G v) = (G u * G v) * proj κ σ
      rw [← mul_assoc, hGP u σ, mul_assoc, hGP v σ, ← mul_assoc]
    have p2 : proj κ ρ' * (G u * S v) * proj κ ρ = e v • (G u * K) := by
      calc proj κ ρ' * (G u * S v) * proj κ ρ = (proj κ ρ' * G u) * S v * proj κ ρ := by noncomm_ring
        _ = G u * (proj κ ρ' * S v * proj κ ρ) := by rw [hGP]; noncomm_ring
        _ = _ := by rw [lower_sum_raising_block hR hl hu v, mul_smul_comm]
    have p3 : proj κ ρ' * (S u * G v) * proj κ ρ = e u • (K * G v) := by
      calc proj κ ρ' * (S u * G v) * proj κ ρ = proj κ ρ' * S u * (G v * proj κ ρ) := by noncomm_ring
        _ = (proj κ ρ' * S u * proj κ ρ) * G v := by rw [← hGP]; noncomm_ring
        _ = _ := by rw [lower_sum_raising_block hR hl hu u, smul_mul_assoc]
    have p4 : proj κ ρ' * (S u * S v) * proj κ ρ = 0 := lower_sum_square_raising_zero hR hl hu u v
    have : (G u + S u) * (G v + S v) = G u * G v + G u * S v + S u * G v + S u * S v := by noncomm_ring
    simp only [hGdef, hSdef] at this p1 p2 p3 p4 ⊢
    rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero]
  have hC : ∀ u v, e v • (G u * K - K * G u) - e u • (G v * K - K * G v) = 0 := by
    intro u v
    have c := hT u v
    rw [(lower_left_commute_self h u v).eq, hT v u] at c
    rw [smul_sub, smul_sub]
    rw [show e v • (G u * K) - e v • (K * G u) - (e u • (G v * K) - e u • (K * G v)) =
      (e v • (G u * K) + e u • (K * G v)) - (e u • (G v * K) + e v • (K * G u)) by abel, c, sub_self]
  set u : ℂ := Complex.I with hu'
  set v : ℂ := 2 * Complex.I with hv'
  have c2 : e v • (M.xC P ρ' u • ((sc_LL h hF).l0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).l0 u)) -
      e u • (M.xC P ρ' v • ((sc_LL h hF).l0 v * K) - M.xC P ρ v • (K * (sc_LL h hF).l0 v)) = 0 := by
    have c' : L0.GG * (e v • (M.xC P ρ' u • ((sc_LL h hF).l0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).l0 u)) -
      e u • (M.xC P ρ' v • ((sc_LL h hF).l0 v * K) - M.xC P ρ v • (K * (sc_LL h hF).l0 v))) = 0 := by
      rw [mul_sub, mul_smul_comm, mul_smul_comm, ← hG u, ← hG v]; exact hC u v
    have := congrArg (fun X => L0.GGi * X) c'
    simp only [← mul_assoc, L0.GGi_GG, one_mul, mul_zero] at this
    exact this
  rw [sc_x_up hl hu u, sc_x_up hl hu v, sc_x_self hl ρ u, sc_x_self hl ρ v, connection_lowering_eq_nabla, connection_lowering_eq_nabla] at c2
  have e2 : ∀ Y : ℂ, K * (-N - (Y + 1 / 2) • Z) = -(K * N) - (Y + 1 / 2) • (Z * K) := by
    intro Y; rw [mul_sub, mul_neg, mul_smul_comm, hKZ]
  have e3 : ∀ Y : ℂ, (-N - (Y + 1 / 2) • Z) * K = -(N * K) - (Y + 1 / 2) • (Z * K) := by
    intro Y; rw [sub_mul, neg_mul, smul_mul_assoc]
  rw [e2, e2, e3, e3] at c2
  have c3 : (e u * e v * (u - v)) • (K * N - N * K - Z * K) = 0 := by
    rw [← c2]; simp only [he]; module
  rcases smul_eq_zero.1 c3 with h0 | h0
  · exfalso
    have h1 : e u ≠ 0 := sc_xEx_ne P ρ {l} (by simp [hu'])
    have h2 : e v ≠ 0 := sc_xEx_ne P ρ {l} (by simp [hv'])
    have h3 : u - v ≠ 0 := by
      rw [hu', hv']; intro h; have := congrArg Complex.im h; norm_num at this
    exact mul_ne_zero (mul_ne_zero h1 h2) h3 h0
  · exact h0

theorem sc_N_pc (h : SHyp P L0 QQ κ) (b : M.Ty P → A) (σ : M.Ty P) :
    proj κ σ * nabDef L0 κ b = nabDef L0 κ b * proj κ σ := by
  unfold proj; exact sc_Nkap h b _

theorem sc_nabSS (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    nabDef L0 κ b * SS l = SS l * nabDef L0 κ b - L0.ζb * L0.GGi * SS l := by
  apply eq_of_rblocks κ
  intro ρ
  by_cases hex : ∃ ρ', M.Up P l ρ ρ'
  · obtain ⟨ρ', hu⟩ := hex
    have k := sc_keyN h hF hR hSS hl hu
    calc nabDef L0 κ b * SS l * proj κ ρ = nabDef L0 κ b * (SS l * proj κ ρ) := by rw [mul_assoc]
      _ = (SS l * proj κ ρ) * nabDef L0 κ b - L0.ζb * L0.GGi * (SS l * proj κ ρ) := by
        rw [← sub_eq_zero, show nabDef L0 κ b * (SS l * proj κ ρ) - ((SS l * proj κ ρ) * nabDef L0 κ b -
          L0.ζb * L0.GGi * (SS l * proj κ ρ)) = -((SS l * proj κ ρ) * nabDef L0 κ b - nabDef L0 κ b * (SS l * proj κ ρ) -
          (L0.ζb * L0.GGi) * (SS l * proj κ ρ)) by abel, k, neg_zero]
      _ = _ := by rw [mul_assoc (SS l), sc_N_pc h b ρ]; noncomm_ring
  · have h0 := ss_pj_none κ hR hex
    rw [mul_assoc, h0, mul_zero, sub_mul, mul_assoc, ← sc_N_pc h b ρ, ← mul_assoc, h0, zero_mul, mul_assoc, h0,
      mul_zero, sub_zero]

end NabSS

section NabsSS

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem sc_not_back {l j : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (h2 : M.Up P j ρ' ρ) :
    False := by
  have a := Finset.mem_Icc.1 hl
  have e1 := hu ⟨l - 1, by omega⟩; have e2 := h2 ⟨l - 1, by omega⟩
  simp only at e1 e2
  split_ifs at e1 e2 <;> omega

theorem upper_sum_block_structure (h : SHyp P L0 QQ κ) (hR : Raises κ SS) (Y : ℂ) :
    GlobalTheory κ (fun τ σ => ∃ j ∈ Icc 1 (P.k - 1), M.Up P j σ τ)
      (∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ Y) * star (SS l)) := by
  refine blk_sum κ _ fun j hj => ?_
  refine blk_mono κ (blk_mul κ (blk_kap κ _) (blk_star κ (H_pj_star h) (blk_ss κ hR j))) ?_
  rintro τ σ ⟨μ, hμ, rfl⟩; exact ⟨j, hj, hμ⟩

theorem connection_raising_projection (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ : M.Ty P) :
    proj κ σ * (sc_LL h hF).m0 Y = (sc_LL h hF).m0 Y * proj κ σ := by
  have hW : proj κ σ * (L0.ζ * L0.GGi) = (L0.ζ * L0.GGi) * proj κ σ := by
    rw [← mul_assoc, sc_pf h σ (sc_mζ L0), mul_assoc, sc_pf h σ (sc_mGGi L0), mul_assoc]
  have hN : proj κ σ * star (nabDef L0 κ b) = star (nabDef L0 κ b) * proj κ σ := by
    unfold proj; exact sc_Nskap h b _
  rw [connection_raising_constant_eq, mul_sub, sub_mul, mul_neg, neg_mul, hN, mul_smul_comm, smul_mul_assoc, hW]

theorem sc_H_pc (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) (σ : M.Ty P) :
    proj κ σ * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) = (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) * proj κ σ := by
  have c1 : proj κ σ * xA κ Y = xA κ Y * proj κ σ := by unfold proj xA; exact kap_comm κ _ _
  rw [← mul_assoc, ← mul_assoc, sc_pf h σ (sc_mGG L0), mul_assoc L0.GG, c1, ← mul_assoc, mul_assoc _ (proj κ σ),
    connection_raising_projection h hF, ← mul_assoc]

theorem connection_raising_gamma_shift (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (Y : ℂ) :
    L0.GG * (sc_LL h hF).m0 Y * L0.GGi = (sc_LL h hF).m0 (Y + 1) := by
  have e1b : L0.GG * (L0.ζ * L0.GGi * L0.GGi) = L0.ζ * L0.GGi := by
    calc L0.GG * (L0.ζ * L0.GGi * L0.GGi) = (L0.GG * L0.ζ) * L0.GGi * L0.GGi := by noncomm_ring
      _ = (L0.ζ * L0.GG) * L0.GGi * L0.GGi := by rw [sc_fc L0 (sc_mGG L0) (sc_mζ L0)]
      _ = L0.ζ * (L0.GG * L0.GGi) * L0.GGi := by noncomm_ring
      _ = L0.ζ * L0.GGi := by rw [L0.GG_GGi, mul_one]
  have e1 : L0.GG * star (nabDef L0 κ b) * L0.GGi = star (nabDef L0 κ b) + L0.ζ * L0.GGi := by
    rw [mul_assoc, sc_NsGGi h hF, mul_add, ← mul_assoc, L0.GG_GGi, one_mul, e1b]
  have e2 : L0.GG * (L0.ζ * L0.GGi) * L0.GGi = L0.ζ * L0.GGi := by rw [sc_GGζGGi]
  rw [connection_raising_constant_eq, connection_raising_constant_eq, mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, e1, e2,
    show (Y + 1 - 1 / 2 : ℂ) = (Y - 1 / 2) + 1 by ring, add_smul, one_smul]
  abel

theorem connection_diagonal_entry (h : SHyp P L0 QQ κ) (Y : ℂ) : QQ Y 1 1 = L0.GG * xA κ Y := diagonal_entry_hypothesis h Y

theorem upper_left_raising_block (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hu : M.Up P l ρ ρ') {v : ℂ} (hv : v.im ≠ 0) :
    proj κ ρ' * QQ v 0 0 * proj κ ρ = M.xEx P {l} ρ v • ((sc_LL h hF).m0 (v + 1) * (SS l * proj κ ρ)) := by
  set K := SS l * proj κ ρ with hK
  set H := fun Y => L0.GG * xA κ Y * (sc_LL h hF).m0 Y with hHdef
  have hne : ρ ≠ ρ' := up_ne P hl hu
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGGi : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)

  have hB : proj κ ρ' * (QQ v 0 1 * QQ (v + 1) 1 0) * proj κ ρ = M.xEx P {l} ρ (v + 1) • (H v * K) := by
    rw [connection_upper_right_eq h hF hR v, connection_lower_left_eq h hF hR (v + 1), connection_upper_right_entry, connection_lower_left_entry]
    set G1 := L0.GG * xA κ (v + 1) * (sc_LL h hF).l0 (v + 1)
    set S1 := ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ (v + 1))
    set H0 := L0.GG * xA κ v * (sc_LL h hF).m0 v
    set T0 := ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ v) * star (SS l)
    have p1 : proj κ ρ' * (H0 * G1) * proj κ ρ = 0 := by
      refine blk_diag κ (X := H0 * G1) (fun σ => ?_) ρ' ρ hne
      show proj κ σ * (H0 * G1) = (H0 * G1) * proj κ σ
      rw [← mul_assoc, sc_H_pc h hF v σ, mul_assoc, sc_G_pc h hF (v + 1) σ, ← mul_assoc]
    have p2 : proj κ ρ' * (H0 * S1) * proj κ ρ = M.xEx P {l} ρ (v + 1) • (H0 * K) := by
      calc proj κ ρ' * (H0 * S1) * proj κ ρ = (proj κ ρ' * H0) * S1 * proj κ ρ := by simp only [mul_assoc]
        _ = H0 * (proj κ ρ' * S1 * proj κ ρ) := by
          rw [show proj κ ρ' * H0 = H0 * proj κ ρ' from sc_H_pc h hF v ρ']; simp only [mul_assoc]
        _ = _ := by rw [lower_sum_raising_block hR hl hu (v + 1), mul_smul_comm]
    have p3 : proj κ ρ' * (T0 * G1) * proj κ ρ = 0 := by
      calc proj κ ρ' * (T0 * G1) * proj κ ρ = proj κ ρ' * T0 * (G1 * proj κ ρ) := by simp only [mul_assoc]
        _ = (proj κ ρ' * T0 * proj κ ρ) * G1 := by
          rw [show G1 * proj κ ρ = proj κ ρ * G1 from (sc_G_pc h hF (v + 1) ρ).symm]; simp only [mul_assoc]
        _ = 0 := by
          rw [upper_sum_block_structure h hR v ρ' ρ (fun ⟨j, _, hj⟩ => sc_not_back hl hu hj), zero_mul]
    have p4 : proj κ ρ' * (T0 * S1) * proj κ ρ = 0 := by
      refine blk_mul κ (upper_sum_block_structure h hR v) (lower_sum_block_structure hR (v + 1)) ρ' ρ ?_
      rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
      exact not_up_down P hi hj hl h1 h2 hu
    have : (H0 + T0) * (G1 + S1) = H0 * G1 + H0 * S1 + T0 * G1 + T0 * S1 := by noncomm_ring
    rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero, add_zero]

  have hD := quantum_determinant_relation h v
  have hq : proj κ ρ' * algebraMap ℂ A (M.qC P v) * proj κ ρ = 0 := by
    rw [← Algebra.commutes, mul_assoc, pj_orth κ hne.symm, mul_zero]
  have hL : proj κ ρ' * (QQ v 0 0 * QQ (v + 1) 1 1) * proj κ ρ =
      M.xC P ρ (v + 1) • (proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG) := by
    rw [connection_diagonal_entry h, mul_assoc, mul_assoc, mul_assoc, xA, kap_mul_pj, mul_smul_comm, mul_smul_comm, mul_smul_comm,
      ← sc_pf h ρ (sc_mGG L0)]
    noncomm_ring
  have hE : M.xC P ρ (v + 1) • (proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG) =
      M.xEx P {l} ρ (v + 1) • (H v * K) := by
    rw [← hL, ← hB]
    have e : QQ v 0 0 * QQ (v + 1) 1 1 = QQ v 0 1 * QQ (v + 1) 1 0 + algebraMap ℂ A (M.qC P v) := by
      rw [← hD]; abel
    rw [e, mul_add, add_mul, hq, add_zero]

  have hHK : H v * K = M.xC P ρ' v • (L0.GG * ((sc_LL h hF).m0 v * K)) := by
    have hPm : proj κ ρ' * ((sc_LL h hF).m0 v * K) = (sc_LL h hF).m0 v * K := by
      rw [← mul_assoc, connection_raising_projection h hF, mul_assoc, hPK]
    simp only [hHdef]; rw [mul_assoc, mul_assoc, sc_x_of_P hPm, mul_smul_comm]
  rw [hHK, smul_smul, sc_x_self hl ρ (v + 1), sc_x_up hl hu v] at hE
  have hn1 : M.xEx P {l} ρ (v + 1) ≠ 0 := sc_xEx_ne P ρ {l} (by simpa using hv)
  have hn2 : (v + 1 + (M.rho P ρ l : ℂ)) ≠ 0 := by
    intro h0; apply hv; have := congrArg Complex.im h0; simpa using this
  have hE2 : proj κ ρ' * QQ v 0 0 * proj κ ρ * L0.GG = M.xEx P {l} ρ v • (L0.GG * ((sc_LL h hF).m0 v * K)) := by
    have hc : (v + 1 + (M.rho P ρ l : ℂ)) * M.xEx P {l} ρ (v + 1) ≠ 0 := mul_ne_zero hn2 hn1
    have := congrArg (fun X => ((v + 1 + (M.rho P ρ l : ℂ)) * M.xEx P {l} ρ (v + 1))⁻¹ • X) hE
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    rw [this]; congr 1; field_simp; ring
  have := congrArg (fun X => X * L0.GGi) hE2
  simp only [mul_assoc, L0.GG_GGi, mul_one, smul_mul_assoc] at this
  rw [show proj κ ρ' * QQ v 0 0 * proj κ ρ = proj κ ρ' * (QQ v 0 0 * proj κ ρ) by rw [mul_assoc], this,
    ← connection_raising_gamma_shift h hF v, hKGGi]
  simp only [mul_assoc]

end NabsSS

section Main

variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}

theorem upper_lower_block_product (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (u w : ℂ) :
    proj κ ρ' * (QQ u 0 1 * QQ w 1 0) * proj κ ρ =
      M.xEx P {l} ρ w • ((L0.GG * xA κ u * (sc_LL h hF).m0 u) * (SS l * proj κ ρ)) := by
  have hne : ρ ≠ ρ' := up_ne P hl hu
  rw [connection_upper_right_eq h hF hR u, connection_lower_left_eq h hF hR w, connection_upper_right_entry, connection_lower_left_entry]
  set G1 := L0.GG * xA κ w * (sc_LL h hF).l0 w
  set S1 := ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ w)
  set H0 := L0.GG * xA κ u * (sc_LL h hF).m0 u
  set T0 := ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ u) * star (SS l)
  have p1 : proj κ ρ' * (H0 * G1) * proj κ ρ = 0 := by
    refine blk_diag κ (X := H0 * G1) (fun σ => ?_) ρ' ρ hne
    show proj κ σ * (H0 * G1) = (H0 * G1) * proj κ σ
    rw [← mul_assoc, sc_H_pc h hF u σ, mul_assoc, sc_G_pc h hF w σ, ← mul_assoc]
  have p2 : proj κ ρ' * (H0 * S1) * proj κ ρ = M.xEx P {l} ρ w • (H0 * (SS l * proj κ ρ)) := by
    calc proj κ ρ' * (H0 * S1) * proj κ ρ = (proj κ ρ' * H0) * S1 * proj κ ρ := by simp only [mul_assoc]
      _ = H0 * (proj κ ρ' * S1 * proj κ ρ) := by
        rw [show proj κ ρ' * H0 = H0 * proj κ ρ' from sc_H_pc h hF u ρ']; simp only [mul_assoc]
      _ = _ := by rw [lower_sum_raising_block hR hl hu w, mul_smul_comm]
  have p3 : proj κ ρ' * (T0 * G1) * proj κ ρ = 0 := by
    calc proj κ ρ' * (T0 * G1) * proj κ ρ = proj κ ρ' * T0 * (G1 * proj κ ρ) := by simp only [mul_assoc]
      _ = (proj κ ρ' * T0 * proj κ ρ) * G1 := by
        rw [show G1 * proj κ ρ = proj κ ρ * G1 from (sc_G_pc h hF w ρ).symm]; simp only [mul_assoc]
      _ = 0 := by
        rw [upper_sum_block_structure h hR u ρ' ρ (fun ⟨j, _, hj⟩ => sc_not_back hl hu hj), zero_mul]
  have p4 : proj κ ρ' * (T0 * S1) * proj κ ρ = 0 := by
    refine blk_mul κ (upper_sum_block_structure h hR u) (lower_sum_block_structure hR w) ρ' ρ ?_
    rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
    exact not_up_down P hi hj hl h1 h2 hu
  have : (H0 + T0) * (G1 + S1) = H0 * G1 + H0 * S1 + T0 * G1 + T0 * S1 := by noncomm_ring
  rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, add_zero, add_zero]

theorem lower_upper_block_product (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS) {l : ℕ}
    (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P} (hu : M.Up P l ρ ρ') (u w : ℂ) :
    proj κ ρ' * (QQ w 1 0 * QQ u 0 1) * proj κ ρ =
      M.xEx P {l} ρ w • ((SS l * proj κ ρ) * (L0.GG * xA κ u * (sc_LL h hF).m0 u)) := by
  have hne : ρ ≠ ρ' := up_ne P hl hu
  rw [connection_upper_right_eq h hF hR u, connection_lower_left_eq h hF hR w, connection_upper_right_entry, connection_lower_left_entry]
  set G1 := L0.GG * xA κ w * (sc_LL h hF).l0 w
  set S1 := ∑ l ∈ Icc 1 (P.k - 1), SS l * κ (fun ρ => M.xEx P {l} ρ w)
  set H0 := L0.GG * xA κ u * (sc_LL h hF).m0 u
  set T0 := ∑ l ∈ Icc 1 (P.k - 1), (κ fun ρ => M.xEx P {l} ρ u) * star (SS l)
  have p1 : proj κ ρ' * (G1 * H0) * proj κ ρ = 0 := by
    refine blk_diag κ (X := G1 * H0) (fun σ => ?_) ρ' ρ hne
    show proj κ σ * (G1 * H0) = (G1 * H0) * proj κ σ
    rw [← mul_assoc, sc_G_pc h hF w σ, mul_assoc, sc_H_pc h hF u σ, ← mul_assoc]
  have p2 : proj κ ρ' * (G1 * T0) * proj κ ρ = 0 := by
    calc proj κ ρ' * (G1 * T0) * proj κ ρ = (proj κ ρ' * G1) * T0 * proj κ ρ := by simp only [mul_assoc]
      _ = G1 * (proj κ ρ' * T0 * proj κ ρ) := by
        rw [show proj κ ρ' * G1 = G1 * proj κ ρ' from sc_G_pc h hF w ρ']; simp only [mul_assoc]
      _ = 0 := by
        rw [upper_sum_block_structure h hR u ρ' ρ (fun ⟨j, _, hj⟩ => sc_not_back hl hu hj), mul_zero]
  have p3 : proj κ ρ' * (S1 * H0) * proj κ ρ = M.xEx P {l} ρ w • ((SS l * proj κ ρ) * H0) := by
    calc proj κ ρ' * (S1 * H0) * proj κ ρ = proj κ ρ' * S1 * (H0 * proj κ ρ) := by simp only [mul_assoc]
      _ = (proj κ ρ' * S1 * proj κ ρ) * H0 := by
        rw [show H0 * proj κ ρ = proj κ ρ * H0 from (sc_H_pc h hF u ρ).symm]; simp only [mul_assoc]
      _ = _ := by rw [lower_sum_raising_block hR hl hu w, smul_mul_assoc]
  have p4 : proj κ ρ' * (S1 * T0) * proj κ ρ = 0 := by
    refine blk_mul κ (lower_sum_block_structure hR w) (upper_sum_block_structure h hR u) ρ' ρ ?_
    rintro ⟨μ, ⟨i, hi, h1⟩, ⟨j, hj, h2⟩⟩
    exact not_down_up P hi hj hl h1 h2 hu
  have : (G1 + S1) * (H0 + T0) = G1 * H0 + G1 * T0 + S1 * H0 + S1 * T0 := by noncomm_ring
  rw [this, mul_add, mul_add, mul_add, add_mul, add_mul, add_mul, p1, p2, p3, p4, zero_add, zero_add, add_zero]

theorem sc_keyNs (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {ρ ρ' : M.Ty P}
    (hu : M.Up P l ρ ρ') :
    (SS l * proj κ ρ) * star (nabDef L0 κ b) - star (nabDef L0 κ b) * (SS l * proj κ ρ) -
      (L0.ζ * L0.GGi) * (SS l * proj κ ρ) = 0 := by
  set K := SS l * proj κ ρ with hK
  set Ns := star (nabDef L0 κ b) with hNs
  set W := L0.ζ * L0.GGi with hW
  set e := fun Y => M.xEx P {l} ρ Y with he
  have hPK : proj κ ρ' * K = K := by rw [hK, ← mul_assoc, pj_ss_pj κ hR hu]
  have hKGG : K * L0.GG = L0.GG * K := sc_K_comm h hSS l ρ (sc_mGG L0)
  have hKW : K * W = W * K := by
    have c1 : K * L0.ζ = L0.ζ * K := sc_K_comm h hSS l ρ (sc_mζ L0)
    have c2 : K * L0.GGi = L0.GGi * K := sc_K_comm h hSS l ρ (sc_mGGi L0)
    rw [hW, ← mul_assoc, c1, mul_assoc, c2, mul_assoc]
  have hKx : ∀ Y, K * xA κ Y = M.xC P ρ Y • K := by
    intro Y; rw [hK, mul_assoc, xA, pj_mul_kap, mul_smul_comm]
  have hH : ∀ Y, (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) * K - K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) =
      L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).m0 Y * K) - M.xC P ρ Y • (K * (sc_LL h hF).m0 Y)) := by
    intro Y
    have hPm : proj κ ρ' * ((sc_LL h hF).m0 Y * K) = (sc_LL h hF).m0 Y * K := by
      rw [← mul_assoc, connection_raising_projection h hF, mul_assoc, hPK]
    have a1 : (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) * K = L0.GG * (M.xC P ρ' Y • ((sc_LL h hF).m0 Y * K)) := by
      rw [mul_assoc, mul_assoc, sc_x_of_P hPm]
    have a2 : K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) = L0.GG * (M.xC P ρ Y • (K * (sc_LL h hF).m0 Y)) := by
      calc K * (L0.GG * xA κ Y * (sc_LL h hF).m0 Y) = (K * L0.GG) * xA κ Y * (sc_LL h hF).m0 Y := by
            simp only [mul_assoc]
        _ = L0.GG * (K * xA κ Y) * (sc_LL h hF).m0 Y := by rw [hKGG]; simp only [mul_assoc]
        _ = _ := by rw [hKx, mul_assoc, smul_mul_assoc]
    rw [a1, a2, mul_sub]
  set u : ℂ := Complex.I with hu'
  set v : ℂ := 2 * Complex.I with hv'
  have huim : u.im ≠ 0 := by simp [hu']
  have hvim : v.im ≠ 0 := by simp [hv']

  have hR1 : proj κ ρ' * ((u - v) • (QQ u 0 1 * QQ v 1 0 - QQ v 1 0 * QQ u 0 1)) * proj κ ρ =
      proj κ ρ' * (QQ u 1 1 * QQ v 0 0 - QQ v 1 1 * QQ u 0 0) * proj κ ρ := by rw [H_rtt h u v 0 1 1 0]
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, upper_lower_block_product h hF hR hl hu u v, lower_upper_block_product h hF hR hl hu u v,
    mul_sub, sub_mul, connection_diagonal_entry h, connection_diagonal_entry h, projection_gamma_coordinate h, projection_gamma_coordinate h, upper_left_raising_block h hF hR hSS hl hu hvim,
    upper_left_raising_block h hF hR hSS hl hu huim, ← smul_sub, ← hK, hH u] at hR1
  have c2 : (u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) - M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
      ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
        (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K)) = 0 := by
    have c' : L0.GG * ((u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
        M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
      ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
        (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K))) = 0 := by
      have e1 : L0.GG * ((u - v) • (M.xEx P {l} ρ v • (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
          M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
        ((M.xC P ρ' u * M.xEx P {l} ρ v) • ((sc_LL h hF).m0 (v + 1) * K) -
          (M.xC P ρ' v * M.xEx P {l} ρ u) • ((sc_LL h hF).m0 (u + 1) * K))) =
        (u - v) • M.xEx P {l} ρ v • (L0.GG * (M.xC P ρ' u • ((sc_LL h hF).m0 u * K) -
          M.xC P ρ u • (K * (sc_LL h hF).m0 u))) -
        (M.xC P ρ' u • (L0.GG * M.xEx P {l} ρ v • ((sc_LL h hF).m0 (v + 1) * K)) -
          M.xC P ρ' v • (L0.GG * M.xEx P {l} ρ u • ((sc_LL h hF).m0 (u + 1) * K))) := by
        simp only [mul_sub, mul_smul_comm, smul_sub]; module
      rw [e1, hR1, sub_self]
    have := congrArg (fun X => L0.GGi * X) c'
    simp only [← mul_assoc, L0.GGi_GG, one_mul, mul_zero] at this
    exact this
  rw [sc_x_up hl hu u, sc_x_up hl hu v, sc_x_self hl ρ u, connection_raising_constant_eq, connection_raising_constant_eq, connection_raising_constant_eq] at c2
  have e2 : ∀ Y : ℂ, K * (-Ns - (Y - 1 / 2) • W) = -(K * Ns) - (Y - 1 / 2) • (W * K) := by
    intro Y; rw [mul_sub, mul_neg, mul_smul_comm, hKW]
  have e3 : ∀ Y : ℂ, (-Ns - (Y - 1 / 2) • W) * K = -(Ns * K) - (Y - 1 / 2) • (W * K) := by
    intro Y; rw [sub_mul, neg_mul, smul_mul_assoc]
  rw [e2, e3, e3, e3] at c2
  have c3 : (e u * e v * (u - v) * (u + (M.rho P ρ l : ℂ))) • (K * Ns - Ns * K - W * K) = 0 := by
    rw [← c2]; simp only [he]; module
  rcases smul_eq_zero.1 c3 with h0 | h0
  · exfalso
    have h1 : e u ≠ 0 := sc_xEx_ne P ρ {l} huim
    have h2 : e v ≠ 0 := sc_xEx_ne P ρ {l} hvim
    have h3 : u - v ≠ 0 := by
      rw [hu', hv']; intro h; have := congrArg Complex.im h; norm_num at this
    have h4 : u + (M.rho P ρ l : ℂ) ≠ 0 := by
      intro h; apply huim; have := congrArg Complex.im h; simpa using this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4 h0
  · exact h0

theorem sc_nabsSS (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hR : Raises κ SS)
    (hSS : ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    star (nabDef L0 κ b) * SS l = SS l * star (nabDef L0 κ b) - L0.ζ * L0.GGi * SS l := by
  have hNp : ∀ ρ, proj κ ρ * star (nabDef L0 κ b) = star (nabDef L0 κ b) * proj κ ρ := by
    intro ρ; unfold proj; exact sc_Nskap h b _
  apply eq_of_rblocks κ
  intro ρ
  by_cases hex : ∃ ρ', M.Up P l ρ ρ'
  · obtain ⟨ρ', hu⟩ := hex
    have k := sc_keyNs h hF hR hSS hl hu
    calc star (nabDef L0 κ b) * SS l * proj κ ρ = star (nabDef L0 κ b) * (SS l * proj κ ρ) := by rw [mul_assoc]
      _ = (SS l * proj κ ρ) * star (nabDef L0 κ b) - L0.ζ * L0.GGi * (SS l * proj κ ρ) := by
        rw [← sub_eq_zero, show star (nabDef L0 κ b) * (SS l * proj κ ρ) - ((SS l * proj κ ρ) * star (nabDef L0 κ b) -
          L0.ζ * L0.GGi * (SS l * proj κ ρ)) = -((SS l * proj κ ρ) * star (nabDef L0 κ b) -
          star (nabDef L0 κ b) * (SS l * proj κ ρ) - (L0.ζ * L0.GGi) * (SS l * proj κ ρ)) by abel, k, neg_zero]
      _ = _ := by rw [mul_assoc (SS l), hNp ρ]; noncomm_ring
  · have h0 := ss_pj_none κ hR hex
    rw [mul_assoc, h0, mul_zero, sub_mul, mul_assoc, ← hNp ρ, ← mul_assoc, h0, zero_mul, mul_assoc, h0,
      mul_zero, sub_zero]

theorem sc_main : Formalism.FourierDecayAlt.NF.SConn := by
  intro P A _ _ _ L0 QQ κ b SS _hP h hF hR hSS
  refine ⟨sc_LL h hF, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
    ⟨h.1, rfl, h.2.1⟩, ⟨H_kstar h, ?_, fun l g hg => hSS l g hg, hR, fun l hl => ⟨sc_nabSS h hF hR hSS hl,
      sc_nabsSS h hF hR hSS hl⟩⟩, fun Y => ⟨connection_lower_left_eq h hF hR Y, connection_upper_right_eq h hF hR Y, diagonal_entry_hypothesis h Y⟩⟩
  intro f g hg
  rcases hg with hg | hg
  · exact H_kops h f g (sc_ops_of_fns L0 hg)
  · rcases hg with rfl | hg
    · exact sc_Nkap h b f
    · rw [Set.mem_singleton_iff] at hg; subst hg; exact sc_Nskap h b f

end Main

end SC

theorem relIsCoreNorm : RelIsCoreNorm := by
  intro P A _ _ _ d
  unfold Q.NFData.Rel RelCore RelNorm
  constructor
  · rintro ⟨a, b, c, e, f, g⟩; exact ⟨⟨a, b, c, e, f⟩, g⟩
  · rintro ⟨⟨a, b, c, e, f⟩, g⟩; exact ⟨a, b, c, e, f, g⟩

theorem thmSOfSteps : ThmSOfSteps := by
  intro hI hC hU hN hRP hW hB hSC hSN hRel P A _ _ _ L0 QQ κ hP h
  obtain ⟨b, SS, hF, hR, hSS⟩ := hB hI hC hU P A L0 QQ κ hP h
  obtain ⟨L, hExt, hnab, hnabs, hst, hcore, hqq⟩ := hSC P A L0 QQ κ b SS hP h hF hR hSS
  obtain ⟨hnorm, h11⟩ := hSN hI hC hU hN hRP hW P A L0 QQ κ b SS L hP h hF hR hSS hExt hnab hnabs hst hcore
    (fun Y => ⟨(hqq Y).1, (hqq Y).2.1⟩)
  refine ⟨⟨L, κ, SS⟩, hExt, rfl, hst, (hRel P A ⟨L, κ, SS⟩).2 ⟨hcore, hnorm⟩, fun Y => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact h11 Y
  · exact (hqq Y).2.1
  · exact (hqq Y).1
  · exact (hqq Y).2.2

end

end Formalism.FourierDecayAlt.P.NFx2

namespace Formalism.FourierDecayAlt.P

theorem shift_block : Formalism.FourierDecayAlt.NF.SBlock := NFx2.sb_main

theorem shift_connection : Formalism.FourierDecayAlt.NF.SConn := NFx2.sc_main

theorem shift_norm : Formalism.FourierDecayAlt.NF.SNorm := NFx2.sn_main

theorem theorem_S_of_steps : Formalism.FourierDecayAlt.NF.ThmSOfSteps := NFx2.thmSOfSteps

theorem theorem_S_ring : Formalism.FourierDecayAlt.NF.ThmSRing :=
  NFx2.thmSOfSteps Mx3.tyInterlaces Mx3.tyComplete Mx3.rhoUp Mx3.nrmFacts Mx3.realPoints Mx3.wExact
    NFx2.sb_main NFx2.sc_main NFx2.sn_main NFx2.relIsCoreNorm

end Formalism.FourierDecayAlt.P
