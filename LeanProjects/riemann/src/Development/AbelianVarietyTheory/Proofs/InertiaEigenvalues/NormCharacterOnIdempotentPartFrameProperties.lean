import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticNormsTraceUniformizerFacts

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

variable {K : UQ} (B : InvAlg K)

theorem eta_c (x : K.E) : K.eta (K.c x) = K.eta x := by
  unfold UQ.eta; rw [UnramNorm.val_c]

theorem norm_sigma (u : B.A) : Algebra.norm K.E (B.σ u) = K.c (Algebra.norm K.E u) := by
  have h := Algebra.norm_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) u
  rw [h, RingEquiv.apply_symm_apply]

theorem norm_ne_zero_of_isUnit {u : B.A} (hu : IsUnit u) : Algebra.norm K.E u ≠ 0 :=
  (hu.map (Algebra.norm K.E)).ne_zero

theorem eta_norm_mul_sigma {v : B.A} (hv : IsUnit v) : K.eta (Algebra.norm K.E (v * B.σ v)) = 1 := by
  rw [map_mul, norm_sigma, eta_mul (norm_ne_zero_of_isUnit B hv)
    ((map_ne_zero K.c).2 (norm_ne_zero_of_isUnit B hv)), eta_c, eta_sq]

theorem twist_mul {E : B.A} (hE : E * E = E) (x y : B.A) :
    (x * E + (1 - E)) * (y * E + (1 - E)) = x * y * E + (1 - E) := by
  linear_combination (x * y - x - y + 1) * hE

theorem twist_isUnit {E : B.A} (hE : E * E = E) {x : B.A} (hx : IsUnit x) : IsUnit (x * E + (1 - E)) := by
  obtain ⟨u, rfl⟩ := hx
  refine isUnit_iff_exists_inv.2 ⟨((u⁻¹ : B.Aˣ) : B.A) * E + (1 - E), ?_⟩
  rw [twist_mul B hE, Units.mul_inv, one_mul]; ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem e_mul_eS {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by
  unfold eS; rw [Finset.mul_sum]; split_ifs with h
  · rw [Finset.sum_eq_single i (fun j _ hji => he.ortho (Ne.symm hji)) (fun h' => absurd h h'), (he.idem i).eq]
  · exact Finset.sum_eq_zero fun j hj => he.ortho (fun hij => h (hij ▸ hj))

theorem eS_idem {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) :
    eS B e I * eS B e I = eS B e I := by
  show (∑ i ∈ I, e i) * eS B e I = _
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [e_mul_eS B he, if_pos hi]

theorem sigma_e {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (i : ι) : B.σ (e i) = e i := by
  obtain ⟨f, -, -, -, h1, h2⟩ := h.2 i
  by_cases hi : i ∈ S
  · rw [(h1 hi).1, (h1 hi).2]
  · rw [(h2 hi).2, map_add, B.σ_σ, add_comm]

theorem sigma_eS {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) : B.σ (eS B e I) = eS B e I := by
  unfold eS; rw [map_sum]; exact Finset.sum_congr rfl fun i _ => sigma_e B h i

theorem chi_mul {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by
  unfold chi
  have hE := eS_idem B he I
  rw [← twist_mul B hE, map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hx))
    (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy))]

theorem chi_norm {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) (I : Finset ι) {w : B.A} (hw : IsUnit w) :
    chi B e I (w * B.σ w) = 1 := by
  unfold chi
  have hE := eS_idem B h.1.toOrthogonalIdempotents I
  have hσ : B.σ (w * eS B e I + (1 - eS B e I)) = B.σ w * eS B e I + (1 - eS B e I) := by
    rw [map_add, map_mul, map_sub, map_one, sigma_eS B h]
  rw [← twist_mul B hE, ← hσ]
  exact eta_norm_mul_sigma B (twist_isUnit B hE hw)

theorem eta_prod {s : Finset ι} (x : ι → K.E) (hx : ∀ i ∈ s, x i ≠ 0) :
    K.eta (∏ i ∈ s, x i) = ∏ i ∈ s, K.eta (x i) := by
  induction s using Finset.induction_on with
  | empty => simp [UQ.eta, val]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      eta_mul (hx a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.2 fun i hi => hx i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hx i (Finset.mem_insert_of_mem hi)]

theorem chi_prod {e π : ι → B.A} {S : Finset ι} (h : IsFrame B e π S) (I J : Finset ι) (hJ : J ⊆ S) :
    chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card := by
  have he := h.1.1.toOrthogonalIdempotents
  set E := eS B e I with hEdef
  have hE := eS_idem B he I

  have h1 : (∏ j ∈ J.filter (· ∉ I), π j) * E = E := by
    refine Finset.prod_induction _ (fun t => t * E = E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : E = (1 - e j) * E := by
      rw [sub_mul, one_mul, mul_comm (e j) E, hEdef, mul_comm, e_mul_eS B he, if_neg hjI, sub_zero]
    show π j * E = E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have h2 : (∏ j ∈ J.filter (· ∈ I), π j) * (1 - E) = 1 - E := by
    refine Finset.prod_induction _ (fun t => t * (1 - E) = 1 - E) (fun a b ha hb => by rw [mul_assoc, hb, ha]) (one_mul _) ?_
    intro j hj
    obtain ⟨hjJ, hjI⟩ := Finset.mem_filter.1 hj
    have hEe : 1 - E = (1 - e j) * (1 - E) := by
      have := e_mul_eS B he j I
      rw [if_pos hjI] at this
      rw [← hEdef] at this
      linear_combination -this
    show π j * (1 - E) = 1 - E
    rw [hEe, ← mul_assoc, (h.2 j (hJ hjJ)).2.1]
  have hprod : (∏ j ∈ J, π j) * E + (1 - E) = ∏ j ∈ J.filter (· ∈ I), π j := by
    rw [← Finset.prod_filter_mul_prod_filter_not J (· ∈ I), mul_assoc]
    rw [h1]
    linear_combination -h2
  unfold chi
  rw [← hEdef, hprod, map_prod, eta_prod]
  · rw [Finset.filter_mem_eq_inter]
    rw [Finset.prod_congr rfl fun j hj => (h.2 j (hJ (Finset.mem_inter.1 hj).1)).2.2, Finset.prod_const]
  · intro j hj
    exact norm_ne_zero_of_isUnit B (h.2 j (hJ (Finset.mem_filter.1 hj).1)).1.1

theorem mul_eq_zero_of_idem {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by
  rw [← ha, ← hb, show a * e i * (b * e j) = a * b * (e i * e j) by ring, he.ortho hij, mul_zero]

theorem sum_mul_sum_diag {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact Finset.sum_eq_single i (fun j hj hji => mul_eq_zero_of_idem B he (Ne.symm hji) (ha i hi) (hb j hj))
    (fun h => absurd hi h)

theorem chi_plus {e : ι → B.A} {S : Finset ι} (h : IsPre B e S) {y : B.A} (hy : B.Plus y) :
    chi B e S y = K.eta (Algebra.norm K.E y) := by
  have he := h.1.toOrthogonalIdempotents
  have hcomp := h.1.complete
  choose f hf using h.2
  set E := eS B e S with hEdef
  have hE : E * E = E := eS_idem B he S
  have hσE : B.σ E = E := sigma_eS B h S
  have hfe : ∀ i ∈ Sᶜ, f i * e i = f i := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, hid.eq, (h2 hiS).1, add_zero]
  have hge : ∀ i ∈ Sᶜ, B.σ (f i) * e i = B.σ (f i) := by
    intro i hi
    have hiS := Finset.mem_compl.1 hi
    obtain ⟨hid, -, -, -, h2⟩ := hf i
    rw [(h2 hiS).2, mul_add, mul_comm (B.σ (f i)) (f i), (h2 hiS).1, zero_add, ← map_mul, hid.eq]
  set F := ∑ i ∈ Sᶜ, f i with hFdef
  set G := ∑ i ∈ Sᶜ, B.σ (f i) with hGdef
  have hGσ : G = B.σ F := by rw [hGdef, hFdef, map_sum]
  have hFF : F * F = F := by
    rw [hFdef, sum_mul_sum_diag B he _ f f hfe hfe]; exact Finset.sum_congr rfl fun i _ => (hf i).1.eq
  have hFG : F * G = 0 := by
    rw [hFdef, hGdef, sum_mul_sum_diag B he _ f _ hfe hge]
    exact Finset.sum_eq_zero fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).1
  have hGG : G * G = G := by rw [hGσ, ← map_mul, hFF]
  have hFE : F * E = 0 := by
    rw [hFdef, hEdef, eS, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
      mul_eq_zero_of_idem B he (fun hij => Finset.mem_compl.1 hi (by rw [hij]; exact hj)) (hfe i hi) (he.idem j).eq
  have hGE : G * E = 0 := by rw [hGσ, ← hσE, ← map_mul, hFE, map_zero]
  have hFGsum : F + G = 1 - E := by
    have h1 : F + G = ∑ i ∈ Sᶜ, e i := by
      rw [hFdef, hGdef, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => ((hf i).2.2.2.2 (Finset.mem_compl.1 hi)).2.symm
    rw [h1, ← hcomp, ← Finset.sum_add_sum_compl S e, hEdef, eS]; ring
  set w := y * F + G + E with hwdef
  have hσw : B.σ w = y * G + F + E := by
    rw [hwdef, map_add, map_add, map_mul, hy.2, hσE, hGσ, B.σ_σ]
  have hw : w * B.σ w = y * (1 - E) + E := by
    rw [hσw, ← hFGsum]
    linear_combination (y ^ 2 + 1) * hFG + y * hFF + (y + 1) * hFE + y * hGG + (y + 1) * hGE + hE
  have hE' : (1 - E) * (1 - E) = 1 - E := by linear_combination hE
  have hwwU : IsUnit (w * B.σ w) := by
    have := twist_isUnit B hE' hy.1
    rwa [sub_sub_cancel, ← hw] at this
  have hwU : IsUnit w := isUnit_of_mul_isUnit_left hwwU
  have hsplit : y = (y * E + (1 - E)) * (w * B.σ w) := by
    rw [hw]; linear_combination (y ^ 2 - 2 * y + 1) * hE
  unfold chi
  rw [← hEdef]
  conv_rhs => rw [hsplit]
  rw [map_mul, eta_mul (norm_ne_zero_of_isUnit B (twist_isUnit B hE hy.1)) (norm_ne_zero_of_isUnit B hwwU),
    eta_norm_mul_sigma B hwU, mul_one]

theorem chi_frame_props : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S →
    (∀ (I : Finset ι) (x y : B.A), IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y) ∧
    (∀ (I : Finset ι) (w : B.A), IsUnit w → chi B e I (w * B.σ w) = 1) ∧
    (∀ I J : Finset ι, I ⊆ S → J ⊆ S → chi B e I (∏ j ∈ J, π j) = (-1) ^ (J ∩ I).card) ∧
    (∀ y, B.Plus y → chi B e S y = K.eta (Algebra.norm K.E y)) := by
  intro K B ι _ _ e π S h
  exact ⟨fun I x y hx hy => chi_mul B h.1.1.toOrthogonalIdempotents I hx hy, fun I w hw => chi_norm B h.1 I hw,
    fun I J _ hJ => chi_prod B h I J hJ, fun y hy => chi_plus B h.1 hy⟩

end GlobalTheory.UnitLemma.Desc
