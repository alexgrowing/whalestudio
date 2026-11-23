import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SigmaSplitSymmInl
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapInclKMemTwCentResOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormProductIterateTwistedConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigIterateApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigResIterateEqSelf
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AtPBd

variable {p : ℕ} [Fact p.Prime]

def EBd {n : ℕ} (M : Matrix (Fin n) (Fin n) (PadicAlgCl p)) (c : ℝ) : Prop :=
  GlobalTheory.InnerAutomorphism.EntriesBounded M c

theorem EBd.mono {n : ℕ} {M : Matrix (Fin n) (Fin n) (PadicAlgCl p)} {a b : ℝ} (h : EBd M a) (hab : a ≤ b) :
    EBd M b := fun i j => (h i j).trans hab

theorem EBd.mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) (PadicAlgCl p)} {a b : ℝ} (hA : EBd A a) (hB : EBd B b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : EBd (A * B) (a * b) := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

theorem EBd.one (n : ℕ) : EBd (1 : Matrix (Fin n) (Fin n) (PadicAlgCl p)) 1 := by
  intro i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem norm_root_le {n : ℕ} {M : Matrix (Fin n) (Fin n) (PadicAlgCl p)} {c : ℝ} (hM : EBd M c) (hc : 0 ≤ c)
    {μ : PadicAlgCl p} (hμ : M.charpoly.IsRoot μ) : ‖μ‖ ≤ c := by
  have hdet : (Matrix.scalar (Fin n) μ - M).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hμ
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv' : M *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
  haveI : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv0 (funext fun i => (IsEmpty.false i).elim)
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖v j‖
  have hvi : v i ≠ 0 := by
    intro h0
    apply hv0
    funext j
    have := hi j
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  have e : μ * v i = ∑ j, M i j * v j := by
    have := congrFun hv' i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hle : ‖μ * v i‖ ≤ c * ‖v i‖ := by
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc (norm_nonneg _)) fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hM i j) (hi j) (norm_nonneg _) hc
  rw [norm_mul] at hle
  exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hvi)

end GlobalTheory.AtPBd

noncomputable section

namespace GlobalTheory.AtPBd

variable {p : ℕ} [Fact p.Prime]

def GB (G : HTGroup p) (r : ℕ) (g : Gr G r) (c : ℝ) : Prop :=
  EBd ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)).map (Qr p r).val) c ∧
    ∀ w, EBd ((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) c

variable (G : HTGroup p) (r : ℕ)

theorem GB.mono {g : Gr G r} {a b : ℝ} (h : GB G r g a) (hab : a ≤ b) : GB G r g b :=
  ⟨h.1.mono hab, fun w => (h.2 w).mono hab⟩

theorem GB.mul {g h : Gr G r} {a b : ℝ} (hg : GB G r g a) (hh : GB G r h b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    GB G r (g * h) (a * b) := by
  refine ⟨?_, fun w => ?_⟩
  · have := hg.1.mul hh.1 ha hb
    rwa [← Matrix.map_mul] at this
  · have := (hg.2 w).mul (hh.2 w) ha hb
    rwa [← Matrix.map_mul] at this

theorem GB.one : GB G r 1 1 := by
  refine ⟨?_, fun w => ?_⟩
  · have := EBd.one (p := p) 1
    simpa [Matrix.map_one] using this
  · have := EBd.one (p := p) G.n
    simpa [Matrix.map_one] using this

theorem GB.of_mem {k : Gr G r} (hk : k ∈ KHT p G.m G.n r G.Fw) : GB G r k 1 := by
  refine ⟨?_, fun w => ?_⟩
  · obtain ⟨h, e⟩ := hk.1
    intro i j
    rw [Matrix.map_apply, ← e]
    exact (mem_Obar_iff (p := p)).1 ((h : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (GlobalTheory.LKRes.Q0 p) r)) i j).2
  · obtain ⟨h, e⟩ := hk.2 w (Set.mem_univ _)
    intro i j
    rw [Matrix.map_apply, ← e]
    exact GlobalTheory.LKRes.Model.mulMap_intKQ p (G.Fw w) r _ ((h : Matrix (Fin G.n) (Fin G.n) (intKQ p (G.Fw w) r)) i j).2

theorem GB.exists (g : Gr G r) : ∃ c : ℝ, 1 ≤ c ∧ GB G r g c := by
  let a : ℝ := ∑ i, ∑ j, ‖((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)).map (Qr p r).val) i j‖
  let b : ℝ := ∑ w, ∑ i, ∑ j,
    ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) i j‖
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  refine ⟨1 + a + b, by linarith, fun i j => ?_, fun w i j => ?_⟩
  · have h1 : ‖((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)).map (Qr p r).val) i j‖ ≤ a :=
      (Finset.single_le_sum (f := fun j => ‖((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)).map (Qr p r).val) i j‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖((g.1 : Matrix (Fin 1) (Fin 1) (Qr p r)).map (Qr p r).val) i j‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
    linarith
  · have h1 : ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map
        (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) i j‖ ≤ b :=
      ((Finset.single_le_sum (f := fun j => ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map
          (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map
          (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) i j‖) (fun _ _ => by positivity) (Finset.mem_univ i))).trans
        (Finset.single_le_sum (f := fun w => ∑ i, ∑ j, ‖((g.2 w : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map
          (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r)) i j‖) (fun _ _ => by positivity) (Finset.mem_univ w))
    linarith

theorem GB.list_prod (l : List (Gr G r)) {c : ℝ} (hc : 1 ≤ c) (h : ∀ x ∈ l, GB G r x c) :
    GB G r l.prod (c ^ l.length) := by
  induction l with
  | nil => simpa using GB.one G r
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ']
    exact (h x List.mem_cons_self).mul G r (ih fun y hy => h y (List.mem_cons_of_mem _ hy))
      (by linarith) (by positivity)

end GlobalTheory.AtPBd

noncomputable section

namespace GlobalTheory.AtPBd

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (r : ℕ)

theorem gl_one_mul_comm {R : Type} [CommRing R] (a b : GL (Fin 1) R) : a * b = b * a := by
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply, mul_comm]

theorem mulMap_inclK (w : Fin G.m) (a : G.Fw w) :
    GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r (inclK p (G.Fw w) r a) = algebraMap (G.Fw w) (PadicAlgCl p) a := by
  show (a : PadicAlgCl p) * 1 = _
  rw [mul_one]; rfl

theorem bound_of_conj (g : Gp G) (M P : Gr G r) (h : inclG G r g = P * M * P⁻¹) {c : ℝ} (hc : 0 ≤ c)
    (hM : GB G r M c) :
    ‖((g.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ c ∧ ∀ (w : Fin G.m) (μ : PadicAlgCl p),
      (((g.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map
        (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ c := by
  refine ⟨?_, fun w μ hμ => ?_⟩
  · have h1 : (inclG G r g).1 = M.1 := by
      rw [h, Prod.fst_mul, Prod.fst_mul, Prod.fst_inv, gl_one_mul_comm P.1 M.1, mul_inv_cancel_right]
    have h2 := congrArg (fun x : GL (Fin 1) (Qr p r) => (Qr p r).val ((x : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0)) h1
    have h3 : (Qr p r).val (((inclG G r g).1 : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0) =
        algebraMap ℚ_[p] (PadicAlgCl p) (g.1 : ℚ_[p]) := by
      simp [inclG]
    rw [← PadicAlgCl.norm_extends, ← h3, h2]
    exact hM.1 0 0
  · let f : KQ p (G.Fw w) r →+* PadicAlgCl p := (GlobalTheory.LKRes.Model.mulMap p (G.Fw w) r).toRingHom
    let u : (Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p))ˣ := Units.map f.mapMatrix.toMonoidHom (P.2 w)
    have h1 := congrArg (fun x : Gr G r => ((x.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
      Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map f) h
    have hl : (((inclG G r g).2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map f =
        ((g.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).map
          (algebraMap (G.Fw w) (PadicAlgCl p)) := by
      ext i j
      simp only [Matrix.map_apply]
      exact mulMap_inclK G r w _
    have hr : (((P * M * P⁻¹).2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) :
        Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map f =
        (u : Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p)) *
          ((M.2 w : GL (Fin G.n) (KQ p (G.Fw w) r)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r)).map f *
          ((u⁻¹ : (Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p))ˣ) : Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p)) := by
      simp only [Prod.snd_mul, Prod.snd_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul, u]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [hl, hr] at h1
    rw [← Matrix.charpoly_map, h1, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at hμ
    exact norm_root_le (hM.2 w) hc hμ

end GlobalTheory.AtPBd

noncomputable section

namespace GlobalTheory.AtPBd

section Iter

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p) (r : ℕ)

theorem sig_iter_apply (k : ℕ) (g : Gr G r) :
    (⇑(sigG G r))^[k] g = ((⇑(GlobalTheory.LKLoc.sig p (GlobalTheory.LKRes.Q0 p) 1 r))^[k] g.1,
      fun i => (⇑(sigRes p (G.Fw i) G.n r))^[k] (g.2 i)) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    rfl

theorem sig_iter_self {r : ℕ} (hr : 0 < r) (g : Gr G r) : (⇑(sigG G r))^[r] g = g := by
  rw [sig_iter_apply]
  refine Prod.ext ?_ (funext fun i => ?_)
  · exact GlobalTheory.LKLoc.sig_iterate_r p (GlobalTheory.LKRes.Q0 p) inferInstance 1 r hr g.1
  · exact sigRes_iterate_eq_self p (G.Fw i) G.n r hr (g.2 i)

theorem sig_iter_mem (k : ℕ) {g : Gr G r} (hg : g ∈ KHT p G.m G.n r G.Fw) :
    (⇑(sigG G r))^[k] g ∈ KHT p G.m G.n r G.Fw := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact GlobalTheory.LKRes.Model.sigHT_KHT p G.m G.n r G.Fw _ ih

end Iter

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → IsTest (sigG G r) (KHT p G.m G.n r G.Fw) K φ → ∃ k : ℕ, ∀ (γ : Gp G) (δ z y : Gr G r), IsNrm G r γ δ z → φ (y⁻¹ * δ * sigG G r y) ≠ 0 → ‖((γ.1 : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ ‖((γ.1⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ ≤ (p : ℝ) ^ k ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), (((γ.2 w : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) ∧ (∀ (w : Fin G.m) (μ : PadicAlgCl p), ((((γ.2 w)⁻¹ : GL (Fin G.n) (G.Fw w)) : Matrix (Fin G.n) (Fin G.n) (G.Fw w)).charpoly.map (algebraMap (G.Fw w) (PadicAlgCl p))).IsRoot μ → ‖μ‖ ≤ (p : ℝ) ^ k) := by
  intro p _ G r K φ hr hT
  obtain ⟨-, -, -, S, hS⟩ := hT
  choose cf hcf using fun g : Gr G r => GB.exists G r g
  let B : ℝ := 1 + ∑ s ∈ S, ∑ i ∈ Finset.range r,
    (cf ((⇑(sigG G r))^[i] s) + cf ((⇑(sigG G r))^[i] s⁻¹))
  have hsum : ∀ s ∈ S, ∀ i ∈ Finset.range r,
      cf ((⇑(sigG G r))^[i] s) + cf ((⇑(sigG G r))^[i] s⁻¹) ≤ B - 1 := by
    intro s hs i hi
    have h0 : ∀ t ∈ S, ∀ j ∈ Finset.range r,
        0 ≤ cf ((⇑(sigG G r))^[j] t) + cf ((⇑(sigG G r))^[j] t⁻¹) := fun t _ j _ => by
      linarith [(hcf ((⇑(sigG G r))^[j] t)).1, (hcf ((⇑(sigG G r))^[j] t⁻¹)).1]
    have := (Finset.single_le_sum (f := fun j => cf ((⇑(sigG G r))^[j] s) + cf ((⇑(sigG G r))^[j] s⁻¹))
      (h0 s hs) hi).trans (Finset.single_le_sum
        (f := fun t => ∑ j ∈ Finset.range r, (cf ((⇑(sigG G r))^[j] t) + cf ((⇑(sigG G r))^[j] t⁻¹)))
        (fun t ht => Finset.sum_nonneg (h0 t ht)) hs)
    simp only [B]
    linarith
  have hB1 : 1 ≤ B := by
    have : 0 ≤ ∑ s ∈ S, ∑ i ∈ Finset.range r,
        (cf ((⇑(sigG G r))^[i] s) + cf ((⇑(sigG G r))^[i] s⁻¹)) :=
      Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ => by
        linarith [(hcf ((⇑(sigG G r))^[j] t)).1, (hcf ((⇑(sigG G r))^[j] t⁻¹)).1]
    simp only [B]
    linarith
  have hBs : ∀ s ∈ S, ∀ i ∈ Finset.range r, GB G r ((⇑(sigG G r))^[i] s) B ∧
      GB G r ((⇑(sigG G r))^[i] s⁻¹) B := by
    intro s hs i hi
    have h := hsum s hs i hi
    have h1 := (hcf ((⇑(sigG G r))^[i] s)).1
    have h2 := (hcf ((⇑(sigG G r))^[i] s⁻¹)).1
    exact ⟨(hcf _).2.mono G r (by linarith), (hcf _).2.mono G r (by linarith)⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B ^ r) hp1
  refine ⟨k, fun γ δ z y hN hφ => ?_⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hS _ hφ
  have hN' : nrmG (sigG G r) r (y⁻¹ * δ * sigG G r y) = (z * y)⁻¹ * inclG G r γ * (z * y) := by
    rw [(nrmG_twConj (sigG G r) r δ y).1, sig_iter_self G hr, hN]
    group
  have hc1 : inclG G r γ = (z * y) * nrmG (sigG G r) r (y⁻¹ * δ * sigG G r y) * (z * y)⁻¹ := by
    rw [hN']; group
  have hc2 : inclG G r γ⁻¹ = (z * y) * (nrmG (sigG G r) r (y⁻¹ * δ * sigG G r y))⁻¹ * (z * y)⁻¹ := by
    rw [map_inv, hc1]; group
  have hG1 : GB G r (nrmG (sigG G r) r (y⁻¹ * δ * sigG G r y)) (B ^ r) := by
    have h := GB.list_prod G r (List.map (fun i => (⇑(sigG G r))^[i] (y⁻¹ * δ * sigG G r y)) (List.range r))
      hB1 ?_
    · rw [List.length_map, List.length_range] at h; exact h
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' : i ∈ Finset.range r := Finset.mem_range.2 (List.mem_range.1 hi)
    rw [e, iter_hom_mul, iter_hom_mul]
    have := (((GB.of_mem G r (sig_iter_mem G r i hk₁)).mul G r (hBs s hs i hi').1 zero_le_one (by linarith)).mul
      G r (GB.of_mem G r (sig_iter_mem G r i hk₂)) (by linarith) zero_le_one)
    simpa using this
  have hG2 : GB G r (nrmG (sigG G r) r (y⁻¹ * δ * sigG G r y))⁻¹ (B ^ r) := by
    unfold nrmG
    rw [List.prod_inv_reverse]
    have h := GB.list_prod G r (List.map (fun x => x⁻¹)
      (List.map (fun i => (⇑(sigG G r))^[i] (y⁻¹ * δ * sigG G r y)) (List.range r))).reverse hB1 ?_
    · rw [List.length_reverse, List.length_map, List.length_map, List.length_range] at h; exact h
    intro x hx
    rw [List.mem_reverse, List.map_map] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' : i ∈ Finset.range r := Finset.mem_range.2 (List.mem_range.1 hi)
    simp only [Function.comp_apply]
    rw [← iter_hom_inv, e, _root_.mul_inv_rev, _root_.mul_inv_rev, iter_hom_mul, iter_hom_mul, ← mul_assoc]
    have := (((GB.of_mem G r (sig_iter_mem G r i (inv_mem hk₂))).mul G r (hBs s hs i hi').2 zero_le_one
      (by linarith)).mul G r (GB.of_mem G r (sig_iter_mem G r i (inv_mem hk₁))) (by linarith) zero_le_one)
    simpa using this
  have hBp : B ^ r ≤ (p : ℝ) ^ k := hk.le
  have hB0 : 0 ≤ B ^ r := by positivity
  obtain ⟨a1, a2⟩ := bound_of_conj G r γ _ _ hc1 hB0 hG1
  obtain ⟨b1, b2⟩ := bound_of_conj G r γ⁻¹ _ _ hc2 hB0 hG2
  exact ⟨a1.trans hBp, b1.trans hBp, fun w μ hμ => (a2 w μ hμ).trans hBp,
    fun w μ hμ => (b2 w μ hμ).trans hBp⟩

end GlobalTheory.AtPBd
