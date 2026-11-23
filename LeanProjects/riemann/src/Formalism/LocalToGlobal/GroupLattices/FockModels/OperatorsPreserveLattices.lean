import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

def Wc {r n : ℕ} (c : Fin r) : Fin r × Fin n → ℤ := fun v => ((lgraded_wa (n := n) c v : ℕ) : ℤ)

theorem weight_wc {r n : ℕ} (c : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (Wc c) d = ((Finsupp.weight (rowW r n) d c : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Wc, lgraded_wa, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs with h1 h2 h2 <;> simp_all

theorem rowDiv_hom (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (k : ℕ) (μ : Fin r → ℕ)
    (y : MvPolynomial (Fin r × Fin n) R) (hy : IsWeightedHomogeneous (rowW r n) y μ) :
    ∃ μ', IsWeightedHomogeneous (rowW r n) (rowDiv R a b k y) μ' := by
  classical
  set δ : Fin r → ℤ := fun c => ((if a = c then 1 else 0 : ℕ) : ℤ) - ((if b = c then 1 else 0 : ℕ) : ℤ)
    with hδ
  have hc : ∀ c : Fin r, IsWeightedHomogeneous (Wc c) y (μ c : ℤ) := by
    intro c d hd
    rw [weight_wc, hy hd]
  have hs : ∀ c : Fin r, ∀ s : Fin n, Wc c (a, s) = Wc c (b, s) + δ c := by
    intro c s
    simp only [hδ, Wc, lgraded_wa]
    ring
  refine ⟨fun c => ((μ c : ℤ) + (k : ℤ) * δ c).toNat, ?_⟩
  intro d hd
  funext c
  have h1 := lehw_rowDiv_shift R (Wc c) (δ c) a b (hs c) (μ c) k y (hc c) hd
  rw [weight_wc] at h1
  omega

theorem applyWord_hom (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (wd : List (Fin r × Fin r × ℕ)) : ∃ μ, IsWeightedHomogeneous (rowW r n) (applyWord R wd (hw R hn ν)) μ := by
  have hwhom : ∃ μ0, IsWeightedHomogeneous (rowW r n) (hw R hn ν) μ0 :=
    ⟨_, IsWeightedHomogeneous.prod _ _ _ fun s _ => (lpMinor_rowHom R (s.val + 1) _ _).pow _⟩
  induction wd with
  | nil => exact hwhom
  | cons x wd ih =>
    obtain ⟨μ, hμ⟩ := ih
    exact rowDiv_hom R x.1 x.2.1 x.2.2 μ _ hμ

theorem dom_support (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ) (r : ℕ) :
    dualWeyl R k n ν ≤ restrictSupport R
      {m | (∑ a : Fin k with a.val < r, rowDeg m a) ≤ ∑ t : Fin n with t.val < r, ν t} := by
  obtain ⟨b, hb, h2⟩ := sSBasis R k n ν
  rw [← hb.2.1, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨-, -, K, sz, hsz, I, hshape, -, hbm⟩ := h2 i
  rw [SetLike.mem_coe, mem_restrictSupport_iff]
  intro m hm
  have h3 := (bidetDominance R k n K sz hsz I m (by rw [← hbm]; exact hm)).1 r
  rw [hshape] at h3
  exact h3

theorem hom_map {R S σ M : Type} [CommRing R] [CommRing S] [AddCommMonoid M] (φ : R →+* S) (wt : σ → M)
    (f : MvPolynomial σ R) (μ : M) (h : IsWeightedHomogeneous wt f μ) : IsWeightedHomogeneous wt (map φ f) μ := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [MvPolynomial.coeff_map, h0, map_zero]

theorem weyl_scale (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] (k r : ℕ) (ν : Fin k → ℕ)
    (hν : Antitone ν) (w : O) (hw0 : algebraMap O Kf w ≠ 0) :
    ∀ f ∈ weyl O k k le_rfl ν,
      (algebraMap O Kf w ^ (∑ t : Fin k with t.val < r, ν t)) •
          rowAct Kf (lb_D k r (algebraMap O Kf w)) (map (algebraMap O Kf) f) ∈
        Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν) := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set N : ℕ := ∑ t : Fin k with t.val < r, ν t with hN
  let T : MvPolynomial (Fin k × Fin k) O →ₗ[O] MvPolynomial (Fin k × Fin k) Kf :=
    ((LinearMap.lsmul Kf _ (c ^ N)).restrictScalars O) ∘ₗ
      ((rowAct Kf (n := k) (lb_D k r c)).toLinearMap.restrictScalars O) ∘ₗ
        (mapAlgHom (Algebra.ofId O Kf)).toLinearMap
  have hT : ∀ x, T x = c ^ N • rowAct Kf (lb_D k r c) (map (algebraMap O Kf) x) := fun x => rfl
  have key : weyl O k k le_rfl ν ≤
      (Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν)).comap T := by
    unfold weyl
    rw [Submodule.span_le]
    rintro _ ⟨wd, rfl⟩
    set f := applyWord O wd (hw O le_rfl ν) with hf
    have hfW : f ∈ weyl O k k le_rfl ν := Submodule.subset_span ⟨wd, rfl⟩
    show T f ∈ Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O k k le_rfl ν)
    by_cases h0 : f = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    obtain ⟨μ, hμ⟩ := applyWord_hom O le_rfl ν hν wd
    obtain ⟨d0, hd0⟩ := MvPolynomial.support_nonempty.mpr h0
    have hdom := ((mem_restrictSupport_iff O).1 (dom_support O k k ν r (weylLeDual O k k le_rfl ν hν hfW))) hd0
    have hwt : ∀ a, rowDeg d0 a = μ a := by
      intro a
      rw [← lehw_weight_rowW, hμ (mem_support_iff.mp hd0)]
    set π' : ℕ := ∑ a : Fin k with a.val < r, μ a with hπ
    have hle : π' ≤ N := by
      have h1 : (∑ a : Fin k with a.val < r, rowDeg d0 a) = π' := Finset.sum_congr rfl fun a _ => hwt a
      rw [← h1]
      exact hdom
    refine ⟨w ^ (N - π') • f, Submodule.smul_mem _ _ hfW, ?_⟩
    rw [hT]
    unfold lb_D
    rw [rowActDiagWeight Kf k k _ μ _ (hom_map _ _ _ _ hμ), smul_smul]
    have h2 : ∏ a : Fin k, (if a.val < r then c⁻¹ else 1) ^ μ a = (c⁻¹) ^ π' := by
      rw [hπ, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro a _
      split_ifs <;> simp
    rw [h2]
    have h4 : c ^ N * (c⁻¹) ^ π' = c ^ (N - π') := by
      rw [inv_pow, pow_sub₀ c hw0 hle]
    rw [h4]
    show map (algebraMap O Kf) (w ^ (N - π') • f) = _
    rw [smul_eq_C_mul, map_mul, map_C, map_pow, ← smul_eq_C_mul]
  exact fun f hf => key hf

theorem dl_P (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ deltaLTw O Kf m lam g) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) := by
  classical
  set c : Kf := algebraMap O Kf w with hc
  set e : ℤ := lam (Fin.last m) with he
  set A : ℤ := ∑ i : Fin (m + 1) with i.val < r, lam i with hA
  set N : ℕ := ∑ t : Fin (m + 1) with t.val < r, nuOf lam t with hN
  obtain ⟨F0, hF0, rfl⟩ := hF
  obtain ⟨f, hf, hfe⟩ := hF0
  have hfe' : map (algebraMap O Kf) f = rowAct Kf g F0 := hfe
  refine ⟨c ^ N • F0, ?_, ?_⟩
  · show rowAct Kf (g * lb_D (m + 1) r c) (c ^ N • F0) ∈
      Submodule.map (mapAlgHom (Algebra.ofId O Kf)).toLinearMap (weyl O (m + 1) (m + 1) le_rfl (nuOf lam))
    have h1 := rowActMul Kf (m + 1) (m + 1) (lb_D (m + 1) r c) g
    rw [← h1, map_smul, AlgHom.comp_apply, ← hfe']
    exact weyl_scale O Kf (m + 1) r (nuOf lam) (kp_nuOf_antitone lam hlam) w hw f hf
  · show (g * lb_D (m + 1) r c).det ^ (-e) • (c ^ N • F0) = c ^ A • (g.det ^ (-e) • F0)
    rw [smul_smul, smul_smul]
    congr 1
    set ρ : ℕ := (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card with hρ
    have h1 : (g * lb_D (m + 1) r c).det = g.det * (c⁻¹) ^ ρ := by
      rw [Matrix.det_mul, lb_D, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const_one, mul_one]
    have h3 : A = (N : ℤ) + ρ * e := by
      rw [hA, hN, hρ]
      push_cast
      rw [Finset.card_eq_sum_ones]
      push_cast
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have : 0 ≤ lam a - lam (Fin.last m) := sub_nonneg.2 (hlam (Fin.le_last a))
      simp only [nuOf, Int.toNat_of_nonneg this, he]
      ring
    have h5 : ((c⁻¹) ^ ρ) ^ (-e) = c ^ ((ρ : ℤ) * e) := by
      rw [inv_pow, inv_zpow, zpow_neg, inv_inv, ← zpow_natCast c ρ, ← zpow_mul]
    rw [h1, h3, mul_zpow, h5, zpow_add₀ hw, zpow_natCast]
    ring

theorem dl_indep {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g h : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) (heq : colSpan O g = colSpan O h) :
    deltaLTw O Kf m lam g ≤ deltaLTw O Kf m lam h := by
  obtain ⟨U, hU⟩ := la_factor g h heq.ge
  obtain ⟨U2, hU2⟩ := la_factor h g heq.le
  have hUU : U * U2 = 1 := by
    have h1 : g * (U * U2).map (algebraMap O Kf) = g * 1 := by
      rw [Matrix.mul_one, Matrix.map_mul, ← Matrix.mul_assoc, ← hU, ← hU2]
    have hgu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hg
    have h2 : (U * U2).map (algebraMap O Kf) = 1 := hgu.mul_left_cancel h1
    apply Matrix.map_injective hinj
    beta_reduce
    rw [h2]
    simp
  have hdet : U.det * U2.det = 1 := by rw [← Matrix.det_mul, hUU, Matrix.det_one]
  let u : Oˣ := ⟨U.det, U2.det, hdet, by rw [mul_comm]; exact hdet⟩
  let γ : GL (Fin (m + 1)) O := ⟨U2, U, mul_eq_one_comm.1 hUU, hUU⟩
  have hdU : (U.map (algebraMap O Kf)).det = algebraMap O Kf U.det := by
    rw [RingHom.map_det]; rfl
  have hc : algebraMap O Kf U.det ≠ 0 := by
    intro h0
    have := congrArg (algebraMap O Kf) hdet
    rw [map_mul, h0, zero_mul, map_one] at this
    exact zero_ne_one this
  have hz : ∀ e : ℤ, algebraMap O Kf ((u ^ e : Oˣ) : O) = (algebraMap O Kf U.det) ^ e := by
    intro e
    have h1 : ((Units.map (algebraMap O Kf : O →* Kf) u ^ e : Kfˣ) : Kf) = (algebraMap O Kf U.det) ^ e := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [← h1, ← map_zpow]
    rfl
  rintro _ ⟨F, hF, rfl⟩
  have hFh : F ∈ deltaL O Kf (m + 1) (nuOf lam) h := by
    obtain ⟨f, hf, hfe⟩ := hF
    have hst : rowAct O U f ∈ weyl O (m + 1) (m + 1) le_rfl (nuOf lam) :=
      Formalism.UG.P.weyl_module_GL_stable O (m + 1) (m + 1) le_rfl (nuOf lam) γ f hf
    refine ⟨rowAct O U f, hst, ?_⟩
    have h3 : rowAct Kf (n := m + 1) h = (rowAct Kf (U.map (algebraMap O Kf))).comp (rowAct Kf g) := by
      rw [rowActMul, hU]
    change map (algebraMap O Kf) (rowAct O U f) = rowAct Kf h F
    rw [h3, AlgHom.comp_apply, ← la_rowAct_map]
    congr 1
  refine ⟨((u ^ (lam (Fin.last m)) : Oˣ) : O) • F, Submodule.smul_mem _ _ hFh, ?_⟩
  change h.det ^ (-(lam (Fin.last m))) • (((u ^ (lam (Fin.last m)) : Oˣ) : O) • F) =
    g.det ^ (-(lam (Fin.last m))) • F
  rw [← algebraMap_smul Kf (((u ^ (lam (Fin.last m)) : Oˣ) : O)) F, hz, smul_smul, hU, Matrix.det_mul, hdU,
    mul_zpow, mul_assoc, ← zpow_add₀ hc, neg_add_cancel, zpow_zero, mul_one]

theorem dl_pos (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (w : O) (hw : algebraMap O Kf w ≠ 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det)
    (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (hF : F ∈ Dl0 O m lam (colSpan O g)) :
    (algebraMap O Kf w ^ (∑ i : Fin (m + 1) with i.val < r, lam i)) • F ∈
      Dl0 O m lam (colSpan O (g * lb_D (m + 1) r (algebraMap O Kf w))) := by
  have hgD : IsUnit (g * lb_D (m + 1) r (algebraMap O Kf w)).det := by
    rw [Matrix.det_mul]; exact hg.mul (lb_D_det _ _ _ hw)
  unfold Dl0 at hF ⊢
  rw [if_pos hlam] at hF ⊢
  have h1 : F ∈ deltaLTw O Kf m lam g := (iInf₂_le g ⟨hg, rfl⟩ : _ ≤ deltaLTw O Kf m lam g) hF
  have h2 := dl_P O Kf m r lam hlam w hw g F h1
  exact (le_iInf₂ fun h hh => dl_indep hinj m lam _ h hgD hh.2 :
    deltaLTw O Kf m lam (g * lb_D (m + 1) r (algebraMap O Kf w)) ≤ _) h2

variable {p : ℕ}

theorem steps_gen (G : GAtP p) (v : Fin G.P.nV)
    (Φ : (Fin (G.P.m + 1) → ℤ) → Submodule G.O (Fin (G.P.m + 1) → G.Kf) →
      Submodule G.O (MvPolynomial (Fin (G.P.m + 1) × Fin (G.P.m + 1)) G.Kf))
    (hΦ : ∀ (lam : Fin (G.P.m + 1) → ℤ), Antitone lam → ∀ g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) G.Kf,
      IsUnit g.det → ∀ F ∈ Φ lam (colSpan G.O g),
        (algebraMap G.O G.Kf G.P.w ^ (∑ i : Fin (G.P.m + 1) with i.val < G.P.r, lam i)) • F ∈
          Φ lam (colSpan G.O (g * lb_D (G.P.m + 1) G.P.r (algebraMap G.O G.Kf G.P.w))))
    (e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1)) (he : IsEdge p (G.P.n' v) G.P.r e) :
    ∀ P ∈ tensorLat G.O G.Kf (fun s : Fin (G.P.n' v) =>
        Φ (lamAt (G.P.lam0 v) s) (extO G.O (G.P.ι v) (G.P.σ v) s.val e.src)),
      ((p : G.Kf) ^ G.P.ArV v) • P ∈ tensorLat G.O G.Kf (fun s : Fin (G.P.n' v) =>
        Φ (lamAt (G.P.lam0 v) s) (extO G.O (G.P.ι v) (G.P.σ v) s.val e.tgt)) := by
  obtain ⟨gs, hgs, h1, -, h3⟩ := lb_edgeLat_of_basis G v (restEdgeBasis G v) e he
  have hw := ch_w_ne_zero G v
  set c : G.Kf := algebraMap G.O G.Kf G.P.w with hc
  have hgD : ∀ s, IsUnit (gs s * lb_D (G.P.m + 1) G.P.r c).det := by
    intro s
    rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hw)
  have hA : ∏ s : Fin (G.P.n' v), (c ^ (∑ i : Fin (G.P.m + 1) with i.val < G.P.r, lamAt (G.P.lam0 v) s i) *
      c ^ (∑ i : Fin (G.P.m + 1) with i.val < G.P.r, lamAt (G.P.lam0 v) s i)) = (p : G.Kf) ^ G.P.ArV v := by
    rw [Finset.prod_mul_distrib, lb_zpow_sum _ hw, nt_p_eq G v, ← hc]
    unfold Places.ArV Ar
    rw [← zpow_natCast c 2, ← zpow_mul, ← zpow_add₀ hw]
    congr 1
    ring
  intro P hP
  rw [← hA]
  refine lb_tensor G.O G.Kf _ _ _ (fun s F hF => ?_) P hP
  beta_reduce at hF ⊢
  rw [h1] at hF
  rw [h3, mul_smul]
  have hl := kp_lamAt_antitone _ (G.P.dom v) s
  exact hΦ _ hl _ (hgD _) _ (hΦ _ hl _ (hgs _) F hF)

theorem yv_pres (G : GAtP p) (v : Fin G.P.nV)
    (Φ : ∀ u, Submodule (G.P.W u) (Fin (G.P.m + 1) → G.P.Qq u) →
      Submodule G.O (MvPolynomial (Fin (G.P.n' u) × (Fin (G.P.m + 1) × Fin (G.P.m + 1))) G.Kf))
    (hloc : ∀ e : Edge (G.P.W v) (G.P.Qq v) (G.P.m + 1), IsEdge p (G.P.n' v) G.P.r e →
      ∀ z ∈ Φ v e.src, ((p : G.Kf) ^ G.P.ArV v) • z ∈ Φ v e.tgt) :
    ∀ x ∈ G.funMod (G.P.sys Φ), G.yv v x ∈ G.funMod (G.P.sys Φ) := by
  classical
  intro x hx
  unfold GAtP.funMod at hx ⊢
  rw [Submodule.mem_pi] at hx ⊢
  intro i hi
  have h0 := hx i hi
  unfold Level.funMod at h0 ⊢
  rw [Submodule.mem_inf, Submodule.mem_inf] at h0 ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := h0
  have hA' := fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hA L) hL
  have hB' : ∀ L : G.P.Tup, ¬ G.P.IsLatTup L → x i L = 0 :=
    fun L hL => (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hB L) hL
  have hne : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) (u : Fin G.P.nV),
      u ≠ v → Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' u = L u :=
    fun L L'' u hu => Function.update_of_ne hu L'' L
  have hself : ∀ (L : G.P.Tup) (L'' : Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)),
      Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'' v = L'' :=
    fun L L'' => Function.update_self v L'' L
  refine ⟨⟨?_, ?_⟩, nt_equiv G v i _ hC⟩
  · refine (Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_
    change Level.yv (P := G.P) v (x i) L ∈ G.P.sys Φ L
    rw [ef_yv_eq, Finset.smul_sum]
    refine Submodule.sum_mem _ fun L'' hL'' => ?_
    have hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩ :=
      (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''
    have hlat : G.P.IsLatTup
        (Function.update (β := fun v => Submodule (G.P.W v) (Fin (G.P.m + 1) → G.P.Qq v)) L v L'') := by
      intro u
      by_cases huv : u = v
      · subst huv
        rw [hself]
        exact hE.1
      · rw [hne L L'' u huv]
        exact hL u
    have hval := hA' _ hlat
    refine nt_tenV_smulK G v _ _ _ ?_ ?_ _ hval
    · intro z hz
      rw [hself] at hz
      exact hloc ⟨L'', L v⟩ hE z hz
    · intro u hu
      rw [hne L L'' u hu]
  · refine (Submodule.mem_iInf _).2 fun L => (Submodule.mem_iInf _).2 fun hL => ?_
    change Level.yv (P := G.P) v (x i) L = 0
    rw [ef_yv_eq, Finset.sum_eq_zero, smul_zero]
    intro L'' hL''
    have hE : IsEdge p (G.P.n' v) G.P.r ⟨L'', L v⟩ :=
      (Set.Finite.mem_toFinset (ef_places_finite G.P v (L v))).1 hL''
    apply hB'
    intro hlat
    apply hL
    intro u
    by_cases huv : u = v
    · subst huv
      exact hE.2.1
    · have := hlat u
      rw [hne L L'' u huv] at this
      exact this

theorem operators_preserve_lattices (D : Formalism.BasicNotions.D7) (G : GAtP p) : Formalism.MainNotions.FormalGroupSystem.adm12 D G := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · exact yv_pres G v (fun u Lu => Hten G.O (G.P.lam0 u) fun s => extO G.O (G.P.ι u) (G.P.σ u) s.val Lu)
      (fun e he => steps_gen G v (fun lam Λ => H0 G.O G.P.m lam Λ)
        (fun lam hl g hg F hF => lb_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r lam hl G.P.w (ch_w_ne_zero G v) g hg F hF)
        e he)
  · exact yv_pres G v (fun u Lu => HtenW G.O (G.P.lam0 u) fun s => extO G.O (G.P.ι u) (G.P.σ u) s.val Lu)
      (fun e he => steps_gen G v (fun lam Λ => Dl0 G.O G.P.m lam Λ)
        (fun lam hl g hg F hF => dl_pos G.O G.Kf (lb_inj G v) G.P.m G.P.r lam hl G.P.w (ch_w_ne_zero G v) g hg F hF)
        e he)

end Formalism.L2.G.Model
