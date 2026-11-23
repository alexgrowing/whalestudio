import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisLaw

open GlobalTheory.BesselCompare GlobalTheory.RootExch GlobalTheory.BesselClosed

variable {D : D7} {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem rat_decomp (d : FJDat L A B ι) (v : B.V) :
    ∃ (c : Fin d.ρ → D.host.E) (a : A.V) (c' : Fin d.ρ → D.host.E), v = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := by
  let Φ : ((Fin d.ρ → D.host.E) × A.V × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
    (Fintype.linearCombination D.host.E d.e).coprod (ι.coprod (Fintype.linearCombination D.host.E d.f))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := fun c a c' => by
    simp [Φ, Fintype.linearCombination_apply, add_assoc]
  have sw : ∀ x y : B.V, B.hT y x = star (B.hT x y) := fun x y => (B.herm.eq _ _).symm
  have ef : ∀ i l, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i l => d.ef l i
  have fe : ∀ i l, B.hT (d.e i) (d.f l) = if l = i then 1 else 0 := fun i l => by
    rw [sw, ef]; by_cases h : i = l
    · simp [h]
    · simp [h, Ne.symm h]
  have ee : ∀ i l, B.hT (d.e i) (d.e l) = 0 := fun i l => d.ee l i
  have ff : ∀ i l, B.hT (d.f i) (d.f l) = 0 := fun i l => d.ff l i
  have eA : ∀ i x, B.hT (d.e i) (ι x) = 0 := fun i x => hD_swap_zero (d.eA i x)
  have fA : ∀ i x, B.hT (d.f i) (ι x) = 0 := fun i x => hD_swap_zero (d.fA i x)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    rintro ⟨c, a, c'⟩ h
    rw [hΦ] at h
    have h1 : c = 0 := funext fun i => by simpa [map_sum, ef, ff, fA] using congrArg (B.hT (d.f i)) h
    have h2 : c' = 0 := funext fun i => by simpa [map_sum, fe, ee, eA] using congrArg (B.hT (d.e i)) h
    subst h1 h2
    have h3 : ι a = 0 := by simpa using h
    have h4 : a = 0 := A.nondeg.1 a fun y => by rw [← d.isom a y, h3]; simp
    rw [h4]; rfl
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  have hs : Function.Surjective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    have := d.codim
    simp only [Module.finrank_prod, Module.finrank_fin_fun, A.rank_eq, B.rank_eq]
    omega)).1 hinj
  obtain ⟨⟨c, a, c'⟩, h⟩ := hs v
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {ρ : ℕ} (c : Fin ρ → D.host.E) (e : Fin ρ → B.V) :
    vecA B (∑ l, c l • e l) = ∑ l, incA D (c l) • vecA B (e l) := by
  funext k; simp [vecA, map_sum]

theorem iA_eq (s : Fin A.rank → AE D) : iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq]
  conv_lhs => rw [← A.frame.sum_repr a]
  simp only [map_sum, map_smul]
  rw [vecA_sum]
  rfl

theorem eq_sum_frame (x : Fin B.rank → AE D) : x = ∑ k, x k • vecA B (B.frame k) := by
  funext j
  simp [vecA, Finsupp.single_apply, apply_ite (incA D)]

theorem ad_decomp (d : FJDat L A B ι) (x : Fin B.rank → AE D) :
    ∃ (c : Fin d.ρ → AE D) (a : Fin A.rank → AE D) (c' : Fin d.ρ → AE D),
      x = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := by
  let Φ : ((Fin d.ρ → AE D) × (Fin A.rank → AE D) × (Fin d.ρ → AE D)) →ₗ[AE D] (Fin B.rank → AE D) :=
    (Fintype.linearCombination (AE D) fun l => vecA B (d.e l)).coprod
      (((frameMat B A ι).map (incA D)).mulVecLin.coprod (Fintype.linearCombination (AE D) fun l => vecA B (d.f l)))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := fun c a c' => by
    simp only [Φ, LinearMap.coprod_apply, Fintype.linearCombination_apply, add_assoc, Matrix.mulVecLin_apply, iA]
  have hx : x ∈ LinearMap.range Φ := by
    rw [eq_sum_frame x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    obtain ⟨c, a, c', h⟩ := rat_decomp d (B.frame k)
    refine ⟨(fun l => incA D (c l), vecA A a, fun l => incA D (c' l)), ?_⟩
    rw [hΦ, h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota]
  obtain ⟨⟨c, a, c'⟩, h⟩ := hx
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

variable (d : FJDat L A B ι)

theorem mem_NS {n : GA D B} (hn : n ∈ d.N) : n ∈ NS B d.e := by
  rw [← closure_NS, SetLike.mem_coe, ← NFlag_eMat]; exact hn

theorem lower {n : GA D B} (hn : n ∈ d.N) {k : ℕ} {v} (hv : v ∈ spanLt B d.e (k + 1)) :
    (mt B n).mulVec v - v ∈ spanLt B d.e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  rcases lt_or_ge l.1 (k + 1) with hl | hl
  · exact Submodule.smul_mem _ _ (spanLt_mono (by omega) ((mem_NS_iff.1 (mem_NS d hn)).1 l))
  · rw [hc l hl, zero_smul]; exact zero_mem _

theorem lower_iA {n : GA D B} (hn : n ∈ d.N) (a) : (mt B n).mulVec (iA ι a) - iA ι a ∈ spanLt B d.e d.ρ := by
  rw [iA_eq, ← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ _ ((mem_NS_iff.1 (mem_NS d hn)).2 _ fun i => hD_swap_zero (d.eA i _))

theorem hA_zero_swap {x y : Fin B.rank → AE D} (h : hA B x y = 0) : hA B y x = 0 := by
  rw [← hA_herm, h, map_zero]

theorem hA_span_of {k : ℕ} {v y} (hv : v ∈ spanLt B d.e k) (h : ∀ l : Fin d.ρ, l.1 < k → hA B (vecA B (d.e l)) y = 0) :
    hA B v y = 0 := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [hA_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hA_smul]
  rcases lt_or_ge l.1 k with hl | hl
  · rw [h l hl, mul_zero]
  · rw [hc l hl, zero_mul]

theorem hA_span_iA {k : ℕ} {v} (hv : v ∈ spanLt B d.e k) (a) : hA B v (iA ι a) = 0 :=
  hA_span_of d hv fun l _ => hA_vec_iA (d.eA l) a

theorem hA_span_span {k k' : ℕ} {v w} (hv : v ∈ spanLt B d.e k) (hw : w ∈ spanLt B d.e k') : hA B v w = 0 :=
  hA_span_of d hv fun l _ => hA_zero_swap (hA_span_of d hw fun j _ => by rw [hA_vec, d.ee, map_zero])

theorem hD_e_fTop (l : Fin d.ρ) : B.hD (d.e l) d.fTop = if l.1 + 1 = d.ρ then 1 else 0 := by
  have ef : ∀ i, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i => d.ef l i
  unfold HSpace.hD
  rw [FJDat.fTop, map_sum, LinearMap.sum_apply, Finset.sum_eq_single l]
  · split_ifs
    · rw [ef, if_pos rfl]
    · rw [map_zero, LinearMap.zero_apply]
  · intro i _ hi
    split_ifs
    · rw [ef, if_neg hi.symm]
    · rw [map_zero, LinearMap.zero_apply]
  · exact fun hl => absurd (Finset.mem_univ l) hl

theorem hA_span_fTop {v} (hv : v ∈ spanLt B d.e (d.ρ - 1)) : hA B v (vecA B d.fTop) = 0 :=
  hA_span_of d hv fun l hl => by rw [hA_vec, hD_e_fTop, if_neg (by omega), map_zero]

theorem hA_fTop_iA (a) : hA B (vecA B d.fTop) (iA ι a) = 0 :=
  hA_vec_iA (fun x => d.hD_fTop _ fun l => d.fA l x) a

theorem hA_fTop_fTop : hA B (vecA B d.fTop) (vecA B d.fTop) = 0 := by
  rw [hA_vec, d.hD_fTop _ fun i => hD_swap_zero (d.hD_fTop _ fun j => d.ff j i), map_zero]

theorem vecA_fTop : vecA B d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : AE D) else 0) • vecA B (d.f l) := by
  have : d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : D.host.E) else 0) • d.f l :=
    Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
  rw [this, vecA_sum]
  exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

theorem sum_mem_span (b : Fin d.ρ → AE D) : ∑ l, b l • vecA B (d.e l) ∈ spanLt B d.e d.ρ :=
  ⟨b, fun l hl => absurd l.2 (by omega), rfl⟩

theorem act_fTop {n : GA D B} (hn : n ∈ d.N) : ∃ b : Fin d.ρ → AE D,
    actV B n d.fTop = vecA B d.fTop + iA ι (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  obtain ⟨c, a, c', h⟩ := ad_decomp d (actV B n d.fTop)
  have fe : ∀ i j, B.hD (d.f i) (d.e j) = if i = j then 1 else 0 := fun i j => by
    have h1 : B.hD (d.f i) (d.e j) = star (B.hD (d.e j) (d.f i)) := (B.herm.eq _ _).symm
    rw [h1, d.ef]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : ∀ j : Fin d.ρ, c' j = if j.1 + 1 = d.ρ then 1 else 0 := fun j => by
    have h1 : hA B (actV B n d.fTop) (vecA B (d.e j)) = c' j := by
      rw [h, hA_add, hA_add, hA_coeff B d.f d.e fe, hA_zero_swap (hA_vec_iA (d.eA j) a),
        hA_span_span d (sum_mem_span d c) (vec_mem_spanLt j.2), zero_add, zero_add]
    have h2 := hA_span_fTop d (spanLt_mono (by have := j.2; omega)
      (lower d (inv_mem hn) (vec_mem_spanLt (B := B) (e := d.e) (l := j) (Nat.lt_succ_self _))))
    rw [hA_sub, sub_eq_zero, hA_vec, hD_e_fTop] at h2
    rw [← h1, actV, hA_mt_left, ← hA_herm, h2]
    split_ifs <;> simp
  have h' : actV B n d.fTop = vecA B d.fTop + iA ι a + ∑ l, c l • vecA B (d.e l) := by
    rw [h, vecA_fTop]; simp only [hc]; abel
  exact ⟨c, by rw [(d.coords_of n a c h').1]; exact h'⟩

theorem span_pred {n : GA D B} (hn : n ∈ d.N) {v} (hv : v ∈ spanLt B d.e d.ρ) :
    (mt B n).mulVec v - v ∈ spanLt B d.e (d.ρ - 1) :=
  lower d hn (spanLt_mono (by omega) hv)

theorem aCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) : d.aCo (n * n') = d.aCo n + d.aCo n' := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  obtain ⟨c, -, hc⟩ := add_mem (add_mem (sum_mem_span d b) (lower_iA d hn (d.aCo n')))
    (add_mem (spanLt_mono (Nat.sub_le _ _) (span_pred d hn (sum_mem_span d b'))) (sum_mem_span d b'))
  refine (d.coords_of _ _ c ?_).1
  change _ = _ + iA ι _ + _
  unfold actV at h h' ⊢
  rw [mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, h, ← hc, iA_add]
  abel

theorem tCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) :
    d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  have hs := lower_iA d hn (d.aCo n')
  have h1 := hA_span_fTop d (span_pred d hn (sum_mem_span d b'))
  rw [hA_sub, sub_eq_zero] at h1
  have h2 : d.tCo n' = hA B (∑ l, b' l • vecA B (d.e l)) (vecA B d.fTop) := by
    rw [FJDat.tCo, h', hA_add, hA_add, hA_fTop_fTop, hA_zero_swap (hA_fTop_iA d _), zero_add, zero_add]
  have h3 := hA_mt n (iA ι (d.aCo n')) (vecA B d.fTop)
  have h4 := hA_span_iA d hs (d.aCo n)
  have h5 := hA_span_span d hs (sum_mem_span d b)
  rw [hA_sub, sub_eq_zero] at h4 h5
  rw [hA_iA d.isom] at h4
  rw [hA_zero_swap (hA_span_iA d (sum_mem_span d b) _)] at h5
  unfold actV at h
  rw [h, hA_add_right, hA_add_right, h4, h5, hA_zero_swap (hA_fTop_iA d _)] at h3
  have h6 : d.tCo (n * n') = d.tCo n + hA B ((mt B n).mulVec (iA ι (d.aCo n'))) (vecA B d.fTop) + d.tCo n' := by
    unfold actV at h'
    rw [h2, ← h1, FJDat.tCo, FJDat.tCo, actV, actV, mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, hA_add, hA_add]
  linear_combination h6 + h3

theorem simple_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (i j : Fin d.ρ) (hij : j.1 = i.1 + 1) :
    hA B (actV B (n * n') (d.e j)) (vecA B (d.f i)) =
      hA B (actV B n (d.e j)) (vecA B (d.f i)) + hA B (actV B n' (d.e j)) (vecA B (d.f i)) := by
  have h1 := (mem_NS_iff.1 (mem_NS d hn')).1 j
  rw [hij] at h1
  have h2 := ((mem_spanLt_iff d.ef).1 (lower d hn h1)).1 i le_rfl
  rw [hA_sub, hA_sub, hA_vec, d.ef, if_neg (fun e => by subst e; omega), map_zero, Matrix.mulVec_sub, hA_sub] at h2
  unfold actV at h2 ⊢
  rw [mulVec_mul]
  linear_combination h2

theorem chr_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (ψ : AddChar (AF D.host.F) ℂ) :
    d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n' := by
  unfold FJDat.chr
  rw [← AddChar.map_add_eq_mul, ← map_add, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [simple_mul d hn hn' _ _ rfl, mul_add]

theorem law : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N,
    d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧
    (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧
    ∃ b : Fin d.ρ → AE D, actV B n d.fTop =
      vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) :=
  fun _ _ _ _ _ d _ hn _ hn' => ⟨aCo_mul d hn hn', tCo_mul d hn hn', chr_mul d hn hn', act_fTop d hn⟩

end GlobalTheory.HeisLaw

end
