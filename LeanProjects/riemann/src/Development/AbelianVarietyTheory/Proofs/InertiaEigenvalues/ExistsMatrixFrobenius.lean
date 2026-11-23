import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie.MatF

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.φD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (a : _root_.Formalism.BasicNotions.LetA O n)
    (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.γD_smulA (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) (g : W.Gam) (a : _root_.Formalism.BasicNotions.LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in

theorem _root_.GlobalTheory.WachTie.MatF.coord_unique (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (c d : Fin r → _root_.Formalism.BasicNotions.LetA O n)
    (h : ∑ m, c m • (b m : W.DD T) = ∑ m, d m • (b m : W.DD T)) : c = d := by
  have h' : ∑ m, c m • b m = ∑ m, d m • b m := Subtype.ext (by simpa [Submodule.coe_sum] using h)
  exact b.equivFun.symm.injective (by rw [b.equivFun_symm_apply, b.equivFun_symm_apply]; exact h')

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_coord (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (x : W.DD T) (hx : x ∈ W.N T) :
    ∃ c : Fin r → _root_.Formalism.BasicNotions.LetA O n, x = ∑ m, c m • (b m : W.DD T) := by
  refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_equivFun ⟨x, hx⟩)
  rw [Submodule.coe_sum] at h
  simpa only [Submodule.coe_smul] using h.symm

open PowerSeries in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) {l : ℕ} in
theorem _root_.GlobalTheory.WachTie.MatF.exists_matrix_frobenius (R : _root_.GlobalTheory.NB.Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}
    (b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) (hF : _root_.GlobalTheory.WachTie.FrTie W R j)
    (_hE : _root_.GlobalTheory.WachTie.EETie W R j jE)
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (hs : W.s = 1) (hu : IsUnit (W.DelF.card : O)) :
    ∃ (M : ℕ) (Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧),
      (∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧),
        Φ i * Ψ = R.E ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) ∧
      (∀ k, (fun _ => j R.E : _root_.Formalism.BasicNotions.LetA O n) ^ M • W.φD T (b k : W.DD T) =
        ∑ m, (fun i => j (Φ i m k) : _root_.Formalism.BasicNotions.LetA O n) • (b m : W.DD T)) := by
  classical
  obtain ⟨hj, hrange, -, -, -, -, -, u, hu'⟩ := hF
  set q : _root_.Formalism.BasicNotions.LetA O n := fun _ => W.q₀ with hq
  set e : _root_.Formalism.BasicNotions.LetA O n := fun _ => j R.E with he
  set w : _root_.Formalism.BasicNotions.LetA O n := fun _ => ((u⁻¹ : O⟦X⟧ˣ) : O⟦X⟧) with hw
  have hqe : e = w * q := by
    funext i
    simp only [he, hw, hq, Pi.mul_apply]
    rw [← hu', mul_left_comm, Units.inv_mul, mul_one]
  have hpow : ∀ k (x : W.DD T), ((_root_.Formalism.BasicNotions.letφ (n := n) W.φ₀ ^ (W.s - 1)) fun _ => W.q₀) ^ k • x = q ^ k • x := by
    intro k x
    rw [hs, Nat.sub_self, pow_zero]
    rfl
  have hinv : ∀ y : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ y = y) → j (Function.invFun j y) = y :=
    fun y hy => Function.invFun_eq ((hrange y).2 hy)
  have hγe : ∀ δ ∈ W.DelF, W.γA δ e = e := by
    intro δ hδ
    funext i
    exact (hrange _).1 ⟨_, rfl⟩ δ hδ
  have hbN : ∀ k, (b k : W.DD T) ∈ W.N T := fun k => (b k).2
  have hbΔ : ∀ k, ∀ δ ∈ W.DelF, W.γD T δ (b k) = b k := fun k => (hb k).2
  have hlift : ∀ (f : Fin r → ℕ) (k : Fin r) (x : W.DD T), q ^ f k • x ∈ W.N T →
      e ^ (∑ m, f m) • x ∈ W.N T := by
    intro f k x hx
    have h1 := (W.N T).smul_mem (w ^ (∑ m, f m) * q ^ (∑ m, f m - f k)) hx
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)),
      ← mul_pow, ← hqe] at h1
  choose nφ hnφ using fun k => W.N_φ T _ (hbN k)
  have hyN : ∀ k, e ^ (∑ m, nφ m) • W.φD T (b k) ∈ W.N T := fun k =>
    hlift nφ k _ (by rw [← hpow]; exact hnφ k)
  set M := ∑ m, nφ m with hM
  choose C hC using fun k => _root_.GlobalTheory.WachTie.MatF.exists_coord W T b _ (hyN k)
  have hCinv : ∀ k m, ∀ δ ∈ W.DelF, W.γA δ (C k m) = C k m := by
    intro k m δ hδ
    have h := congrArg (W.γD T δ) (hC k)
    rw [_root_.GlobalTheory.WachTie.MatF.γD_smulA, map_pow, hγe δ hδ, ← W.φγ_comm, hbΔ k δ hδ, hC k, map_sum] at h
    simp only [_root_.GlobalTheory.WachTie.MatF.γD_smulA, hbΔ _ δ hδ] at h
    exact congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h.symm) m

  choose kk hkk using fun m => W.N_φinv T _ (hbN m)
  have hspan : Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T) ≤
      Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (Set.range fun t => W.φD T (b t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := _root_.GlobalTheory.WachTie.MatF.exists_coord W T b y hy
    rw [map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [_root_.GlobalTheory.WachTie.MatF.φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hA : ∀ m, ∃ a : Fin r → _root_.Formalism.BasicNotions.LetA O n,
      ∑ t, a t • W.φD T (b t) = e ^ (∑ m', kk m') • (b m : W.DD T) := by
    intro m
    rw [← Submodule.mem_span_range_iff_exists_fun]
    apply hspan
    have h1 := (Submodule.span (_root_.Formalism.BasicNotions.LetA O n) (W.φD T '' W.N T)).smul_mem
      (w ^ (∑ m', kk m') * q ^ (∑ m', kk m' - kk m)) (hkk m)
    rw [hpow] at h1
    rwa [smul_smul, mul_assoc, ← pow_add,
      Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)),
      ← mul_pow, ← hqe] at h1
  choose a ha using hA
  set K := ∑ m', kk m' with hK
  set c := e ^ (M + K) with hc
  set P : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun m k => C k m with hP
  set A : Matrix (Fin r) (Fin r) (_root_.Formalism.BasicNotions.LetA O n) := Matrix.of fun t m => a m t with hAdef
  have hPA : P * A = c • 1 := by
    refine Matrix.ext fun m' m => ?_
    have h : ∑ m'', (∑ t, a m t * C t m'') • (b m'' : W.DD T) =
        ∑ m'', (Pi.single m c : Fin r → _root_.Formalism.BasicNotions.LetA O n) m'' • (b m'' : W.DD T) := by
      simp only [Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hc, pow_add, mul_smul, ← ha m, Finset.smul_sum]
      simp_rw [smul_comm (e ^ M) (a m _), hC, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2 := congrFun (_root_.GlobalTheory.WachTie.MatF.coord_unique W T b _ _ h) m'
    simp only [Matrix.mul_apply, hP, hAdef, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [Finset.sum_congr rfl fun t _ => mul_comm _ _, h2, Pi.single_apply]
    split_ifs <;> simp

  have hγP : ∀ δ ∈ W.DelF, P.map (W.γA δ) = P := by
    intro δ hδ
    refine Matrix.ext fun m k => ?_
    exact hCinv k m δ hδ
  have hγc : ∀ δ ∈ W.DelF, W.γA δ c = c := by
    intro δ hδ
    rw [hc, map_pow, hγe δ hδ]
  have hdet : P.det * A.det = c ^ r := by
    rw [← Matrix.det_mul, hPA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hγdetP : ∀ δ ∈ W.DelF, W.γA δ P.det = P.det := by
    intro δ hδ
    have h := RingHom.map_det (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact h
  have hγadj : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (P.adjugate x y) = P.adjugate x y := by
    intro δ hδ x y
    have h := RingHom.map_adjugate (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n) P
    rw [show (W.γA δ : _root_.Formalism.BasicNotions.LetA O n →+* _root_.Formalism.BasicNotions.LetA O n).mapMatrix P = P from hγP δ hδ] at h
    exact congrFun (congrFun h x) y
  set v := c ^ r * A.det with hv
  have hγv : ∀ δ ∈ W.DelF, W.γA δ v = v := by
    intro δ hδ
    have h1 : P.det * W.γA δ A.det = P.det * A.det := by
      rw [hdet, ← hγdetP δ hδ, ← map_mul, hdet, map_pow, hγc δ hδ]
    rw [hv, map_mul, map_pow, hγc δ hδ]
    calc c ^ r * W.γA δ A.det = A.det * (P.det * W.γA δ A.det) := by rw [← hdet]; ring
      _ = c ^ r * A.det := by rw [h1, ← hdet]; ring
  set Ψf := v • P.adjugate with hΨf
  have hPΨ : P * Ψf = c ^ (r + r) • 1 := by
    rw [hΨf, Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, pow_add, hv, ← hdet]
    congr 1
    ring
  have hγΨ : ∀ δ ∈ W.DelF, ∀ x y, W.γA δ (Ψf x y) = Ψf x y := by
    intro δ hδ x y
    rw [hΨf, Matrix.smul_apply, smul_eq_mul, map_mul, hγv δ hδ, hγadj δ hδ]
  have hjP : ∀ i m k, j (Function.invFun j (P m k i)) = P m k i := fun i m k =>
    hinv _ fun δ hδ => congrFun (hCinv k m δ hδ) i
  have hjΨ : ∀ i x y, j (Function.invFun j (Ψf x y i)) = Ψf x y i := fun i x y =>
    hinv _ fun δ hδ => congrFun (hγΨ δ hδ x y) i
  refine ⟨M, fun i => Matrix.of fun m k => Function.invFun j (P m k i), fun i =>
    ⟨(M + K) * (r + r), Matrix.of fun x y => Function.invFun j (Ψf x y i), ?_⟩, fun k => ?_⟩
  · refine Matrix.ext fun x y => ?_
    apply hj
    have h := congrFun (congrFun (congrFun hPΨ x) y) i
    simp only [Matrix.mul_apply, Finset.sum_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Pi.mul_apply] at h
    simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, hjP, hjΨ, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    rw [h]
    split_ifs <;> simp [hc, he, pow_mul]
  · rw [hC k]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    funext i
    exact (hjP i m k).symm

end GlobalTheory.WachTie.MatF
