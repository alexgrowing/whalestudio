import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem extend_step {R : Type} [CommRing R] (K : DCx.{w} R) (n b : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n)
    (h0 : ∀ p r, p < b → K.D x p r = 0)
    (hB : ∀ q, b + q = n + 1 → K.D x b q ∈ (K.col b).B q) :
    ∃ x' : ∀ p q, K.X p q, x' ∈ K.T n ∧ (∀ p r, p < b → x' p r = x p r) ∧
      ∀ p r, p < b + 1 → K.D x' p r = 0 := by
  have hD : K.D x ∈ K.T (n + 1) := K.D_mem n x hx
  by_cases hbn : b ≤ n
  · obtain ⟨r, rfl⟩ : ∃ r, n = b + r := ⟨n - b, by omega⟩
    obtain ⟨y, hy⟩ := CrystallineSemistableComparison.Cx.mem_B_succ.mp (hB (r + 1) (by omega))
    have hy' : K.dv b r y = K.D x b (r + 1) := hy
    refine ⟨x - K.sgl b r (((-1 : ℤ) ^ b) • y), sub_mem hx ?_, ?_, ?_⟩
    · intro p q hpq
      exact K.sgl_ne _ (by omega)
    · intro p r' hp
      simp only [Pi.sub_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
    · intro p r' hp
      simp only [map_sub, CrystallineSemistableComparison.DCx.D_sgl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), zero_add]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · rw [h0 p r' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
      · by_cases hr : r' = r + 1
        · subst hr
          rw [K.sgl_self, map_zsmul, hy', smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, sub_self]
        · have h1 : K.D x p r' = 0 := hD p r' (by omega)
          rw [h1, K.sgl_ne _ (Or.inr hr), smul_zero, sub_zero]
  · refine ⟨x, hx, fun _ _ _ => rfl, ?_⟩
    intro p r hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact h0 p r hp
    · by_cases hr : p + r = n + 1
      · obtain rfl : r = 0 := by omega
        exact CrystallineSemistableComparison.Cx.mem_B_zero.mp (hB 0 hr)
      · exact hD p r hr

theorem leadE_surjective {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hac : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    Function.Surjective (leadE K j a (n := a + j)) := by
  intro t
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (colH K a) j).1 t
  obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K.col j) a).1 c
  have hcls : ∀ (C : CrystallineSemistableComparison.Cx R) (m : ℕ) (u v : C.X m) (hu : C.d m u = 0) (hv : C.d m v = 0),
      u = v → C.cls u hu = C.cls v hv := by
    rintro C m u v hu hv rfl
    rfl
  have hy' : K.dv j a y = 0 := hy
  have hdh : K.dh j a y ∈ (K.col (j + 1)).B a := by
    have hb : (K.col (j + 1)).d a ((colMap K j).f a y) = 0 := by
      show K.dv (j + 1) a (K.dh j a y) = 0
      rw [← K.hv j a y, hy', map_zero]
    have h1 : (colMap K j).mapH a ((K.col j).cls y hy) = 0 := hc
    rw [CrystallineSemistableComparison.P.mapH_cls (colMap K j) a y hy hb] at h1
    exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 1)) a).2.1 _ hb).mp h1
  have hmemT : ∀ (m : ℕ) (u : ∀ p q, K.X p q), u ∈ K.T m ↔ ∀ p q, p + q ≠ m → u p q = 0 :=
    fun _ _ => Iff.rfl
  have hx0 : K.sgl j a y ∈ K.T (a + j) := (hmemT _ _).2 fun p q hpq => K.sgl_ne y (by omega)
  have hDx0 : ∀ p r, p < j + 1 → K.D (K.sgl j a y) p r = 0 := by
    intro p r hp
    rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_ne _ (Or.inl (by omega))]
  have hstep : ∀ k : ℕ, ∃ x ∈ K.T (a + j), (∀ p r, p < j + 1 → x p r = K.sgl j a y p r) ∧
      ∀ p r, p < j + 2 + k → K.D x p r = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨x', hx', hag, hD'⟩ := extend_step K (a + j) (j + 1) (K.sgl j a y) hx0 hDx0 (by
        intro q hq
        obtain rfl : q = a := by omega
        rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_self]
        exact hdh)
      exact ⟨x', hx', hag, fun p r hp => hD' p r (by omega)⟩
    | succ k ih =>
      obtain ⟨x, hx, hag, hD⟩ := ih
      obtain ⟨x', hx', hag', hD'⟩ := extend_step K (a + j) (j + 2 + k) x hx hD (by
        intro q hq
        have hqa : q < a := by omega
        have hdv : (K.col (j + 2 + k)).d q (K.D x (j + 2 + k) q) = 0 :=
          dv_lead K (K.D x) (K.DD x) (j + 2 + k) q hD
        have := hac (j + 2 + k) q hqa
        exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 2 + k)) q).2.1 _ hdv).mp (Subsingleton.elim _ _))
      exact ⟨x', hx', fun p r hp => (hag' p r (by omega)).trans (hag p r hp),
        fun p r hp => hD' p r (by omega)⟩
  obtain ⟨x, hx, hag, hD⟩ := hstep a
  have hD0 : K.D x = 0 := by
    funext p r
    by_cases hp : p < j + 2 + a
    · exact hD p r hp
    · exact (hmemT _ _).1 (K.D_mem _ x hx) p r (by omega)
  have hZ : (⟨x, hx⟩ : K.T (a + j)) ∈ K.tot.Z (a + j) := LinearMap.mem_ker.2 (Subtype.ext hD0)
  have hxy : x j a = y := (hag j a (by omega)).trans (K.sgl_self j a y)
  have hzf : (⟨⟨x, hx⟩, hZ⟩ : K.tot.Z (a + j)) ∈ Zf K (a + j) j := by
    intro p q hp
    exact (hag p q (by omega)).trans (K.sgl_ne y (Or.inl (by omega)))
  refine ⟨⟨⟨⟨x, hx⟩, hZ⟩, hzf⟩, ?_⟩
  rw [leadE_eq]
  apply hcls
  rw [leadC_eq K j a _ (by show (K.col j).d a (x j a) = 0; rw [hxy]; exact hy)]
  exact hcls _ _ _ _ _ _ hxy

end GlobalTheory.CompanionTheory.CechSerre
