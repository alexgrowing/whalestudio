import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.FinDefs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

set_option maxHeartbeats 1000000

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {S : LevSys R} {G : Model l K → Prop}
  {D : Dat R} {c1K : ∀ {M : Model l K}, D.Ch M → HdR M.q 2 → Prop}

theorem ext_P (hS : S.Good) {x y : R.P} (h : ∀ m, (S.L m).toB x = (S.L m).toB y) : x = y := by
  obtain ⟨z, -, hz⟩ := hS.cpl (fun m => (S.L m).toB x) (fun m => hS.dB_toB m x)
  exact (hz x fun m => rfl).trans (hz y fun m => (h m).symm).symm

theorem exists_lim (hS : S.Good) (P : RhoSys S G D c1K) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) :
    ∃ k : (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.P), ∀ m x f, P.ρ a j m x f → ∀ φ, (S.L m).toB (k x φ) = f φ := by
  classical
  let f : ∀ m, (D.H a).N j → (Module.Dual K (HdR M.q j) →+ (S.L m).B) :=
    fun m x => (P.ex a hM j m x).choose
  have hf : ∀ m x, P.ρ a j m x (f m x) := fun m x => (P.ex a hM j m x).choose_spec
  have hcomp : ∀ m x φ, S.dB m (f (m + 1) x φ) = f m x φ := by
    intro m x φ
    have e := P.uniq a hM j m x _ _ (P.lev a hM j m x _ (hf (m + 1) x)) (hf m x)
    exact congrArg (fun g => g φ) e
  have hlim : ∀ x φ, ∃! z : R.P, ∀ m, (S.L m).toB z = f m x φ :=
    fun x φ => hS.cpl (fun m => f m x φ) (fun m => hcomp m x φ)
  let k0 : (D.H a).N j → Module.Dual K (HdR M.q j) → R.P := fun x φ => (hlim x φ).exists.choose
  have hk0 : ∀ x φ m, (S.L m).toB (k0 x φ) = f m x φ := fun x φ => (hlim x φ).exists.choose_spec
  have haddφ : ∀ x φ ψ, k0 x (φ + ψ) = k0 x φ + k0 x ψ := by
    intro x φ ψ
    apply ext_P hS
    intro m
    rw [map_add, hk0, hk0, hk0, map_add]
  have haddx : ∀ x y φ, k0 (x + y) φ = k0 x φ + k0 y φ := by
    intro x y φ
    apply ext_P hS
    intro m
    rw [map_add, hk0, hk0, hk0]
    have e := P.uniq a hM j m (x + y) _ _ (hf m (x + y)) (P.add a hM j m x y _ _ (hf m x) (hf m y))
    rw [e]
    rfl
  let kx : (D.H a).N j → (Module.Dual K (HdR M.q j) →+ R.P) := fun x => AddMonoidHom.mk' (k0 x) (haddφ x)
  let k : (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.P) :=
    AddMonoidHom.mk' kx (fun x y => AddMonoidHom.ext fun φ => haddx x y φ)
  refine ⟨k, fun m x g hg φ => ?_⟩
  show (S.L m).toB (k0 x φ) = g φ
  rw [hk0, P.uniq a hM j m x _ _ (hf m x) hg]

theorem kap_abs (hR : R.Facts) (hi : ∀ c, R.i c ∈ R.P) (hS : S.Good) (P : RhoSys S G D c1K) : Nonempty (KapA G D c1K) := by
  classical
  obtain ⟨kP, hkP⟩ : ∃ kP : ∀ {M : Model l K} (a : D.Ch M), G M → ∀ j : ℕ,
      (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.P),
      ∀ {M : Model l K} (a : D.Ch M) (hM : G M) (j m : ℕ) x f, P.ρ a j m x f →
        ∀ φ, (S.L m).toB (kP a hM j x φ) = f φ :=
    ⟨fun a hM j => (exists_lim hS P a hM j).choose,
      fun a hM j m x f hf φ => (exists_lim hS P a hM j).choose_spec m x f hf φ⟩
  let κ : ∀ {M : Model l K} (a : D.Ch M) (j : ℕ), (D.H a).N j →+ (Module.Dual K (HdR M.q j) →+ R.B) :=
    fun {M} a j => if hM : G M then (AddMonoidHom.compHom R.P.subtype.toAddMonoidHom).comp (kP a hM j) else 0
  have hκ : ∀ {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) x φ,
      κ a j x φ = ((kP a hM j x φ : R.P) : R.B) := by
    intro M a hM j x φ
    rw [show κ a j = (AddMonoidHom.compHom R.P.subtype.toAddMonoidHom).comp (kP a hM j) from dif_pos hM]
    rfl
  have hB : ∀ u v : R.P, (∀ m, (S.L m).toB u = (S.L m).toB v) → (u : R.B) = v :=
    fun u v h => congrArg Subtype.val (ext_P hS h)
  refine ⟨{ κ := κ, lin := ?_, lin' := ?_, act := ?_, nat := ?_, fil := ?_, cup := ?_, one := ?_, c1 := ?_ }⟩
  · intro M a hM j c x φ
    rw [hκ a hM, hκ a hM]
    refine hB (kP a hM j (c • x) φ) (⟨R.i c, hi c⟩ * kP a hM j x φ) fun m => ?_
    obtain ⟨f, hf⟩ := P.ex a hM j m x
    rw [hkP a hM j m _ _ (P.smul a hM j m c x f hf), map_mul, hkP a hM j m x f hf,
      (hS.lev m).ι_lam c ⟨R.i c, hi c⟩ rfl] <;> rfl
  · intro M a hM j kk x φ
    rw [hκ a hM, hκ a hM]
    refine hB (kP a hM j x (kk • φ)) (⟨R.o kk, hR.o_mem kk⟩ * kP a hM j x φ) fun m => ?_
    obtain ⟨f, hf⟩ := P.ex a hM j m x
    rw [hkP a hM j m x f hf, map_mul, hkP a hM j m x f hf, P.lin' a hM j m x f hf kk φ,
      (hS.lev m).toB_K kk ⟨R.o kk, hR.o_mem kk⟩ rfl]
  · intro M a hM j σ x φ
    rw [hκ a hM, hκ a hM]
    refine hB (kP a hM j ((D.H a).act j σ x) φ)
      ⟨R.σ σ (kP a hM j x φ), hR.σ_mem σ _ (kP a hM j x φ).2⟩ fun m => ?_
    obtain ⟨f, hf⟩ := P.ex a hM j m x
    rw [hkP a hM j m _ _ (P.act a hM j m σ x f hf),
      ← (hS.lev m).σB_toB σ (kP a hM j x φ) ⟨R.σ σ (kP a hM j x φ), hR.σ_mem σ _ (kP a hM j x φ).2⟩ rfl,
      hkP a hM j m x f hf] <;> rfl
  · intro M N u hu a b μ hM hN j x φ
    rw [hκ a hM, hκ b hN]
    refine hB _ _ fun m => ?_
    obtain ⟨f, hf⟩ := P.ex b hN j m x
    obtain ⟨f', hf'⟩ := P.ex a hM j m (D.pullH μ j x)
    rw [hkP a hM j m _ f' hf', hkP b hN j m x f hf]
    exact P.nat μ hM hN j m x f f' hf hf' φ
  · intro M a hM j n r x φ hfil hφ
    rw [hκ a hM]
    rcases lt_or_ge n r with hnr | hrn
    · refine ⟨R.tB ^ (r - n) * (kP a hM j x φ : R.B),
        R.P.mul_mem (R.P.pow_mem hR.t_mem _) (kP a hM j x φ).2, ?_⟩
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnr.le]
    · obtain ⟨f, hf⟩ := P.ex a hM j n x
      have hmem := P.fil a hM j n x f hf n r le_rfl hfil φ hφ
      rw [(hS.lev n).pdP_B (n - r) ⟨R.tB, hR.t_mem⟩ rfl, Ideal.mem_span_singleton'] at hmem
      obtain ⟨b0, hb0⟩ := hmem
      obtain ⟨y0, rfl⟩ := (hS.lev n).toB_surj b0
      have hz : (S.L n).toB (kP a hM j x φ - y0 * ⟨R.tB, hR.t_mem⟩ ^ (n - r)) = 0 := by
        rw [map_sub, map_mul, map_pow, hb0, hkP a hM j n x f hf, sub_self]
      obtain ⟨z, hz'⟩ := ((hS.lev n).toB_ker _).mp hz
      have hk : ((kP a hM j x φ : R.P) : R.B) - (y0 : R.B) * R.tB ^ (n - r) = R.tB ^ (n + 1) * z := hz'
      refine ⟨(y0 : R.B) + R.tB ^ (r + 1) * z,
        R.P.add_mem y0.2 (R.P.mul_mem (R.P.pow_mem hR.t_mem _) z.2), ?_⟩
      have e1 : R.tB ^ r * R.tB ^ (n - r) = R.tB ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' hrn]
      have e2 : R.tB ^ r * R.tB ^ (n + 1) = R.tB ^ n * R.tB ^ (r + 1) := by
        rw [← pow_add, ← pow_add, show r + (n + 1) = n + (r + 1) by omega]
      linear_combination R.tB ^ r * hk + (y0 : R.B) * e1 + (z : R.B) * e2
  · intro M a hM i j x y z hc e e' b b' φ
    simp only [hκ a hM]
    have key := hB (kP a hM (i + j) z φ)
      (∑ s, ∑ s', kP a hM i x (b.coord s) * kP a hM j y (b'.coord s') *
        ⟨R.o (φ (cupK M.q rfl (b s) (b' s'))), hR.o_mem _⟩) ?_
    · rw [key]
      push_cast
      rfl
    intro m
    obtain ⟨f, hf⟩ := P.ex a hM i m x
    obtain ⟨g, hg⟩ := P.ex a hM j m y
    obtain ⟨hh, hhh⟩ := P.ex a hM (i + j) m z
    rw [hkP a hM (i + j) m z hh hhh, P.cup a hM m x y z f g hh hf hg hhh hc b b' φ, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [map_mul, map_mul, hkP a hM i m x f hf, hkP a hM j m y g hg,
      (hS.lev m).toB_K (φ (cupK M.q rfl (b s) (b' s'))) ⟨_, hR.o_mem _⟩ rfl]
  · intro M a hM x hx φ
    rw [hκ a hM]
    refine hB (kP a hM 0 x φ) ⟨R.o (φ (oneK M.q)), hR.o_mem _⟩ fun m => ?_
    obtain ⟨f, hf⟩ := P.ex a hM 0 m x
    rw [hkP a hM 0 m x f hf, P.one a hM m x f hf hx φ, (hS.lev m).toB_K (φ (oneK M.q)) ⟨_, hR.o_mem _⟩ rfl]
  · intro M a hM x c hx hc φ
    rw [hκ a hM]
    refine hB (kP a hM 2 x φ) ⟨R.o (φ c), hR.o_mem _⟩ fun m => ?_
    obtain ⟨f, hf⟩ := P.ex a hM 2 m x
    rw [hkP a hM 2 m x f hf, P.c1 a hM m x f c hf hx hc φ, (hS.lev m).toB_K (φ c) ⟨_, hR.o_mem _⟩ rfl]

end CrystallineSemistableComparison.Pb.Kap
