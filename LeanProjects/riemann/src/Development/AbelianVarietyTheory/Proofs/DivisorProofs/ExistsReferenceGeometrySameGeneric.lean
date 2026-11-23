import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRootsUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIsLevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSliceTrivialOfWeilPairingOneTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPairingEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimePowerRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEvaluationHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.PadicTate

theorem exists_padic_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z)))) := by
  intro p _ D R _ b N hN3 hN S s o k _ _ _ x β hβ
  have hp : p.Prime := Fact.out
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hB : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have ub := GlobalTheory.Ex.Specialise.unitOn_bijective (R := k)
  let Q := Over.mk x ⟶ o.A
  let act : D.O → Q → Q := fun c g => g ≫ o.act.act c
  let E : ℕ → Q → Q → kˣ → Prop := fun n g g' z =>
    Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)
  have amul : ∀ c a b, act c (a * b) = act c a * act c b := fun c a b => by
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have apow : ∀ c (a : Q) n, a ^ n = 1 → act c a ^ n = 1 := fun c a n h => by
    haveI := o.act.hom c
    show (a ≫ _) ^ n = 1
    rw [← MonObj.pow_comp, h, MonObj.one_comp]
  have powl : ∀ (n : ℕ) (a b : Q), (lift a b) ^ n = lift (a ^ n) (b ^ n) := by
    intro n a b
    ext <;> simp [MonObj.pow_comp]
  have ex : ∀ (n : ℕ) (a b : Q), ∃ c : kˣ, 0 < n → a ^ n = 1 → b ^ n = 1 →
      Out.WeilIs (G2 o.A) o.P n (lift a 1) (lift 1 b) (unitOn c) := fun n a b => by
    by_cases h : 0 < n ∧ a ^ n = 1 ∧ b ^ n = 1
    · obtain ⟨c, -, hc⟩ := GlobalTheory.ProdPairing.exists_weilIs_prod_root S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample n h.1 _
        (lift a 1) (lift 1 b) (by rw [powl, h.2.1, one_pow]; ext <;> simp) (by rw [powl, h.2.2, one_pow]; ext <;> simp)
      obtain ⟨c, rfl⟩ := ub.2 c
      exact ⟨c, fun _ _ _ => hc⟩
    · exact ⟨1, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ h⟩
  choose W hW using ex
  have uq : ∀ {n : ℤ} {X Y : Over.mk x ⟶ G2 o.A} {c c' : kˣ}, Out.WeilIs (G2 o.A) o.P n X Y (unitOn c) →
      Out.WeilIs (G2 o.A) o.P n X Y (unitOn c') → c = c' := fun h h' =>
    ub.1 (CommutatorPairing.weilIs_unique hG hB o.isLB h h')
  have upow : ∀ (c : kˣ) (m : ℕ), unitOn (c ^ m) = unitOn c ^ m := fun c m => map_pow _ _ _
  have umul : ∀ c c' : kˣ, unitOn (c * c') = unitOn c * unitOn c' := fun c m => map_mul _ _ _
  have uone : unitOn (1 : kˣ) = 1 := map_one _
  have hE : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → E n a b (W n a b ^ 2) := fun n hn a b ha hb => by
    have h := GlobalTheory.DiagSqAxes.weilIs_diag_sq S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm k x n hn
      (Nat.cast_ne_zero.2 hn.ne') a b ha hb _ (hW n a b hn ha hb)
    rw [← upow] at h
    exact h
  have lev : ∀ n m, 0 < n → 0 < m → ∀ a b : Q, a ^ (n * m) = 1 → b ^ (n * m) = 1 →
      W n (a ^ m) (b ^ m) = W (n * m) a b ^ m := fun n m hn hm a b ha hb => by
    have h := GlobalTheory.LevelChangePairing.weilIs_levelChange S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ k x n m hn hm
      (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne') a b ha hb _ (hW (n * m) a b (Nat.mul_pos hn hm) ha hb)
    rw [← upow] at h
    exact uq (hW n _ _ hn (by rw [← pow_mul, mul_comm, ha]) (by rw [← pow_mul, mul_comm, hb])) h
  have wmul : ∀ n, 0 < n → ∀ a a' b : Q, a ^ n = 1 → a' ^ n = 1 → b ^ n = 1 →
      W n (a * a') b = W n a b * W n a' b := fun n hn a a' b ha ha' hb => by
    have h := GlobalTheory.SiegelTypings.weilIs_mul hB o.isLB (hW n a b hn ha hb) (hW n a' b hn ha' hb)
    have e : lift a (1 : Q) * lift a' 1 = lift (a * a') 1 := by ext <;> simp [MonObj.mul_comp]
    rw [← umul, e] at h
    exact uq (hW n _ _ hn (by rw [mul_pow, ha, ha', _root_.mul_one]) hb) h
  have wskew : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → W n a b * W n b a = 1 := fun n hn a b ha hb => by
    have h := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm n _ a b _ _
      (CommPairing.weilIs_symm o.isLB (hW n b a hn hb ha)) (hW n a b hn ha hb)
    apply ub.1
    rw [umul, ← h, uone, inv_mul_cancel]
  have wadj : ∀ n, 0 < n → ∀ (c : D.O) (a b : Q), a ^ n = 1 → b ^ n = 1 →
      W n (act c a) b = W n a (act (D.star c).unop b) := fun n hn c a b ha hb =>
    ub.1 (GlobalTheory.AdjPairing.weilIs_adj_eq S o.A o.P o.ab o.isLB _ _ (o.act.hom c) (o.act.hom _) (o.rosati c) n _ a b _ _
      (hW n _ b hn (apow c a n ha) hb) (hW n a _ hn ha (apow _ b n hb)))
  have wnd : ∀ r, ∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W (p ^ r) a b = 1) → a = 1 := by
    intro r a ha h
    have hq : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨e, he, hk⟩ := o.kerP
    have h1 := hk _ a (GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ k x (p ^ r) (Nat.cast_ne_zero.2 hq.ne') a ha
      fun b hb => by
        have := hW _ a b hq ha hb
        rwa [h b hb, uone] at this)
    have h2 := pow_gcd_eq_one.2 ⟨h1, ha⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right r he), pow_one] at h2
  obtain ⟨ζ, hζ, hζ'⟩ := GlobalTheory.T.exists_compatible_prime_power_roots p k
  obtain ⟨ev, hev, hev'⟩ := GlobalTheory.T.exists_compatible_similitude_level_tower p D k Q act (fun r => W (p ^ r)) ζ amul hζ'
    (fun r a b ha hb => lev (p ^ r) p (pow_pos hp.pos r) hp.pos a b ha hb) fun r => by
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_level_evaluation_hom p D R b N hN3 hN S s o k x β hβ r
      have hq : 0 < p ^ r := pow_pos hp.pos r
      exact GlobalTheory.T.exists_level_pairing_eq_alt p D k Q act r (W (p ^ r)) (ζ r) (hζ r) (wmul _ hq) (wskew _ hq) (wadj _ hq) (wnd r) f hf
  refine ⟨ζ, ev, hζ, hζ', fun r => (hev r).1.1, fun r => (hev r).1.2.1, fun r => (hev r).1.2.2.1,
    fun r => (hev r).1.2.2.2, hev', fun r y z => ?_⟩
  have hq : 0 < p ^ r := pow_pos hp.pos r
  have h := hE _ hq (ev r y) (ev r z) (((hev r).1.2.2.2 _).2 ⟨y, rfl⟩) (((hev r).1.2.2.2 _).2 ⟨z, rfl⟩)
  have e := (hev r).2 y z
  rw [e, ← zpow_natCast, ← zpow_mul, mul_comm] at h
  simp only [E, Nat.cast_pow] at h
  exact h

end GlobalTheory.UPel.HT.PadicTate
