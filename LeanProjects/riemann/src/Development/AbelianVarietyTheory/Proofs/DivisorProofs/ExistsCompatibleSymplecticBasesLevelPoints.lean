import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCountableModel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationWeilPairingProperties
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WpQTrivRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientFreeRankTwiceDimensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingNondegenerateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprModTrivialQuotientPairingLevelPushEqPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SympQ.compatible_symplectic_bases : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ g : ℕ, g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → ∃ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) ∧ (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) ∧ (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) ∧ ∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F) := by
  intro R _ _ _ hR D F _ _ _ ζ hζ hζc g hg
  subst hg
  have hL : Laws := GlobalTheory.allSixLaws.1
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : GlobalTheory.Ex.BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam hL GlobalTheory.allSixLaws.2.1)
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.T.exists_integral_degeneration_values hL R D.toPre D.psi_even D.tau_bimult F ⊤ (fun _ => trivial)
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν
  have hcl : ∀ n (p p' : QkPt D.toPre F n) v v', ν.QPt p v → ν.QPt p' v' →
      (QkPt.Equiv D.toPre F p p' ↔ (QuotientGroup.mk v : GlobalTheory.SympQ.Qq N n) = QuotientGroup.mk v') :=
    fun n p p' v v' h h' => ((gQ n).2.2 p p' v v' h h').trans (GlobalTheory.SympQ.qEq_iff_mk_eq N v v')
  have h1 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n (x + y).toMul z.toMul = GlobalTheory.SympQ.wpQ N n x.toMul z.toMul * GlobalTheory.SympQ.wpQ N n y.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_left]
  have h2 : ∀ n (x y z : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul (y + z).toMul = GlobalTheory.SympQ.wpQ N n x.toMul y.toMul * GlobalTheory.SympQ.wpQ N n x.toMul z.toMul := by
    intro n x y z
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    obtain ⟨p'', hp''⟩ := QuotientGroup.mk_surjective (Additive.toMul z)
    simp only [toMul_add]
    rw [← hp, ← hp', ← hp'', ← QuotientGroup.mk_mul, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk,
      GlobalTheory.Ex.WpPairing.wp_mul_right]
  have h3 : ∀ n (x : Additive (GlobalTheory.SympQ.Qq N n)), GlobalTheory.SympQ.wpQ N n x.toMul x.toMul = 1 := by
    intro n x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← hp, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.Ex.NumD.wp_self]
  have h4 : ∀ n, 0 < n → ∀ x : Additive (GlobalTheory.SympQ.Qq N n), (∀ y : Additive (GlobalTheory.SympQ.Qq N n), GlobalTheory.SympQ.wpQ N n x.toMul y.toMul = 1) → x = 0 := by
    intro n hn x hx
    exact Additive.toMul.injective (GlobalTheory.T.reprModTrivialQuotient_pairing_nondegenerate R hR D F N ν n hn x.toMul fun y => hx (Additive.ofMul y))
  have h5 : ∀ n m, 0 < n → 0 < m → ∀ x y : Additive (GlobalTheory.SympQ.Qq N (n * m)), GlobalTheory.SympQ.wpQ N n ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive x).toMul ((GlobalTheory.SympQ.pushQ N (n * m) n).toAdditive y).toMul = GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m := by
    intro n m hn hm x y
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    obtain ⟨p', hp'⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
    change GlobalTheory.SympQ.wpQ N n (GlobalTheory.SympQ.pushQ N (n * m) n x.toMul) (GlobalTheory.SympQ.pushQ N (n * m) n y.toMul) =
      GlobalTheory.SympQ.wpQ N (n * m) x.toMul y.toMul ^ m
    rw [← hp, ← hp', GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.wpQ_mk, GlobalTheory.SympQ.wpQ_mk]
    exact GlobalTheory.T.reprModTrivialQuotient_pairing_levelPush_eq_pow R hR D F N ν n m hn hm p p'
  have h6 : ∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x : Additive (GlobalTheory.SympQ.Qq N M), (GlobalTheory.SympQ.pushQ N n k).toAdditive ((GlobalTheory.SympQ.pushQ N M n).toAdditive x) = (GlobalTheory.SympQ.pushQ N M k).toAdditive x := by
    intro M n k hk hM hkn hnM x
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    apply Additive.toMul.injective
    change GlobalTheory.SympQ.pushQ N n k (GlobalTheory.SympQ.pushQ N M n x.toMul) = GlobalTheory.SympQ.pushQ N M k x.toMul
    rw [← hp, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk, GlobalTheory.SympQ.pushQ_mk]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rw [GlobalTheory.SympQ.pushRep_fst N hkn, GlobalTheory.SympQ.pushRep_fst N hnM, GlobalTheory.SympQ.pushRep_fst N (hkn.trans hnM)]
    · have e : M / n * (n / k) = M / k := by
        obtain ⟨b, rfl⟩ := hkn
        obtain ⟨a, rfl⟩ := hnM
        have hb : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
        rw [Nat.mul_div_cancel_left _ (Nat.mul_pos hk hb), Nat.mul_div_cancel_left _ hk, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ hk, Nat.mul_comm]
      rw [GlobalTheory.SympQ.pushRep_snd N hkn, GlobalTheory.SympQ.pushRep_snd N hnM, GlobalTheory.SympQ.pushRep_snd N (hkn.trans hnM), ← pow_mul, e]
  obtain ⟨ev', hker, hsurj, htow, hweil⟩ := GlobalTheory.T.exists_compatible_symplectic_alt F ζ hζ hζc (D.toPre.P.g + Module.finrank ℤ D.toPre.X)
    (fun n => Additive (GlobalTheory.SympQ.Qq N n)) (fun n x y => GlobalTheory.SympQ.wpQ N n x.toMul y.toMul)
    (fun M n => (GlobalTheory.SympQ.pushQ N M n).toAdditive) (GlobalTheory.T.reprModTrivialQuotient_free_rank_twice_dimension R hR D F N ν) h1 h2 h3 h4 h5 h6
  have hrep : ∀ n a, ∃ q : N.QT n, (QuotientGroup.mk q : GlobalTheory.SympQ.Qq N n) = (ev' n a).toMul :=
    fun n a => QuotientGroup.mk_surjective _
  choose q hq using hrep
  choose P hP using fun n a => (gQ n).2.1 (q n a)
  refine ⟨P, fun n hn a b => ?_, fun n hn a b => ?_, fun n hn p => ?_, fun n m hn hm a => ?_, fun n hn a b => ?_⟩
  · obtain ⟨r, hr⟩ := (gQ n).2.1 (q n a * q n b)
    refine ⟨r, ?_, (gAdd _ _ _ _ _ _ (hP n a).2 (hP n b).2 hr.2).2 rfl, ?_⟩
    · rw [← hr.1, ← (hP n a).1, ← (hP n b).1, ← map_add]
      rfl
    · rw [hcl n _ _ _ _ hr (hP n (a + b)), QuotientGroup.mk_mul, hq, hq, hq, map_add, toMul_add]
  · rw [hcl n _ _ _ _ (hP n a) (hP n b), hq, hq, Additive.toMul.injective.eq_iff]
    exact hker n hn a b
  · obtain ⟨v, hv⟩ := ((gQ n).1 p).exists
    obtain ⟨a, ha⟩ := hsurj n hn (Additive.ofMul (QuotientGroup.mk v))
    exact ⟨a, (hcl n _ _ _ _ (hP n a) hv).2 (by rw [hq, ha]; rfl)⟩
  · have hd : n ∣ n * m := dvd_mul_right n m
    obtain ⟨r, hr⟩ := (gQ n).2.1 (GlobalTheory.SympQ.pushRep N (n * m) n (q (n * m) a))
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [← hr.1, ← (hP (n * m) a).1, GlobalTheory.SympQ.pushRep_fst N hd]
    · refine (GlobalTheory.Ex.GtValues.isNsmul_val ν m (hP (n * m) a).2 hr.2).2 ?_
      rw [GlobalTheory.SympQ.pushRep_snd N hd, Nat.mul_div_cancel_left m hn]
    · rw [hcl n _ _ _ _ hr (hP n a), ← GlobalTheory.SympQ.pushQ_mk, hq, hq, ← htow n m hn hm a]
      rfl
  · refine (hW n hn (P n a) (P n b) (q n a) (q n b) _ (hP n a) (hP n b)).2 ?_
    rw [← GlobalTheory.SympQ.wpQ_mk, hq, hq]
    exact congrArg Units.val (hweil n hn a b).symm
