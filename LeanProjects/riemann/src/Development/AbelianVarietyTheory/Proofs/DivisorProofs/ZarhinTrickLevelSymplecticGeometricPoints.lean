import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInclusionCyclotomicAwayRingFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductLevelStructureEqMkPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinSymplecticTransferBijectiveModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinProductMkPointBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalZarhinBundleEqZetaPowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

theorem siegPre_lev_nsmul {S : Scheme.{0}} {h M : ℕ} {Bs : Type} [CommRing Bs] {ζ : Bs} {s : S ⟶ Sp Bs}
    (c : SiegPre h M ζ s) (n : ℕ) (b : Fin h ⊕ Fin h → ℤ) : c.lev (n • b) = c.lev b ^ n := by
  have h0 : c.lev 0 = 1 := by
    have := c.lev_add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [succ_nsmul, c.lev_add, ih, pow_succ]

theorem geom_levZ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : cycAway M →+* k) (z : kˣ), x ≫ t = spMap β → (z : k) = β (zetaAway M) → (∀ a, (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = 1 ↔ ∃ b, a = M • b)) ∧ (∀ g : Over.mk x ⟶ (GlobalTheory.ZarhinFam.Zob c.A B), g ^ M = 1 → ∃ a, toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a = g) ∧ ∀ a b, Out.WeilIs (GlobalTheory.ZarhinFam.Zob c.A B) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left) M (toUnit (Over.mk x) ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a) (toUnit _ ≫ (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) (unitOn (z ^ (2 * omegaStd a b))) := by
  intro h M d S t c B _ _ Q la mu hZ hh hM hMo hd hcop hdu hker κ hκ k _ _ x β z hx hz
  have hla : IsMonHom la := hZ.2.2.2.1
  have hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hml : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  set X : Over.mk x ⟶ 𝟙_ (Over S) := toUnit (Over.mk x) with hXdef
  have hpt : ∀ a, X ≫ levZ c.lev (incZ c.A B) (actZ c.A B d la mu) (oMat d) κ a =
      mkZ c.A B (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a)) (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) := by
    intro a
    rw [GlobalTheory.T.zarhinProductLevelStructure_eq_mkPoint c.A B d h (8 * h) la mu c.lev κ a]
    exact (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B X _ _ 1 1).1
  have geo := c.geom k x β z hx hz
  have geo1 : ∀ q, X ≫ c.lev q = 1 ↔ ∃ b, q = M • b := geo.1
  have htA := GlobalTheory.T.isogeny_bijective_on_torsion_coprime_degree c.A B la mu d M (Over.mk x) hla hmu hlm hml hcop
  have hK := GlobalTheory.T.zarhinSymplecticTransfer_bijective_mod h M d κ (by omega) hκ
  have htor : ∀ q, (X ≫ c.lev q) ^ M = 1 := fun q => by rw [← comp_pow, c.lev_tors, comp_one]
  have hlev1 : ∀ q, (X ≫ c.lev q ≫ la = 1 ↔ X ≫ c.lev q = 1) := fun q => by
    constructor
    · intro e
      exact htA.1 _ (htor q) (by rw [Category.assoc]; exact e)
    · intro e
      rw [← Category.assoc, e, one_comp]
  have hlevM : ∀ q b, c.lev (q + M • b) = c.lev q := fun q b => by
    rw [c.lev_add, siegPre_lev_nsmul, c.lev_tors, _root_.mul_one]
  refine ⟨fun a => ?_, fun g hg => ?_, fun a b => ?_⟩
  ·
    rw [hpt a, (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => X ≫ c.lev (κ (Fin.castAdd 4 i) a))
      (fun j => X ≫ c.lev (κ (Fin.natAdd 4 j) a) ≫ la) 1 1).2.2.1, ← (hK.1 a)]
    simp only [hlev1, geo1]
    exact (Fin.forall_fin_add (m := 4) (n := 4) (fun k : Fin 8 => ∃ b, κ k a = M • b)).symm
  ·
    obtain ⟨-, hpow, hone, hg'⟩ := GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => g ≫ pa c.A B i) (fun j => g ≫ pb c.A B j) g M
    have hgM : mkZ c.A B (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) = 1 := by
      rw [← hpow, ← hg', hg]
    obtain ⟨hu, hv⟩ := (GlobalTheory.T.zarhinProductMkPoint_basic_facts c.A B (𝟙 _) (fun i => (g ≫ pa c.A B i) ^ M) (fun j => (g ≫ pb c.A B j) ^ M) g M).2.2.1.1 hgM
    have eu : ∀ i, ∃ q, X ≫ c.lev q = g ≫ pa c.A B i := fun i => geo.2.1 _ (hu i)
    have ev : ∀ j, ∃ q, X ≫ c.lev q ≫ la = g ≫ pb c.A B j := fun j => by
      obtain ⟨y, hyM, hy⟩ := htA.2 _ (hv j)
      obtain ⟨q, hq⟩ := geo.2.1 y hyM
      exact ⟨q, by rw [← Category.assoc, hq, hy]⟩
    choose qa hqa using eu
    choose qb hqb using ev
    let cc : Fin 8 → (Fin h ⊕ Fin h → ℤ) := fun k =>
      Fin.addCases (m := 4) (n := 4) (motive := fun _ => Fin h ⊕ Fin h → ℤ) qa qb k
    obtain ⟨a, ha⟩ := hK.2 cc
    refine ⟨a, ?_⟩
    rw [hpt a, hg']
    congr 1
    · funext i
      obtain ⟨b, hb⟩ := ha (Fin.castAdd 4 i)
      rw [hb, hlevM]
      exact (congrArg (X ≫ c.lev ·) (Fin.addCases_left (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) i)).trans (hqa i)
    · funext j
      obtain ⟨b, hb⟩ := ha (Fin.natAdd 4 j)
      rw [hb, hlevM]
      exact (congrArg (fun q => X ≫ c.lev q ≫ la) (Fin.addCases_right (motive := fun _ => Fin h ⊕ Fin h → ℤ) (left := qa) (right := qb) j)).trans (hqb j)
  ·
    rw [hpt a, hpt b]
    have W := GlobalTheory.T.weilPairing_diagonal_zarhinBundle_eq_zeta_pow h M d S t c B Q la mu hZ hh hM hMo hd hcop hdu hker k x β z hx hz
      (fun k => κ k a) (fun k => κ k b)
    have hzM : z ^ M = 1 := by
      ext
      rw [Units.val_pow_eq_pow_val, hz, ← map_pow, zetaAway_pow_self (by omega : M ≠ 0), map_one, Units.val_one]
    obtain ⟨m, hm⟩ := (hκ.1 a b).symm.dvd
    have e : z ^ (2 * formZ d h (fun k => κ k a) (fun k => κ k b)) = z ^ (2 * omegaStd a b) := by
      have : 2 * formZ d h (fun k => κ k a) (fun k => κ k b) = 2 * omegaStd a b + (M : ℤ) * (2 * m) := by
        linear_combination 2 * hm
      rw [this, zpow_add, zpow_mul z (M : ℤ), zpow_natCast, hzM, one_zpow, _root_.mul_one]
    rw [e] at W
    exact W

end GlobalTheory.ZarhinFam
