import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinKer

open Matrix GlobalTheory.ZarhinFam

def kerN (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, single]⟩

def kerM (d : ℕ) : ord d :=
  ⟨single (Sum.inl 0) (Sum.inr 0) 1 * formInv d, fun i j => by simp [Matrix.mul_apply, single]⟩

theorem idem_mul_kerN (d : ℕ) : idem d * kerN d = polUnit d := by
  ext1
  simp only [Subring.coe_mul, idem, kerN, polUnit_coe]
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem kerM_mul_bar_kerN {d : ℕ} (hd : 0 < d) : kerM d * bar d (kerN d) = idem d := by
  ext1
  simp only [Subring.coe_mul, bar_coe, kerM, kerN, idem, Matrix.transpose_mul, transpose_single, form_transpose]
  calc single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * formInv d *
        (form d * (single (Sum.inr 0) (Sum.inl 0) 1 * form d) * formInv d)
      = single (Sum.inl 0) (Sum.inr 0) (1 : ℤ) * (formInv d * form d) * single (Sum.inr 0) (Sum.inl 0) 1 *
          (form d * formInv d) := by simp only [Matrix.mul_assoc]
    _ = single (Sum.inl 0) (Sum.inl 0) 1 := by
      rw [formInv_mul_form hd, form_mul_formInv hd, Matrix.mul_one, Matrix.mul_one, single_mul_single_same, _root_.one_mul]

end GlobalTheory.ZarhinKer

namespace GlobalTheory.ZarhinKer

open GlobalTheory.ZarhinFam

theorem polUnit_ker_le : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 → ∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen := by
  intro h M d hd S t c z act inc pr _hdu _hker _hprin hact hadj _hinc _hpr hip hpi hP T x hx
  have hinc_idem : inc ≫ act (idem d) = inc := by
    rw [← hpi, ← Category.assoc, hip, Category.id_comp]
  have hN : inc ≫ act (kerN d) = inc ≫ act (polUnit d) := by
    calc inc ≫ act (kerN d) = (inc ≫ act (idem d)) ≫ act (kerN d) := by rw [hinc_idem]
      _ = inc ≫ act (polUnit d) := by rw [Category.assoc, ← hact.2.2.1, idem_mul_kerN]
  have hM : inc ≫ act (kerM d) ≫ act (bar d (kerN d)) = inc := by
    rw [← hact.2.2.1, kerM_mul_bar_kerN hd, hinc_idem]
  have hv : (snd c.A T ≫ x ≫ inc) ≫ act (kerN d) = 1 := by
    rw [Category.assoc, Category.assoc, hN, hx, comp_one]
  have e1 : ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A ≫ act (kerN d)) (snd z.A z.A)).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, comp_one]
      rw [← hv]; simp only [Category.assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.comp_id]
  have e2 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc ≫ act (kerM d))).left ≫
        (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (kerN d)))).left := by
    rw [← Over.comp_left]
    congr 1
    ext1
    · simp only [Category.assoc, lift_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, hM]
  have e3 : (lift (snd c.A T ≫ x ≫ inc) (fst c.A T ≫ inc)).left =
      (lift (snd c.A T ≫ x) (fst c.A T)).left ≫ (inc ⊗ₘ inc).left := by
    rw [← Over.comp_left]
    congr 1
    rw [lift_map, Category.assoc]
  have i1 := GlobalTheory.GenSpread.lbIso_pull_comp _ e1 e2 (hadj (kerN d))
  have i2 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP (lift (snd c.A T ≫ x) (fst c.A T)).left e3
  obtain ⟨t0, ht0⟩ := z.rig₁
  have g1 : ∃ u : LB.Gen (z.P.pull ((fst c.A T ≫ inc ≫ act (kerM d)) ≫ lift (1 : z.A ⟶ z.A) (𝟙 z.A)).left),
      u.IsGen :=
    ⟨LB.pullGen z.P _ _ t0 (fst c.A T ≫ inc ≫ act (kerM d)).left,
      LB.isGen_pullGen z.P _ _ t0 ht0 (fst c.A T ≫ inc ≫ act (kerM d)).left⟩
  have g2 := GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB z.isLB _) i1 g1
  exact GlobalTheory.RigidBundleGlue.exists_gen_of_lbIso (pull_isLB z.isLB _) (pull_isLB c.isLB _) i2.symm g2

end GlobalTheory.ZarhinKer
