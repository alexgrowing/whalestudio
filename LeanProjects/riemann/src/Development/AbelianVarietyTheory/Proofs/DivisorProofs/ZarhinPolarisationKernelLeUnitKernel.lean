import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

open Matrix

def formPolUnit (d : ℕ) : ord d :=
  ⟨form d * single (Sum.inl 0) (Sum.inr 0) 1, fun i j => by simp [Matrix.mul_apply, Matrix.single_apply]⟩

theorem idem_mul_formPolUnit (d : ℕ) : idem d * formPolUnit d = polUnit d := by
  ext1
  show single (Sum.inl 0) (Sum.inl 0) 1 * (form d * single (Sum.inl 0) (Sum.inr 0) 1) = single (Sum.inl 0) (Sum.inr 0) 1
  rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single]
  simp [form]

theorem bar_formPolUnit_mul_idem {d : ℕ} (hd : 0 < d) : bar d (formPolUnit d) * idem d = bar d (formPolUnit d) := by
  ext1
  have e : ((bar d (formPolUnit d) : ord d) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) =
      form d * single (Sum.inr 0) (Sum.inl 0) 1 := by
    rw [bar_coe]
    show form d * (form d * single (Sum.inl 0) (Sum.inr 0) 1)ᵀ * formInv d = _
    rw [Matrix.transpose_mul, form_transpose, Matrix.transpose_single, Matrix.mul_assoc, Matrix.mul_assoc,
      form_mul_formInv hd, Matrix.mul_one]
  rw [Subring.coe_mul, e]
  show form d * single (Sum.inr 0) (Sum.inl 0) 1 * single (Sum.inl 0) (Sum.inl 0) 1 = _
  rw [Matrix.mul_assoc, Matrix.single_mul_single_same, _root_.mul_one]

end GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinFam.KerSup

variable {X Y : Scheme.{0}}

theorem exists_gen_of_lbIso' {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X))
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X)) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem gen_pull_comp (L : LB X) (f : Y ⟶ X) {Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull (h ≫ f)), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  exact gen_chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl)) t ht

theorem gen_congr (L : LB X) {f g : Y ⟶ X} (e : f = g)
    (H : ∃ t : LB.Gen (L.pull f), t.IsGen) : ∃ t : LB.Gen (L.pull g), t.IsGen := by
  subst e; exact H

theorem lbIso_pull_comp (L : LB X) {f g : Y ⟶ X} {Y' : Scheme.{0}} (h : Y' ⟶ Y) (H : LBIso (L.pull f) (L.pull g)) :
    LBIso (L.pull (h ≫ f)) (L.pull (h ≫ g)) :=
  H.chartPull (chartPullSame L (fun _ => h ≫ f) (fun _ => f) (fun _ => 1) h (fun _ => rfl))
    (chartPullSame L (fun _ => h ≫ g) (fun _ => g) (fun _ => 1) h (fun _ => rfl))

theorem lbIso_pull_pull {L : LB X} {M : LB Y} {j : X ⟶ Y} {Y' : Scheme.{0}} (h : Y' ⟶ X) (H : LBIso L (M.pull j)) :
    LBIso (L.pull h) (M.pull (h ≫ j)) := by
  have a : ChartPull (L.pull h) L h := chartPullPull L h
  have b : ChartPull (M.pull (h ≫ j)) (M.pull j) h :=
    chartPullSame M (fun _ => h ≫ j) (fun _ => j) (fun _ => 1) h (fun _ => rfl)
  exact LBIso.chartPull a b H

end GlobalTheory.ZarhinFam.KerSup

namespace GlobalTheory.ZarhinFam

theorem ker_pol_le_ker_polUnit : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  intro h M d hd S t c z act inc pr hdu hker hz hact hadj hinc hpr hip hpi hP T x hx
  have hNp : act (polUnit d) = act (idem d) ≫ act (formPolUnit d) := by
    rw [← idem_mul_formPolUnit, hact.2.2.1]
  have hbar : act (bar d (formPolUnit d)) ≫ pr ≫ inc = act (bar d (formPolUnit d)) := by
    rw [hpi, ← hact.2.2.1, bar_formPolUnit_mul_idem hd]
  have hy : x ≫ inc ≫ act (polUnit d) = x ≫ inc ≫ act (formPolUnit d) := by
    rw [hNp, ← hpi]
    simp only [Category.assoc]
    rw [← Category.assoc inc pr, hip, Category.id_comp]
  rw [hy]
  apply hz.2 T
  let q : z.A ⟶ c.A := act (bar d (formPolUnit d)) ≫ pr
  let ψ₁ : z.A ⊗ T ⟶ c.A ⊗ c.A := lift (snd z.A T ≫ x) (fst z.A T ≫ q)
  let φ : z.A ⊗ T ⟶ z.A ⊗ z.A := lift (snd z.A T ≫ x ≫ inc) (fst z.A T)
  have g1 : ∃ u : (c.P.pull ψ₁.left).Gen, u.IsGen := by
    have := KerSup.gen_pull_comp c.P _ (lift (fst z.A T ≫ q) (snd z.A T)).left hx
    refine KerSup.gen_congr c.P ?_ this
    rw [← Over.comp_left]
    congr 1
    simp [ψ₁]
  have g2 : ∃ u : (z.P.pull (ψ₁.left ≫ (inc ⊗ₘ inc).left)).Gen, u.IsGen :=
    KerSup.exists_gen_of_lbIso' (pull_isLB c.isLB _) (pull_isLB z.isLB _) (KerSup.lbIso_pull_pull ψ₁.left hP) g1
  have e3 : ψ₁.left ≫ (inc ⊗ₘ inc).left =
      φ.left ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar d (formPolUnit d)))).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    simp only [ψ₁, φ, q, lift_map, comp_lift, lift_fst, lift_snd_assoc, Category.assoc, hbar]
  have i4 := KerSup.lbIso_pull_comp z.P φ.left (hadj (formPolUnit d))
  have g4 := KerSup.exists_gen_of_lbIso' (pull_isLB z.isLB _) (pull_isLB z.isLB _) i4.symm
    (KerSup.gen_congr z.P e3 g2)
  refine KerSup.gen_congr z.P ?_ g4
  rw [← Over.comp_left]
  congr 1
  simp [φ]

end GlobalTheory.ZarhinFam
