import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSum

set_option maxHeartbeats 1000000 in

theorem part_eq_of_congMod : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∀ (p : ℕ) [Fact p.Prime] (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → ∀ a a' ν ν' κ, yy a = QuotientAddGroup.mk ν → yy a' = QuotientAddGroup.mk ν' → CongMod D.m ν ν' → GSum.part D z₁ z₂ a κ = GSum.part D z₁ z₂ a' κ := by
  intro g n F W Z i X₁ hg hn hodd hi hE hT hP ε₁ hd D z₁ z₂ hq p _ c y h hy yy hl a a' ν ν' κ ha ha' hc
  subst hy
  obtain ⟨hon, hker⟩ := GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X hg hn hodd hi hE hT D.proj D.ε D.diag p
    (y (cPt p)) (D.lift c y h) yy hl
  obtain ⟨w, hw⟩ := hc
  obtain ⟨b, hb⟩ := hon (QuotientAddGroup.mk w)
  have hk : a - a' - D.m • b ∈ D.X.S.HH D.X.M (y (cPt p)) := by
    rw [← hker, AddMonoidHom.mem_ker]
    have e1 : yy (a - a' - D.m • b) = yy a - yy a' - D.m • yy b := by
      rw [map_sub, map_sub, map_nsmul]
    rw [e1, ha, ha', hb, hw]
    show ((QuotientAddGroup.mk (ν' + D.m • w) - QuotientAddGroup.mk ν' - D.m • QuotientAddGroup.mk w :
      ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X))) = 0
    rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_sub, ← QuotientAddGroup.mk_sub]
    simp
  have hw' : wtChar D (D.X.S.TT D.X.M (y (cPt p))) a = wtChar D (D.X.S.TT D.X.M (y (cPt p))) a' := by
    ext t
    have ht : eStdBilin D.X.S.g _ (t : D.X.S.Gam) (a - a' - D.m • b) = 0 := t.2 _ hk
    have hsplit : D.m • a = D.m • a' + (D.m * D.m) • b + D.m • (a - a' - D.m • b) := by
      rw [mul_nsmul', ← smul_add, ← smul_add]
      congr 1
      abel
    have key : eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a) =
        eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a') + (D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b := by
      rw [hsplit]
      simp only [← eStdBilin_apply, map_add, map_nsmul, ht, smul_zero, add_zero]
    have hN : ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N)
        ((D.m * D.m) • eStd D.X.S.g _ (t : D.X.S.Gam) b) = 0 := by
      rw [map_nsmul, ← sq, ← D.sq, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    show ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a)) =
      ZMod.castHom (dvd_mul_left D.X.S.N D.X.S.r) (ZMod D.X.S.N) (eStd D.X.S.g _ (t : D.X.S.Gam) (D.m • a'))
    rw [key, map_add, hN, add_zero]
  simp only [part, hw']

end GlobalTheory.Poinc.GSum
