import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem rosati_of_quasiInv_root : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ hIso act' hact a
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit ((p ^ e : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL', r₁, r₂⟩ := hP'
  haveI := act'.hom a
  haveI := act'.hom (D.star a).unop
  have e₁ : Hecke.sq2 ψ ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : Hecke.sq2 ψ ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      𝟙 _ ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (act'.act a).left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (act'.act (D.star a).unop).left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      𝟙 _ ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hX₂ : ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hL₁ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e))
      ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati a) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  have A₁ : IsAxesTriv B (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂⟩
  have A₂ : IsAxesTriv B (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂⟩
  exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' _ _ hB hpos hunit hq A₁ A₂ hsq

end GlobalTheory.UPel.HT.ES
