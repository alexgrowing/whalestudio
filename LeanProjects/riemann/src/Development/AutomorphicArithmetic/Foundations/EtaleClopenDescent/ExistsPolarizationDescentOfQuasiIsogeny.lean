import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfRoot

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hce hB hq hker
  obtain ⟨e, rfl⟩ := hce
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  haveI := hψ
  haveI := hψ'
  have hc0 : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hP := o.isLB
  have hlb : ∀ m, (Hecke.lbPow o.P m).IsLB := fun m => by
    unfold Hecke.lbPow
    exact LB.isLB_linComb hP _ _
  obtain ⟨Dd, _, Q, h, hD, hdual, hadd, hh, hiso⟩ :=
    GlobalTheory.T.exists_dual_abelian_scheme Y B o.A ψ' o.P hB o.ab hψ' hP o.rig₁ o.rig₂
  have hQ := hdual.isLB
  have etens : (ψ' ⊗ₘ ψ') = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by
    ext <;> simp
  have esq : Hecke.sq2 ψ' = Over.Hom.left (ψ' ⊗ₘ ψ') := by
    rw [etens]
    rfl
  have kiso := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hQ _)).2 hiso
  rw [GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull hQ] at kiso
  have hkerh : ∀ (T : Over Y) (σ : T.left ⟶ Y), σ ≫ 𝟙 Y = T.hom →
      ∀ a : T ⟶ B, a ^ (p ^ e) = 1 → a ≫ h = 1 := by
    intro T σ hσ a ha
    have ha3 : a ^ (p ^ e) ^ 3 = 1 := by
      rw [show (p ^ e) ^ 3 = p ^ e * (p ^ e) ^ 2 by ring, pow_mul, ha, one_pow]
    have htriv := (hker T σ hσ a ha3).2 ha
    apply hdual.eq_one
    have e1 : lift (fst B T) (snd B T ≫ a ≫ h) =
        lift (fst B T) (snd B T ≫ a) ≫ lift (fst B B) (snd B B ≫ h) := by
      ext <;> simp
    have e2 : lift (fst B T ≫ ψ') (snd B T ≫ a ≫ ψ') =
        lift (fst B T) (snd B T ≫ a) ≫ (ψ' ⊗ₘ ψ') := by
      rw [etens]
      ext <;> simp
    have k2 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 htriv
    rw [GlobalTheory.CechPic.cls_pull hP, e2, Over.comp_left, GlobalTheory.CechPic.pull_comp, kiso,
      ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, ← e1, ← GlobalTheory.CechPic.cls_pull hQ _ (pull_isLB hQ _)] at k2
    exact (GlobalTheory.CechPic.cls_eq_zero_iff _).1 k2
  have hunit : IsUnit (((p ^ e : ℕ) : Γ(Y, ⊤))) := by
    have h0 : IsUnit ((p : ℕ) : Γ(Sp R, ⊤)) := by
      have := hp.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have h3 := h0.map s.appTop.hom
    rw [map_natCast] at h3
    simpa using h3.pow e
  obtain ⟨P', hP'lb, hr1, hr2, hP'iso⟩ :=
    GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle Y B Dd Q h (p ^ e) _ o.P (Over.Hom.left (ψ' ⊗ₘ ψ')) hB hD hdual hadd hh hc0 hunit hP
      hiso Y (𝟙 Y) B (𝟙 _) (𝟙 _) (GlobalTheory.SiegLower.isGrpPullback_id B) ⟨by simp, by simp⟩ hkerh
  have kP' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (GlobalTheory.isLB_lbPow hP'lb _)).2 hP'iso
  rw [Category.id_comp, GlobalTheory.CechPic.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, ← esq] at kP'
  have hP2 : (P'.pull (Hecke.sq2 ψ)).IsLB := pull_isLB hP'lb _
  have sqc : Hecke.sq2 (ψ ≫ ψ') = Hecke.sq2 ψ ≫ Hecke.sq2 ψ' := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL1 : Over.Hom.left (lift (1 : o.A ⟶ o.A) (𝟙 o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (1 : B ⟶ B) (𝟙 B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL2 : Over.Hom.left (lift (𝟙 o.A) (1 : o.A ⟶ o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (𝟙 B) (1 : B ⟶ B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  refine ⟨P', ⟨hP'lb, hr1, hr2⟩, ?_, ?_⟩
  · rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (by unfold Hecke.lbPow; exact LB.isLB_linComb hP'lb _ _),
      GlobalTheory.BirigidPow.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, kP']
  · refine GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified Y o.A (p ^ e) _ _ o.ab hc0 hunit (hlb _) ?_ ?_ hP2 ?_ ?_ ?_
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₁, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₂, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL1, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr1, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL2, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr2, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow (hlb _) _) (GlobalTheory.isLB_lbPow hP2 _),
        GlobalTheory.CechPic.cls_lbPow (hlb _), GlobalTheory.CechPic.cls_lbPow hP2, GlobalTheory.BirigidPow.cls_lbPow hP, smul_smul,
        ← pow_two, ← GlobalTheory.BirigidPow.cls_lbPow hP _ (hlb _),
        (GlobalTheory.CechPic.cls_eq_iff (hlb _) (pull_isLB hP _)).2
          (GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple Y o.A o.ab o.P hP o.rig₁ o.rig₂ o.ample (p ^ e)),
        ← h1, sqc, GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.pull_comp, kP', map_nsmul,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ hP2]
