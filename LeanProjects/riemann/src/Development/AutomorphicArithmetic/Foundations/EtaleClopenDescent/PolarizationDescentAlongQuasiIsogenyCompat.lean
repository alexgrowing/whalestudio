import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowCompMonHomOverSchemeGrpObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveQcPow
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.Cb.PowerClasses

open GlobalTheory.AbDual GlobalTheory.CechPic

private theorem powClass {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ) (h : (Hecke.lbPow L m).IsLB) :
    cls (Hecke.lbPow L m) h = m • cls L hL := by
  have hsum := cls_linComb hL (fun _ : Fin m => 𝟙 X) (fun _ => 1) h
  refine hsum.trans ?_
  simp [pull_id]

end UpperTheory.Cb.PowerClasses

theorem UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ B), (∃ t : (P'.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hpunit hck hB hq hpol P' hax hI1 hI2
  obtain ⟨hmonψ, hmonψ', h1, h2⟩ := hq
  obtain ⟨e0, he0, hkerP⟩ := o.kerP
  refine ⟨e0, he0, ?_⟩
  rintro T x ⟨t, ht⟩
  have hP : o.P.IsLB := o.isLB
  have hP' : P'.IsLB := hax.1
  have addP : GlobalTheory.AbDual.IsAdditive o.P := (GlobalTheory.CubeAxes.additive_of_triv_axes o.ab hP o.rig₁ o.rig₂).1
  have addP' : GlobalTheory.AbDual.IsAdditive P' := (GlobalTheory.CubeAxes.additive_of_triv_axes hB hP' hax.2.1 hax.2.2).1
  have hx0 : GlobalTheory.AbDual.evc hP' (snd B T ≫ x) (fst B T) = 0 := (GlobalTheory.AbDual.triv_ev_iff hP' _ _).mp ⟨t, ht⟩
  have F1 : ∀ {Z : Over Y} (a a' : Z ⟶ B),
      GlobalTheory.AbDual.evc hP (a ≫ ψ') (a' ≫ ψ') = c • GlobalTheory.AbDual.evc hP' a a' := by
    intro Z a a'
    have hlb : (Hecke.lbPow P' c).IsLB := LB.isLB_linComb hP' _ _
    have hcls : GlobalTheory.CechPic.cls (o.P.pull (Hecke.sq2 ψ')) (pull_isLB hP _) = c • GlobalTheory.CechPic.cls P' hP' := by
      rw [(GlobalTheory.CechPic.cls_eq_iff _ hlb).mpr hI1]
      exact UpperTheory.Cb.PowerClasses.powClass hP' c hlb
    simp only [GlobalTheory.AbDual.evc]
    rw [← map_nsmul, ← hcls, GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
    congr 2
    rw [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have Fsym : ∀ {Z : Over Y} (a a' : Z ⟶ o.A), GlobalTheory.AbDual.evc hP a a' = GlobalTheory.AbDual.evc hP a' a := by
    intro Z a a'
    have hs : GlobalTheory.CechPic.cls o.P hP =
        GlobalTheory.CechPic.pull (lift (snd o.A o.A) (fst o.A o.A)).left (GlobalTheory.CechPic.cls o.P hP) := by
      rw [← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr o.symm
    simp only [GlobalTheory.AbDual.evc]
    conv_lhs => rw [hs]
    rw [← GlobalTheory.CechPic.pull_comp, ← Over.comp_left]
    congr 3
    ext <;> simp
  have hyc : ((x ≫ ψ') ^ c) ^ e0 = 1 := by
    apply hkerP T
    refine (GlobalTheory.AbDual.triv_ev_iff hP _ _).mpr ?_
    let u : o.A ⊗ T ⟶ B ⊗ T := lift (fst o.A T ≫ ψ) (snd o.A T)
    calc GlobalTheory.AbDual.evc hP (snd o.A T ≫ (x ≫ ψ') ^ c) (fst o.A T)
        = GlobalTheory.AbDual.evc hP ((snd o.A T ≫ x ≫ ψ') ^ c) (fst o.A T) := by rw [MonObj.comp_pow]
      _ = c • GlobalTheory.AbDual.evc hP (snd o.A T ≫ x ≫ ψ') (fst o.A T) := GlobalTheory.KerCalc.evc_pow_left hP addP _ _ c
      _ = c • GlobalTheory.AbDual.evc hP (fst o.A T) (snd o.A T ≫ x ≫ ψ') := by rw [Fsym (snd o.A T ≫ x ≫ ψ')]
      _ = GlobalTheory.AbDual.evc hP (fst o.A T ^ c) (snd o.A T ≫ x ≫ ψ') := (GlobalTheory.KerCalc.evc_pow_left hP addP _ _ c).symm
      _ = GlobalTheory.AbDual.evc hP (u ≫ fst B T ≫ ψ') (u ≫ snd B T ≫ x ≫ ψ') := by
          congr 1
          · rw [← Category.comp_id (fst o.A T), ← MonObj.comp_pow, ← h1]
            simp [u]
          · simp [u]
      _ = GlobalTheory.CechPic.pull u.left (GlobalTheory.AbDual.evc hP (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ')) :=
          (GlobalTheory.AbDual.pull_evc hP u _ _).symm
      _ = 0 := by
          rw [Fsym (fst B T ≫ ψ'), ← Category.assoc, F1, hx0, smul_zero, map_zero]
  have hxc : x ^ c = (x ≫ ψ') ≫ ψ := by
    rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id]
  have hx3 : x ^ (c * (c * e0)) = 1 := by
    rw [pow_mul, hxc, ← MonObj.pow_comp, pow_mul, hyc, MonObj.one_comp]
  have hz2 : (x ^ e0) ^ (c ^ 2) = 1 := by
    rw [← pow_mul, show e0 * c ^ 2 = c * (c * e0) by ring, hx3]
  have hcpos : 0 < c := by
    obtain ⟨k, rfl⟩ := hck
    exact pow_pos (Fact.out : p.Prime).pos k
  obtain ⟨hfl, hsu, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow Y B hB c hcpos
  have hsq : pullback.fst (x ^ e0).left (𝟙 B ^ c).left ≫ (x ^ e0).left =
      pullback.snd (x ^ e0).left (𝟙 B ^ c).left ≫ (𝟙 B ^ c).left := pullback.condition
  let T' : Over Y := Over.mk (pullback.fst (x ^ e0).left (𝟙 B ^ c).left ≫ T.hom)
  let πo : T' ⟶ T := Over.homMk (pullback.fst (x ^ e0).left (𝟙 B ^ c).left) rfl
  have hwl : pullback.snd (x ^ e0).left (𝟙 B ^ c).left ≫ B.hom = T'.hom := by
    have e1 := Over.w (𝟙 B ^ c)
    have e2 := Over.w (x ^ e0)
    calc pullback.snd (x ^ e0).left (𝟙 B ^ c).left ≫ B.hom
        = pullback.snd (x ^ e0).left (𝟙 B ^ c).left ≫ (𝟙 B ^ c).left ≫ B.hom := by rw [e1]
      _ = pullback.fst (x ^ e0).left (𝟙 B ^ c).left ≫ (x ^ e0).left ≫ B.hom := by
          rw [← Category.assoc, ← hsq, Category.assoc]
      _ = T'.hom := by rw [e2]; rfl
  let w : T' ⟶ B := Over.homMk (pullback.snd (x ^ e0).left (𝟙 B ^ c).left) hwl
  have hwc : w ^ c = πo ≫ x ^ e0 := by
    rw [← Category.comp_id w, ← MonObj.comp_pow]
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, πo]
    exact hsq.symm
  have hw3 : w ^ c ^ 3 = 1 := by
    rw [show c ^ 3 = c * c ^ 2 by ring, pow_mul, hwc, ← MonObj.comp_pow, hz2, MonObj.comp_one]
  have hppt : PullPolTriv o ψ' w := by
    refine (GlobalTheory.AbDual.triv_ev_iff hP _ _).mpr ?_
    rw [Fsym (fst B T' ≫ ψ'), ← Category.assoc, F1, ← GlobalTheory.KerCalc.evc_pow_left hP' addP', ← MonObj.comp_pow, hwc]
    let v : B ⊗ T' ⟶ B ⊗ T := lift (fst B T') (snd B T' ≫ πo)
    have hv : GlobalTheory.AbDual.evc hP' (snd B T' ≫ πo ≫ x ^ e0) (fst B T') =
        GlobalTheory.CechPic.pull v.left (GlobalTheory.AbDual.evc hP' (snd B T ≫ x ^ e0) (fst B T)) := by
      rw [GlobalTheory.AbDual.pull_evc]
      congr 1 <;> simp [v]
    rw [hv, MonObj.comp_pow, GlobalTheory.KerCalc.evc_pow_left hP' addP', hx0, smul_zero, map_zero]
  have hwc1 := (hpol T' T'.hom (Category.comp_id _) w hw3).mp hppt
  rw [hwc] at hwc1
  haveI : Epi (pullback.fst (x ^ e0).left (𝟙 B ^ c).left) := Flat.epi_of_flat_of_surjective _
  have e1 : πo ≫ x ^ e0 = πo ≫ (1 : T ⟶ B) := by rw [hwc1, MonObj.comp_one]
  have e2 := congrArg Over.Hom.left e1
  simp only [Over.comp_left, Over.homMk_left, πo] at e2
  ext1
  exact (cancel_epi _).mp e2
