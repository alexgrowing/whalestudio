import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfPullbackQuasiInverseIsogenyTrivialAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

open GlobalTheory.BirigidPow (val_one_left val_one_right val_pow_right comp_pow_pt) in
open GlobalTheory.CechPic (cls cls_pull cls_eq_iff cls_eq_zero_iff pull_comp) in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  intro p _ D R _ b N c Y s o o' ψ ψ' hp hI hq T σ hσ x hx
  have hP := o.isLB
  have hP' := o'.isLB
  have hc0 : 0 < c := hI.pos
  obtain ⟨k, hk⟩ := hI.1
  haveI := hq.1
  haveI := hq.2.1
  have hu : IsUnit (c : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [hk, Nat.cast_pow]
    exact h.pow k

  have hQ1 : (o.P.pull (sq2 ψ')).IsLB := pull_isLB hP _
  have hQ2 : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb hP' _ _
  have cQ1 : cls _ hQ1 = GlobalTheory.CechPic.pull (sq2 ψ') (cls o.P hP) := cls_pull hP _ hQ1
  have cQ2 : cls _ hQ2 = c • cls o'.P hP' := GlobalTheory.BirigidPow.cls_lbPow hP' c hQ2
  have atQ₁ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ1) = GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') := by
    intro U a b
    rw [cQ1, GlobalTheory.BirigidPow.val, ← pull_comp, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have atQ₂ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ2) = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [cQ2, map_nsmul, GlobalTheory.BirigidPow.val]
  have ax1 : IsAxesTriv o'.A (o.P.pull (sq2 ψ')) := by
    refine ⟨hQ1, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_⟩
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_left hP o.rig₁ _
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_right hP o.rig₂ _
  have ax2 : IsAxesTriv o'.A (Hecke.lbPow o'.P c) := by
    refine ⟨hQ2, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_⟩
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_left hP' o'.rig₁, smul_zero]
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_right hP' o'.rig₂, smul_zero]

  have eP : GlobalTheory.CechPic.pull (sq2 ψ) (cls o'.P hP') = c • cls o.P hP := by
    obtain ⟨i⟩ := hI.2.2.2.2.1
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP c _
  have eC : GlobalTheory.CechPic.pull (sq2 ((𝟙 o.A) ^ c)) (cls o.P hP) = (c ^ 2) • cls o.P hP := by
    have i := GlobalTheory.BirigidPow.lineBundleIso_tensorPowSq_pullback_mulPair hP o.ab o.ample o.rig₁ o.rig₂ c
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP _)).2 i
    rw [cls_pull hP _ (pull_isLB hP _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP _ _
  have eS : sq2 ψ ≫ sq2 ψ' = sq2 ((𝟙 o.A) ^ c) := by
    rw [← hq.2.2.1, sq2, sq2, sq2, ← Over.comp_left, comp_lift]
    simp
  have iso : LBIso ((o.P.pull (sq2 ψ')).pull (sq2 ψ)) ((Hecke.lbPow o'.P c).pull (sq2 ψ)) := by
    refine (cls_eq_iff (pull_isLB hQ1 _) (pull_isLB hQ2 _)).1 ?_
    rw [cls_pull hQ1 _ (pull_isLB hQ1 _), cls_pull hQ2 _ (pull_isLB hQ2 _), cQ1, cQ2, map_nsmul, eP,
      ← pull_comp, eS, eC, smul_smul, sq]
  have cE : cls _ hQ1 = cls _ hQ2 := (cls_eq_iff hQ1 hQ2).2
    (GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A o'.A c ψ ψ' _ _ o'.ab hc0 hu hq ax1 ax2 iso)
  have key : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [← atQ₁, cE, atQ₂]
  have hT : PullPolTriv o ψ' x ↔ GlobalTheory.BirigidPow.val hP' (fst o'.A T) (snd o'.A T ≫ x ^ c) = 0 := by
    unfold PullPolTriv
    rw [← cls_eq_zero_iff (pull_isLB hP _), cls_pull hP _ (pull_isLB hP _)]
    change GlobalTheory.BirigidPow.val hP _ _ = 0 ↔ _
    rw [← Category.assoc (snd o'.A T) x ψ', key, comp_pow_pt,
      val_pow_right hP' o'.ab o'.ample o'.rig₁ o'.rig₂]
  have hsym : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP' a b = GlobalTheory.BirigidPow.val hP' b a := by
    intro U a b
    obtain ⟨i⟩ : Nonempty (LBIso o'.P (o'.P.pull (lift (snd o'.A o'.A) (fst o'.A o'.A)).left)) := ⟨o'.symm⟩
    have h := (cls_eq_iff hP' (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [GlobalTheory.BirigidPow.val, h, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst, GlobalTheory.BirigidPow.val]
  rw [hT]
  constructor
  · intro h
    obtain ⟨e, he, hker⟩ := o'.kerP
    have h1 : (x ^ c) ^ e = 1 := hker T (x ^ c)
      ((cls_eq_zero_iff (pull_isLB hP' _)).1 (by
        rw [cls_pull hP' _ (pull_isLB hP' _)]
        exact (hsym _ _).trans h))
    have h2 : (x ^ c) ^ (c ^ 2) = 1 := by
      rw [← pow_mul, ← pow_succ', hx]
    have hco : e.gcd (c ^ 2) = 1 := by
      rw [hk]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ he)
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hco, pow_one] at this
  · intro h
    rw [h, MonObj.comp_one]
    exact val_one_right hP' o'.rig₂ _
