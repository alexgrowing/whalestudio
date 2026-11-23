import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderActionRosatiAdjoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.KerC

theorem ker_zarhinPolarization_of_pullback : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → (∀ j, x ≫ GlobalTheory.ZarhinFam.pb c.A B j = 1) → ∀ j, ∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx hv j
  obtain ⟨hB, hD1, hD2, hla, hmu, hlm, hml, hPiso⟩ := id hZ
  haveI : IsMonHom la := hla
  have hQ : Q.IsLB := hD1.isLB
  have hPQ : ∀ (Y : Over S) (a a' : Y ⟶ c.A), evc c.isLB a a' = evc hQ a (a' ≫ la) := by
    have e : cls c.P c.isLB = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ _)).2 hPiso
    intro Y a a'
    show CechPic.pull (lift a a').left (cls c.P c.isLB) = _
    rw [e, pull_evc, lift_fst, lift_snd_assoc]
  have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ d mu
  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull hz]
    exact (cls_eq_zero_iff (pull_isLB hz _)).2 hx
  have h1 := congrArg (CechPic.pull
    (lift (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then snd T B else 1)) (fst T B) :
      T ⊗ B ⟶ Zob c.A B ⊗ T).left) h0
  rw [← pull_comp, ← Over.comp_left, comp_lift, map_zero, lift_snd_assoc, lift_fst,
    AdjPf.pull_zCls c.isLB hQ d la mu hPQ] at h1
  simp only [AdjPf.zf, Category.assoc, AdjPf.mkZ_pa, AdjPf.mkZ_pb, hv, MonObj.comp_one, MonObj.one_comp,
    evc_one_right hQ hD1.zero, hD1.additive.evc_one hQ, smul_zero, Finset.sum_const_zero, zero_add, add_zero] at h1
  simp only [apply_ite (evc hQ _), evc_one_right hQ hD1.zero, smul_ite, smul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at h1
  refine (hD1.isPerfect hD2).ker_left T _ ((triv_ev_iff hQ _ _).2 ?_)
  let F : (T ⊗ B ⟶ c.A) →* Multiplicative (Pic (T ⊗ B).left) :=
    MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hQ a (snd T B))) fun a a' => by
      rw [(isAdditive_iff hQ).1 hD1.additive, ofAdd_add]
  have eF : ∀ a, evc hQ a (snd T B) = Multiplicative.toAdd (F a) := fun _ => rfl
  have ep : fst T B ≫ ∏ i, (x ≫ pa c.A B i) ^ quat d j i = ∏ i, (fst T B ≫ x ≫ pa c.A B i) ^ quat d j i := by
    have := map_prod (AdjPf.pre (G := c.A) (fst T B)) (fun i => (x ≫ pa c.A B i) ^ quat d j i) Finset.univ
    simp only [map_zpow] at this
    exact this
  rw [ep, eF, map_prod, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, ← eF]
  exact h1

end GlobalTheory.ZarhinFam.KerC
