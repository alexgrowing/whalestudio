import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPtSSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemScLatOfMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inlS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV G i j).rank) : ofMaps t e x p (e (.inl k)) = GlobalTheory.BigDat.divG (spW₁ G i j) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inrS (t : T) (e : Num G i j) (x : HomA G t i j × HomB G i j) (p : Fin (spW₁ G i j).rank)
    (k : Fin (spV₁ G i j).rank) : ofMaps t e x p (e (.inr k)) = cA D (GlobalTheory.BigDat.divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genA (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW₁ G i j).rank → D.host.E)
    (r : Fin (spV G i j).rank → D.host.E) :
    ofMaps t e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spW₁ G i j).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • r) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((GlobalTheory.BigDat.divG_gen (spW₁ G i j) β a s r k p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero,
      GlobalTheory.BigDat.divG_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genB (t : T) (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (r : Fin (spW₁ G i j).rank → D.host.E) :
    ofMaps t e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star r) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  have hneg : -(Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (negSp (spV₁ G i j)).gram k j') :
      Matrix _ _ (AE D)) = Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * r i' * ∑ k, star (s k) * (spV₁ G i j).gram k j') := by
    ext p q
    simp only [Matrix.neg_apply, of_apply, negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg,
      TensorProduct.tmul_neg]
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inlS t e _ p k).trans ((congrFun (congrFun (GlobalTheory.BigDat.divG_zero (spW₁ G i j)) k) p).trans ?_)
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inrS t e _ p k).trans ?_
    rw [GlobalTheory.BigDat.smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, hneg,
      GlobalTheory.BigDat.divG_gen]
    change β ⊗ₜ[D.host.F] star (a * r p * star (s k)) = β ⊗ₜ[D.host.F] (star (r p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem smul_ofMaps_inl_memS {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomA G t i j}
    (hx : x ∈ latA G t i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (x, 0) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genA t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hs))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha hr) (zero_mem _))))

theorem smul_ofMaps_inr_memS {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsDoublyCompatible t i j e Bs Γ X) (v : Pl D.host.F) {x : HomB G i j}
    (hx : x ∈ latB G i j) : GlobalTheory.LatVac.liftV v 1 • ofMaps t e (0, x) ∈ latAtV Γ.V' Γ.W v := by
  refine GlobalTheory.BigDat.map_mem_of_closure ((DistribMulAction.toAddMonoidHom (PtS G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps t e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, r, hr, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V' Γ.W v) (ofMaps_genB t e (pairA _ 0 α) a s r)).mpr
    (GlobalTheory.BigDat.one_smul_gen_mem _ _ v hα (h.2.ge (GlobalTheory.BigDat.star_mem_conjSub hr))
      (h.1.2.1.ge (GlobalTheory.BigDat.pair_mem e (zero_mem _)
        (GlobalTheory.BigDat.star_mem_conjSub (GlobalTheory.BigDat.smul_mem_scLat_of_mem ha (GlobalTheory.BigDat.star_mem_conjSub hs))))))

theorem latPtS_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), GlobalTheory.FlipMatch.IsDoublyCompatible t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps t e (mapA t e u, 0) + ofMaps t e (0, mapB e u) :=
    ((ofMaps_maps t e u).symm.trans (congrArg (ofMaps t e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps t e).symm (mapA t e u, 0) (0, mapB e u))
  have e3 := add_mem (smul_ofMaps_inl_memS h v h1) (smul_ofMaps_inr_memS h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.SmallDat

end
