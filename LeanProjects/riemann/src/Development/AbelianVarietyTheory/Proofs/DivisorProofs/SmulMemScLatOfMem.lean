import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

noncomputable section

namespace GlobalTheory.BigDat

theorem smul_mem_scLat_of_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}
    {Λ : Submodule (𝓞 E) (Fin n → E)} {a : E} (ha : a ∈ 𝔞) {y : Fin n → E} (hy : y ∈ Λ) :
    a • y ∈ GlobalTheory.SkewLat.scLat 𝔞 Λ := by
  intro c hc
  have h : a * c ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :=
    FractionalIdeal.mul_one_div_le_one (FractionalIdeal.mul_mem_mul ha hc)
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h
  rw [smul_smul, mul_comm, ← hr, algebraMap_smul]
  exact Λ.smul_mem r hy

theorem divG_gen {D : D7} (S : HSp D) {n : ℕ} (β : AF D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin n → D.host.E) (p : Fin n) (q : Fin S.rank) :
    divG S (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) p q =
      β ⊗ₜ[D.host.F] (a * t p * star (s q)) := by
  have h : (Matrix.of fun i j => β ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : Matrix _ _ (AE D)) =
      mulG S (Matrix.of fun i k => β ⊗ₜ[D.host.F] (a * t i * star (s k))) := by
    ext i j
    rw [mulG_eq, Matrix.mul_apply]
    simp only [of_apply, map_apply, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change _ = (β ⊗ₜ[D.host.F] (a * t i * star (s k))) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] S.gram k j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc (a * t i)]
  rw [h, divG_mulG, of_apply]

theorem divG_zero {D : D7} (S : HSp D) {n : ℕ} : divG S (0 : Matrix (Fin n) (Fin S.rank) (AE D)) = 0 :=
  Matrix.zero_mul _

theorem divG_neg {D : D7} (S : HSp D) {n : ℕ} (x : Matrix (Fin n) (Fin S.rank) (AE D)) : divG S (-x) = -divG S x :=
  Matrix.neg_mul _ _

theorem smul_incM_apply {D : D7} {m n : Type} (β : AF D.host.F) (M : Matrix m n D.host.E) (p : m) (q : n) :
    (β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F M) p q = β ⊗ₜ[D.host.F] M p q := by
  change β • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M p q) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem one_smul_gen_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) {α : Af F} (hα : α ∈ intAf F) {x : Fin n → E} (hx : x ∈ X.L)
    {y : Fin d → E} (hy : y ∈ Y.L) :
    GlobalTheory.LatVac.liftV v 1 • pairA F 0 α • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (vecMulVec x y) ∈ latAtV X Y v := by
  rw [smul_smul]
  refine AddSubgroup.subset_closure ⟨_, ?_, ?_, x, hx, y, hy, rfl⟩
  · intro u hu
    rw [smul_eq_mul, ← mul_assoc, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v 1 u hu, zero_mul]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV, one_mul]
    exact hα v

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem ofMaps_inl (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV G i j).rank) :
    ofMaps e x p (e (.inl k)) = divG (negSp (spW G i j)) x.1 k p := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inl, transpose_apply]

theorem ofMaps_inr (e : Num G i j) (x : HomV G i j × HomW G i j) (p : Fin (spW G i j).rank) (k : Fin (spV₁ G i j).rank) :
    ofMaps e x p (e (.inr k)) = cA D (divG (spV₁ G i j) (-x.2) p k) := by
  simp only [ofMaps, submatrix_apply, id, Equiv.symm_apply_apply, fromCols_apply_inr, map_apply]

theorem ofMaps_genV (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spW G i j).rank → D.host.E)
    (t : Fin (spV G i j).rank → D.host.E) :
    ofMaps e (Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (negSp (spW G i j)).gram k j'), 0) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star s) (Sum.elim (a • t) 0 ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((divG_gen (negSp (spW G i j)) β a s t k p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, mul_comm]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, neg_zero, divG_zero,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    exact map_zero _

theorem ofMaps_genW (e : Num G i j) (β : AF D.host.F) (a : D.host.E) (s : Fin (spV₁ G i j).rank → D.host.E)
    (t : Fin (spW G i j).rank → D.host.E) :
    ofMaps e (0, Matrix.of fun i' j' => β ⊗ₜ[D.host.F] (a * t i' * ∑ k, star (s k) * (spV₁ G i j).gram k j')) =
      β • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (vecMulVec (star (-t)) (Sum.elim 0 (star (a • star s)) ∘ e.symm)) := by
  ext p q
  obtain ⟨k | k, rfl⟩ := e.surjective q
  · refine (ofMaps_inl e _ p k).trans ((congrFun (congrFun (divG_zero (negSp (spW G i j))) k) p).trans ?_)
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
    rfl
  · refine (ofMaps_inr e _ p k).trans ?_
    rw [smul_incM_apply, vecMulVec_apply, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr, divG_neg, Matrix.neg_apply,
      divG_gen, ← TensorProduct.tmul_neg]
    change β ⊗ₜ[D.host.F] star (-(a * t p * star (s k))) = β ⊗ₜ[D.host.F] (star (-t p) * star (a * star (s k)))
    rw [← star_mul']
    congr 2
    ring

theorem map_mem_of_closure {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) {s : Set A} {H : AddSubgroup B}
    (h : ∀ x ∈ s, f x ∈ H) {x : A} (hx : x ∈ AddSubgroup.closure s) : f x ∈ H :=
  (AddSubgroup.closure_le (H.comap f)).2 h hx

theorem pair_mem {E : Type} [Field E] [NumberField E] {a b d : ℕ} {ΛA : Submodule (𝓞 E) (Fin a → E)}
    {ΛB : Submodule (𝓞 E) (Fin b → E)} (e : Fin a ⊕ Fin b ≃ Fin d) {x : Fin a → E} {y : Fin b → E} (hx : x ∈ ΛA) (hy : y ∈ ΛB) :
    Sum.elim x y ∘ e.symm ∈ GlobalTheory.SkewLat.pairLat ΛA ΛB e := by
  rw [GlobalTheory.SkewLat.mem_pairLat]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  exact ⟨hx, hy⟩

theorem star_mem_conjSub {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)}
    {y : Fin n → E} (hy : y ∈ Λ) : star y ∈ GlobalTheory.TripleSpaceW.conjSub Λ := by
  rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hy

theorem smul_ofMaps_inl_mem {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomV G i j} (hx : x ∈ latV G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (x, 0) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribMulAction.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inl _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genV e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub hs))
      (h.2.1.ge (pair_mem e (smul_mem_scLat_of_mem ha ht) (zero_mem _))))

theorem smul_ofMaps_inr_mem {t : T} {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j}
    {X : Chars D.host.F D.host.E} (h : IsTied t i j e Bs Γ X) (v : Pl D.host.F) {x : HomW G i j} (hx : x ∈ latW G i j) :
    GlobalTheory.LatVac.liftV v 1 • ofMaps e (0, x) ∈ latAtV Γ.V Γ.W v := by
  refine map_mem_of_closure ((DistribMulAction.toAddMonoidHom (Pt G i j) (GlobalTheory.LatVac.liftV v 1)).comp
    ((maps e).symm.toLinearMap.toAddMonoidHom.comp (AddMonoidHom.inr _ _))) ?_ hx
  rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
  exact (congrArg (fun z => GlobalTheory.LatVac.liftV v 1 • z ∈ latAtV Γ.V Γ.W v) (ofMaps_genW e (pairA _ 0 α) a s t)).mpr
    (one_smul_gen_mem _ _ v hα (h.1.ge (star_mem_conjSub (neg_mem ht)))
      (h.2.1.ge (pair_mem e (zero_mem _) (star_mem_conjSub (smul_mem_scLat_of_mem ha (star_mem_conjSub hs))))))

theorem latPt_le_latAtV : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), IsTied t i j e Bs Γ X →
    ∀ v : Pl D.host.F, ∀ u ∈ latPt e v, u ∈ latAtV Γ.V Γ.W v := by
  intro D T L sc G t i j e Bs Γ X h v u hu
  obtain ⟨hat, h1, h2⟩ := hu
  have e1 : GlobalTheory.LatVac.liftV v 1 • u = u := by
    have := hat (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at this
    exact this.symm
  have e2 : u = ofMaps e (mapV e u, 0) + ofMaps e (0, mapW e u) :=
    ((ofMaps_maps e u).symm.trans (congrArg (ofMaps e) (Prod.ext (add_zero _).symm (zero_add _).symm))).trans
      (map_add (maps e).symm (mapV e u, 0) (0, mapW e u))
  have e3 := add_mem (smul_ofMaps_inl_mem h v h1) (smul_ofMaps_inr_mem h v h2)
  rwa [← smul_add, ← e2, e1] at e3

end GlobalTheory.BigDat

end
