import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompletionPlaceData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocGrp GlobalTheory.LocMod

theorem mem_bes {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1)) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ + 1) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ + 1)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ + 1)) :
    g ∈ besGrp (diagDec (besDec d rfl) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* k := p.π.comp (incA D)
  set dd := diagDec (besDec d rfl) l hl with hdd
  set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ + 1)) := { β := sumCols d p.π b u, γ := Γ, βγ := h2, γβ := h1 }
  let FA : Frame k A.rank (Fin A.rank) := { β := b, γ := b', βγ := hb, γβ := hb' }
  let F₀ : Frame k (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank (Fin A.rank ⊕ Fin 1) :=
    { β := (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id
      γ := (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix id E.symm
      βγ := by
        refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb]
      γβ := by
        refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb'] }
  have hloc : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    change _ = sumCols d p.π b u * x.val * Γ
    rw [e, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * (dd.jX.map p.π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) = φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z k), dd.j0.map p.π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : dd.j0.map p.π = (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  have jA : dd.j0.map p.π * o.jA.map p.π = (frameMat B A d.ι).map φ := by
    have e : o.jA.map p.π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) k) (0 : Matrix (Fin 1) (Fin A.rank) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have jB : dd.j0.map p.π * o.jB.map p.π = (midCol d rfl).map φ := by
    have e : o.jB.map p.π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) k) (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    refine (congrArg (dd.j0.map p.π * ·) e).trans ((core _).trans ?_)
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  have fX : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i)) = u (Fin.castLE hσ i) * φ (l i)⁻¹ * (dd.jX.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
  have fY : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i).rev) =
      u (Fin.castLE hσ i).rev * φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
  have fZ : ∀ r, F.β r (Sum.inr ⟨σ, hσ'⟩) = u ⟨σ, hσ'⟩ * (dd.j0.map p.π * o.jB.map p.π) r (0 : Fin 1) := fun r =>
    (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun jB r) (0 : Fin 1)).symm))
  have ec := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k))
  rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at ec
  obtain ⟨Φ, hΦ⟩ := exists_hom p F
  have hN : N k (Fin A.rank) (2 * σ + 1) (σ + 1) ≤ (besGrp dd o).comap Φ := by
    refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_sup_left (flag_of_strict p dd F₀ F
      (Sum.elim (Sum.map id fun _ => ⟨σ, hσ'⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, hσ'⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i)))) ?_
      (GlobalTheory.RootEx.lev (σ + 1)) ?_ (hΦ y) fun r s hrs => by rw [Matrix.sub_apply, hy r s hrs, sub_self])
    · rintro (a | j)
      · exact ⟨Sum.inl (Sum.inl a), rfl⟩
      · rcases lt_trichotomy j.val σ with h | h | h
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
    · rintro r ((a | a) | i | i)
      · exact (congrFun (congrFun ec r) (Sum.inl a)).symm.trans (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun ec r) (Sum.inr a)).symm))
      · exact fX i r
      · exact fY i r
    · rintro ((a | a) | i | i)
      · rfl
      · rfl
      · rfl
      · have := i.2
        simp only [GlobalTheory.RootEx.lev, wlev, Sum.elim_inr, Fin.val_rev, Fin.val_castLE]
        omega
  have hle : symR k (Fin A.rank) (2 * σ + 1) ≤ (besGrp dd o).comap Φ := by
    rw [symR, symN_odd]
    refine sup_le ?_ hN
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨h, hh⟩ := Witness.exists_isLoc p FA g₀
    have eA : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jA) = dd.j0 ⬝ o.jA ⬝ mt A h := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
    have eB : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jB) = dd.j0 ⬝ o.jB := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
    have eZ := map_fix p eB
    rw [Matrix.map_mul] at eZ
    have hm : p.IsLoc F (dd.emb0 (o.emb (h, 1))) (embX (2 * σ + 1) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding dd (suppAt_emb o hh.1), eq_embX F _ g₀ ((dd.j0 ⬝ o.jA).map p.π * FA.β) (fun r a => ?_)
        (intertwine p eA hh) fun j => ?_⟩
      · change ((frameMat B A d.ι).map φ * b) r a = _
        rw [Matrix.map_mul, jA]
      · rcases lt_trichotomy j.val σ with hj | hj | hj
        · exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (fX ⟨j.val, hj⟩)
        · obtain rfl : j = ⟨σ, hσ'⟩ := Fin.ext hj
          exact fix_col eZ _ (0 : Fin 1) fZ
        · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, j = (Fin.castLE hσ q).rev :=
            ⟨⟨2 * σ - j.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
          exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclY _)) _ q (fY q)
    change Φ _ ∈ besGrp _ _
    rw [isLoc_unique p (hΦ _) hm]
    exact Subgroup.mem_sup_right ⟨h, rfl⟩
  rw [isLoc_unique p hloc (hΦ x)]
  exact hle hx

end GlobalTheory.RowRepBes

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocMod

theorem mem_besGrp_of_symR {D : D7} {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D))
    (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank)
    (hb : b = B.rank) (hab : a + c = b) (p : Place D (Kw w)) (hp : piAt w = p.π) (g : GA D B) (hg : SuppAt p.e B g)
    (hx : frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c) :
    g ∈ besGrp (diagDec (besDec d h) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  rw [hp] at h1 h2 e
  exact mem_bes p d l hl (GlobalTheory.StdFrames.loc w β).mul_inv (GlobalTheory.StdFrames.loc w β).inv_mul h1 h2 hg (e g) hx

theorem mem_besGrp_of_locAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  intro D T L sc G W U S t ht w hw ew hew j σ hj hj' h' h hs hx
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.PlcAtW.exists_plc D w ew he
  exact mem_besGrp_of_symR (G.rowDec j hj') (by omega) _ _ w _ _ _ (S.row t ht w hw j hj') (topRank_eq G t w hj)
    (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ p (RingHom.ext fun x => (hp.2.1 x).symm) h hs hx

end GlobalTheory.RowRepBes

end
