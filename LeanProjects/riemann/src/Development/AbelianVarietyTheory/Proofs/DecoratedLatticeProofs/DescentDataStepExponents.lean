import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFiniteAdeleOfSplitPlaceComponentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionAtLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalGroupsMatrixReadingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem mt_mul {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : mt V a⁻¹ * mt V a = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem isHalf_mul {D : D7} {S T : HSp D} (e : AE D) (A : Matrix (Fin T.rank) (Fin T.rank) (AE D))
    (B : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (y : WO S T) (hy : IsHalf e y) :
    IsHalf e (HMul.hMul (HMul.hMul A (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) B : WO S T) := by
  intro i j
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    Matrix.ext fun i j => hy i j
  have := congrFun (congrFun (congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) => HMul.hMul (HMul.hMul A M) B) hy') i) j
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem isHalf_actO_iff {D : D7} (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    IsHalf e (actO S T g h x) ↔ IsHalf e x := by
  constructor
  · intro hx
    have e1 : x = actO S T g⁻¹ h⁻¹ (actO S T g h x) := by
      unfold actO
      rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc,
        mt_inv_mul, Matrix.mul_one]
    rw [e1]
    exact isHalf_mul e _ _ _ hx
  · intro hx
    exact isHalf_mul e _ _ _ hx

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}

theorem down_moved_actO (p : Place D k) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (g : GA D S) (h : GA D T) (x : WO S T) :
    p.down (moved p FS g⁻¹) (moved p FT h⁻¹) (actO S T g⁻¹ h⁻¹ x) = p.down FS FT x := by
  have hm : ∀ (V : HSp D) (a : GA D V), (mt V a⁻¹⁻¹).map p.π * (mt V a⁻¹).map p.π = 1 := fun V a => by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold Place.down moved actO
  simp only [Matrix.map_mul]
  have e1 : FT.γ * (mt T h⁻¹⁻¹).map p.π * ((mt T h⁻¹).map p.π * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
      (mt S g⁻¹⁻¹).map p.π) * ((mt S g⁻¹).map p.π * FS.β) =
      FT.γ * ((mt T h⁻¹⁻¹).map p.π * (mt T h⁻¹).map p.π) * (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π *
        ((mt S g⁻¹⁻¹).map p.π * (mt S g⁻¹).map p.π) * FS.β := by
    simp only [Matrix.mul_assoc]
  rw [e1, hm, hm, Matrix.mul_one, Matrix.mul_one]

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem phi_down_eq (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) {u : D.what₂.Word} (f : FamCh W u) (v : VCom f.c) (G0 : GLoc v)
    (π' : Formalism.IndefR.Datum.EAf D →+* G0.k) (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) (j a : ℕ) (ha : j + a = G0.s)
    (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank)
    (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin (Yc D (j + 1)).rank)
    (mS : MovedTo (ofSplit G0.q) (Yc D j) (f.g.b j) ((pk W).βY j)
      (((G0.FY j (a + 1) (by omega)).β * ((G0.S.T (Fin D.R.t)).bas j (a + 1) (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega) (ea.symm i)))
    (mT : MovedTo (ofSplit G0.q) (Yc D (j + 1)) (f.g.b (j + 1)) ((pk W).βY (j + 1))
      (((G0.FY (j + 1) a (by omega)).β * ((G0.S.T (Fin D.R.t)).bas (j + 1) a (by omega)).val).submatrix id
        fun i => stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega) (eb.symm i)))
    (x : WO (Yc D j) (Yc D (j + 1))) :
    ((G0.S.T (Fin D.R.t)).Phi j a ha ((ofSplit G0.q).down (G0.FY j (a + 1) (by omega)) (G0.FY (j + 1) a (by omega)) x)) =
      G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j
        (((frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1))
          (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)).map π').submatrix eb ea) := by
  have hS := map_eq_of_movedTo (ofSplit G0.q) (G0.FY j (a + 1) (by omega)) hπ _ _ mS
  have hT := map_eq_of_movedTo (ofSplit G0.q) (G0.FY (j + 1) a (by omega)) hπ _ _ mT
  have key := coords_down (ofSplit G0.q) _ _ hπ (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) j (a + 1) (by omega)))
    (typeFrame G0.S.ϖ (stdOrd (Fin D.R.k) (Fin D.R.t) (j + 1) a (by omega))) ea eb hS hT
    (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)
  rw [down_moved_actO] at key
  rw [← key]
  rfl

end GlobalTheory.MovedDat

namespace GlobalTheory.MovedDat

theorem moved_datum_eq_prod : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B) ((pk W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hP hRow v hv hVT n G pl hGP hGR j hj a ha
  refine ⟨1, one_ne_zero, fun x => ?_⟩
  rw [one_mul, isHalf_actO_iff]
  choose π' hπ hred hint hres using fun i => GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D (G i).k (G i).q (pl i).1 (hGR.idem i).1
  choose ea hea mS using fun i => hGR.frame i j (a i + 1) (by have := ha i; omega)
  choose eb heb mT using fun i => hGR.frame i (j + 1) (a i) (by have := ha i; omega)
  have hC := fun i => phi_down_eq D L hT Gi Gl Kc Yd cX ex W f v (G i) (π' i) (hπ i) j (a i) (ha i) (ea i) (eb i) (mS i) (mT i) x
  by_cases hx : IsHalf (∑ i, (G i).q.e) x
  · rw [if_pos hx]
    have hx' := (isHalf_actO_iff _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ _ x).2 hx
    have hQ : ∀ y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin (Yc D (j + 1)).rank) (Fin (Yc D j).rank) (Formalism.L2.DIV.kP PP),
        omegaQ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) (datY _ D.R.r D.R.t j (r_le_Y j) (pk W).Pg ∅ (lvP W) (pk W).chi
          (fun _ => 1) Frm.B).r (fun _ => 1) 1 y = 1 := fun y => by
      rw [omegaQ, dif_pos (by simp)]; simp
    by_cases hI : IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((pk W).βY j) ((pk W).βY (j + 1))
      (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))
    · rw [if_pos ⟨hx, hI⟩, hQ, mul_one, GlobalTheory.T.local_groups_matrix_reading D L hT Gi Gl Kc Yd cX ex W u f v n G pl hGR j]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hC i, GlobalTheory.LocMod.StepVec.redM_eq_map (pl i).1 hI, GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum D f.c v (G i) (pl i).1 (π' i) (hπ i) (hred i) (pk W).chi j
        (fun c hc => GlobalTheory.T.reduction_at_level_place D L hT Gi Gl Kc Yd cX ex W hP (G i).k (G i).q (pl i).1 (pl i).2 (hGR.idem i).1 (π' i) (hπ i) (hred i)
          (c + 1) (by omega) (by omega) _ ((G i).S.tame _) (hGR.mu i (c + 1) (by omega) (by omega)))
        _ _ (r_le_Y j) (ea i) (eb i) (hea i) (heb i)]
      rfl
    · rw [if_neg (fun h => hI h.2)]
      symm
      by_contra hne
      apply hI
      have hnz := fun i h => hne (Finset.prod_eq_zero (Finset.mem_univ i) h)
      intro r s
      refine GlobalTheory.T.integral_finiteAdele_of_split_place_components D n (fun i => (G i).k) (fun i => (G i).q) (fun i => (pl i).1) (fun i => (hGR.idem i).1)
        (fun i l h => pl.injective (Subtype.ext h)) π' hπ hint _ ?_ fun i => ?_
      · rw [← GlobalTheory.LocMod.StepVec.frMapO_smul]
        congr 1
        exact Matrix.ext fun r' s' => hx' r' s'
      · have h1 := hnz i
        rw [hC i] at h1
        have h2 := GlobalTheory.StepData.TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ _ j).symm ((eb i).symm r)) ((ea i).symm s)
        simpa using h2
  · rw [if_neg (fun h => hx h.1), if_neg hx]

end GlobalTheory.MovedDat

end
