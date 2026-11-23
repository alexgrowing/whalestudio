import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RescOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemEMulIdemE

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def frameAt {N : ℕ} (π' : EAf D →+* k) (β : GL (Fin N) (EAf D)) : GlobalTheory.LocMod.Frame k N (Fin N) where
  β := β.val.map π'
  γ := (β⁻¹).val.map π'
  βγ := by rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  γβ := by rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

variable {S T : HSp D} (q : GlobalTheory.FinPl.SplitPt D k) {π' : EAf D →+* k}
  (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem down_eq (hπ : ∀ a, π' (toEAf D a) = q.pr a) (x : WO S T) :
    (ofSplit q).down (frameAt π' βS) (frameAt π' βT) x = (frMapO S T βS βT x).map π' := by
  have h2 : ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D)).map π' = x.map q.pr := Matrix.ext fun i j => hπ _
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h2]
  rfl

theorem up_down {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (t : WO S T) :
    p.up FS FT (p.down FS FT t) = p.e • t := by
  unfold Place.up Place.down
  have : FT.β * (FT.γ * (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π * FS.β) * FS.γ = t.map p.π := by
    simp only [← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rw [Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
  rw [this]
  exact Matrix.ext fun i j => p.ι_π _

theorem down_up {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (p : Place D k)
    (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (x : Matrix Y Y' k) :
    p.down FS FT (p.up FS FT x) = x := by
  unfold Place.up Place.down
  have : ((FT.β * x * FS.γ).map p.ι : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map p.π = FT.β * x * FS.γ :=
    Matrix.ext fun i j => p.π_ι _
  rw [this]
  simp only [← Matrix.mul_assoc, FT.γβ, Matrix.one_mul]
  rw [Matrix.mul_assoc, FS.γβ, Matrix.mul_one]

theorem frMapO_smul (a : AE D) (x : WO S T) (i : Fin T.rank) (j : Fin S.rank) :
    frMapO S T βS βT (a • x) i j = toEAf D a * frMapO S T βS βT x i j := by
  have : (a • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D a • x.map (toEAf D) :=
    Matrix.ext fun i j => (toEAf D).map_mul _ _
  exact (congrArg (fun z => GlobalTheory.FunObj.Comparison₂.fr βT βS z i j) this).trans
    (congrFun (congrFun (GlobalTheory.FunObj.Comparison₂.fr_smul βT βS _ _) i) j)

theorem smul_mem_at {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {x : WO S T}
    (hx : x ∈ latO S T LS LT fun _ => True) : q.e • x ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, hε, h⟩ := q.above
  have h1 : IsPlaceIdem D q.v (pairA _ 0 (GlobalTheory.VacUnion.idemF q.v)) :=
    ⟨_, rfl, by rw [GlobalTheory.VacUnion.evalV_idemF, if_pos rfl], fun w hw => by rw [GlobalTheory.VacUnion.evalV_idemF, if_neg hw]⟩
  have h2 : GlobalTheory.VacUnion.idemE q.v = q.e + cA D q.e := by
    rw [h, GlobalTheory.IdemSupport.placeIdem_unique hε h1]; rfl
  have h3 := GlobalTheory.VacUnion.idemE_smul_mem q.v (GlobalTheory.PlaceModelSum.idem_smul_latO q.split.1 hx)
  have h4 : GlobalTheory.VacUnion.idemE q.v * q.e = q.e := by
    rw [h2]
    linear_combination q.split.1 + q.split.2.1
  rwa [smul_smul, h4] at h3

theorem latO_le_top {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, k⟩ => ⟨α, hα, fun _ hw => (hw trivial).elim, k⟩

theorem eq_sum {r : ℕ} {a : Fin r → AE D} {pl : Fin r → Formalism.L2.DIV.Pl D.host.E} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D}
    (ha : ∀ i, Formalism.L2.NTheta.IsIdemAt (a i) (pl i)) (hinj : Function.Injective pl) (hQ : ∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP)
    (he : IsIdemSum e Q) : e = ∑ i, a i := by
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  refine (Finset.sum_bij (fun i _ => pl i) (fun i _ => (hQ _).2 ⟨i, rfl⟩) (fun i _ j _ h => hinj h)
    (fun PP hPP => by obtain ⟨i, hi⟩ := (hQ PP).1 hPP; exact ⟨i, Finset.mem_univ _, hi⟩) fun i _ => ?_).symm
  exact GlobalTheory.IdemSupport.delta_unique hΦ (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (ha i))
    (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (h1 _ ((hQ _).2 ⟨i, rfl⟩)))

theorem isIntM_iff_mem_latO : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D r k _ _ _ _ q pl Q e hq hu hinj hQ he S T LS LT hS hT βS βT hβ x hx
  choose π' hπ hrest using fun i => GlobalTheory.FinPl.SplitPt.exists_lift_isRed D (k i) (q i) (pl i) (hq i)
  have hint := fun i => (hrest i).2.1
  have he' : e = ∑ i, (q i).e := eq_sum hq hinj hQ he
  have hxe : e • x = x := Matrix.ext fun i j => hx i j
  constructor
  · intro h
    rw [← hxe, he', Finset.sum_smul]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    have h1 := GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
      (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 ((frMapO S T βS βT x).map (π' i)) fun a b => ((hint i _).1 (h a b)).2
    rw [← down_eq (q i) βS βT (hπ i), up_down] at h1
    exact latO_le_top h1
  · intro h a b
    rw [← hxe, frMapO_smul, he', GlobalTheory.FunObj.Comparison₂.hom_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun i _ => (hint i _).2 ⟨?_, ?_⟩
    · rw [← mul_assoc, sub_mul, one_mul, ← RingHom.map_mul, (q i).split.1, sub_self, zero_mul]
      exact zero_mem _
    · obtain ⟨y, hy, h1⟩ := GlobalTheory.T.exists_integral_matrix_up_image_completed_hom_lattice D (k i) (q i) (hu i) _ _ S T (frameAt (π' i) βS) (frameAt (π' i) βT) LS LT hS hT
        (hβ i _ (hπ i)).1 (hβ i _ (hπ i)).2 _ (smul_mem_at (q i) h)
        (fun a b => by
          change (q i).e * ((q i).e * _) = (q i).e * _
          rw [← mul_assoc, (q i).split.1])
      have h2 := down_eq (q i) βS βT (hπ i) ((q i).e • x)
      rw [h1, down_up, ← h1] at h2
      rw [← frMapO_smul]
      have h3 := hy a b
      rw [h2] at h3
      exact h3

end GlobalTheory.HalfInt

end
