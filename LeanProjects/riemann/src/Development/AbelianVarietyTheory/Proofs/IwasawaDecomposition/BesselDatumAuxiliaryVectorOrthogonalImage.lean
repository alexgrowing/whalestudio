import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

def exF (d : BesselDatum A B ι) (ε : AE D) (i : Fin (d.ρ + 1)) (m : Measure (d.Ex ε i)) (β : GA D B → ℂ) :
    GA D B → ℂ := fun g => ∫ u, β ((u : GA D B) * g) ∂m

def toPosF (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ) (β : GA D B → ℂ) : GA D B → ℂ :=
  ((List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1)).foldr (fun i β' => exF d ε i (m i) β') β

def moveF (P : PosDatum A B ι) (β : GA D B → ℂ) : GA D B → ℂ :=
  (List.finRange P.n).foldr (fun a β' => toPosF P.bes (P.ε a) (P.m a) (P.p a) β') β

def Lvl (β : GA D B → ℂ) : Prop :=
  ∃ U : Subgroup (GA D B), IsOpen (U : Set (GA D B)) ∧ ∀ k ∈ U, k ∈ GfC B → ∀ g, β (g * k) = β g

def Eqv (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D) (β : GA D B → ℂ) : Prop :=
  ∀ n ∈ d.N, SuppAt ε B n → ∀ g, β (n * g) = d.psiN ψ n * β g

def IsK (B : HSp D) (v y : Fin B.rank → AE D) (k : GA D B) : Prop :=
  ∀ x, (mt B k).mulVec x = x + hA B x y • v - hA B x v • y

def iA (ι : A.V →ₗ[D.host.E] B.V) (t : Fin A.rank → AE D) : Fin B.rank → AE D :=
  ((frameMat B A ι).map (incA D)).mulVec t

def dual (d : BesselDatum A B ι) : Fin (d.ρ + 1) → B.V :=
  Fin.snoc (α := fun _ => B.V) d.f ((B.hD d.z d.z)⁻¹ • d.z)

def ExGe (d : BesselDatum A B ι) (ε : AE D) (p : ℕ) : Subgroup (GA D B) :=
  Subgroup.closure (⋃ l : Fin (d.ρ + 1), ⋃ _ : p ≤ l.1, d.ExSet ε l)

theorem rTr_rTr (u g : GA D B) (F : GA D B → ℂ) : rTr B u (rTr B g F) = rTr B (u * g) F := by
  funext x; simp only [rTr, mul_assoc]

theorem rTr_one (F : GA D B → ℂ) : rTr B 1 F = F := by funext x; simp only [rTr, mul_one]

theorem toPos_rTr (d : BesselDatum A B ι) (ε : AE D) (m : ∀ i, Measure (d.Ex ε i)) (p : ℕ)
    (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => d.toPos ε m p b (rTr B g F)) = toPosF d ε m p fun g => b (rTr B g F) := by
  unfold BesselDatum.toPos toPosF
  induction (List.finRange (d.ρ + 1)).filter fun i => decide (p ≤ i.1) with
  | nil => rfl
  | cons i l ih =>
    funext g
    simp only [List.foldr_cons, BesselDatum.exch, exF, ← ih, rTr_rTr]

theorem move_rTr (P : PosDatum A B ι) (b : (GA D B → ℂ) → ℂ) (F : GA D B → ℂ) :
    (fun g => P.move b (rTr B g F)) = moveF P fun g => b (rTr B g F) := by
  unfold PosDatum.move moveF
  induction List.finRange P.n with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ← ih, toPos_rTr]

theorem cA_cA (a : AE D) : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a

theorem mt_inj {g h : GA D B} (e : mt B g = mt B h) : g = h := Subtype.ext (Units.ext e)

theorem mt_ext {g h : GA D B} (e : ∀ x, (mt B g).mulVec x = (mt B h).mulVec x) : g = h :=
  mt_inj (Matrix.mulVec_injective (funext e))

theorem mulVec_mul (g h : GA D B) (x) : (mt B (g * h)).mulVec x = (mt B g).mulVec ((mt B h).mulVec x) := by
  rw [mt_mul, Matrix.mulVec_mulVec]

theorem mulVec_inv_cancel (g : GA D B) (x) : (mt B g⁻¹).mulVec ((mt B g).mulVec x) = x := by
  rw [← mulVec_mul, inv_mul_cancel, mt_one, Matrix.one_mulVec]

theorem mulVec_cancel_inv (g : GA D B) (x) : (mt B g).mulVec ((mt B g⁻¹).mulVec x) = x := by
  rw [← mulVec_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]

theorem hA_eq (x y : Fin B.rank → AE D) : hA B x y = (fun i => cA D (y i)) ⬝ᵥ (B.gram.map (incA D)).mulVec x := by
  simp only [hA, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem hA_herm (x y : Fin B.rank → AE D) : cA D (hA B x y) = hA B y x := by
  simp only [hA, map_sum, RingHom.map_mul, cA_inc, cA_cA, GlobalTheory.LatVac.gram_star]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem hA_add_right (x y y' : Fin B.rank → AE D) : hA B x (y + y') = hA B x y + hA B x y' := by
  simp only [hA, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hA_neg (x y : Fin B.rank → AE D) : hA B (-x) y = -hA B x y := by
  simp only [hA, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hA_neg_right (x y : Fin B.rank → AE D) : hA B x (-y) = -hA B x y := by
  simp only [hA, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hA_sub (x x' y : Fin B.rank → AE D) : hA B (x - x') y = hA B x y - hA B x' y := by
  rw [sub_eq_add_neg, hA_add, hA_neg, ← sub_eq_add_neg]

theorem hA_sub_right (x y y' : Fin B.rank → AE D) : hA B x (y - y') = hA B x y - hA B x y' := by
  rw [sub_eq_add_neg, hA_add_right, hA_neg_right, ← sub_eq_add_neg]

theorem hA_zero (y : Fin B.rank → AE D) : hA B 0 y = 0 := by simp [hA]

theorem hA_zero_right (x : Fin B.rank → AE D) : hA B x 0 = 0 := by simp [hA]

theorem hA_mt (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) ((mt B g).mulVec y) = hA B x y := by
  have hg : ((mt B g).map (cA D))ᵀ * B.gram.map (incA D) * mt B g = B.gram.map (incA D) := g.2
  have e : (fun i => cA D ((mt B g).mulVec y i)) = ((mt B g).map (cA D)).mulVec fun i => cA D (y i) :=
    funext fun i => RingHom.map_mulVec (cA D) _ y i
  rw [hA_eq, hA_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]

theorem hA_mt_left (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B ((mt B g).mulVec x) y = hA B x ((mt B g⁻¹).mulVec y) := by
  rw [← hA_mt g x, mulVec_cancel_inv]

theorem hA_nondeg {x : Fin B.rank → AE D} (h : ∀ y, hA B x y = 0) : x = 0 := by
  have hu : IsUnit (B.gram.map (incA D)) := (GlobalTheory.BesselCompare.gram_isUnit B).map (incA D).mapMatrix
  refine Matrix.mulVec_injective_of_isUnit hu ?_
  rw [Matrix.mulVec_zero]
  funext i
  have := h (Pi.single i 1)
  rw [hA_eq, show (fun j => cA D ((Pi.single i 1 : Fin B.rank → AE D) j)) = Pi.single i 1 from
    funext fun j => by by_cases e : j = i <;> simp [e], single_one_dotProduct] at this
  exact this

theorem suppAt_iff {ε : AE D} {g : GA D B} : SuppAt ε B g ↔ (ε + cA D ε) • (mt B g - 1) = mt B g - 1 :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem suppAt_iff_vec {ε : AE D} {g : GA D B} :
    SuppAt ε B g ↔ ∀ x, (ε + cA D ε) • ((mt B g).mulVec x - x) = (mt B g).mulVec x - x := by
  rw [suppAt_iff]
  refine ⟨fun h x => ?_, fun h => Matrix.mulVec_injective (funext fun x => ?_)⟩
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using congrArg (· *ᵥ x) h
  · simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using h x

theorem suppAt_one (ε : AE D) : SuppAt ε B 1 := by
  rw [suppAt_iff, mt_one, sub_self, smul_zero]

theorem suppAt_mul {ε : AE D} {g h : GA D B} (hg : SuppAt ε B g) (hh : SuppAt ε B h) : SuppAt ε B (g * h) := by
  have e : mt B (g * h) - 1 = (mt B g - 1) * mt B h + (mt B h - 1) := by
    rw [mt_mul, Matrix.sub_mul, Matrix.one_mul, sub_add_sub_cancel]
  rw [suppAt_iff, e, smul_add, ← Matrix.smul_mul, suppAt_iff.1 hg, suppAt_iff.1 hh]

theorem suppAt_inv {ε : AE D} {g : GA D B} (hg : SuppAt ε B g) : SuppAt ε B g⁻¹ := by
  have h := suppAt_iff.1 hg
  have h1 : mt B g⁻¹ - 1 = (mt B g - 1) * (-mt B g⁻¹) := by
    rw [Matrix.mul_neg, Matrix.sub_mul, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mul, neg_sub]
  rw [suppAt_iff, h1, ← Matrix.smul_mul, h]

def suppGrp (ε : AE D) (B : HSp D) : Subgroup (GA D B) where
  carrier := {g | SuppAt ε B g}
  one_mem' := suppAt_one ε
  mul_mem' := suppAt_mul
  inv_mem' := suppAt_inv

theorem suppAt_of_mem_Ex {d : BesselDatum A B ι} {ε : AE D} {i} {g : GA D B} (hg : g ∈ d.Ex ε i) : SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2 (fun _ h => h.1) hg

theorem suppAt_of_mem_ExGe {d : BesselDatum A B ι} {ε : AE D} {p} {g : GA D B} (hg : g ∈ ExGe d ε p) :
    SuppAt ε B g :=
  (Subgroup.closure_le (suppGrp ε B)).2
    (Set.iUnion_subset fun _ => Set.iUnion_subset fun _ _ h => h.1) hg

theorem Ex_le_ExGe (d : BesselDatum A B ι) (ε : AE D) {p : ℕ} {i : Fin (d.ρ + 1)} (h : p ≤ i.1) :
    d.Ex ε i ≤ ExGe d ε p :=
  Subgroup.closure_mono fun _ hg => Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨h, hg⟩⟩

theorem mem_GfC {e : AE D} (he : IsSplitIdem D e) {g : GA D B} (hg : SuppAt e B g) : g ∈ GfC B := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt B g - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add, GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt B g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

theorem commute_of_apart {ε ε' : AE D} (h : (ε + cA D ε) * (ε' + cA D ε') = 0) {g g' : GA D B}
    (hg : SuppAt ε B g) (hg' : SuppAt ε' B g') : g * g' = g' * g := by
  have h1 : (mt B g - 1) * (mt B g' - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]
  have h2 : (mt B g' - 1) * (mt B g - 1) = 0 := by
    rw [← suppAt_iff.1 hg, ← suppAt_iff.1 hg', Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm, h, zero_smul]
  refine mt_inj ?_
  rw [mt_mul, mt_mul]
  have : mt B g * mt B g' - mt B g' * mt B g = (mt B g - 1) * (mt B g' - 1) - (mt B g' - 1) * (mt B g - 1) := by
    noncomm_ring
  rw [h1, h2, sub_zero, sub_eq_zero] at this
  exact this

theorem hA_iA (hι : HSpace.IsIsomEmb A B ι) (s t : Fin A.rank → AE D) : hA B (iA ι s) (iA ι t) = hA A s t := by
  have e : ∀ s, iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := fun s => by
    rw [iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec]
  have e2 : ∀ l, hA B (vecA B (ι (A.frame l))) (iA ι t) = ∑ k, cA D (t k) * incA D (A.gram k l) := fun l => by
    rw [← hA_herm, e, GlobalTheory.BesselCompare.hA_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec]
    congr 2
    exact hι _ _
  rw [e s, GlobalTheory.BesselCompare.hA_sum]
  simp only [hA_smul, e2]
  rw [hA, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem hA_vec_iA {v : B.V} (h : ∀ x, B.hD v (ι x) = 0) (t : Fin A.rank → AE D) : hA B (vecA B v) (iA ι t) = 0 := by
  rw [← hA_herm, iA, GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.eMat_mulVec, GlobalTheory.BesselCompare.hA_sum, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [hA_smul, RingHom.map_mul, hA_herm, hA_vec, h, map_zero, mul_zero]

theorem iA_smul (a : AE D) (t : Fin A.rank → AE D) : iA ι (a • t) = a • iA ι t := Matrix.mulVec_smul _ _ _

theorem iA_add (s t : Fin A.rank → AE D) : iA ι (s + t) = iA ι s + iA ι t := Matrix.mulVec_add _ _ _

theorem iA_neg (t : Fin A.rank → AE D) : iA ι (-t) = -iA ι t := Matrix.mulVec_neg _ _

theorem besselDatum_auxiliaryVector_orthogonal_image (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (d.aux i) (ι x) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]; exact d.zA x
  · rw [Fin.snoc_castSucc]; exact d.eA j x

theorem dual_perp (d : BesselDatum A B ι) (i) (x : A.V) : B.hD (dual d i) (ι x) = 0 := by
  unfold dual
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    have := d.zA x
    unfold HSpace.hD at this ⊢
    rw [map_smul, this, smul_zero]
  · rw [Fin.snoc_castSucc]; exact d.fA j x

end GlobalTheory.RootExch

end
