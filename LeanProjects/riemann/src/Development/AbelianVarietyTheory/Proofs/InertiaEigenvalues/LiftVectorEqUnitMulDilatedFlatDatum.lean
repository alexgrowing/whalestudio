import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVectorIsThetaFunctionTwoStepModelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeHalfIffFrameMatrixIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixIntegralIffUniformiserMultipleOnHalfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfUniformiserFrameMatrixPrescribedReductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNatIntegralFrameOfUniformizerMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SymplecticPairingHalfLatticesEqProdPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueTwistFactorEqUnitMulFlatFourierStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.LiftFlatModel

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem isIntM_add {b a : ℕ} {N M : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (hM : IsIntM M) :
    IsIntM (N + M) := fun i j => by rw [Matrix.add_apply]; exact add_mem (hN i j) (hM i j)

theorem isIntM_neg {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) : IsIntM (-N) :=
  fun i j => by rw [Matrix.neg_apply]; exact neg_mem (hN i j)

theorem frMapO_add (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapO S T βS βT (x + y) = frMapO S T βS βT x + frMapO S T βS βT y := by
  unfold frMapO
  rw [Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

theorem frMapO_neg (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    frMapO S T βS βT (-x) = -frMapO S T βS βT x := by
  unfold frMapO
  rw [Matrix.map_neg (toEAf D) (fun a => (toEAf D).map_neg a), Matrix.mul_neg, Matrix.neg_mul]

theorem redM_add (PP : Pl D.host.E) {b a : ℕ} {M N : Matrix (Fin b) (Fin a) (EAf D)} (hM : IsIntM M) (hN : IsIntM N) :
    redM PP (M + N) = redM PP M + redM PP N := by
  funext i j
  have h2 : (M + N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := add_mem (hM i j) (hN i j)
  rw [Matrix.add_apply]
  unfold redM
  rw [dif_pos h2, dif_pos (hM i j), dif_pos (hN i j), ← RingHom.map_add]
  rfl

theorem redM_neg (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) :
    redM PP (-N) = -redM PP N := by
  funext i j
  have h2 : (-N) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := neg_mem (hN i j)
  rw [Matrix.neg_apply]
  unfold redM
  rw [dif_pos h2, dif_pos (hN i j), ← RingHom.map_neg]
  rfl

theorem omegaFlat_congr {a b : ℕ} (Q : Finset (Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {y y' : ∀ PP : Pl D.host.E, Matrix (Fin a) (Fin b) (kP PP)} (h : ∀ PP ∈ Q, y PP = y' PP) :
    omegaFlat Q r ξ y = omegaFlat Q r ξ y' := by
  have hiff : (∀ PP ∈ Q, IsUnit (topL r (y PP)).det) ↔ ∀ PP ∈ Q, IsUnit (topL r (y' PP)).det :=
    forall_congr' fun PP => forall_congr' fun hPP => by rw [h PP hPP]
  unfold omegaFlat
  by_cases h1 : ∀ PP ∈ Q, IsUnit (topL r (y PP)).det
  · rw [dif_pos h1, dif_pos (hiff.1 h1)]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : (h1 PP.1 PP.2).unit = (hiff.1 h1 PP.1 PP.2).unit :=
      Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h PP.1 PP.2])
    rw [e]
  · rw [dif_neg h1, dif_neg fun h2 => h1 (hiff.2 h2)]

end GlobalTheory.LiftFlatModel

namespace GlobalTheory.LiftFlatModel

variable {D : D7} {m n : ℕ}

theorem isHalf_add_iff {e : AE D} {x u : Mx D m n} (hu : IsHalf e u) : IsHalf e (x + u) ↔ IsHalf e x := by
  constructor
  · intro h i j
    have h1 := h i j
    have h2 := hu i j
    simp only [Matrix.add_apply, mul_add] at h1
    rw [h2] at h1
    exact add_right_cancel h1
  · intro h i j
    simp only [Matrix.add_apply, mul_add, h i j, hu i j]

theorem isHalf_neg {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := by
  intro i j
  simp only [Matrix.neg_apply, mul_neg, hu i j]

theorem isHalf_nsmul {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) := by
  induction k with
  | zero => rw [zero_nsmul]; exact fun i j => mul_zero e
  | succ k ih => rw [succ_nsmul]; exact (isHalf_add_iff hu).2 ih

set_option maxHeartbeats 1000000 in

theorem isSBHalf_of_sum {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Ψ : Mx D m n → ℂ} {Rs : Finset (Mx D m n)}
    {c : Mx D m n → ℂ} (hR : ∀ u ∈ Rs, IsHalf e u) (hΨ : ∀ x, Ψ x = ∑ u ∈ Rs, c u * halfInd e Λ (x + u))
    (hk : ∃ k : ℕ, 0 < k ∧ ∀ u ∈ Rs, k • u ∈ Λ) : IsSBHalf e Λ Ψ := by
  obtain ⟨k, hk0, hkR⟩ := hk
  have hne : ∀ x, Ψ x ≠ 0 → ∃ u ∈ Rs, x + u ∈ Λ ∧ IsHalf e (x + u) := by
    intro x hx
    rw [hΨ x] at hx
    obtain ⟨u, hu, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    refine ⟨u, hu, ?_⟩
    by_contra hc
    apply hne
    simp [halfInd, hc]
  refine ⟨fun x hx => ?_, k, hk0, fun v hv hve x => ?_, fun x hx => ?_⟩
  · obtain ⟨u, hu, -, hh⟩ := hne x hx
    exact (isHalf_add_iff (hR u hu)).1 hh
  · rw [hΨ, hΨ]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hkv : k • v ∈ Λ := AddSubgroup.nsmul_mem Λ hv k
    have hkh : IsHalf e (k • v) := isHalf_nsmul hve k
    have e1 : x + k • v + u = (x + u) + k • v := by abel
    have e2 : (x + u + k • v ∈ Λ ∧ IsHalf e (x + u + k • v)) ↔ (x + u ∈ Λ ∧ IsHalf e (x + u)) :=
      and_congr (Λ.add_mem_cancel_right hkv) (isHalf_add_iff hkh)
    rw [e1]
    unfold halfInd
    rw [if_congr e2 rfl rfl]
  · obtain ⟨u, hu, hl, -⟩ := hne x hx
    have h1 : k • (x + u) ∈ Λ := AddSubgroup.nsmul_mem Λ hl k
    rw [nsmul_add] at h1
    exact (Λ.add_mem_cancel_right (hkR u hu)).1 h1

theorem placeModel_sum {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f₀ : Mx D m n → ℂ}
    {Tm : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)} (hT : IsPlaceModel ψ B hs e Λ 1 f₀ Tm) {Ψ : Mx D m n → ℂ}
    {Rs : Finset (Mx D m n)} {c : Mx D m n → ℂ} (hR : ∀ u ∈ Rs, IsHalf e u)
    (hΨ : ∀ x, Ψ x = ∑ u ∈ Rs, c u * halfInd e Λ (x + u)) : Tm Ψ = ∑ u ∈ Rs, c u • hs u f₀ := by
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hT.vac
  have hΨ' : Ψ = ∑ u ∈ Rs, c u • fun x => halfInd e Λ (x + u) := by
    funext x
    rw [hΨ x, Finset.sum_apply]
    rfl
  rw [hΨ', map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, hT.trans _ (GlobalTheory.isSBHalf_halfInd e Λ) u (hR u hu), hvac]

theorem thetaAt_sum {ψ : AddChar (AF D.host.F) ℂ} {B : Mx D m n → Mx D m n → AF D.host.F}
    {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {f₀ Φ f : Mx D m n → ℂ}
    (hθ : IsThetaAt ψ B hs e Λ 1 f₀ Φ f) {Y : Finset (Mx D m n)} {a : Mx D m n → ℂ} (hY : ∀ y ∈ Y, IsHalf (cA D e) y)
    (hΦ : ∀ t, Φ t = halfInd e Λ t * ∑ y ∈ Y, a y * ψ (B t y)) : f = ∑ y ∈ Y, a y • hs y f₀ := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hΦ' : Φ = ∑ y ∈ Y, a y • fun t => ψ (B t y) * halfInd e Λ t := by
    funext t
    rw [hΦ t, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac
  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) y (hY y hy), hvac]

end GlobalTheory.LiftFlatModel

namespace GlobalTheory.LiftFlatModel

set_option maxHeartbeats 2000000 in

theorem exists_reps_pairing : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eQ : AE D), IsIdemSum eQ (R.Q t) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (Rs : Finset (WO (Vc D i) (Wc D i))), (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ (∀ u ∈ Rs, IsHalf eQ u ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w))) ∧ (∃ k : ℕ, 0 < k ∧ ∀ u ∈ Rs, k • u ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) ∧ (∀ y : ∀ PP : ↥(R.Q t), Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1), ∃! u, u ∈ Rs ∧ ∀ PP : ↥(R.Q t), redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)) = y PP) ∧ (∀ x, IsHalf eQ x → ∀ u ∈ Rs, (x + u ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) = -redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)))) ∧ (∀ x, IsHalf (cA D eQ) x → (x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))) ∧ (∀ x, IsHalf (cA D eQ) x → IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) → ∀ u ∈ Rs, R.ψ (symplO (Vc D i) (Wc D i) x u) = ∏ PP ∈ (R.Q t).attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV eQ heQ ϖ hϖ0 hϖ
  obtain ⟨cV, hcV⟩ := hC.lev.βV i
  obtain ⟨cW, hcW⟩ := hC.lev.βW i
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  have hP := hQG.2 t
  have hfr := GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1 (R.Q t) eQ heQ hP
  have hker := GlobalTheory.T.frameMatrix_integral_iff_uniformiser_multiple_on_half D (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.Q t) eQ heQ ϖ hϖ0 hϖ
  obtain ⟨k, hk0, hk⟩ := GlobalTheory.T.exists_nat_integral_frame_of_uniformizer_mul D (Vc D i) (Wc D i) (R.βV i) (R.βW i) ϖ hϖ0
  obtain ⟨ψP, hprim, hpair⟩ := GlobalTheory.T.symplectic_pairing_half_lattices_eq_prod_primitive D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) hψ sV sW hcV.1 hcW.1
    (R.Q t) eQ heQ hP ϖ hϖ0 hϖ
  choose g hg1 hg2 hg3 using fun y : ∀ PP : ↥(R.Q t), Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP.1) =>
    GlobalTheory.T.exists_half_uniformiser_frameMatrix_prescribed_reductions D (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.Q t) eQ heQ ϖ hϖ0 (fun PP => if h : PP ∈ R.Q t then y ⟨PP, h⟩ else 0)
  have hg4 : ∀ y (PP : ↥(R.Q t)), redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
      ((g y).map fun w => incA D (ϖ : D.host.E) * w)) = y PP := fun y PP => by
    rw [hg3 y PP.1 PP.2, dif_pos PP.2]
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  have hmem : ∀ u ∈ Finset.univ.image g, IsHalf eQ u ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
      (u.map fun w => incA D (ϖ : D.host.E) * w)) := by
    intro u hu
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨hg1 y, hg2 y⟩
  refine ⟨ψP, Finset.univ.image g, hprim, hmem, ⟨k, hk0, fun u hu => ?_⟩, fun y => ?_, fun x hx u hu => ?_,
    fun x hx => ⟨fun h => ?_, fun h => ?_⟩, fun x hx hi u hu => hpair x hx hi u (hmem u hu).1 (hmem u hu).2⟩
  · exact (hfr _ (isHalf_nsmul (hmem u hu).1 k)).2 (hk u (hmem u hu).2)
  · refine ⟨g y, ⟨Finset.mem_image_of_mem g (Finset.mem_univ y), hg4 y⟩, ?_⟩
    rintro u ⟨hu, hred⟩
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hu
    have : y' = y := funext fun PP => (hg4 y' PP).symm.trans (hred PP)
    rw [this]
  · have hxu : IsHalf eQ (x + u) := (isHalf_add_iff (hmem u hu).1).2 hx
    have e1 : ((x + u).map fun w => incA D (ϖ : D.host.E) * w) =
        (x.map fun w => incA D (ϖ : D.host.E) * w) + (u.map fun w => incA D (ϖ : D.host.E) * w) := by
      ext a b
      simp only [Matrix.map_apply, Matrix.add_apply, mul_add]
    rw [hfr _ hxu, hker _ hxu, e1, frMapO_add]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := isIntM_add h1 (isIntM_neg (hmem u hu).2)
      rw [add_neg_cancel_right] at h3
      refine ⟨h3, fun PP hPP => ?_⟩
      have h4 := h2 PP hPP
      rw [redM_add PP h3 (hmem u hu).2] at h4
      exact eq_neg_of_add_eq_zero_left h4
    · rintro ⟨h1, h2⟩
      refine ⟨isIntM_add h1 (hmem u hu).2, fun PP hPP => ?_⟩
      rw [redM_add PP h1 (hmem u hu).2, h2 PP hPP, neg_add_cancel]
  · exact GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1 (R.Q t) eQ heQ hP x h hx
  · exact GlobalTheory.T.idempotent_sum_self_dual_frames_bound D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) sV sW hcV.1 hcW.1 (R.Q t) eQ heQ hP x hx h

end GlobalTheory.LiftFlatModel

namespace GlobalTheory.LiftFlatModel

set_option maxHeartbeats 4000000 in

theorem lift_eq_model_flat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ R.Q t, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ Gc : ℂ, UnitOff (GlobalTheory.TwistField.tupPrime R t) Gc ∧ IsSBHalf eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) ∧ ∀ (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)), IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg Tm → R.vP i t = Tm (fun x => Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i t hV eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨ψP, Rs, hprim, hRs, hk, hbij, hiii, hiv, hv⟩ := exists_reps_pairing D G Pl0 T0 A Ks R F hC hQG i t hV eQ heQ ϖ hϖ0 hϖ
  have hN : 0 < GlobalTheory.TwistField.tupPrime R t := by
    unfold GlobalTheory.TwistField.tupPrime
    refine Finset.prod_pos fun q hq => ?_
    obtain ⟨PP, -, rfl⟩ := Finset.mem_image.1 hq
    exact Nat.card_pos
  letI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  obtain ⟨Gc, hGc, hfin⟩ := GlobalTheory.T.residueTwistFactor_eq_unit_mul_flat_fourier D (R.Q t) (R.xiR t) ψP (Wc D i).rank (Vc D i).rank (GlobalTheory.TwistField.tupPrime R t) hN
    (fun PP hPP => ⟨hprim PP hPP, GlobalTheory.ChainTw.RModel.xiR_ne R hC.lev t PP hPP,
      Finset.dvd_prod_of_mem (fun q : ℕ => q) (Finset.mem_image_of_mem (fun PP => Nat.card (kP PP)) hPP)⟩)
  have hE : (ϖ : D.host.E) ≠ 0 := fun h => hϖ0 (by exact_mod_cast h)
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hE).map (incA D)
  have F1 : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ↔ IsHalf eQ x := by
    intro x
    constructor
    · intro h a b
      have h1 := h a b
      simp only [Matrix.map_apply] at h1
      rw [mul_left_comm] at h1
      exact hu.mul_left_cancel h1
    · intro h a b
      simp only [Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have F2 : ∀ x : WO (Vc D i) (Wc D i), ((-x).map fun w => incA D (ϖ : D.host.E) * w) =
      -(x.map fun w => incA D (ϖ : D.host.E) * w) := by
    intro x
    ext a b
    simp [mul_neg]
  have hPsiNeg : ∀ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => if h : PP ∈ R.Q t then
        -((fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) ⟨PP, h⟩) else 0) := by
    intro u hu'
    have hh : IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) := by
      rw [F2]
      exact LiftFlatModel.isHalf_neg ((F1 u).2 (hRs u hu').1)
    have hi : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [F2, LiftFlatModel.frMapO_neg]
      exact LiftFlatModel.isIntM_neg (hRs u hu').2
    rw [if_pos ⟨hh, hi⟩]
    apply LiftFlatModel.omegaFlat_congr
    intro PP hPP
    rw [dif_pos hPP, F2, LiftFlatModel.frMapO_neg, redM_neg _ (hRs u hu').2]

  have hA : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    by_cases hx : IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w))
    · obtain ⟨u, ⟨huR, hured⟩, huniq⟩ := hbij (fun PP => -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
        (x.map fun w => incA D (ϖ : D.host.E) * w))))
      have hxh : IsHalf eQ x := (F1 x).1 hx.1
      rw [Finset.sum_eq_single u]
      · have hmem : x + u ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) :=
          (hiii x hxh u huR).2 ⟨hx.2, fun PP hPP => by rw [hured ⟨PP, hPP⟩, neg_neg]⟩
        have hhalf : IsHalf eQ (x + u) := (LiftFlatModel.isHalf_add_iff (hRs u huR).1).2 hxh
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 1 from
          if_pos ⟨hmem, hhalf⟩, mul_one, hPsiNeg u huR, if_pos hx]
        apply LiftFlatModel.omegaFlat_congr
        intro PP hPP
        rw [dif_pos hPP]
        show _ = -(redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (u.map fun w => incA D (ϖ : D.host.E) * w)))
        rw [hured ⟨PP, hPP⟩, neg_neg]
      · intro u' hu' hne
        rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u') = 0 from if_neg ?_,
          mul_zero]
        rintro ⟨hmem, -⟩
        obtain ⟨-, hred⟩ := (hiii x hxh u' hu').1 hmem
        exact hne (huniq u' ⟨hu', fun PP => by
          show _ = -(redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)))
          rw [hred PP.1 PP.2, neg_neg]⟩)
      · intro h
        exact absurd huR h
    · rw [if_neg hx]
      symm
      refine Finset.sum_eq_zero fun u hu' => ?_
      rw [show halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) = 0 from if_neg ?_,
        mul_zero]
      rintro ⟨hmem, hhalf⟩
      have hxh : IsHalf eQ x := (LiftFlatModel.isHalf_add_iff (hRs u hu').1).1 hhalf
      exact hx ⟨(F1 x).2 hxh, ((hiii x hxh u hu').1 hmem).1⟩
  have hB : ∀ x : WO (Vc D i) (Wc D i),
      (if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) =
      halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x *
        ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
          IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
          omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
            ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) * R.ψ (symplO (Vc D i) (Wc D i) x u) := by
    intro x
    by_cases hx : x ∈ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) ∧ IsHalf (cA D eQ) x
    · have hint := (hiv x hx.2).1 hx.1
      rw [if_pos ⟨hx.2, hint⟩, show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 1 from
        if_pos hx, one_mul, hfin, Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun u _ => fun PP : ↥(R.Q t) => redM PP.1 (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (u.map fun w => incA D (ϖ : D.host.E) * w))) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro a ha b hb hab
        exact (hbij _).unique ⟨ha, fun PP => rfl⟩ ⟨hb, fun PP => (congrFun hab PP).symm⟩
      · intro y _
        obtain ⟨u, ⟨hu', hred⟩, -⟩ := hbij y
        exact ⟨u, hu', funext hred⟩
      · intro u hu'
        rw [hPsiNeg u hu', hv x hx.2 hint u hu', ← Finset.univ_eq_attach]
        ring
    · rw [show halfInd (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) x = 0 from if_neg hx,
        zero_mul, if_neg]
      rintro ⟨hh, hint⟩
      exact hx ⟨(hiv x hh).2 hint, hh⟩
  have hθ := GlobalTheory.T.thetaLiftVector_isThetaFunction_twoStepModel D G Pl0 T0 A Ks R F hC hQG i t eg eQ fg heg heQ hfg
  have hvP := LiftFlatModel.thetaAt_sum hθ (fun u hu' => by rw [LiftFlatModel.cA_cA]; exact (hRs u hu').1) hB
  have hΨ : ∀ x : WO (Vc D i) (Wc D i), Gc * (if IsHalf eQ (x.map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (x.map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          (x.map fun w => incA D (ϖ : D.host.E) * w))) else 0) =
      ∑ u ∈ Rs, (Gc * (if IsHalf eQ ((-u).map fun w => incA D (ϖ : D.host.E) * w) ∧
        IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) ((-u).map fun w => incA D (ϖ : D.host.E) * w)) then
        omegaFlat (R.Q t) (Wc D i).rank (R.xiR t) (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
          ((-u).map fun w => incA D (ϖ : D.host.E) * w))) else 0)) *
        halfInd eQ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) (x + u) := by
    intro x
    rw [hA x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  refine ⟨Gc, hGc, LiftFlatModel.isSBHalf_of_sum (fun u hu' => (hRs u hu').1) hΨ hk, fun Tm hTm => ?_⟩
  rw [LiftFlatModel.placeModel_sum hTm (fun u hu' => (hRs u hu').1) hΨ]
  exact hvP

end GlobalTheory.LiftFlatModel
