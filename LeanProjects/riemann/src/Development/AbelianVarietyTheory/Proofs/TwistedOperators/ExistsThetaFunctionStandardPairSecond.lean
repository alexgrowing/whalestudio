import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.CompanionTheory.StdSndTheta

variable {D : D7}

local notation "OO" => Formalism.L2.Herm.intAf D.host.F D.host.E

theorem frMapAdj_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : frMapAdj A' WW βA' βW (k • x) = k • frMapAdj A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (frMapAdj A' WW βA' βW) (GlobalTheory.PlaceVec.frMapAdj_add A' WW βA' βW)) k x

theorem dualCoord_apply (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x : WO A' WW)
    (i j) : dualCoord A' WW βA' βW x i j = eToEAf D D.host.xi0 * frMapAdj A' WW βA' βW x i j := rfl

theorem dualCoord_add (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x y : WO A' WW) :
    dualCoord A' WW βA' βW (x + y) = dualCoord A' WW βA' βW x + dualCoord A' WW βA' βW y := by
  ext i j
  rw [Matrix.add_apply, dualCoord_apply, dualCoord_apply, dualCoord_apply, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.add_apply,
    mul_add]

theorem dualCoord_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : dualCoord A' WW βA' βW (k • x) = k • dualCoord A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (dualCoord A' WW βA' βW) (dualCoord_add A' WW βA' βW)) k x

theorem exists_den_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ M : ℕ, 0 < M ∧
      ∀ u ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True),
        ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ OO := by
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := A') (T := WW) hS hT
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.frMapAdj_up A' WW βA' βW
  obtain ⟨d, hd, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0)
  refine ⟨d * k₁ * k₃, by positivity, fun u hu i j => ?_⟩
  have h1 := h₁ (k₃ • u) (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₃ u hu) i j
  have e : ((d * k₁ * k₃ : ℕ) : EAf D) * dualCoord A' WW βA' βW u i j =
      (d • eToEAf D D.host.xi0) * (k₁ • frMapAdj A' WW βA' βW (k₃ • u)) i j := by
    rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e]
  exact mul_mem hξ h1

theorem exists_mul_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : Submodule.IsLattice D.host.E ΛS)
    (hT : Submodule.IsLattice D.host.E ΛT) {a : AE D} (hinf : infPart D a = 0) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf a t → IsIntM (dualCoord A' WW βA' βW t) →
      K • t ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨m, hm, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0⁻¹)
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down A' WW βA' βW
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := A') (T := WW)
  refine ⟨k₄ * (k₂ * m), by positivity, fun t ht hi => ?_⟩
  have hF : IsIntM (frMapAdj A' WW βA' βW (m • t)) := fun i j => by
    have e : frMapAdj A' WW βA' βW (m • t) i j = (m • eToEAf D D.host.xi0⁻¹) * dualCoord A' WW βA' βW t i j := by
      rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, mul_assoc, ← mul_assoc (eToEAf D _),
        ← RingHom.map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    exact mul_mem hξ (hi i j)
  have h3 := h₄ (k₂ • m • t)
    (GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 ht) _) _))
    (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ _ hF)
  rwa [smul_smul, smul_smul, mul_assoc] at h3

theorem isIntM_rightBlock {k d a : ℕ} {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) : IsIntM (rightBlock a Y) :=
  fun i j => by
    unfold rightBlock
    split_ifs
    · exact h _ _
    · exact zero_mem _

theorem rightBlock_shift {k d a : ℕ} {Y Y' W : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a W i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]

set_option maxHeartbeats 1000000 in

theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A' WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {W : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, dualCoord A' WW βA' βW t' i j = dualCoord A' WW βA' βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdSnd ν e I a A' WW βA' βW t' = stdSnd ν e I a A' WW βA' βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ OO := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A' WW βA' βW t i j =
      dualCoord A' WW βA' βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A' WW βA' βW t') ↔ IsIntM (dualCoord A' WW βA' βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j) :=
    ⟨fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hj),
      fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (hW1 i j) (ha i j) (H i j hj)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.unitChar_congr he hl hc (isIntM_rightBlock hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * W i j) (isIntM_rightBlock fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (rightBlock_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]

set_option maxHeartbeats 1000000 in

theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A' WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ OO)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf (cA D e) t → IsIntM (dualCoord A' WW βA' βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A' WW βA' βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places S
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M), Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A' WW βA' βW
      (W := fun i j => (K : EAf D) * ((M : EAf D) * dualCoord A' WW βA' βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A' WW, GlobalTheory.PlaceModel.isHalf_iff A' WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hh) _)
    · rw [dualCoord_add, dualCoord_nsmul, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
      push_cast
      ring
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

theorem exists_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A' WW : HSp D) (rA' : Rig A') (rW : Rig WW) (ν : (AE D)ˣ →* Circle) (e : AE D) (S : Finset (Pl D.host.E)) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (vac : WO A' WW → ℂ), rA'.Is → rW.Is → IsHeckeChar D ν → IsIdemSum e S → I ≠ ⊥ → IsVacO ψ θ A' WW rA'.s rW.s rA'.Λ rW.Λ vac → ∃ f, IsThetaAt ψ (symplO A' WW) (heisO ψ A' WW) (cA D e) (latO A' WW rA'.Λ rW.Λ fun _ => True) 1 vac (stdSnd ν e I a A' WW rA'.β rW.β) f ∧ IsThetaFunO ψ A' WW f := by
  intro D ψ θ A' WW rA' rW ν e S I a vac hA hW hν he hI hv
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have ha : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hSd : IsSelfDualC A' rA'.Λ := hA.1
  have hSB : IsSBHalf (cA D e) (latO A' WW rA'.Λ rW.Λ fun _ => True) (stdSnd ν e I a A' WW rA'.β rW.β) :=
    stdSnd_isSB hν.1 he hI a A' WW rA'.β rW.β _ (exists_den_dualCoord hSd.1.fg hW.1.1.fg rA'.β rW.β)
      (exists_mul_dualCoord hSd.1 hW.1.1 hinf rA'.β rW.β)
  obtain ⟨Tm, hTm⟩ := (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hv.1 A' WW rA'.Λ rW.Λ hSd hW.1 _ e he vac hv.2.theta
    hv.2.lat).2
  obtain ⟨f, h⟩ := GlobalTheory.PlaceVec.exists_isThetaAt hv.1 hSd hW.1 ha hinf ⟨Tm, hTm⟩ hSB
  refine ⟨f, h, ?_⟩
  rw [h.2 Tm hTm]
  exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hv.1 A' WW rA'.Λ rW.Λ hSd hW.1 (cA D e) ha hinf vac hv.2.theta Tm hTm _ hSB

end GlobalTheory.CompanionTheory.StdSndTheta
