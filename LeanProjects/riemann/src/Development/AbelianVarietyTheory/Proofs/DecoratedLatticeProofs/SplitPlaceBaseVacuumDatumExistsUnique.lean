import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaAtEqSumHeisOfFourierSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerIntertwinerSchwartzBruhatIsTheta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSplitHalfLatticeCoordinatesIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemHomLatticeOfIntegralFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatMatrixUniformlyLocallyConstantBounStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticPairingLatticeAwaySupportedAtPlaceEqZeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhatStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.OverProof

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum GlobalTheory.SchrTheta

theorem rd_bounded : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), IsHalf p.e u →
      ∀ i j, (N : k) * rd α β u i j ∈ 𝒪[k] := GlobalTheory.T.exists_nat_mul_splitHalf_latticeCoordinates_integral

theorem nsmul_mem_of_rd_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∃ N : ℕ, 0 < N ∧ ∀ t : WO S T, IsHalf p.e t → (∀ i j, rd α β t i j ∈ 𝒪[k]) →
      N • t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := GlobalTheory.T.exists_nsmul_mem_homLattice_of_integral_frameCoords

theorem sb_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (Ψ : Matrix n n' k → ℂ), Ψ ∈ SB (Matrix n n' k) →
    ∃ N : ℕ, 0 < N ∧ (∀ X Y : Matrix n n' k, (∀ i j, Y i j ∈ 𝒪[k]) → Ψ (X + (N : k) • Y) = Ψ X) ∧
      ∀ X, Ψ X ≠ 0 → ∀ i j, (N : k) * X i j ∈ 𝒪[k] := GlobalTheory.T.schwartzBruhat_matrix_uniformly_locallyConstant_bounded

section Rd
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {S T : HSp D}

theorem rd_add (α : Frame p S n') (β : Frame p T n) (t s : WO S T) : rd α β (t + s) = rd α β t + rd α β s := by
  unfold rd
  rw [Matrix.map_add p.pr (map_add p.pr), Matrix.mul_add, Matrix.add_mul]

theorem rd_nsmul (α : Frame p S n') (β : Frame p T n) (N : ℕ) (t : WO S T) : rd α β (N • t) = (N : k) • rd α β t := by
  unfold rd
  have : (N • t).map p.pr = (N : k) • t.map p.pr := by
    ext i j
    simp [Matrix.map_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

end Rd

theorem isSBHalf_extFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ Ψ ∈ SB (Matrix n n' k), IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (extFun α β Ψ) := by
  classical
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT Ψ hΨ
  obtain ⟨Na, hNa, ha⟩ := rd_bounded D k p n n' S T α β LS LT hS hT
  obtain ⟨Nb, hNb, hb⟩ := nsmul_mem_of_rd_int D k p n n' S T α β LS LT hS hT
  obtain ⟨Nc, hNc, hc1, hc2⟩ := sb_uniform k n n' Ψ hΨ
  have hhalf_add : ∀ {t u : WO S T}, IsHalf p.e u → (IsHalf p.e (t + u) ↔ IsHalf p.e t) := fun {t u} hu =>
    forall_congr' fun i => forall_congr' fun j => by
      rw [Matrix.add_apply, mul_add, hu i j, add_left_inj]
  have hhalf_nsmul : ∀ (N : ℕ) {t : WO S T}, IsHalf p.e t → IsHalf p.e (N • t) := fun N t ht i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, ht i j]
  refine ⟨fun t ht => ?_, Na * Nb * Nc, Nat.mul_pos (Nat.mul_pos hNa hNb) hNc, fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by simp [extFun, h])
  · have hu' : IsHalf p.e ((Na * Nb * Nc) • u) := hhalf_nsmul _ hh
    unfold extFun
    rw [if_congr (hhalf_add hu') rfl rfl]
    split_ifs with h
    · rw [rd_add, rd_nsmul, show ((Na * Nb * Nc : ℕ) : k) • rd α β u = (Nc : k) • (((Nb : k) * Na) • rd α β u) by
        rw [smul_smul]; push_cast; ring_nf]
      refine hc1 _ _ fun i j => ?_
      rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
      exact mul_mem (by exact_mod_cast (algebraMap ℤ 𝒪[k] Nb).2) (ha u hu hh i j)
    · rfl
  · have hth : IsHalf p.e t := by
      by_contra h
      exact ht (by simp [extFun, h])
    have hΨt : Ψ (rd α β t) ≠ 0 := by simpa [extFun, hth] using ht
    have h1 := hb (Nc • t) (hhalf_nsmul _ hth) fun i j => by
      rw [rd_nsmul, Matrix.smul_apply, smul_eq_mul]
      exact hc2 _ hΨt i j
    rw [show (Na * Nb * Nc) • t = Na • (Nb • (Nc • t)) by rw [smul_smul, smul_smul, mul_assoc]]
    exact nsmul_mem h1 Na

theorem symplO_off_eq_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop),
    ¬ P p.v → ∀ u ∈ latO S T MS MT P, ∀ x : WO S T, (∀ i j, (p.e + cA D p.e) * x i j = x i j) → symplO S T u x = 0 := GlobalTheory.T.symplecticPairing_latticeAway_supportedAt_place_eq_zero

theorem extFun_latInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA →
    ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
      extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator

theorem latInd_mem_SB : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D)
    (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT →
      latInd ΛS ΛT ∈ SB (Matrix n n' k) := GlobalTheory.T.indicator_hom_selfDual_components_schwartzBruhat

variable {D : D7}

theorem dualPair {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {LS : Lat S} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {e : AE D} {v : Pl D} (hs : IsSplitIdem D e) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (heq : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    let Λ := latO S T (LS : Set _) (LT : Set _) (· = v)
    (∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1) ∧
    (∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e) ∧
    (∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e)) ∧
    (∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧ ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u) ∧
    (∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ) := by
  intro Λ
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have heε : algebraMap (AF D.host.F) (AE D) ε * e = e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T LS LT hS.1.fg hT.1.fg fun w => w = v
  refine ⟨fun u hu y hy => (hdual u (infPart_half hε heε hu.2)).1 (latO_le_top _ hu.1) y (latO_le_top _ hy.1),
    mem_of_dual hε hdual he heε heε', fun y hy h => ?_, fun k hk => ?_, fun y hy => ?_⟩
  · refine mem_of_dual hε hdual he' heε' (by rwa [cA_cA]) y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_mem hε he heε (latO_le_top _ hu), ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]
  · obtain ⟨k, hk, hky⟩ := exists_nsmul_mem_latO' hS.1 hT.1 y (infPart_half hε heε' hy)
    refine ⟨k, hk, ?_⟩
    have := (idem_smul_mem hε he' heε' hky).1
    rwa [smul_comm, (mem_half S T).1 hy] at this

theorem heisO_zero_fun (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (u : WO S T) : heisO ψ S T u 0 = 0 := by
  funext t; simp [heisO]

theorem isLatVac_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) :
    IsLatVac (heisO ψ S T) Λ 0 :=
  ⟨fun u _ => heisO_zero_fun ψ S T _, fun _ _ u _ _ => heisO_zero_fun ψ S T u⟩

theorem isLatVac_add {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {f g : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) (hg : IsLatVac (heisO ψ S T) Λ g) : IsLatVac (heisO ψ S T) Λ (f + g) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have := (heisL S T ψ (2 • u)).map_add f g
    change heisO ψ S T (2 • u) (f + g) = _ at this
    rw [this]; change heisO ψ S T (2 • u) f + heisO ψ S T (2 • u) g = _; rw [hf.1 u hu, hg.1 u hu]
  · have := (heisL S T ψ u).map_add f g
    change heisO ψ S T u (f + g) = _ at this
    rw [this]; change heisO ψ S T u f + heisO ψ S T u g = _; rw [hf.2 e he u hu hh, hg.2 e he u hu hh]

theorem isLatVac_smul {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} (c : ℂ) {f : WO S T → ℂ}
    (hf : IsLatVac (heisO ψ S T) Λ f) : IsLatVac (heisO ψ S T) Λ (c • f) := by
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have := (heisL S T ψ (2 • u)).map_smul c f
    change heisO ψ S T (2 • u) (c • f) = _ at this
    rw [this]; change c • heisO ψ S T (2 • u) f = _; rw [hf.1 u hu]
  · have := (heisL S T ψ u).map_smul c f
    change heisO ψ S T u (c • f) = _ at this
    rw [this]; change c • heisO ψ S T u f = _; rw [hf.2 e he u hu hh]

theorem isLatVac_heis {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {x : WO S T}
    (hx : ∀ u ∈ Λ, symplO S T u x = 0) {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (heisO ψ S T x f) := by
  have key : ∀ u ∈ Λ, heisO ψ S T u f = f → heisO ψ S T u (heisO ψ S T x f) = heisO ψ S T x f := by
    intro u hu h
    have := heisL_comm S T ψ u x f
    change heisO ψ S T u (heisO ψ S T x f) = ψ (symplO S T u x) • heisO ψ S T x (heisO ψ S T u f) at this
    rw [this, hx u hu, AddChar.map_zero_eq_one, one_smul, h]
  exact ⟨fun u hu => key _ (nsmul_mem hu 2) (hf.1 u hu), fun e he u hu hh => key u hu (hf.2 e he u hu hh)⟩

theorem overBasic : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ S T α β LS LT hS hT f₀ hvac
  obtain ⟨ε, hε, heq⟩ := p.above
  have hs := p.split
  have he := hs.1
  have hec := hs.2.1
  have he' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, he]
  have hs' : IsSplitIdem D (cA D p.e) :=
    ⟨he', by rw [cA_cA, mul_comm, hec], p.v, ε, hε, by rw [cA_cA, add_comm, heq]⟩
  have heε : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by rw [← heq]; linear_combination he + hec
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by rw [← heq]; linear_combination he' + hec
  obtain ⟨hLL', hX, hY, hfin, hden⟩ := dualPair hψ hS hT hs hε heq
  set Λ := latO S T (LS : Set _) (LT : Set _) (· = p.v) with hΛ
  have hex : ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ Tm :=
    exists_placeModel ψ hec Λ hLL' hX hY hfin one_ne_zero f₀
      (fun u hu => hvac.2.2 p.e hs u hu.1 ((isHalf_iff S T).2 hu.2))
      (fun u hu => hvac.2.2 _ hs' u hu.1 ((isHalf_iff S T).2 hu.2))
  obtain ⟨Tm, hTm⟩ := hex
  have huniq := fun {T₁ T₂} (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ T₁)
      (h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) p.e Λ 1 f₀ T₂) {Φ} (hΦ : IsSBHalf p.e Λ Φ) =>
    placeModel_unique_of_dual ψ Λ hLL' hX hfin hden h₁ h₂ hΦ
  have hfX : ∀ x ∈ half S T p.e, ∀ i j, (p.e + cA D p.e) * x i j = x i j := fun x hx i j => by
    have h1 := (isHalf_iff S T).2 hx i j
    linear_combination (1 - cA D p.e) * h1 + x i j * hec
  have hfY : ∀ y ∈ half S T (cA D p.e), ∀ i j, (p.e + cA D p.e) * y i j = y i j := fun y hy i j => by
    have h1 := (isHalf_iff S T).2 hy i j
    linear_combination (1 - p.e) * h1 + y i j * hec
  refine ⟨fun Ψ hΨ => ?_, fun Ψ f hf => ?_, fun hU ΛS ΛT hLS hLT => ?_⟩
  · have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hΨ
    refine ⟨Tm (extFun α β Ψ), ⟨hS, hT, hvac, hΨ, ⟨Tm, hTm⟩, fun T' hT' => huniq hTm hT' hΦ⟩, fun f hf => ?_⟩
    exact hf.2.2.2.2.2 Tm hTm
  · have hΦ := isSBHalf_extFun D k p n n' S T α β LS LT hS hT Ψ hf.2.2.2.1
    have hfe : f = Tm (extFun α β Ψ) := hf.2.2.2.2.2 Tm hTm
    rw [hfe]
    refine ⟨placeModel_induction ψ Λ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
      (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
      (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
      (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
      hvac.1 hΦ, fun MS MT P hP hv => ⟨?_, ?_⟩⟩
    · exact placeModel_induction ψ Λ hLL' hX hfin hden hTm (IsThetaFunO ψ S T) GlobalTheory.WeilVacMove.isTheta_zero
        (fun _ _ => GlobalTheory.WeilVacMove.isTheta_add) (fun c _ => GlobalTheory.WeilVacMove.isTheta_smul c)
        (fun x hx g hg => isTheta_heis_fin hψ hg (infPart_half hε heε hx))
        (fun y hy g hg => isTheta_heis_fin hψ hg (infPart_half hε heε' hy))
        hvac.1 hΦ
    · have hv2 : IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) P) f₀ := hv.2
      exact placeModel_induction ψ Λ hLL' hX hfin hden hTm
        (IsLatVac (heisO ψ S T) (latO S T (MS : Set (Fin S.rank → D.host.E)) (MT : Set (Fin T.rank → D.host.E)) P)) (isLatVac_zero ψ S T _)
        (fun _ _ => isLatVac_add) (fun c _ => isLatVac_smul c)
        (fun x hx g hg => isLatVac_heis (fun u hu => symplO_off_eq_zero D k p S T _ _ P hP u hu x (hfX x hx)) hg)
        (fun y hy g hg => isLatVac_heis (fun u hu => symplO_off_eq_zero D k p S T _ _ P hP u hu y (hfY y hy)) hg)
        hv2 hΦ
  · have hE := extFun_latInd D k p n n' S T α β LS LT hS hT hU ΛS ΛT hLS hLT
    refine ⟨hS, hT, hvac, latInd_mem_SB D k p n n' S T α β LS LT hS hT ΛS ΛT hLS hLT, ⟨Tm, hTm⟩, fun T' hT' => ?_⟩
    have := hT'.vac
    rw [one_smul] at this
    change f₀ = T' (extFun α β (latInd ΛS ΛT))
    rw [hE, this]

end GlobalTheory.FinPl.OverProof

theorem GlobalTheory.FinPl.overBasic : ∀ D : D7, GlobalTheory.FinPl.OverBasic D := GlobalTheory.FinPl.OverProof.overBasic
