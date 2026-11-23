import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunTransportS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFinVecOfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteDatumOfHomLatticeCosetSelfDualStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKer

variable {D : D7}

theorem unitMap_perm {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (σ : Equiv.Perm (Fin n))
    (σ' : Equiv.Perm (Fin m)) (i : Fin m) (j : Fin n) :
    unitMap (B.submatrix id σ) (B'.submatrix id σ') i j = unitMap B B' (σ' i) (σ j) := by
  unfold unitMap
  have h : (B.submatrix id σ)⁻¹ = B⁻¹.submatrix σ id := by
    simpa using Matrix.inv_submatrix_equiv B (Equiv.refl _) σ
  rw [h]
  ext a b
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

theorem pureTensorO_perm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (σS : D.what₂.Tau → Equiv.Perm (Fin S.rank)) (σT : D.what₂.Tau → Equiv.Perm (Fin T.rank))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (Q : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT (fun τ => (BS τ).submatrix id (σS τ)) (fun τ => (BT τ).submatrix id (σT τ)) f
        (MvPolynomial.rename (fun k : FVar D T.rank S.rank => (k.1, (σT k.1).symm k.2.1, (σS k.1).symm k.2.2)) Q) =
      pureTensorO ψ θ S T sS sT BS BT f Q := by
  unfold pureTensorO
  refine GlobalTheory.ArchRec.LieAtPlace.pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => ?_) Q
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, unitMap_perm, Equiv.apply_symm_apply]

open GlobalTheory.GridJoin

theorem heq_ker {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) (ω : GlobalTheory.Grid.WRep U1 U0)
    (om : GA D (negSp V1) × GA D V0 →* Module.End ℂ (WO (negSp V1) V0 → ℂ)) (hom : HEq (ω.toSgn true) om)
    (F : WO U1 U0 → ℂ) (F' : WO (negSp V1) V0 → ℂ) (hF : HEq F F') :
    HEq (fun (h : GA D U1) (g : GA D U0) => thetaKO ω h g F)
      (fun (h : GA D V1) (g : GA D V0) => thetaKO om (negGA V1 h) g F') := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  cases hom
  cases hF
  rfl

theorem heq_fock {V1 V0 U1 U0 : HSp D} (h1 : SameSp V1 U1) (h0 : SameSp V0 U0) {ψ ψ' : AddChar (AF D.host.F) ℂ}
    {θ θ' : InfFam D} (eψ : ψ' = ψ) (eθ : θ' = θ) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {s1 b1 : D.what₂.Tau → Matrix (Fin V1.rank) (Fin V1.rank) ℂ} {s0 b0 : D.what₂.Tau → Matrix (Fin V0.rank) (Fin V0.rank) ℂ}
    {t1 c1 : D.what₂.Tau → Matrix (Fin U1.rank) (Fin U1.rank) ℂ} {t0 c0 : D.what₂.Tau → Matrix (Fin U0.rank) (Fin U0.rank) ℂ}
    (ht1 : HEq t1 s1) (ht0 : HEq t0 s0) (σ1 : D.what₂.Tau → Equiv.Perm (Fin V1.rank)) (σ0 : D.what₂.Tau → Equiv.Perm (Fin V0.rank))
    (hc1 : HEq c1 fun τ => (b1 τ).submatrix id (σ1 τ)) (hc0 : HEq c0 fun τ => (b0 τ).submatrix id (σ0 τ))
    (hs1 : ∀ τ, IsCartanInv (gramAt D V1 τ) (s1 τ)) (hs0 : ∀ τ, IsCartanInv (gramAt D V0 τ) (s0 τ))
    {f : WO U1 U0 → ℂ} {f' : WO (negSp V1) V0 → ℂ} (hf : HEq f f') (hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn true U1) U0 f)
    (q : PolF D V0.rank V1.rank) : ∃ p : PolF D U0.rank U1.rank,
      HEq (pureTensorO ψ θ (GlobalTheory.Grid.sgn true U1) U0 (fun τ => GlobalTheory.Grid.sgnM true (t1 τ)) t0 c1 c0 f p)
        (pureTensorO ψ' θ' (negSp V1) V0 (fun τ => -s1 τ) s0 b1 b0 f' q) := by
  obtain ⟨L, a, b, rfl⟩ := h1
  obtain ⟨L', a', b', rfl⟩ := h0
  subst eψ eθ
  cases ht1; cases ht0; cases hc1; cases hc0; cases hf
  have hth' : IsThetaFunO _ (negSp V1) V0 _ := ⟨hth.1, hth.2, hth.3, hth.4⟩
  exact ⟨_, heq_of_eq (pureTensorO_perm (S := negSp V1) (T := V0) hψ hθ (fun τ => isCartanInv_neg (hs1 τ)) hs0 b1 b0 σ1 σ0
    hth' q)⟩

end GlobalTheory.RowKer

namespace GlobalTheory.RowKer

open GlobalTheory.GridJoin

theorem kernel_row : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R),
    IsSelfDualC (Yc D 0) (R.ΛY 0) → ch.W.Over R → ∀ (G : GlobalTheory.Grid.GridPre R), G.Is → GlobalTheory.GridJoin.Match G ch.W →
    ∀ (ρ : ch.G.RealVec) (Φ : ch.G.Datum) (i : Fin D.R.m), ∃ f,
      GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f ∧ ∃ p,
        HEq (fun h g => thetaKO (G.X i 0).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) f p))
          (fun h g => ch.W.kerA (.right (i : ℕ) 0) (ch.W.datum ρ Φ i) g h) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hY hO G hG hM ρ Φ i
  obtain ⟨hsp, harr⟩ := hM
  have hi : (i : ℕ) < D.R.m := i.2
  obtain ⟨c, hc⟩ := (harr.cos i hi).2 (Φ i)
  have sd : ∀ k, k ≤ D.R.m → IsSelfDualC (G.V k 0).V (G.V k 0).Λ := by
    rintro (_ | k) hk
    · exact hY
    · exact GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ 1 (hG.spaces.vert k 0 hk (Nat.zero_le _)).frame
  have hfin : GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V ((i : ℕ) + 1) 0) (G.V i 0) (G.vC i c) :=
    GlobalTheory.T.isFiniteDatum_of_homLatticeCoset_selfDual c (hG.arrows.X i 0 hi (Nat.zero_le _)).vac (sd _ hi) (sd _ hi.le) hG.chars.places.idem
      (G.toPlaceDat.ideal_ne_bot _) (hG.data i hi c)
  refine ⟨G.vC i c, hfin, ?_⟩
  have n1 := hsp.vert ((i : ℕ) + 1) 0 hi (Nat.zero_le _)
  have n0 := hsp.vert i 0 hi.le (Nat.zero_le _)
  obtain ⟨σ1, hσ1⟩ := n1.onb (by simp)
  obtain ⟨σ0, hσ0⟩ := n0.onb (by simp)
  obtain ⟨p, hp⟩ := heq_fock n1.sp n0.sp hO.ψ hO.θ (hO.ψ ▸ ch.W.ψ_std) (hO.θ ▸ ch.W.θ_is) n1.cart n0.cart σ1 σ0 hσ1 hσ0
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ)
    (fun τ => ch.W.cart_is _ (by simp only [GlobalTheory.ChiGrid.Node.InRange]; omega) τ) hc hfin.1 (ρ i)
  exact ⟨p, heq_ker n1.sp n0.sp (G.X i 0).ω (ch.W.om (.chi i 0)) (harr.omX i 0 hi (Nat.zero_le _)) _ _ hp⟩

end GlobalTheory.RowKer
