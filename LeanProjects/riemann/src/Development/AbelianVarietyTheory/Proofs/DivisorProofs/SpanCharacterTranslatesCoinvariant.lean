import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreMemInducedSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreZeroMemCoinvariantsStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.RankFibre

def stabSub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hg]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem of_parts (Lirr : (GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β → ∀ M : Submodule ℂ (GL (Fin (a + b)) k → ℂ), M ≤ GlobalTheory.RankFibre.indScal ν β a b → (∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M) → M = ⊥ ∨ GlobalTheory.RankFibre.indScal ν β a b ≤ M)) (Llaw : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ), GlobalTheory.RankFibre.fibre ν β a b Φ ∈ GlobalTheory.PRep.indSpace (GlobalTheory.SmGL.parab k (GlobalTheory.RankFibre.blocks a b)) (GlobalTheory.SmGL.ofChar (GlobalTheory.RankFibre.parChar ν β a b)))) (Lsmooth : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ})) (Linteg : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), MeasureTheory.Integrable (fun g : GL (Fin a) k => Φ (g.val * GlobalTheory.SplitFlip.X0 k finSumFinEquiv) * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (((a + b : ℕ) : ℂ) / 2)) (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))))) (Lker : (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.RankFibre.fullRankSB k a (a + b), GlobalTheory.RankFibre.fibre ν β a b Φ = 0 → Φ ∈ GlobalTheory.RankFibre.coinv ν β a (a + b))) : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) := by
  intro HB k _ _ _ _ a d had ν β hνs hνu hβs hβu N hCN hNSB hNst
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  borelize k

  have hS0 : ∀ (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      Φ ∈ fullRankSB k a (a + b) → omA ν β 1 h Φ ∈ fullRankSB k a (a + b) := by
    intro h Φ hΦ
    refine ⟨omA_mem_SB ν β 1 h hΦ.1, fun Y hY => ?_⟩
    have hr : (((1 : GL (Fin a) k)⁻¹).val * Y * (invT h).val).rank ≠ a := by
      rwa [inv_one, Units.val_one, Matrix.one_mul,
        Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units (invT h))]
    simp only [omA, hΦ.2 _ hr, mul_zero]

  have hint : ∀ Φ ∈ fullRankSB k a (a + b), ∀ x : GL (Fin (a + b)) k,
      Integrable (fun g : GL (Fin a) k => omA ν β 1 x Φ (g.val * X0 k finSumFinEquiv) * (ν (gdet g) : ℂ) *
        apow (gdet g) (((a + b : ℕ) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) :=
    fun Φ hΦ x => Linteg k a b ν hνs _ (hS0 x Φ hΦ)
  have hadd : ∀ Φ ∈ fullRankSB k a (a + b), ∀ Ψ ∈ fullRankSB k a (a + b),
      fibre ν β a b (Φ + Ψ) = fibre ν β a b Φ + fibre ν β a b Ψ := by
    intro Φ hΦ Ψ hΨ
    funext x
    rw [Pi.add_apply]
    unfold fibre
    rw [← integral_add (hint Φ hΦ x) (hint Ψ hΨ x)]
    congr 1
    funext g
    simp only [omA, Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℂ) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ),
      fibre ν β a b (c • Φ) = c • fibre ν β a b Φ := by
    intro c Φ
    funext x
    rw [Pi.smul_apply, smul_eq_mul]
    unfold fibre
    rw [← integral_const_mul]
    congr 1
    funext g
    simp only [omA, Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : fibre ν β a b 0 = 0 := by
    funext x
    simp [fibre, omA]

  let M : Submodule ℂ (GL (Fin (a + b)) k → ℂ) :=
    { carrier := {f | ∃ Ψ ∈ N, Ψ ∈ fullRankSB k a (a + b) ∧ fibre ν β a b Ψ = f}
      zero_mem' := ⟨0, N.zero_mem, (fullRankSB k a (a + b)).zero_mem, hzero⟩
      add_mem' := by
        rintro _ _ ⟨Φ, h1, h2, rfl⟩ ⟨Ψ, h3, h4, rfl⟩
        exact ⟨Φ + Ψ, N.add_mem h1 h3, (fullRankSB k a (a + b)).add_mem h2 h4, hadd Φ h2 Ψ h4⟩
      smul_mem' := by
        rintro c _ ⟨Φ, h1, h2, rfl⟩
        exact ⟨c • Φ, N.smul_mem c h1, (fullRankSB k a (a + b)).smul_mem c h2, hsmul c Φ⟩ }
  have hind : ∀ Ψ ∈ fullRankSB k a (a + b), fibre ν β a b Ψ ∈ indScal ν β a b := by
    intro Ψ hΨ
    refine ⟨?_, Llaw k a b ν β Ψ⟩
    have hle : stabSub ((repA ν β).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin (a + b)) k))) Ψ ≤
        stabSub (rightReg ℂ (GL (Fin (a + b)) k) ℂ) (fibre ν β a b Ψ) := by
      intro h hh
      have hh' : omA ν β 1 h Ψ = Ψ := hh
      show rightReg ℂ (GL (Fin (a + b)) k) ℂ h (fibre ν β a b Ψ) = fibre ν β a b Ψ
      funext x
      show fibre ν β a b Ψ (x * h) = fibre ν β a b Ψ x
      rw [← fibre_omA, hh']
    exact Subgroup.isOpen_mono hle (Lsmooth k a (a + b) ν β hβs Ψ hΨ.1)
  have hMle : M ≤ indScal ν β a b := by
    rintro _ ⟨Ψ, -, hΨ, rfl⟩
    exact hind Ψ hΨ
  have hMst : ∀ f ∈ M, ∀ h : GL (Fin (a + b)) k, (fun x => f (x * h)) ∈ M := by
    rintro _ ⟨Ψ, h1, h2, rfl⟩ h
    exact ⟨omA ν β 1 h Ψ, hNst h Ψ h1, hS0 h Ψ h2, funext fun x => fibre_omA ν β a b h Ψ x⟩
  rcases Lirr HB k a b ν β hνs hνu hβs hβu M hMle hMst with h0 | hT
  · left
    intro Ψ hΨN hΨr
    have hΨ : Ψ ∈ fullRankSB k a (a + b) := ⟨hNSB hΨN, hΨr⟩
    have hm : fibre ν β a b Ψ ∈ M := ⟨Ψ, hΨN, hΨ, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact Lker k a b ν β hνs hβs Ψ hΨ hm
  · right
    intro Φ hΦ hΦr
    have hΦS : Φ ∈ fullRankSB k a (a + b) := ⟨hΦ, hΦr⟩
    obtain ⟨Ψ, hΨN, hΨS, hZ⟩ := hT (hind Φ hΦS)
    have hd : Φ - Ψ ∈ coinv ν β a (a + b) := by
      refine Lker k a b ν β hνs hβs _ ((fullRankSB k a (a + b)).sub_mem hΦS hΨS) ?_
      rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, hadd Φ hΦS _ ((fullRankSB k a (a + b)).smul_mem _ hΨS),
        hsmul, hZ]
      simp
    have := N.add_mem (hCN hd) hΨN
    simpa using this

theorem coinv_or_fullRank_le : GlobalTheory.Published.BernsteinUnitaryProductIrreducible →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → GlobalTheory.SmGL.IsSmoothChar β → GlobalTheory.SmGL.IsUnitaryChar β →
    ∀ N : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ),
      Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} ≤ N →
      N ≤ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) →
      (∀ (h : GL (Fin d) k), ∀ Ψ ∈ N, GlobalTheory.SplitFlip.omA ν β 1 h Ψ ∈ N) →
      (∀ Ψ ∈ N, (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) →
          Ψ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
            Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ}) ∨
      (∀ Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Ψ Y = 0) → Ψ ∈ N) :=
  of_parts GlobalTheory.T.induced_scalar_irreducible GlobalTheory.T.fibre_mem_induced_space GlobalTheory.T.isOpen_stabilizer_schwartzBruhat GlobalTheory.T.integrable_full_rank_fibre GlobalTheory.T.fibre_zero_mem_coinvariants

end GlobalTheory.RankFibre
