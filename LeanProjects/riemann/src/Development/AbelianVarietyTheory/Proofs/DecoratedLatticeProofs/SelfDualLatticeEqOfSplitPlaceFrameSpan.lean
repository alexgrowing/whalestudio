import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAtPlacesMemCompletedHermitianLa
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeWithPrescribedSplitComponen
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_intAt (q : GlobalTheory.FinPl.SplitPt D k) : q.e ∈ intAt D (· = q.v) := by
  refine ⟨GlobalTheory.FrameGlob.e_mem_idAt q, ?_⟩
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  have h := (q.int_iff 1).1 (one_mem _)
  rwa [h1] at h

theorem smul_mem_latV {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : Submodule.IsLattice D.host.E L) {v : GlobalTheory.FinPl.Pl D}
    {z : Fin V.rank → AE D} (hz : z ∈ latV V L (· = v)) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    a • z ∈ latV V L (· = v) :=
  ((((GlobalTheory.FinPl.localComponents D (· = v)).2 V).2.2.2 L z hL).1 hz).2 v rfl a ha

theorem sec_pr_mul (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (c : k) : q.sec (q.pr a * c) = a * q.sec c := by
  calc q.sec (q.pr a * c) = q.sec (q.pr (a * q.sec c)) := by rw [RingHom.map_mul q.pr, q.pr_sec]
    _ = q.e * (a * q.sec c) := q.sec_pr _
    _ = a * q.sec c := by rw [mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul]

theorem sec_int_iff (q : GlobalTheory.FinPl.SplitPt D k) (c : k) :
    toEAf D (q.sec c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ 𝒪[k] := by
  have h := q.pr_mem_iff (q.sec c)
  rw [q.pr_sec, ← map_mul, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem sec_mem_iff (V : HSp D) (t : GA D V) (Λ L : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D))
    (q : GlobalTheory.FinPl.SplitPt D k) (M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hm : GlobalTheory.FinPl.Moves V t Λ L (· = q.v)) (hM : MovedTo (ofSplit q) V t β M)
    (x : Fin V.rank → k) :
    (fun i => q.sec ((M *ᵥ x) i)) ∈ latV V L (· = q.v) ↔ ∀ i, x i ∈ 𝒪[k] := by
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin V.rank) (Fin V.rank) (AE D), b.map (toEAf D) = β.val := by
    choose f hf using fun s : Lev.EAf D => GlobalTheory.ResLoc.toEAf_surj (D := D) s
    exact ⟨β.val.map f, by ext i j; simp [hf]⟩
  set s : Fin V.rank → AE D := fun i => q.sec (x i) with hsdef
  have hs : ∀ i, s i ∈ idAt D (· = q.v) := fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _
  have hy : ∀ i, (b *ᵥ s) i ∈ idAt D (· = q.v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hs j)
  have hkey : (fun i => q.sec ((M *ᵥ x) i)) = Formalism.L2.Theta.mt V t *ᵥ (b *ᵥ s) := by
    rw [Matrix.mulVec_mulVec, ← hM b hb]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sec_pr_mul q _ _
  rw [hkey, ← hm _ hy]
  have hbridge : b *ᵥ s ∈ latV V Λ (· = q.v) ↔
      (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ⟨GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _, GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy⟩
  rw [hbridge, hβ]
  have h2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) = β.val *ᵥ fun i => toEAf D (s i) := by
    funext i
    change toEAf D ((b *ᵥ s) i) = _
    rw [← hb]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum (toEAf D)]
    simp only [RingHom.map_mul]
  rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact forall_congr' fun i => sec_int_iff q (x i)

end GlobalTheory.SplitFrameLat

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

theorem latV_eq : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  intro D V t Λ L N β k _ _ _ _ q Y _ _ F σ ht hΛ hβ hL hN hm hM hI
  have he := e_mem_intAt q

  have hw : ∀ z : Fin V.rank → AE D, q.e • z ∈ latV V L (· = q.v) ↔ q.e • z ∈ latV V N (· = q.v) := by
    intro z
    set y : Fin V.rank → k := fun i => q.pr (z i) with hydef
    have hz : q.e • z = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := by
      rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
      funext i
      simp only [hydef, q.sec_pr, Pi.smul_apply, smul_eq_mul]
    have hL' := sec_mem_iff V t Λ L β q (F.β.submatrix id σ) hβ hm hM ((F.γ *ᵥ y) ∘ σ)
    rw [Matrix.submatrix_mulVec_equiv] at hL'
    have e1 : ((F.γ *ᵥ y) ∘ σ) ∘ σ.symm = F.γ *ᵥ y := by
      funext i; simp
    rw [e1] at hL'
    rw [hz, ← hI]
    have e2 : (fun i => q.sec (((F.β *ᵥ (F.γ *ᵥ y)) ∘ id) i)) = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := rfl
    rw [e2] at hL'
    rw [hL']
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hherm : ∀ y x : Fin V.rank → AE D,
      GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) x = GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) (q.e • x) := by
    intro y x
    unfold GlobalTheory.IwaPlace.hermAt
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(cA D (x i) * gA V i j * y j)) * hce
  have hbar : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V B (· = q.v) → q.e • z ∈ latV V A (· = q.v)) →
      ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) →
        cA D q.e • z ∈ latV V A (· = q.v) → cA D q.e • z ∈ latV V B (· = q.v) := by
    intro A B hA hB hBA z hz h
    have hz' : ∀ i, (cA D q.e • z) i ∈ idAt D (· = q.v) := fun i => Ideal.mul_mem_left _ _ (hz i)
    refine ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V B q.v hB).2.2 _ hz').2 fun x hx => ?_
    rw [hherm]
    have hex : q.e • x ∈ latV V A (· = q.v) := hBA x (smul_mem_latV hB.1 hx he)
    exact ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V A q.v hA).2.2 _ hz').1 h _ hex
  have hsplit : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) → q.e • z + cA D q.e • z = z := by
    intro z hz
    obtain ⟨ε, hε, hs⟩ := q.above
    rw [← add_smul, hs]
    funext i
    exact ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 (z i)).1 (hz i)
  have hgen : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V A (· = q.v) ↔ q.e • z ∈ latV V B (· = q.v)) →
      latV V A (· = q.v) ≤ latV V B (· = q.v) := by
    intro A B hA hB hAB z hz
    have hs := GlobalTheory.FinPl.FrameLat.latV_supp hz
    have h1 : q.e • z ∈ latV V A (· = q.v) := smul_mem_latV hA.1 hz he
    have h3 : cA D q.e • z = z - q.e • z := by
      rw [eq_sub_iff_add_eq']
      exact hsplit z hs
    have h2 : cA D q.e • z ∈ latV V A (· = q.v) := by
      rw [h3]
      exact sub_mem hz h1
    have := add_mem ((hAB z).1 h1) (hbar A B hA hB (fun z => (hAB z).2) z hs h2)
    rwa [hsplit z hs] at this
  exact le_antisymm (hgen L N hL hN hw) (hgen N L hN hL fun z => (hw z).symm)

end GlobalTheory.SplitFrameLat

end
