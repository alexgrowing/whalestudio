import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l}

private theorem fa (a : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (hr : IsPst P ρ) :
    finrank ℂ (WDSpace P ι ρ) = a := by
  rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι K LL _ ρ hr]
  simp

set_option maxHeartbeats 1600000 in
private theorem ringS' (hRing : RingS) (LL : FinExt l) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra ℂ S) (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S), Nontrivial S ∧
      (∀ x : ↥LL.1, π (x ⊗ₜ[ℚ_[l]] (1 : Bst P)) = algebraMap ℂ S (ι (x : Om l))) ∧
      ∀ c : ↥(MaximalUnramifiedExtension l), π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c) =
        algebraMap ℂ S (ι (c : Om l)) := by
  haveI : Nontrivial P.R.B := nontrivial_B P
  haveI : Nontrivial (Bst P) := inferInstanceAs (Nontrivial (Polynomial P.R.B))
  have hz : ∀ z : ℚ_[l], (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (algebraMap ℚ_[l] ↥LL.1 z) =
      (urC ι) (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) z) := by
    intro z
    simp only [urC, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact hRing ℚ_[l] ↥LL.1 ↥(MaximalUnramifiedExtension l) (Bst P) ℂ
    (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (urC ι) hz

set_option maxHeartbeats 1600000 in
private theorem core (hCo : CoFacts) (hCore : DetCore) (a : ℕ)
    (ρ : Representation ↥LL.1 ↥(GK K) (Fin a → ↥LL.1)) (ρ' : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ')]
    (S : Type) [CommRing S] [Algebra ℂ S] [Nontrivial S] (π : ↥LL.1 ⊗[ℚ_[l]] Bst P →+* S)
    (hfa : finrank ℂ (WDSpace P ι ρ) = a) (hf1 : finrank ℂ (WDSpace P ι ρ') = 1)
    (j : WDSpace P ι ρ →ₗ[ℂ] (Fin a → S)) (j1 : WDSpace P ι ρ' →ₗ[ℂ] (Fin 1 → S))
    (hj : ∀ x i, j (wdMk P ι ρ x) i = π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (hj1 : ∀ x i, j1 (wdMk P ι ρ' x) i = π (co (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (M : End ℂ (WDSpace P ι ρ)) (M' : End ℂ (WDSpace P ι ρ'))
    (w : ↥(Dpst P ρ) → ↥(Dpst P ρ)) (w' : ↥(Dpst P ρ') → ↥(Dpst P ρ'))
    (hM : ∀ x, M (wdMk P ι ρ x) = wdMk P ι ρ (w x)) (hM' : ∀ x, M' (wdMk P ι ρ' x) = wdMk P ι ρ' (w' x))
    (T : End ↥LL.1 (Fin a → ↥LL.1)) (T' : End ↥LL.1 (Fin 1 → ↥LL.1))
    (B : Matrix (Fin a) (Fin a) ↥LL.1) (B' : Matrix (Fin 1) (Fin 1) ↥LL.1)
    (hT : ∀ v, T v = B.mulVec v) (hT' : ∀ v, T' v = B'.mulVec v) (hB : B'.det = B.det)
    (σ : Bst P →ₐ[ℚ_[l]] Bst P)
    (hw : ∀ x, (w x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) =
      AlgebraTensorModule.map T σ.toLinearMap (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (hw' : ∀ x, (w' x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) =
      AlgebraTensorModule.map T' σ.toLinearMap (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (hmem : ∀ x : Fin a → ↥(Dpst P ρ), ∃ x' : ↥(Dpst P ρ'),
      co (x' : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0 =
        Matrix.det (Matrix.of fun i k => co (x k : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i))
    (hspan : Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i =>
      π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) = ⊤) :
    LinearMap.det M = LinearMap.det M' := by
  have hc4 := (hCo ℚ_[l] ↥LL.1 (Bst P) a).2.2.2.1
  have hc4' := (hCo ℚ_[l] ↥LL.1 (Bst P) 1).2.2.2.1
  refine hCore ℂ (↥LL.1 ⊗[ℚ_[l]] Bst P) S (WDSpace P ι ρ) (WDSpace P ι ρ') ↥(Dpst P ρ) ↥(Dpst P ρ') a π
    (wdMk P ι ρ) (wdMk P ι ρ') (fun x => co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P))
    (fun x => co (x : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] Bst P) 0) j ((LinearMap.proj 0).comp j1) M M' w w'
    (B.map (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P))) (onR ↥LL.1 σ) hfa hf1 (span_wdMk P ι ρ) hj
    (fun x => hj1 x 0) hM hM' ?_ ?_ hmem hspan
  · intro x
    rw [hw x]
    exact hc4 T B hT σ _
  · intro x
    rw [hw' x, hc4' T' B' hT' σ _]
    have e : (B.map (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P))).det =
        algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P) (B' 0 0) := by
      have e1 := RingHom.map_det (algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] Bst P)) B
      rw [RingHom.mapMatrix_apply] at e1
      rw [← e1, ← hB, Matrix.det_fin_one]
    rw [e]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one]
end

set_option maxHeartbeats 1600000 in
theorem UpperTheory.Gal.crystallineComparison.detOne_of :
    CoFacts → RingS → DetCore → DetMem → WeilCo → SpanS → CoLift → DetE := by
  intro hCo hRing hCore hMem hWeil hSpan hLift l _ P AI hAI ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a LL r c
    hdet hsst hr hc g hg
  haveI := hr.finite
  haveI := hc.finite
  obtain ⟨S, _, _, π, hS, hπL, hπU⟩ := ringS' P ι hRing LL
  refine (hLift l P ι Bw.Kw LL a (Bw.repE LL r) S π hπL hπU).elim ?_
  intro j hj1
  refine (hLift l P ι Bw.Kw LL 1 (Bw.repE LL c) S π hπL hπU).elim ?_
  intro j1 hj2
  have hdv : ∀ x, ((c x : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1).det =
      ((r x : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1).det := fun x => by
    have e := congrArg Units.val (hdet x)
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply] at e
  exact core P ι hCo hCore a (Bw.repE LL r) (Bw.repE LL c) S π (fa P ι a _ hr) (fa P ι 1 _ hc) j j1 hj1 hj2
    (wdRho P ι Bw h hj (Bw.repE LL r) g) (wdRho P ι Bw h hj (Bw.repE LL c) g)
    (weilD Bw h P (Bw.repE LL r) g) (weilD Bw h P (Bw.repE LL c) g) (fun x => rfl) (fun x => rfl)
    (Bw.repE LL r (weilToGK Bw h g)) (Bw.repE LL c (weilToGK Bw h g))
    ((r (Bw.e.symm (weilToGK Bw h g)) : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1)
    ((c (Bw.e.symm (weilToGK Bw h g)) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1)
    (fun v => GlobalTheory.ConjLocal.repE_apply Bw LL r _ v) (fun v => GlobalTheory.ConjLocal.repE_apply Bw LL c _ v) (hdv _)
    ((actSt P (weilToGK Bw h g : GQ l)).comp (phiSt P ^ resDeg l w))
    (fun x => hWeil l P E Ω A w h O Bw LL _ (Bw.repE LL r) g hg x)
    (fun x => hWeil l P E Ω A w h O Bw LL _ (Bw.repE LL c) g hg x)
    (hMem l P Bw.Kw LL a (Bw.repE LL r) (Bw.repE LL c)
      (fun y => ((r (Bw.e.symm y) : GL (Fin a) ↥LL.1) : Matrix (Fin a) (Fin a) ↥LL.1))
      (fun y => ((c (Bw.e.symm y) : GL (Fin 1) ↥LL.1) : Matrix (Fin 1) (Fin 1) ↥LL.1))
      (fun y v => GlobalTheory.ConjLocal.repE_apply Bw LL r y v) (fun y v => GlobalTheory.ConjLocal.repE_apply Bw LL c y v)
      (fun y => hdv _))
    (hSpan l P AI hAI Bw.Kw LL a (Bw.repE LL r) hsst S π)
