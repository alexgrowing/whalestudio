import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.DualRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.PairOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (r : Resid F O n) [IsCO O O] [IsCO O (DualNumber O)] (ρ : F.G₀ →* GL (Fin n) O) (ψ : ∀ v, Fin n → F.Gv v →* Oˣ)
    (ρ' : F.G₀ →* GL (Fin n) (DualNumber O)) (P' : GL (Fin n) (DualNumber O)) (ψ' : ∀ v, Fin n → F.Gv v →* (DualNumber O)ˣ)
    (hn : 1 ≤ n) (hD : (GDet.ofRep (mat ρ)).map (res O O : O →+* ResidueField O) = r.Dbar) (hψ : ∀ v i, r.IsPsi v i (ψ v i))
    (hcont : ∀ i j, AdicCont (maximalIdeal (DualNumber O)) fun g => mat ρ' g i j) (hform : F.IsForm O n ρ' P')
    (hflag : ∀ v, HasFlag (ρ'.comp (F.φ v)) (ψ' v)) (hine : ∀ u, ∀ g ∈ r.Ip u, ρ' g = 1)
    (hρ : pushRep (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) ρ' = ρ)
    (hψ' : ∀ v i, pushCh (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) (ψ' v i) = ψ v i ∧
      (AdicCont (maximalIdeal (DualNumber O)) fun g => ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O)) ∧
      ∀ g, g ∈ F.Iv v ∨ g ∈ F.mu v → ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O).snd = 0) :
    ∃ p : Pair r (DualNumber O), p.Maps (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) (GDet.ofRep (mat ρ)) ψ ∧
      (∀ g, p.D.tr (MonoidAlgebra.single g 1) = (mat ρ' g).trace) ∧
      ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber O)ˣ) : DualNumber O).snd = 0 := by
  set f : DualNumber O →+* O := (TrivSqZeroExt.fstHom O O O : DualNumber O →+* O) with hf
  have hmap : (GDet.ofRep (mat ρ')).map f = GDet.ofRep (mat ρ) := by
    rw [(CA.d_gmap (GDet.ofRep (mat ρ'))).2.2.2 f (mat ρ'), ← hρ]
    rfl
  have hres : ((res O (DualNumber O) : DualNumber O →ₐ[O] ResidueField O) : DualNumber O →+* ResidueField O) =
      (res O O : O →+* ResidueField O).comp f :=
    RingHom.ext fun x => (res_map (TrivSqZeroExt.fstHom O O O) x).symm
  have hfst : ∀ v i g, f ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O) = ((ψ v i g : Oˣ) : O) := by
    intro v i g
    have := congrArg (fun χ : F.Gv v →* Oˣ => ((χ g : Oˣ) : O)) (hψ' v i).1
    simpa [pushCh] using this
  have hpsi : ∀ v i, r.IsPsi v i (ψ' v i) := by
    intro v i
    refine ⟨(hψ' v i).2.1, fun g => ?_, fun g => ?_⟩
    · have h1 := res_map (TrivSqZeroExt.fstHom O O O) ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O)
      rw [← h1]
      have h2 := hfst v i g
      simp only [hf] at h2
      rw [show (TrivSqZeroExt.fstHom O O O) ((ψ' v i g : (DualNumber O)ˣ) : DualNumber O) = ((ψ v i g : Oˣ) : O) from h2]
      exact (hψ v i).red g
    · have hs := (hψ' v i).2.2 g (Or.inr g.2)
      have h2 := hfst v i g
      have h3 := (hψ v i).mu g
      ext
      · simp only [hf] at h2
        simpa [h3, TrivSqZeroExt.algebraMap_eq_inl] using h2
      · simpa [TrivSqZeroExt.algebraMap_eq_inl] using hs
  have hred : (GDet.ofRep (mat ρ')).map (res O (DualNumber O) : DualNumber O →+* ResidueField O) = r.Dbar := by
    rw [hres, ← (CA.d_gmap (GDet.ofRep (mat ρ'))).2.1, hmap, hD]
  obtain ⟨p, hpD, hpψ⟩ := pairOfRep F O r (DualNumber O) ρ' P' ψ' hn hcont hred hform hpsi hflag hine
  refine ⟨p, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hpD, hmap]
  · intro v i
    rw [hpψ]
    exact (hψ' v i).1
  · intro g
    rw [hpD, (AlgebraTools.Det.repApi (mat ρ')).2.2.1 hn]
    simp [GDet.repAlg]
  · intro v i g hg
    rw [hpψ]
    exact (hψ' v i).2.2 g (Or.inl hg)

theorem UpperTheory.V.Th.Nm.pairDual :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (y : Pt (reIu F r.Ip) c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O c.O] [IsCO c.O (DualNumber c.O)], 1 ≤ n → OCoc y z → (GDet.ofRep (mat y.ρ)).map (res c.O c.O : c.O →+* ResidueField c.O) = r.Dbar → (∀ v i, r.IsPsi v i (y.ψ v i)) → ∃ p : Pair r (DualNumber c.O), p.Maps (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (GDet.ofRep (mat y.ρ)) y.ψ ∧ (∀ g, (p.D.tr (MonoidAlgebra.single g 1)).snd = (z g * mat y.ρ g).trace) ∧ ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  intro l _ n F c r y z _ _ hn hz hD hψ
  obtain ⟨ρ', P', ψ', hcont, hform, hflag, hine, hρ, htr, hψ'⟩ := dualRep (reIu F r.Ip) c y z hz
  obtain ⟨p, h1, h2, h3⟩ := auxiliaryVectors_pairing_eq_antiDiagonal_gram F c.O r y.ρ y.ψ ρ' P' ψ' hn hD hψ hcont hform hflag hine hρ hψ'
  exact ⟨p, h1, fun g => (congrArg TrivSqZeroExt.snd (h2 g)).trans (htr g), h3⟩
