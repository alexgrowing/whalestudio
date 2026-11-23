import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section agree

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def agNN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), p.2.2))

def agN (p : B.SS k r) : B.SS k r :=
  ((Matrix.of.symm (1 : B.Mat k r), p.1.2), (Matrix.of.symm (1 : B.Mat k r), Matrix.of.symm (1 : B.Mat k r)))

theorem agNN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agNN p) := by
  obtain ⟨_, h2, _, h4⟩ := hp
  refine ⟨?_, h2, ?_, h4⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _

theorem agN_inSS (Bs : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : Bs.inSS p) : Bs.inSS (agN p) := by
  obtain ⟨_, h2, _, _⟩ := hp
  refine ⟨?_, h2, ?_, ?_⟩
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.one_uw _
  · show Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ _
    rw [Equiv.apply_symm_apply]; exact WeylGroupFacts.mem_n_one

theorem sgs_agNN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agNN p) g = (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 := by
  simp only [B.sgs, agNN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_agN (p : B.SS k r) (g : B.Mat k r) :
    B.sgs (agN p) g = (Matrix.of p.1.2)⁻¹ * g := by
  simp only [B.sgs, agN, Equiv.apply_symm_apply, inv_one, one_mul, mul_one]

theorem sgs_split (p : B.SS k r) (g : B.Mat k r) :
    B.sgs p g = (Matrix.of p.1.1)⁻¹ * ((Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2) * Matrix.of p.2.1 := by
  simp only [B.sgs, mul_assoc]

theorem agree_sgs (Bs : B.RealPlaceData k r Wp Wq) (f₁ f₂ : B.Mat k r → (Wq →L[ℂ] Wp))
    (hL₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (n * g) = psi k r Bs.z cStd n • f₁ g)
    (hR₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₁ (g * n) = psi k r Bs.z' cStd n • f₁ g)
    (hU₁ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₁ (h * g * h') = (Bs.π h).comp ((f₁ g).comp (Bs.π' h')))
    (hL₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (n * g) = psi k r Bs.z cStd n • f₂ g)
    (hR₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ n ∈ Nset k r, f₂ (g * n) = psi k r Bs.z' cStd n • f₂ g)
    (hU₂ : ∀ g ∈ JF.Om k r Bs.z Bs.z', ∀ h ∈ UWset k r Bs.z, ∀ h' ∈ UWset k r Bs.z',
      f₂ (h * g * h') = (Bs.π h).comp ((f₂ g).comp (Bs.π' h')))
    {p : B.SS k r} (hp : Bs.inSS p) {x : B.Mat k r} (hx : x ∈ JF.Om k r Bs.z Bs.z') (he : f₁ x = f₂ x) :
    f₁ (B.sgs p x) = f₂ (B.sgs p x) := by
  have hp' := hp
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have hx1 : (Matrix.of p.1.2)⁻¹ * x ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agN_inSS Bs hp) hx
  have hx2 : (Matrix.of p.1.2)⁻¹ * x * Matrix.of p.2.2 ∈ JF.Om k r Bs.z Bs.z' := by
    rw [← sgs_agNN p x]; exact Formalism.FourierDecayAlt.P.PositiveOrbitOpen.sgs_Om Bs (agNN_inSS Bs hp) hx
  have hn := WeylGroupFacts.mem_n_inv h2
  have hu := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv h1
  rw [sgs_split, hU₁ _ hx2 _ hu _ h3, hU₂ _ hx2 _ hu _ h3, hR₁ _ hx1 _ h4, hR₂ _ hx1 _ h4,
    hL₁ _ hx _ hn, hL₂ _ hx _ hn, he]

variable [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem agreement_on_domain_holds : AgreeOm := by
  intro k r Wp Wq _ _ _ _ _ _ Bs J F U hJ hag g hg hgU
  obtain ⟨p, hp, q, hq, rfl⟩ := Formalism.FourierDecayAlt.P.psiOnto_true k r Wp Wq Bs g hg
  have hgq := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom Bs hq
  have hGq : Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U := by
    have e : Gf k r Bs.z Bs.z' (B.sgs p (B.gq Bs q)) = Gf k r Bs.z Bs.z' (B.gq Bs q) := by
      unfold Gf
      rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp, Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp]
    rw [← e]; exact hgU
  have hD : ∀ y ∈ JF.Om k r Bs.z Bs.z', y ∈ Q.Glev k r 0 ∩ {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := fun y hy =>
    ⟨Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hy.1, Formalism.FourierDecayAlt.P.CutMP.jdc_of_om _ _ hy⟩
  have hNl : ∀ n ∈ Formalism.QuantumDeterminants.Nset k r, n ∈ Q.Nlev k r 0 := fun n hn => ⟨hn, Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.glev0 hn.1⟩
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bs.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Bs.z Bs.z' cStd Bs.π Bs.π' Bs.μW Bs.μN Bs.μW' F Bs.z_mem Bs.z'_mem
    Bs.haarN.conc (fun n₀ h => Bs.haarN.left n₀ h)
  refine agree_sgs Bs J (B.JF Bs F)
    (fun y hy n hn => hJ.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy n hn => hJ.2.2.1 y (hD y hy) n (hNl n hn))
    (fun y hy h hh h' hh' => hJ.2.2.2 y (hD y hy) h hh h' hh')
    (fun y _ n hn => ?_) (fun y _ n hn => ?_)
    (fun y _ h hh h' hh' => Formalism.FourierDecayAlt.P5.jf_uEquiv Bs F y hh hh')
    hp hgq (hag q hq hGq)
  · have e := hN y n hn 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z'_mem, mul_one] at e
    exact e
  · have e := hN y 1 WeylGroupFacts.mem_n_one n hn
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Bs.z_mem, one_mul] at e
    exact e

end agree

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
