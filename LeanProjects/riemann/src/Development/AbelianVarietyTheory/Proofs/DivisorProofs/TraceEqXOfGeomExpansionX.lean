import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TestFnConstTermVanishX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricExpansionOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqualityOfGeomExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesOddRankGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalSpectrumFinitenessOfDecayHarishChandraStatement

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.PsCo.Pc.ArchT

section General

variable {H H' n V : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H'] [Fintype n]
  [DecidableEq n] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {e : H ≃ₜ* H'} {ι : H →* Matrix n n ℂ} {ι' : H' →* Matrix n n ℂ} {a : Matrix n n ℂ}
  [MeasurableSpace H] [BorelSpace H] [MeasurableSpace H'] [BorelSpace H']
  [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H]
  [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']

theorem isPCG_of_map (ha : IsUnit a) (hι : ∀ g, ι' (e g) = a * ι g * a⁻¹) {μ : Measure H} [μ.IsHaarMeasure]
    {D' : H' →* (V →L[ℂ] V)} {f' : H' → ℂ} (h : IsPCG ι' (μ.map e) D' f') :
    IsPCG ι μ (D'.comp (e : H →* H')) (f' ∘ e) := by
  refine ⟨comp_mem_ccMat hι h.mem, repOp_map e D' μ f' ▸ h.trace_self, fun U _ _ _ π h1 h2 h4 => ?_,
    fun s hs hT dt _ _ => ?_⟩
  · obtain ⟨π', rfl⟩ : ∃ π' : H' →* (U →L[ℂ] U), π = π'.comp (e : H →* H') :=
      ⟨π.comp (e.symm : H' →* H), MonoidHom.ext fun x => by simp⟩
    rw [← repOp_map]
    refine h.trace_other U π' ⟨fun g v => ?_, fun v => ?_⟩ ⟨h2.1, fun S hS => h2.2 S ⟨hS.1, fun g => hS.2 _⟩⟩
      fun ⟨A, hA⟩ => h4 ⟨A, fun g => hA _⟩
    · simpa using h1.1 (e.symm g) v
    · simpa [Function.comp_def] using (h1.2 v).comp (map_continuous e.symm)
  · exact (hasOrbInt_map e rfl f' _).1.1 (h.orb_noncompact _ ((isRegSS_conj_iff ha hι s).2 hs)
      (mt (isCompact_cent_iff e s).1 hT) _)

theorem orb_of_map {μ : Measure H} [μ.IsHaarMeasure] {f' : H' → ℂ} {s : H} {c : ℂ}
    (h : ∀ (dt : Measure (cent (e s))) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
      HasOrbInt (μ.map e) (e s) dt f' (c / dt.real univ))
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] :
    HasOrbInt μ s dt (f' ∘ e) (c / dt.real univ) := by
  have := h (dt.map (centEquiv e s rfl))
  rw [map_measureReal_apply (map_continuous _).measurable MeasurableSet.univ, preimage_univ] at this
  exact (hasOrbInt_map e rfl f' _).1.1 this

end General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem isPCG_dsRep (M : DSModel V S) (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ) :
    haveI := (M.ds ρ).1
    IsPCG (ujMat (M.ε ρ)) (μ.map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1) f →
      IsPCG (matAt V ρ) μ (dsRep M ρ) (f ∘ frameEquiv M ρ) :=
  haveI := (M.ds ρ).1
  fun h => isPCG_of_map (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ) h

theorem orb_dsRep (M : DSModel V S) (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ)
    (h : ∀ s, IsRegSS (ujMat (M.ε ρ) s) → IsCompact (cent s : Set (Formalism.REAL.UJ (M.ε ρ))) →
      ∀ (y : Formalism.REAL.UJ (M.ε ρ)) (θ : Fin V.rank → ℝ), y⁻¹ * s * y = torusPt (M.ε ρ) θ →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        HasOrbInt (μ.map (frameEquiv M ρ)) s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ))
    (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (hs : IsRegSS (matAt V ρ s))
    (hT : IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))))
    (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ)
    (hy : frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)))
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] :
    HasOrbInt μ s dt (f ∘ frameEquiv M ρ) (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  have h2 : (frameEquiv M ρ y)⁻¹ * frameEquiv M ρ s * frameEquiv M ρ y = torusPt (M.ε ρ) θ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subtype.ext (Units.ext hy)
  exact orb_of_map (h _ ((isRegSS_conj_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ) s).2 hs)
    ((isCompact_cent_iff (frameEquiv M ρ) s).2 hT) _ θ h2) dt

theorem exists_testArch (hL : LocalPC) (M : DSModel V S) (lam : D.what₂.Tau → Fin V.rank → ℤ) (hodd : Odd V.rank)
    (hgap : ∀ ρ, GapG V.rank (lam ρ)) (hlam : ∀ ρ i, M.lam ρ i = lam ρ i)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure] :
    ∃ fa, GlobalTheory.Orb.IsTestArchGX M μa fa ∧
      ∀ (ρ : D.what₂.Tau) (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
        IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
        ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
        frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
        ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        HasOrbInt (μa (placeOf D ρ)) s dt (fa (placeOf D ρ)) (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  have h1 : ∀ ρ, haveI := (M.ds ρ).1
      ∃ f, IsPCG (matAt V ρ) (μa (placeOf D ρ)) (dsRep M ρ) f ∧
        ∀ (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
        IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
        ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
        frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
        ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        HasOrbInt (μa (placeOf D ρ)) s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := fun ρ => by
    haveI := (M.ds ρ).1
    haveI : ((μa (placeOf D ρ)).map (frameEquiv M ρ)).IsHaarMeasure := (frameEquiv M ρ).isHaarMeasure_map _
    have e : M.lam ρ = fun a => (lam ρ a : ℝ) := funext (hlam ρ)
    obtain ⟨f, hf⟩ := hL V.rank hodd (M.ε ρ) (lam ρ) (hgap ρ) (M.H ρ) (M.σ ρ) (e ▸ M.ds ρ)
      ((μa (placeOf D ρ)).map (frameEquiv M ρ))
    refine ⟨f ∘ frameEquiv M ρ, isPCG_dsRep M ρ _ f hf.isPCG, fun s hs hT y θ hy dt _ _ => ?_⟩
    exact orb_dsRep M ρ _ f (by rw [e]; exact hf.2.2.2.2.2) s hs hT y θ hy dt
  choose f hf using h1
  let p := Equiv.ofBijective _ (placeOf_bijective D)
  have hp : ∀ ρ, Equiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w → ℂ) p f (placeOf D ρ) = f ρ := fun ρ =>
    Equiv.piCongrLeft_apply_apply (fun w => GArch D.sp.cm.sig V.gram w → ℂ) p f ρ
  refine ⟨Equiv.piCongrLeft (fun w => GArch D.sp.cm.sig V.gram w → ℂ) p f, fun ρ => ?_, fun ρ => ?_⟩
  · exact (hp ρ).symm ▸ (hf ρ).1
  · rw [hp ρ]; exact (hf ρ).2

end GlobalTheory.PsCo.Pc.ArchT

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.PsCo.Pc

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ArchO (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) : Prop :=
  ∀ (ρ : D.what₂.Tau) (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
    IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
    ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
    frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
    HasOrbInt (μa (placeOf D ρ)) s dt (fa (placeOf D ρ)) (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ)

theorem gap_of_gapG {r : ℕ} {lam : Fin r → ℤ} (h : GapG r lam) : Gap lam := by
  intro i j hij
  have h1 := h i j hij
  have h2 : (r : ℤ) ≤ 100 * (r : ℤ) ^ 4 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    · have : (1 : ℤ) ≤ r := by exact_mod_cast hr
      nlinarith [pow_le_pow_left₀ (by positivity : (0:ℤ) ≤ 1) this 3]
  linarith

theorem isPCG_dsRep (M : DSModel V S) (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ) :
    haveI := (M.ds ρ).1
    IsPCG (ujMat (M.ε ρ)) (μ.map (frameEquiv M ρ)) (ujRep (M.ds ρ).2.2.1) f →
      IsPCG (matAt V ρ) μ (dsRep M ρ) (f ∘ frameEquiv M ρ) := by
  exact ArchT.isPCG_dsRep M ρ μ f

theorem orb_dsRep (M : DSModel V S) (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ)))
    [μ.IsHaarMeasure] (f : Formalism.REAL.UJ (M.ε ρ) → ℂ)
    (h : ∀ s, IsRegSS (ujMat (M.ε ρ) s) → IsCompact (cent s : Set (Formalism.REAL.UJ (M.ε ρ))) →
      ∀ (y : Formalism.REAL.UJ (M.ε ρ)) (θ : Fin V.rank → ℝ), y⁻¹ * s * y = torusPt (M.ε ρ) θ →
      ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
        HasOrbInt (μ.map (frameEquiv M ρ)) s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ))
    (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (hs : IsRegSS (matAt V ρ s))
    (hT : IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))))
    (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ)
    (hy : frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)))
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] :
    HasOrbInt μ s dt (f ∘ frameEquiv M ρ) (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  exact ArchT.orb_dsRep M ρ μ f h s hs hT y θ hy dt

theorem exists_testArch (hL : LocalPC) (M : DSModel V S) (lam : D.what₂.Tau → Fin V.rank → ℤ) (hodd : Odd V.rank)
    (hgap : ∀ ρ, GapG V.rank (lam ρ)) (hlam : ∀ ρ i, M.lam ρ i = lam ρ i)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) [∀ w, (μa w).IsHaarMeasure] :
    ∃ fa, GlobalTheory.Orb.IsTestArchGX M μa fa ∧ ArchO M μa fa := by
  exact ArchT.exists_testArch hL M lam hodd hgap hlam μa

end GlobalTheory.PsCo.Pc

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.PsCo.Pc

def RealStableX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ),
    Odd V.rank → (∀ ρ, StrictAnti (lam ρ)) → (∀ ρ i, M.lam ρ i = lam ρ i) → (∀ w, (μa w).IsHaarMeasure) →
    GlobalTheory.Orb.IsTestArchGX M μa fa → ArchO M μa fa →
    ∀ (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) (dt : Measure (Tor P (placeOf D ρ).Completion)), dt.IsHaarMeasure →
      Phi (J := V.gram) (μa (placeOf D ρ)) dt (fa (placeOf D ρ)) = PhiReal P (embOverOf D ρ) (lam ρ) dt

def GeomExpansionX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V lam M T U μa μf μ fa ff → ArchO M μa fa →
    ∀ (dta : ∀ (P : PPol D.sp.cm.sig V.rank) (w : InfinitePlace D.host.F), Measure (Tor P w.Completion))
      (dtf : ∀ (P : PPol D.sp.cm.sig V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)), Measure (Tor P (Fv D.host.F v)))
      (dt : ∀ P : PPol D.sp.cm.sig V.rank, Measure (Tor P (AF D.host.F))),
      (∀ P, IsTorusMeas P (dta P) (dtf P) (dt P)) →
      (∀ P, FinOK V μf ff P (dtf P) (dt P)) ∧
      (Function.support fun P => term V lam μf ff P (dta P) (dtf P) (dt P)).Finite ∧
      HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ᶠ P, term V lam μf ff P (dta P) (dtf P) (dt P))

def TraceEqX : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V lam M T U μa μf μ fa ff → ArchO M μa fa →
    ∀ (V' : HSp D) (hr : V'.rank = V.rank) (S' : D.what₂.Tau → SPar) (M' : DSModel V' S'),
      (∀ ρ i, M'.lam ρ i = lam ρ (i.cast hr)) →
      ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v,
        (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) →
        ∀ (μa' : ∀ w, Measure (GArch D.sp.cm.sig V'.gram w)) (μ' : Measure (GA D V')) [μ'.IsHaarMeasure]
          [μ'.IsMulRightInvariant] (fa' : ∀ w, GArch D.sp.cm.sig V'.gram w → ℂ),
          IsRestrictedProd D.sp.cm.sig V'.gram (frameLat V') μa' (fun v => (μf v).map (j v)) μ' →
          GlobalTheory.Orb.IsTestArchGX M' μa' fa' → ArchO M' μa' fa' →
          ∃ c : ℂ, HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) c ∧
            HasTrace (RopG V' μ' (tensor D.sp.cm.sig V'.gram fa' (transfer j ff))) c

set_option maxHeartbeats 1000000 in

theorem realStableX : RealStableX := by
  intro D V lam S M μa fa hodd hlam hM hμa hfa hO P ρ dt hdt
  have hf := hfa ρ
  have := (M.ds ρ).1
  have := hμa (placeOf D ρ)
  have hl : Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨fun a b hab => ?_, fun a => ⟨lam ρ a - k, ?_⟩⟩
    · rw [hM, hM]; exact_mod_cast hlam ρ hab
    · rw [hM, hk]; push_cast; ring
  rw [Phi, PhiReal]
  split_ifs with hc
  · obtain ⟨hfin, y, θ, hbij, hexp, hconj⟩ := GlobalTheory.T.compactRealPlace_torusClasses_signVectors V M ρ P hc
    have hval : ∀ q : XSet P (placeOf D ρ).Completion V.gram, orbCls (J := V.gram) (μa (placeOf D ρ)) dt (fa (placeOf D ρ)) q =
        conj (dsChar (M.ε ρ) (M.lam ρ) (θ q)) / (dt.real univ : ℂ) := by
      intro q
      obtain ⟨hH, hR, hvol, hcpt⟩ := GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2
      obtain ⟨g, hg⟩ := hconj q
      have := hO ρ _ (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (hcpt.2 hc) g (θ q) hg (centMeas _ dt)
      rw [orbCls, this.orbInt_eq, hvol]
    have : Finite (XSet P (placeOf D ρ).Completion V.gram) := hfin.to_subtype
    have hlam' : M.lam ρ = fun a => ((lam ρ a : ℤ) : ℝ) := funext (hM ρ)
    have hinj : Function.Injective (cxRoots (embOverOf D ρ).1 P) := by
      have := P.2.2.1.separable.map (f := (embOverOf D ρ).1)
      rw [cxRoots_spec] at this
      exact Polynomial.separable_prod_X_sub_C_iff.1 this
    have h2 := GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter V.rank (M.ε ρ) (lam ρ) (cxRoots (embOverOf D ρ).1 P) _ y θ hodd hinj hbij hexp
    rw [finsum_congr hval, hlam', ← h2]
    have := Fintype.ofFinite (XSet P (placeOf D ρ).Completion V.gram)
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.sum_div]
  · refine (finsum_congr fun q => ?_).trans finsum_zero
    obtain ⟨hH, hR, hvol, hcpt⟩ := GlobalTheory.T.centralizer_torusEllipticElement_realPlace V P ρ dt q.2.choose_spec.choose_spec.2
    exact (hf.orb_noncompact _ (GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace V P ρ q.2.choose_spec.choose_spec.2) (mt hcpt.1 hc) _).orbInt_eq

theorem geomExpansionX_of_parts : GlobalTheory.TrMult.EllTraceX → GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX → RealStableX →
    GeomExpansionX := by
  intro hE hP hR D V lam S M T U μa μf μ _ _ fa ff hT hO dta dtf dt hdt
  obtain ⟨hOK, hfin, -, hint⟩ := hP D V lam S M T U μa μf μ fa ff hT dta dtf dt hdt
  have heq : ∀ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb V μa μf fa ff P (dta P) (dtf P) (dt P) = GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta P) (dtf P) (dt P) := by
    intro P
    unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
    congr 1
    rw [← (Equiv.ofBijective _ (GlobalTheory.AdelicU.placeOf_bijective D)).prod_comp]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    exact hR D V lam S M μa fa hT.1 (fun ρ => GlobalTheory.TrMult.strictAnti_of_gap hT.1 (hT.2.1 ρ)) hT.2.2.1 hT.2.2.2.2.1.1
      hT.2.2.2.2.2.1 hO P ρ (dta P (GlobalTheory.AdelicU.placeOf D ρ)) ((hdt P).1 _)
  have hfun : (fun P => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.termOrb V μa μf fa ff P (dta P) (dtf P) (dt P)) =
      fun P => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta P) (dtf P) (dt P) := funext heq
  refine ⟨fun P => (hOK P).1, hfun ▸ hfin, ?_⟩
  have h1 := hE D V lam S M T U μa μf μ fa ff hT
  rw [hint, hfun] at h1
  exact h1

theorem traceEqX_of_geomExpansionX : GeomExpansionX → TraceEqX := by
  intro hG D V lam S M T U μa μf μ _ _ fa ff hTD hO V' hr S' M' hlam' j hj μa' μ' _ _ fa' hR' hA' hO'
  obtain ⟨-, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF, hTF⟩ := hTU T U
  obtain ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩ := hTD
  set lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr) with hlamdef
  have hTD' : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V' lam' M' T' U' μa' (fun v => (μf v).map (j v)) μ' fa' (transfer j ff) := by
    refine ⟨hr ▸ hodd, ?_, hlam', hNF hnf, hR', hA', hTF μf ff hTFin⟩
    intro ρ i k hik
    have h := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    simpa [hr, lam'] using h
  choose dta dtf dt hdt using fun (r : ℕ) (P : PPol D.sp.cm.sig r) => GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.exists_isTorusMeas P
  obtain ⟨hFin, -, hTr⟩ := hG D V lam S M T U μa μf μ fa ff ⟨hodd, hgap, hMl, hnf, hRP, hTA, hTFin⟩ hO
    (dta _) (dtf _) (dt _) (hdt _)
  obtain ⟨hFin', -, hTr'⟩ := hG D V' lam' S' M' T' U' μa' _ μ' fa' _ hTD' hO' (dta _) (dtf _) (dt _) (hdt _)

  have gen : ∀ (r : ℕ) (h : r = V.rank),
      (∀ (P : PPol D.sp.cm.sig r) v, PhiOK (J := V.gram) (μf v) (dtf r P v) (ff v)) ∧
      ∑ᶠ P : PPol D.sp.cm.sig r, ((GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.torVol P (dt r P)).toReal : ℂ) *
          (∏ᶠ v, Phi (J := V.gram) (μf v) (dtf r P v) (ff v)) *
          ∏ ρ : D.what₂.Tau, PhiReal P (embOverOf D ρ) (fun i => lam ρ (i.cast h)) (dta r P (placeOf D ρ)) =
        ∑ᶠ P, GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term V lam μf ff P (dta _ P) (dtf _ P) (dt _ P) := by
    intro r h
    subst h
    exact ⟨fun P v => (hFin P).2.1 v, rfl⟩
  refine ⟨_, hTr, ?_⟩
  convert hTr' using 1
  rw [← (gen _ hr).2]
  refine finsum_congr fun P => ?_
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.term
  congr 2
  refine finprod_congr fun v => ?_
  exact (GlobalTheory.T.stableOrbitalIntegral_preserved_latticeIsometry D V V' _ P v (j v) (hj v) (μf v) (dtf _ P v) (ff v) (hRP.2.1 v) ((hdt _ P).2.1 v) ((gen _ hr).1 P v) ((hFin' P).2.1 v)).symm

end GlobalTheory.PsCo.Pc

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult GlobalTheory.TrMultEnd
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PsCo.Pc

def TRCusp' : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V),
    Odd V.rank → (∀ ρ, GapG V.rank (lam ρ)) → (∀ ρ i, M.lam ρ i = lam ρ i) → NoFixed T →
    ∀ (V' : HSp D) (hr : V'.rank = V.rank) (S' : D.what₂.Tau → SPar) (M' : DSModel V' S'), (∀ ρ i, M'.lam ρ i = lam ρ (i.cast hr)) →
    ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) →
    ∀ Φ : GfC V ≃ₜ* GfC V', (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (μ' : Measure (GA D V')) [μ'.IsHaarMeasure]
      [μ'.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
      σ.IsIrreducible → IsAdmissible σ → HasTypeVec T σ →
      mCuspDS μ σ M = mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M'

set_option maxHeartbeats 1000000 in

theorem trCusp'_of_steps (hL : LocalPC) (hF : SpecFin) (hT : GlobalTheory.TrMult.SpecTraceX) (hS : Separation)
    (hE : TraceEqX) : TRCusp' := by
  intro D V lam S M T hodd hgap hlam hnf V' hr S' M' hlam' j hj Φ hΦ μ _ _ μ' _ _ W _ _ σ hirr hadm htv
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_splitPlaceHermitianSpace_notMem_finset D V T.S
  let μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v) := fun v => haarLoc D.sp.cm.sig V.gram (frameLat V) v
  have hμf : ∀ v, (μf v).IsHaarMeasure := fun v => inferInstance
  have h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1 := Eventually.of_forall fun v => haarLoc_stabLoc _ _ _ v
  have h1K : ∀ v, μf v (Kv V v) = 1 := fun v => haarLoc_stabLoc _ _ _ v
  clear_value μf
  obtain ⟨⟨μa, hμa⟩, ν, hν⟩ := GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V μ μf hμf h1
  obtain ⟨hjK, hTU⟩ := GlobalTheory.T.testFunctions_transport_localLatticeIsometries D V V' hr j hj
  obtain ⟨T', U', hNF', hTF'⟩ := hTU T U
  let μf' : ∀ v, Measure (GLoc D.sp.cm.sig V'.gram v) := fun v => (μf v).map (j v)
  have hμf' : ∀ v, (μf' v).IsHaarMeasure := fun v => (j v).isHaarMeasure_map (μf v)
  have h1' : ∀ᶠ v in cofinite, μf' v (Kv V' v) = 1 := Eventually.of_forall fun v => by
    have hm : MeasurableSet (Kv V' v : Set (GLoc D.sp.cm.sig V'.gram v)) := (isOpen_stabLoc _ _ _ v).measurableSet
    rw [show μf' v (Kv V' v) = μf v ((j v) ⁻¹' (Kv V' v)) from Measure.map_apply (j v).continuous.measurable hm,
      show (j v) ⁻¹' (Kv V' v : Set _) = Kv V v from Set.ext fun g => hjK v g]
    exact h1K v
  obtain ⟨⟨μa', hμa'⟩, -⟩ := GlobalTheory.T.exists_restrictedProduct_haar_given_finiteFactors D V' μ' μf' hμf' h1'
  clear hμf'
  obtain ⟨hfinFn, hνmap⟩ := GlobalTheory.T.transport_pureTensors_productMeasure_finiteAdelic D V V' j hjK Φ hΦ
  have hν' := hνmap μf ν hν
  let lam' : D.what₂.Tau → Fin V'.rank → ℤ := fun ρ i => lam ρ (i.cast hr)
  have hgap' : ∀ ρ, GapG V'.rank (lam' ρ) := fun ρ i k hik => by
    have := hgap ρ (i.cast hr) (k.cast hr) (by simpa using hik)
    rw [hr]; exact this
  have hodd' : Odd V'.rank := hr ▸ hodd
  obtain ⟨fa, hfa, hfo⟩ := haveI := (isRestrictedProd_iff.1 hμa).1; exists_testArch hL M lam hodd hgap hlam μa
  obtain ⟨fa', hfa', hfo'⟩ := haveI := (isRestrictedProd_iff.1 hμa').1; exists_testArch hL M' lam' hodd' hgap' hlam' μa'
  obtain ⟨K, hKo, hKc, hK⟩ := GlobalTheory.T.exists_openCompact_level_sphericalOffTypes D V T U
  obtain ⟨hfin, hfam⟩ := hF D V S M μ
  obtain ⟨hfin', hfam'⟩ := hF D V' S' M' μ'
  obtain ⟨n₁, W₁, _, _, σ₁, hσ₁, hcov₁⟩ := hfam K hKo
  let K' : Subgroup (GfC V') := K.map Φ.toMulEquiv.toMonoidHom
  have hK'coe : (K' : Set (GfC V')) = Φ '' K := Subgroup.coe_map _ _
  have hK'o : IsOpen (K' : Set (GfC V')) := hK'coe ▸ Φ.toHomeomorph.isOpenMap _ hKo
  have hK'c : IsCompact (K' : Set (GfC V')) := hK'coe ▸ hKc.image Φ.continuous
  obtain ⟨n₂, W₂, _, _, σ₂, hσ₂, hcov₂⟩ := hfam' K' hK'o
  let B : ∀ i, Representation ℂ (GfC V) (W₂ i) := fun i => (σ₂ i).comp Φ.symm.symm.toMulEquiv.toMonoidHom
  obtain ⟨m, Ws, _, _, τ, hne, hA, hB, hmem, j₀, hj₀⟩ := exists_family σ₁ B σ

  have hBi : ∀ i, (B i).IsIrreducible ∧ IsAdmissible (B i) := fun i =>
    have h := GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ.symm (ν.map Φ) (W₂ i) (σ₂ i)
    ⟨h.1 (hσ₂.1 i), h.2.1 (hσ₂.2.1 i)⟩
  have hτ : ∀ i, (τ i).IsIrreducible ∧ IsAdmissible (τ i) :=
    hmem (fun X _ _ ρ => ρ.IsIrreducible ∧ IsAdmissible ρ) (fun i => ⟨hσ₁.1 i, hσ₁.2.1 i⟩) hBi ⟨hirr, hadm⟩
  let τ' : ∀ i, Representation ℂ (GfC V') (Ws i) := fun i => (τ i).comp Φ.symm.toMulEquiv.toMonoidHom
  have hfamτ : IsIrrFam τ := ⟨fun i => (hτ i).1, fun i => (hτ i).2, hne⟩
  have hfamτ' : IsIrrFam τ' := by
    refine ⟨fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).1 (hτ i).1, fun i => (GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.1 (hτ i).2,
      fun i k hik => ⟨fun e => (hne i k hik).false ?_⟩⟩
    exact (equivCompSymm (τ i) Φ.toMulEquiv).trans
      ((equivComp e Φ.toMulEquiv.toMonoidHom).trans (equivCompSymm (τ k) Φ.toMulEquiv).symm)

  have cov : ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) →
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V) X), ρ.IsIrreducible → IsAdmissible ρ →
        mCuspDS μ ρ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν ρ (finFn V ff) 0 → ∃ i, Nonempty (ρ.Equiv (τ i)) := by
    intro ff hffin hKinv X _ _ ρ hi ha hm hz
    haveI := hν.1
    obtain ⟨x, hx0, hx⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν ff hffin X ρ ha).2 K hKo hKc hKinv hz
    obtain ⟨i, ⟨e⟩⟩ := hcov₁ X ρ hi ha hm ⟨x, hx0, hx⟩
    obtain ⟨k, ⟨e'⟩⟩ := hA i
    exact ⟨k, ⟨e.trans e'⟩⟩
  have cov' : ∀ ff, IsFinFamily D.sp.cm.sig V'.gram (frameLat V') (transfer j ff) →
      (∀ k ∈ K, ∀ g, finFn V ff (k * g) = finFn V ff g) →
      ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC V') X), ρ.IsIrreducible → IsAdmissible ρ →
        mCuspDS μ' ρ M' ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) ρ (finFn V' (transfer j ff)) 0 →
          ∃ i, Nonempty (ρ.Equiv (τ' i)) := by
    intro ff hffin hKinv X _ _ ρ hi ha hm hz
    haveI := hν'.1
    have hKinv' : ∀ k ∈ K', ∀ g, finFn V' (transfer j ff) (k * g) = finFn V' (transfer j ff) g := by
      intro k hk g
      obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.1 hk
      obtain ⟨g₀, rfl⟩ := Φ.surjective g
      change finFn V' (transfer j ff) (Φ k₀ * Φ g₀) = _
      rw [← map_mul, hfinFn, hfinFn, hKinv k₀ hk₀]
    obtain ⟨x, hx0, hx⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V' (ν.map Φ) (transfer j ff) hffin X ρ ha).2 K' hK'o hK'c hKinv' hz
    obtain ⟨i, ⟨e⟩⟩ := hcov₂ X ρ hi ha hm ⟨x, hx0, hx⟩
    obtain ⟨k, ⟨e'⟩⟩ := hB i
    exact ⟨k, ⟨e.trans ((equivCompSymm' (σ₂ i) Φ).trans (equivComp e' Φ.symm.toMulEquiv.toMonoidHom))⟩⟩

  let a : Fin m → ℂ := fun i => ((mCuspDS μ (τ i) M).toNat : ℂ) - ((mCuspDS μ' (τ' i) M').toNat : ℂ)
  have key : ∀ ff, IsTestFin T U μf ff → SphRest T U ff →
      ∀ c : Fin m → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (τ i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0 := by
    intro ff hff hsph c hc
    obtain ⟨hffin, hKinv⟩ := hK μf hμf ff hff hsph
    clear hμf
    have htd : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V lam M T U μa μf μ fa ff :=
      ⟨hodd, fun ρ => gap_of_gapG (hgap ρ), hlam, hnf, hμa, hfa, hff⟩
    have h₁ := hT D V lam S M T U μa μf μ fa ff htd ν hν m Ws τ hfamτ (cov ff hffin hKinv) c hc
    have hff' := hTF' μf ff hff
    have htd' : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.IsTestDataX V' lam' M' T' U' μa' μf' μ' fa' (transfer j ff) :=
      ⟨hodd', fun ρ => gap_of_gapG (hgap' ρ), hlam', hNF' hnf, hμa', hfa', hff'⟩
    have hc' : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (ν.map Φ) (τ' i) (finFn V' (transfer j ff)) (c i) := by
      intro i
      obtain ⟨A, hA, hA'⟩ := hc i
      exact ⟨A, ((GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν _ (τ i)).2.2 (finFn V ff) (finFn V' (transfer j ff)) (hfinFn ff) A).2 hA, hA'⟩
    have h₂ := hT D V' lam' S' M' T' U' μa' μf' μ' fa' (transfer j ff) htd' (ν.map Φ) hν' m Ws τ' hfamτ'
      (cov' ff hff'.isFinFamily hKinv) c hc'
    obtain ⟨c₀, hc₁, hc₂⟩ := hE D V lam S M T U μa μf μ fa ff htd hfo V' hr S' M' hlam' j hj μa' μ' fa' hμa' hfa' hfo'
    have e : ∑ i, ((mCuspDS μ (τ i) M).toNat : ℂ) * c i = ∑ i, ((mCuspDS μ' (τ' i) M').toNat : ℂ) * c i :=
      h₁.2.symm.trans (hc₁.2.trans (hc₂.2.symm.trans h₂.2))
    simp only [a, sub_mul, Finset.sum_sub_distrib, e, sub_self]
  obtain ⟨hm₁, hm₂, htv₀⟩ := hj₀ (fun X _ _ ρ => mCuspDS μ ρ M = mCuspDS μ σ M ∧
    mCuspDS μ' (ρ.comp Φ.symm.toMulEquiv.toMonoidHom) M' = mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M' ∧
    HasTypeVec T ρ) ⟨rfl, rfl, htv⟩
  have ha := hS D V T U hU μf hμf h1 ν hν m Ws τ hfamτ a key j₀ htv₀
  have hnat : (mCuspDS μ σ M).toNat = (mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M').toNat := by
    have : ((mCuspDS μ (τ j₀) M).toNat : ℂ) = ((mCuspDS μ' (τ' j₀) M').toNat : ℂ) := sub_eq_zero.1 ha
    rw [← hm₁, ← hm₂]
    exact_mod_cast this
  have hσ' := GlobalTheory.T.representation_transport_topGroupEquiv _ _ Φ ν W σ
  rw [← Cardinal.cast_toNat_of_lt_aleph0 (hfin W σ hirr hadm),
    ← Cardinal.cast_toNat_of_lt_aleph0 (hfin' W _ (hσ'.1 hirr) (hσ'.2.1 hadm)), hnat]

end GlobalTheory.PsCo.Pc

end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows GlobalTheory.ParamMatch

noncomputable section

namespace GlobalTheory.PsCo.Pc

theorem params_match' : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)), ∃ (hr : (Wc D i).rank = (Yc D 0).rank) (lam : D.what₂.Tau → Fin (Yc D 0).rank → ℤ), Odd (Yc D 0).rank ∧ (∀ ρ, GapG (Yc D 0).rank (lam ρ)) ∧ (∀ ρ a, M₀.lam ρ a = lam ρ a) ∧ ∀ ρ a, (R.MW i (sg0 D A)).lam ρ a = lam ρ (a.cast hr) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG i M₀
  have hY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
    simp [Ranks.rankY]
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℚ)) = Formalism.L2.NTheta.lamAt (D.hc ρ) n := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast]
  have keyR : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℝ)) = ((Formalism.L2.NTheta.lamAt (D.hc ρ) n : ℚ) : ℝ) := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast, Rat.cast_intCast]
  refine ⟨hW.trans hY.symm, fun ρ a => ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋, hY ▸ Formalism.L2.NTheta.odd_r D.R, ?_, ?_, ?_⟩
  · intro ρ a b hab
    have hb : (b : ℕ) < D.R.r := lt_of_lt_of_eq b.2 hY
    have h1 := hG.gapR ρ a (by omega)
    rw [← hab] at h1
    have : 100 * ((Yc D 0).rank : ℚ) ^ 4 ≤ ((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋ - ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (b : ℕ)⌋ : ℤ) : ℚ) := by
      have hYq : ((Yc D 0).rank : ℚ) = (D.R.r : ℚ) := by exact_mod_cast hY
      push_cast
      rw [key, key, hYq]
      linarith
    exact_mod_cast this
  · intro ρ a
    rw [enum_fst (M₀.enum ρ) (fun a : Fin (Yc D 0).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hY.le) (parA_fst D ρ hY) a, keyR]
  · intro ρ a
    rw [enum_fst ((R.MW i (sg0 D A)).enum ρ) (fun a : Fin (Wc D i).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hW.le) (parAt_fst R i ρ hW) a]
    exact (keyR ρ (a : ℕ)).symm

set_option maxHeartbeats 1000000 in

theorem multEq_of_trCusp' : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → TRCusp' → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hRD hHC hDM hGC hTR D G _ _ Pl0 T A Ks _ _ _ R F hG
  intro i M₀ j Φ hΦ W _ _ σ hirr hadm hgood
  obtain ⟨Ty, hNF, hTV⟩ := GlobalTheory.T.exists_typeVector_of_good_level_representation hGC R F hG W σ hadm hgood
  obtain ⟨jl, Φ₀, b, hjl, hΦ₀, hb⟩ := GlobalTheory.T.exists_localIsometries_innerAut_adelicFrameIsometry R F hG i j Φ hΦ
  obtain ⟨hr, lam, hodd, hgap, hM₀, hMW⟩ := params_match' R F hG i M₀
  have hinf : IsInfFam R.θ := hG.core.models.inf
  let μ : Measure (GA D (Yc D 0)) := Measure.haar
  let μ' : Measure (GA D (Wc D i)) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ inferInstance
  haveI : μ'.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ' inferInstance
  have hadm' : IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom) :=
    GlobalTheory.CuspMult.isAdmissible_comp_equiv σ Φ.symm hadm
  rw [GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Yc D 0) _ M₀ μ W σ hadm.1,
    GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Wc D i) _ (R.MW i (sg0 D A)) μ' W _ hadm'.1,
    hTR D (Yc D 0) lam _ M₀ Ty hodd hgap hM₀ hNF (Wc D i) hr _ (R.MW i (sg0 D A)) hMW jl hjl Φ₀ hΦ₀ μ μ' W σ hirr hadm hTV]
  exact ((mDS_congr (GlobalTheory.MultEqTrace.conjEquiv σ Φ.toMulEquiv Φ₀.toMulEquiv b hb)).2).symm

theorem multEq_of_sides : LocalPC → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → SpecTraceX → Separation → EllTraceX → GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hL rd hf dm gc hS hSep hE hP D G _ _ Pl0 T A Ks _ _ _ R F hG
  exact multEq_of_trCusp' rd hf dm gc (trCusp'_of_steps hL (GlobalTheory.T.cuspidal_spectrum_finiteness_of_decay_harishChandra rd hf dm) hS hSep
    (traceEqX_of_geomExpansionX (geomExpansionX_of_parts hE hP realStableX))) R F hG

end GlobalTheory.PsCo.Pc

end
end
