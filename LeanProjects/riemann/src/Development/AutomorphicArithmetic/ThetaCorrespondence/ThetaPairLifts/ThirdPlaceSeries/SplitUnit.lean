import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypePlacesSplitIdempotents
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LevelPlaces
end GlobalTheory.LevelPlaces
namespace GlobalTheory.LevelPlaces
theorem split_unit_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → GlobalTheory.Core.Mi.IsTypePlaces (_root_.GlobalTheory.Fam.pk_z W).Pg → ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ((∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D (PP.under (𝓞 D.host.F)) ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) ∧ (∀ a ∈ GlobalTheory.FinPl.intAt D (· = (PP.under (𝓞 D.host.F))), incA D D.host.xi0 * a ∈ GlobalTheory.FinPl.intAt D (· = (PP.under (𝓞 D.host.F))) ∧ incA D D.host.xi0⁻¹ * a ∈ GlobalTheory.FinPl.intAt D (· = (PP.under (𝓞 D.host.F)))) ∧ ∀ (V : HSp D) (Λ : GlobalTheory.FinPl.Lat V), GlobalTheory.FinPl.latA V Λ (· = (PP.under (𝓞 D.host.F))) = GlobalTheory.FinPl.latV V Λ (· = (PP.under (𝓞 D.host.F)))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hpk hTy PP hPP
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hTy.1 PP hPP
  rw [Nat.cast_mul] at hg
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    rcases PP.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    rw [map_natCast]; exact hk
  obtain ⟨i, hi⟩ := ((GlobalTheory.PlacesOverG.places_over_g_k D k).2.1 PP).1 hk
  have key : ∀ {v v' : HeightOneSpectrum (𝓞 D.host.F)}, v = v' → Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v) →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v') := by
    rintro v _ rfl h; exact h
  have hτ : Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (PP.under (𝓞 D.host.F))) := by
    rcases i with w | w
    · have hi' : D.naut.plGw k w = PP := hi
      exact key (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi')
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
    · have hi' : GlobalTheory.IdemSupport.cP (D.naut.plGw k w) = PP := hi
      exact key ((GlobalTheory.IdemSupport.under_cP _).symm.trans (congrArg (HeightOneSpectrum.under (𝓞 D.host.F)) hi'))
        (GlobalTheory.LocPlSplit.nonempty_of_not_isConjPl (not_isConjPl_lev (D.naut.plGw_nconj k w w)))
  obtain ⟨τ⟩ := hτ
  have he := GlobalTheory.AdelicU.Supp.splitAt_splitIdemAd (D := D) τ
  have hε := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D (PP.under (𝓞 D.host.F))
  have hs := he.2.2.trans (GlobalTheory.AdelicU.Supp.pl_eq D (PP.under (𝓞 D.host.F)))
  have hsplit : IsSplitIdem D (GlobalTheory.AdelicU.Supp.splitIdemAd _ τ) := ⟨he.1, he.2.1, _, _, hε, hs⟩
  obtain ⟨p, -, hpv⟩ := GlobalTheory.FinPl.SplitPoint.exists_splitPt D _ _ _ hsplit hε hs
  have hne : ∀ m ∈ D.host.condN.primeFactors, D.host.g k ≠ m := fun m hm e => by
    have := GlobalTheory.RamValCheck.g_coprime D k m hm
    rw [e, Nat.coprime_self] at this
    exact hgp.one_lt.ne' (e ▸ this)
  have hc : Nat.Coprime (Ideal.absNorm D.host.ccK) (D.host.g k) := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hgp).2 fun ⟨m, hm⟩ => ?_)
    refine hpk.aa PP (Or.inr (Or.inl hPP)) ?_
    rw [hm, Nat.cast_mul]
    exact PP.asIdeal.mul_mem_right _ hk
  have hu := GlobalTheory.FinPl.UnitAt.unitAA_of_prime p hgp (by rw [hpv]; exact hv) (UpperTheory.Ram.g_notMem_small D k)
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.q_prime, D.host.q_dvd_condN, D.host.condN_ne_zero⟩))
    (hne _ (Nat.mem_primeFactors.2 ⟨D.host.d_prime, D.host.d_dvd_condN, D.host.condN_ne_zero⟩)) hc
  unfold GlobalTheory.FinPl.SplitPt.UnitAA at hu
  rw [hpv] at hu
  exact ⟨⟨_, _, hsplit, hε, hs⟩, hu.1, hu.2⟩
end GlobalTheory.LevelPlaces
end
