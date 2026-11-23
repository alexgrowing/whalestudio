import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.ChiExtend
end GlobalTheory.ChiExtend
namespace GlobalTheory.ChiExtend
end GlobalTheory.ChiExtend
open GlobalTheory.ChiExtend in
theorem GlobalTheory.ChiExtend.chi_eq_of_ext_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₀ L₀ → _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  intro _ D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ _ _ hCheb big₀ big₁ L₀ L₁ hB₀ hB₁ i₀ i₁ hw hj φ hφ hφalg c hc1 hct σ
  obtain ⟨Sp₀, ⟨AS₀⟩, -⟩ := hB₀
  obtain ⟨Sp₁, ⟨AS₁⟩, -⟩ := hB₁
  have hw' : L₀.X.nd.w i₀ = L₁.X.nd.w i₁ := hw
  have hj' : L₀.X.nd.j i₀ = L₁.X.nd.j i₁ := hj
  have hl : L₀.lay.fixZ.nd.l i₀ = L₁.lay.fixZ.nd.l i₁ := by
    rw [← L₀.lay.fixZ.nd.w_l i₀, ← L₁.lay.fixZ.nd.w_l i₁, hw]
  have hmu : L₀.Y.muC i₀ = L₁.Y.muC i₁ := by
    have hr := L₀.X.nd.j_range i₀
    let jj : Fin D.R.m := ⟨L₀.X.nd.j i₀ - 1, by omega⟩
    have e₀ := AS₀.muC i₀ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₀.X.nd.j i₀; omega)
    have e₁ := AS₁.muC i₁ jj (by show L₀.X.nd.j i₀ - 1 + 1 = L₁.X.nd.j i₁; omega)
    apply A.chr.e1.injective
    apply Subtype.ext
    have hm : L₀.X.nd.mu i₀ = L₁.X.nd.mu i₁ := by
      exact (L₀.X.mu_w i₀).trans ((congrArg D.what₂.muTw hw').trans (L₁.X.mu_w i₁).symm)
    exact e₀.trans ((congrArg (fun m => tp.tup m jj) hm).trans e₁.symm)
  have hl₀ := (L₀.lay.fixZ.nd.lPrime i₀).out.ne_zero
  have hfin : (placesOver D.host.E (L₀.lay.fixZ.nd.l i₀) ∪ ((L₀.lay.fixZ.nd.S i₀ : Set (PlE D.host)) ∪
      (L₀.lay.fixZ.nd.Q i₀ : Set (PlE D.host))) ∪ ((L₁.lay.fixZ.nd.S i₁ : Set (PlE D.host)) ∪
      (L₁.lay.fixZ.nd.Q i₁ : Set (PlE D.host)))).Finite :=
    ((placesOver_finite' _ _ hl₀).union ((Finset.finite_toSet _).union (Finset.finite_toSet _))).union
      ((Finset.finite_toSet _).union (Finset.finite_toSet _))
  have hout : ∀ w ∉ hfin.toFinset, IsSplitPl D.host w →
      SplitOut L₀.lay.fixZ.nd i₀ w ∧ SplitOut L₁.lay.fixZ.nd i₁ w := by
    intro w hwF hsp
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Finset.mem_coe, not_or] at hwF
    obtain ⟨⟨hpl, hS₀, hQ₀⟩, hS₁, hQ₁⟩ := hwF
    exact ⟨⟨hsp, hpl, hS₀, hQ₀⟩, ⟨hsp, hl ▸ hpl, hS₁, hQ₁⟩⟩
  have hone : (fun σ : GE L₁.lay.fixZ.nd => ((L₁.lay.fixZ.nd.chi i₁ 1 σ : (L₁.lay.fixZ.nd.O i₁)ˣ) :
      L₁.lay.fixZ.nd.O i₁)) = fun σ => φ ((L₀.lay.fixZ.nd.chi i₀ 1 σ : (L₀.lay.fixZ.nd.O i₀)ˣ) :
      L₀.lay.fixZ.nd.O i₀) := by
    haveI := L₁.lay.fixZ.nd.O_complete i₁
    refine eq_of_dense (L₁.lay.fixZ.nd.O_adic i₁) inferInstance (L₁.lay.fixZ.nd.chi_cont i₁ 1)
      ((continuous_of_le_comap (L₀.lay.fixZ.nd.O_adic i₀) (L₁.lay.fixZ.nd.O_adic i₁) φ
        (maximalIdeal_le_comap hl φ hφalg)).comp (L₀.lay.fixZ.nd.chi_cont i₀ 1)) (hCheb hfin.toFinset) ?_
    rintro σ ⟨w, hwF, hsp, B, hB, hσ⟩
    obtain ⟨ho₀, ho₁⟩ := hout w hwF hsp
    have e₀ := (L₀.lay.fixZ.naut.chi_mu i₀ w ho₀).2 B σ hB hσ
    have e₁ := (L₁.lay.fixZ.naut.chi_mu i₁ w ho₁).2 B σ hB hσ
    have em := congrArg (fun m => D.naut.frobEig (D.naut.lpTw (D.naut.locG (D.naut.tw m D.naut.etaTinv) w)
      (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2))) hmu
    have e := Multiset.singleton_inj.1 (e₀.symm.trans (em.trans e₁))
    apply iotaO_injective L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁
    rw [hφ]
    exact e.symm
  have hu1 : L₁.lay.fixZ.nd.chi i₁ 1 σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ 1 σ) := Units.ext (congrFun hone σ)
  have key : L₁.lay.fixZ.nd.chi i₁ c σ = Units.map (φ : L₀.lay.fixZ.nd.O i₀ →* L₁.lay.fixZ.nd.O i₁)
      (L₀.lay.fixZ.nd.chi i₀ c σ) := by
    rw [L₁.lay.fixZ.nd.chi_def i₁ c hc1 hct, L₀.lay.fixZ.nd.chi_def i₀ c hc1 hct]
    simp only [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    erw [MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, map_mul, map_zpow]
    rw [hu1]
    refine congrArg _ (congrArg (· ^ _) ?_)
    apply Units.ext
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact (hφalg _ _ (cyc_heq _ _ hl σ)).symm
  exact congrArg Units.val key
end
end
