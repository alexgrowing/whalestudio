import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHostStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepDeRhamIffAndMultiplicityAddStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbarStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHostStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

theorem exists_model : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    ∀ L₀ : FinExt l, ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ := GlobalTheory.T.exists_continuous_ladicGalRep_model_finite_ext_host

theorem dsum_local : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O]
      [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (LL' : FinExt l) (a b : ℕ)
      (r₁ : ↥Gw →* GL (Fin a) ↥LL'.1) (r₂ : ↥Gw →* GL (Fin b) ↥LL'.1),
      (Bw.IsdRE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) ↔ Bw.IsdRE P LL' r₁ ∧ Bw.IsdRE P LL' r₂) ∧
      ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (c : ℤ),
        Bw.multE P LL' (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) τ' c = Bw.multE P LL' r₁ τ' c + Bw.multE P LL' r₂ τ' c := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add

theorem exists_place : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host,
    w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := GlobalTheory.T.exists_finitePlace_over_l_of_hostEmbedding_qbar

theorem exists_ext : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O),
    GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
    ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := GlobalTheory.T.exists_completionEmbedding_inducing_hostEmbedding

theorem wdOf_sumRep_away : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) →
    Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) →
    GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') =
      (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') := GlobalTheory.T.weilDeligneParamOfLadicRep_sumRep_awayFrom_l_host

theorem wdAt_sumRep : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)
      (a b : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (r' : ↥(Dec (F := E) A) →* GL (Fin b) (Om l)),
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw r' → GlobalTheory.Pst.IsPstAt P Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') →
      GlobalTheory.Pst.wdAt P ι Bw h hj (Formalism.MainNotions.SumRepresentations.At.sumRep r r') =
        (GlobalTheory.Pst.wdAt P ι Bw h hj r).lpSum (GlobalTheory.Pst.wdAt P ι Bw h hj r') := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable

theorem wdAt_bridge : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (ι : Om l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
      [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O')
      (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw')
      (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)),
      Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) →
      GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r →
      GlobalTheory.Pst.wdAt P ι Bw h hj r = GlobalTheory.Pst.wdAt P ι Bw' h hj' r := GlobalTheory.T.weilDeligneParamAbove_l_independent_localEmbedding

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section Gen
variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}

theorem sumRep_apply (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin (a + b)) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j =
      Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
        (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := rfl

theorem mapRep_sumRep (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) i j) = _
  rw [sumRep_apply, sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

theorem comp_sumRep {Δ : Type} [Group Δ] (φ : Δ →* Γ) (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂).comp φ = Formalism.MainNotions.SumRepresentations.At.sumRep (r₁.comp φ) (r₂.comp φ) := by
  ext g i j
  rfl

theorem cont_sumRep [TopologicalSpace Γ] [TopologicalSpace k] (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k)
    (h₁ : Continuous fun g => ((r₁ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k))
    (h₂ : Continuous fun g => ((r₂ g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k)) :
    Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂ g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [sumRep_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  · exact h₁.matrix_elem i j
  · exact continuous_const
  · exact continuous_const
  · exact h₂.matrix_elem i j
end Gen

end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem model_enlarge {a : ℕ} {L₁ L₂ : FinExt l} (h : L₁.1 ≤ L₂.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L₁.1)
    (hc : Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥L₁.1) : Matrix (Fin a) (Fin a) ↥L₁.1))) :
    Continuous (fun g => ((mapRep (IntermediateField.inclusion h).toRingHom ρ₁ g : GL (Fin a) ↥L₂.1) :
      Matrix (Fin a) (Fin a) ↥L₂.1)) ∧
    mapRep (algebraMap ↥L₂.1 (Qbar l)) (mapRep (IntermediateField.inclusion h).toRingHom ρ₁) =
      mapRep (algebraMap ↥L₁.1 (Qbar l)) ρ₁ := by
  refine ⟨continuous_matrix fun i j => continuous_induced_rng.2 ?_, ?_⟩
  · exact (continuous_subtype_val.comp (hc.matrix_elem i j)).congr fun g => rfl
  · ext g i j; rfl

theorem two_models {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (L₀ : FinExt l) :
    ∃ (LL' : FinExt l) (_ : L₀.1 ≤ LL'.1) (ρ₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥LL'.1)
      (ρ₂ : G D.host.E D.nd.Om →* GL (Fin b) ↥LL'.1),
      Continuous (fun g => ((ρ₁ g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1)) ∧
      Continuous (fun g => ((ρ₂ g : GL (Fin b) ↥LL'.1) : Matrix (Fin b) (Fin b) ↥LL'.1)) ∧
      mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₁ = ρ ∧ mapRep (algebraMap ↥LL'.1 (Qbar l)) ρ₂ = ρ' := by
  obtain ⟨L₁, h₁, ρ₁, c₁, e₁⟩ := exists_model D l a ρ hρ L₀
  obtain ⟨L₂, h₂, ρ₂, c₂, e₂⟩ := exists_model D l b ρ' hρ' L₁
  obtain ⟨c, e⟩ := model_enlarge D l h₂ ρ₁ c₁
  exact ⟨L₂, h₁.trans h₂, _, ρ₂, c, c₂, e.trans e₁, e₂⟩

theorem dR_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) :
    W.IsdRW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w := by
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  rw [← mapRep_sumRep, (H LL' hL a ρ₁ c₁).2.1, (H LL' hL b ρ₂ c₂).2.1,
    (H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)).2.1, comp_sumRep]
  exact (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).1

end W
end GlobalTheory.SumRepAdd

namespace GlobalTheory.SumRepAdd
open Formalism.BasicNotions.Loc

section W2
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

theorem jumps_sum {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (τ : D.host.E →+* Qbar l)
    (hτ : ∀ w : PlE D.host, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) →
      W.IsdRW l ι ρ w ∧ W.IsdRW l ι ρ' w) :
    W.jumpsW l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = W.jumpsW l ι ρ τ + W.jumpsW l ι ρ' τ := by
  obtain ⟨w, hw, hτw⟩ := exists_place D l τ
  obtain ⟨d₁, d₂⟩ := hτ w hτw
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨LL', hL, ρ₁, ρ₂, c₁, c₂, rfl, rfl⟩ := two_models D l ρ ρ' hρ hρ' Bw.LL
  obtain ⟨τ', hτ'⟩ := exists_ext D l w _ Bw hj τ hτw LL' hL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  obtain ⟨-, dd₁, -, J₁⟩ := H LL' hL a ρ₁ c₁
  obtain ⟨-, dd₂, -, J₂⟩ := H LL' hL b ρ₂ c₂
  obtain ⟨-, dd₃, -, J₃⟩ := H LL' hL (a + b) _ (cont_sumRep ρ₁ ρ₂ c₁ c₂)
  rw [← mapRep_sumRep] at d₃ ⊢
  ext c
  have k₁ := (J₁ τ τ' hτ').2 (dd₁.1 d₁) c
  have k₂ := (J₂ τ τ' hτ').2 (dd₂.1 d₂) c
  have k₃ := (J₃ τ τ' hτ').2 (dd₃.1 d₃) c
  rw [comp_sumRep, (dsum_local l (D.loc l) (D.locA l) ⟨D.locT l⟩ _ _ _ _ Bw LL' a b _ _).2 τ' c, ← k₁, ← k₂] at k₃
  rw [Multiset.count_add]
  exact_mod_cast k₃

theorem wd_sum_away {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∉ placesOver D.host.E l) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  apply (T.e w).injective
  rw [T.sum, W.away l ι _ w hw, W.away l ι ρ w hw, W.away l ι ρ' w hw]
  exact wdOf_sumRep_away D l ι a b ρ ρ' w hw hρ hρ'

theorem pst_of_dR (hB : GlobalTheory.Published.DeRhamPotSemistable) {m : ℕ} (r : G D.host.E D.nd.Om →* GL (Fin m) (Qbar l))
    (hr : Continuous (fun g => ((r g : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (hd : W.IsdRW l ι r w) {LL : FinExt l}
    (B : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(OL LL)) (hj : GlobalTheory.Pst.Induces B) :
    GlobalTheory.Pst.IsPstAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) := by
  obtain ⟨LL', hL, r₁, c₁, rfl⟩ := exists_model D l m r hr B.LL
  obtain ⟨-, H⟩ := W.loc l ι w hw _ B hj ((algebraMap ↥B.LL.1 (Om l)).comp B.toLL) (fun _ => rfl)
  have hd' := (H LL' hL m r₁ c₁).2.1
  have hm : GlobalTheory.Pst.IsModel B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) LL'
      (r₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL, rfl⟩
  have hdR : GlobalTheory.Pst.IsdRAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (algebraMap ↥LL'.1 (Qbar l)) r₁) w) :=
    (hm.isdRAt_iff (D.loc l)).2 (hd'.1 hd)
  exact hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val) hdR

theorem wd_sum_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {a b : ℕ} (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l))
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (hρ' : Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (d₁ : W.IsdRW l ι ρ w) (d₂ : W.IsdRW l ι ρ' w) :
    W.wdOf l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (W.wdOf l ι ρ w) (W.wdOf l ι ρ' w) := by
  have d₃ := (dR_sum D T W l ι ρ ρ' hρ hρ' w hw).2 ⟨d₁, d₂⟩
  have c₃ := cont_sumRep ρ ρ' hρ hρ'
  obtain ⟨p_power_smul_sub_sum, B1, j1, E1⟩ := W.above l ι ρ w hw
  obtain ⟨logJacobianTwoPoints, B2, j2, E2⟩ := W.above l ι ρ' w hw
  obtain ⟨ColumnLift, B3, j3, E3⟩ := W.above l ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w hw
  have tie : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  apply (T.e w).injective
  rw [T.sum, E1, E2, E3]
  have p31 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B1 j1
  have p33 := pst_of_dR D T W l ι hB _ c₃ w hw d₃ B3 j3
  have p11 := pst_of_dR D T W l ι hB _ hρ w hw d₁ B1 j1
  have p21 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B1 j1
  have p22 := pst_of_dR D T W l ι hB _ hρ' w hw d₂ B2 j2
  rw [wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B3 B1 (D.nd.plOm.2 w) j3 j1 (a + b) _
      (c₃.comp continuous_subtype_val) p33 p31,
    wdAt_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B2 B1 (D.nd.plOm.2 w) j2 j1 b _
      (hρ'.comp continuous_subtype_val) p22 p21]
  rw [GlobalTheory.Pst.resDec, comp_sumRep] at p31 ⊢
  exact wdAt_sumRep l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ B1 (D.nd.plOm.2 w) j1 a b _ _ p11 p21 p31

end W2

theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, (∀ a b (ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin b) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ' → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w ↔ D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ' w → D.naut.wdOf i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') w = D.naut.lpSum (D.naut.wdOf i ρ w) (D.naut.wdOf i ρ' w)) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w ∧ D.naut.IsdRW i ρ' w) → D.naut.jumpsW i (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') τ = D.naut.jumpsW i ρ τ + D.naut.jumpsW i ρ' τ)) := by
  intro hB hL D P i a b ρ ρ' hρ hρ'
  refine ⟨fun w hw => ?_, fun w h₁ h₂ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ _ w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1, (P.wdOf i _ ρ' w).2.2.2.1]
    exact dR_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · rw [(P.wdOf i _ _ w).1, (P.wdOf i _ ρ w).1, (P.wdOf i _ ρ' w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      have d₂ := (P.wdOf i _ ρ' w).2.2.2.1.1 (h₂.resolve_left (not_not.2 hw))
      exact wd_sum_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' hρ hρ' w hw d₁ d₂
    · exact wd_sum_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' w hw
  · obtain ⟨w₀, -, -⟩ := exists_place D (D.nd.l i) τ
    rw [(P.wdOf i _ _ w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ, (P.wdOf i _ ρ' w₀).2.2.2.2 τ]
    exact jumps_sum D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' hρ hρ' τ fun w hw =>
      ⟨(P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw).1, (P.wdOf i _ ρ' w).2.2.2.1.1 (hτ w hw).2⟩

end GlobalTheory.SumRepAdd
