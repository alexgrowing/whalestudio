import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.IsotConj

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_zero' (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) : conjMap M M' c h 0 = 0 :=
  MultilinearMap.ext fun _ => star_zero _

theorem conjMap_add (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T T' : MMap M) :
    conjMap M M' c h (T + T') = conjMap M M' c h T + conjMap M M' c h T' :=
  MultilinearMap.ext fun _ => star_add _ _

theorem conjMap_smul (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (r : ℂ) (T : MMap M) :
    conjMap M M' c h (r • T) = star r • conjMap M M' c h T := by
  refine MultilinearMap.ext fun v' => ?_
  show star (r • (T : MMap M) _) = star r • star ((T : MMap M) _)
  rw [star_smul]

theorem conjMap_actM {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (k : Formalism.AUTREP.GAf D.host.E n) (T : MMap M) :
    conjMap M M' c h (principalLevelFrame.actM P M k T) = principalLevelFrame.actM P M' k (conjMap M M' c h T) :=
  MultilinearMap.ext fun _ => funext fun _ => rfl

theorem conjMap_minf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (T : MMap M) (hT : T ∈ principalLevelFrame.Minf θ P M) : conjMap M M' c h T ∈ principalLevelFrame.Minf θ P M' := by
  unfold principalLevelFrame.Minf at hT ⊢
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ _) hT ?_ ?_ ?_
  · intro N T hT
    obtain ⟨T', hT', e1⟩ := hM _ _ T hT
    have : conjMap M M' c h T = T' := by
      refine MultilinearMap.ext fun v' => funext fun g => ?_
      rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
      rfl
    rw [this]
    exact Submodule.mem_iSup_of_mem N (mult_congr θ M' (fun k _ => by simp) hT')
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

def cjS {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x : π.S) : (principalLevelFrame.FinTyp.conjT π).S :=
  ⟨fun g => star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g), by
    show (fun g => star (star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g))) ∈ π.S
    simpa using x.2⟩

theorem cjS_add {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x y : π.S) : cjS π (x + y) = cjS π x + cjS π y :=
  Subtype.ext (funext fun _ => star_add _ _)

theorem cjS_smul {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (a : ℂ) (x : π.S) : cjS π (a • x) = star a • cjS π x :=
  Subtype.ext (funext fun _ => by simp [cjS, mul_comm])

theorem conjT_conjT {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) : principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT π) = π := by
  rcases π with ⟨S0, _, _, _, _⟩
  show Formalism.L2.NG.FinTyp.mk (principalLevelFrame.conjSub (principalLevelFrame.conjSub S0)) _ _ _ _ = _
  congr 1
  exact principalLevelFrame.conjSub_conjSub S0

theorem conjMap_isot (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (T : MMap M)
    (hT : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (principalLevelFrame.FinTyp.conjT π)) :
    conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π := by
  unfold principalLevelFrame.isotIn at hT
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
  · intro Φ T hT
    refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
    · rintro ⟨hΦ, hR⟩ T ⟨f, rfl⟩
      let Ψ : π.S →ₗ[ℂ] MMap M' :=
        { toFun := fun x => conjMap M M' c h (Φ (cjS π x))
          map_add' := fun x y => by rw [cjS_add, map_add, conjMap_add]
          map_smul' := fun a x => by simp only [RingHom.id_apply]; rw [cjS_smul, map_smul, conjMap_smul, star_star] }
      have hΨ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M') π Ψ := by
        intro k x
        show conjMap M M' c h (Φ (cjS π _)) = principalLevelFrame.actM P M' k (conjMap M M' c h (Φ (cjS π x)))
        rw [← conjMap_actM, ← hΦ k]
        rfl
      have hΨR : LinearMap.range Ψ ≤ principalLevelFrame.Minf θ P M' := by
        rintro _ ⟨x, rfl⟩
        exact conjMap_minf θ P M M' c h hM _ (hR (LinearMap.mem_range_self Φ _))
      have e : cjS π ⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩ = f :=
        Subtype.ext (funext fun _ => star_star _)
      refine Submodule.mem_iSup_of_mem Ψ (Submodule.mem_iSup_of_mem ⟨hΨ, hΨR⟩ ⟨⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩, ?_⟩)
      show conjMap M M' c h (Φ (cjS π _)) = conjMap M M' c h (Φ f)
      rw [e]
    · rw [conjMap_zero']; exact zero_mem _
    · intro T T' h1 h2
      rw [conjMap_add]; exact add_mem h1 h2
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ}
    (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) :
    Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) ≤ Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π), conjMap M M' c h T ∈ principalLevelFrame.isotL θ P M' J χ' e' π := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, conjMap_isot θ P M M' c h hM π T h3⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
  let j : principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π) →+ principalLevelFrame.isotL θ P M' J χ' e' π :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) = Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  intro D V S S' θ M M' c hc J χ χ' e e' n P π hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' P π hχ he) ?_
  have := rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e P (principalLevelFrame.FinTyp.conjT π) ?_ ?_
  · rwa [conjT_conjT] at this
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]

end GlobalTheory.IsotConj

end
