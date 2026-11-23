import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalHermitianFramesGoodAlmostAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermSplitsUnimodularComplementStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZeroStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCoordinateLatticeIsTermTrivialWitnessesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerFramesCoordinateLatticeGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZeroStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace

theorem term_orbit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (ha : S.a = 0)
    {d d₁ : S.Datum} {Λ Λ₁ : Submodule L.O S.V} (hT : S.IsTerm d Λ) (hT₁ : S.IsTerm d₁ Λ₁)
    (hM : S.M d Λ = S.M d₁ Λ₁) : ∃ h ∈ S.H0, h • Λ₁ = Λ := by
  have : IsArtinianRing E := by
    have := L.free
    have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
    exact IsArtinianRing.of_finite F E
  obtain ⟨u₀, hu₀, hE, hui, hup⟩ := GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero L r k S d Λ hT ha
  obtain ⟨b₀, hbW, hΛ, hbi, hbp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d Λ hT ha
  obtain ⟨c₀, hcW, hΛ₁, hci, hcp⟩ := GlobalTheory.T.hermitianTerm_splits_unimodular_complement L r k S d₁ Λ₁ hT₁ ha
  obtain ⟨u, huo, hus⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm u₀ hui hup
  obtain ⟨b, hbo, hbs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm b₀ hbi hbp
  obtain ⟨c, hco, hcs⟩ := GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular L S.Hm S.herm c₀ hci hcp
  have hsp : ∀ (w : Fin (k - 1) → S.V) (w₀ : Fin (k - 1) → S.V), (∀ i, w₀ i ∈ S.W0) →
      Submodule.span L.O (Set.range w) = Submodule.span L.O (Set.range w₀) → ∀ i, w i ∈ S.W0 := by
    intro w w₀ h0 he i
    have h1 : w i ∈ Submodule.span L.O (Set.range w₀) := by
      rw [← he]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range w₀) ≤ S.W0.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j)
    exact h2 h1
  have hbW' := hsp b b₀ hbW hbs
  have hcW' := hsp c c₀ hcW hcs
  have huME : ∀ i, u i ∈ S.ME := by
    intro i
    have h1 : u i ∈ Submodule.span L.O (Set.range u₀) := by
      rw [← hus]; exact Submodule.subset_span ⟨i, rfl⟩
    have h2 : Submodule.span L.O (Set.range u₀) ≤ S.ME.restrictScalars L.O :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        rw [← hE]; exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 h1
  have horth : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm w (u i) = 0 := fun hw i => hw _ (huME i)
  have horth' : ∀ {w : S.V}, w ∈ S.W0 → ∀ i, hf L S.Hm (u i) w = 0 := fun hw i => by
    rw [GlobalTheory.FrameBasic.hf_conj L S.herm.1, horth hw i, map_zero]

  let x : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u c
  let y : Fin (2 * (r + 1) + (k - 1)) → S.V := Fin.append u b
  have gx : ∀ i j, hf L S.Hm (x i) (x j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [x, huo, Fin.ext_iff]
    · simp [x, horth' (hcW' j), Fin.ext_iff]; omega
    · simp [x, horth (hcW' i), Fin.ext_iff]; omega
    · simp [x, hco, Fin.ext_iff]
  have gy : ∀ i j, hf L S.Hm (y i) (y j) = if i = j then 1 else 0 := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simp [y, huo, Fin.ext_iff]
    · simp [y, horth' (hbW' j), Fin.ext_iff]; omega
    · simp [y, horth (hbW' i), Fin.ext_iff]; omega
    · simp [y, hbo, Fin.ext_iff]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.HermTuple.witt_tuples L S.Hm S.herm _ x y
    (fun i j => by rw [gx, gy]) (by
      have : (Matrix.of fun i j => hf L S.Hm (x i) (x j)) = 1 := by
        ext i j; simp [gx, Matrix.one_apply]
      rw [this]; simp)
  have hgu : ∀ i, g (u i) = u i := fun i => by
    have := hgx (Fin.castAdd _ i)
    simpa [x, y] using this
  have hgc : ∀ i, g (c i) = b i := fun i => by
    have := hgx (Fin.natAdd _ i)
    simpa [x, y] using this
  have hfix : ∀ v ∈ S.ME, g v = v := by
    intro v hv
    rw [← hE] at hv
    let K : Submodule E S.V := LinearMap.eqLocus (g : S.V →ₗ[E] S.V) LinearMap.id
    have h1 : Submodule.span L.O (Set.range u) ≤ K.restrictScalars L.O :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hgu i)
    have h2 : Submodule.span E (Set.range u₀) ≤ K :=
      Submodule.span_le.2 (by
        rintro _ ⟨j, rfl⟩
        apply h1
        rw [hus]
        exact Submodule.subset_span ⟨j, rfl⟩)
    exact h2 hv
  have hH0 : g ∈ S.H0 :=
    ⟨hg, GlobalTheory.HL.FrameStab.mem_unipOn' bot_le g fun v hv => by rw [hfix v hv, sub_self]; exact Submodule.zero_mem _⟩
  have hsm : ∀ s : Set S.V, g • Submodule.span L.O s = Submodule.span L.O (g '' s) := fun s => by
    rw [Submodule.pointwise_smul_def, Submodule.map_span]; rfl
  have e1 : g • S.M d Λ = S.M d Λ := by
    rw [hu₀, ← hus, hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgu i
  have e2 : g • Submodule.span L.O (Set.range c) = Submodule.span L.O (Set.range b) := by
    rw [hsm, ← Set.range_comp]
    congr 2
    funext i
    exact hgc i
  refine ⟨g, hH0, ?_⟩
  have e3 : ∀ A B : Submodule L.O S.V, g • (A ⊔ B) = g • A ⊔ g • B := fun A B => by
    simp only [Submodule.pointwise_smul_def, Submodule.map_sup]
  rw [hΛ₁, ← hM, ← hcs, e3, e1, e2, hbs, ← hΛ]

theorem good_place {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k) (hG : Good S) :
    S.Hp = 1 ∧ S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 ∧ ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 ∧
      S.om d₀ (coordLat S) = 1 ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d₀ = S.complementReferenceCompactSubgroup ∧
      (∀ Λ, S.IsTerm d₀ Λ → ∃ h ∈ S.St, Λ = h • coordLat S) ∧
      (∀ Λ, S.IsTerm d₀ Λ → S.Fr d₀ Λ = S.frameCls S.f S.f' → Λ = coordLat S) ∧
      ∀ d Λ, S.IsTerm d Λ → ∃ h ∈ S.H0, d = h • d₀ := by
  obtain ⟨hvG, hvD⟩ := GlobalTheory.T.goodPlace_gramInvariant_minors_valuation_zero L r k S hG
  have hvth : S.vth = 0 := by simp [Frames.vth, hG.gg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hvG]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses L r k S hG
  have hT₀ : S.IsTerm d₀ (coordLat S) := ⟨(1, 1), hd₀⟩
  obtain ⟨hom, hM₀, hFr₀, -, -⟩ := GlobalTheory.HL.WitIndep.witness_independence L r k S d₀ _ _ _ hd₀
  have hFr₁ : S.Fr d₀ (coordLat S) = S.frameCls S.f S.f' := hFr₀
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  obtain ⟨-, -, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hG.gg hG.D_unit
  have hint : ∀ d Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun d Λ h =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1
  have hdd : ∀ d d' Λ, S.IsTerm d Λ → S.IsTerm d' Λ → d' = d := fun d d' Λ h h' =>
    (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.2 d' h'
  have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S
  have hcom := GlobalTheory.HL.ComplAct.main L r k S
  have hcls := GlobalTheory.HL.FrameClass.frame_classes L r k S
  refine ⟨(GlobalTheory.HL.GoodPlace.equality L r k S hk hG.gg hvG hvD).2.1, GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace L r k S hG ha d₀ hd₀, d₀, hd₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hom]
    have h1 : ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V),
        (∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0) → S.psiOf g gs 1 = 1 := by
      intro g gs hd
      have : ∀ j, S.coef g gs 1 j = 0 := fun j => by
        have := hd j.succ j
        rw [if_neg (by simp [Fin.ext_iff])] at this
        exact this
      simp [Frames.psiOf, this]
    have e1 : S.psi 1 = 1 := h1 _ _ S.dual
    have e2 : S.psi' 1 = 1 := h1 _ _ S.dual'
    simp [e1, e2]
  · ext h
    simp only [Subgroup.mem_inf, Frames.complementReferenceCompactSubgroup, MulAction.mem_stabilizer_iff]
    refine and_congr_right fun hh => ⟨fun e => ?_, fun e => ?_⟩
    · have h1 := hcom d₀ _ hT₀ h hh
      rw [e] at h1
      have := (huniq d₀ _ hT₀).2 _ h1.1 h1.2.2.2.2.2
      exact this
    · have h1 := hcom d₀ _ hT₀ h hh
      have e' : h • coordLat S = coordLat S := e
      rw [e'] at h1
      exact hdd _ _ _ hT₀ h1.1
  · intro Λ hΛ
    obtain ⟨h, hh, e⟩ := hall _ (hint _ _ hΛ)
    refine ⟨h, hh, ?_⟩
    have h2 := hact d₀ _ hT₀ h hh
    exact (huniq d₀ _ h2.1).2 _ hΛ (by rw [h2.2.2.2.2.1, hFr₁, e])
  · intro Λ hΛ e
    exact (huniq d₀ _ hT₀).2 _ hΛ (by rw [e, hFr₁])
  · intro d Λ hΛ
    obtain ⟨s, hs, e⟩ := hall _ (hint _ _ hΛ)
    have hsi := S.St.inv_mem hs
    have h2 := hact d _ hΛ _ hsi
    have hT₂ := h2.1
    have hFr₂ : S.Fr d (s⁻¹ • Λ) = S.Fr d₀ (coordLat S) := by
      rw [h2.2.2.2.2.1, e, hFr₁, smul_smul, inv_mul_cancel, one_smul]
    have hM₂ : S.M d (s⁻¹ • Λ) = S.M d₀ (coordLat S) := by
      have h3 : (S.fr d (s⁻¹ • Λ), S.fr' d (s⁻¹ • Λ)) ∈ S.Fr d₀ (coordLat S) := by
        rw [← hFr₂]; exact (hcls _ _).1
      exact ((hcls _ _).2.1 _ h3).2
    obtain ⟨h, hh, e₁⟩ := term_orbit L r k S ha hT₂ hT₀ hM₂
    refine ⟨h, hh, ?_⟩
    have h4 := (hcom d₀ _ hT₀ h hh).1
    rw [e₁] at h4
    exact hdd _ _ _ h4 hT₂

theorem coordinate_lattice_standard : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → {p | ¬ ((G.S p).gg = false ∧ (G.S p).Hp = 1 ∧ (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = (G.S p).K0 ∧ ∃ d₀, (G.S p).IsTermW d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) 1 1 ∧ (G.S p).om d₀ (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V))) = 1 ∧ (G.S p).H0 ⊓ MulAction.stabilizer (G.S p).GLV d₀ = (G.S p).complementReferenceCompactSubgroup ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → ∃ h ∈ (G.S p).St, Λ = h • (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ (∀ Λ, (G.S p).IsTerm d₀ Λ → (G.S p).Fr d₀ Λ = (G.S p).frameCls (G.S p).f (G.S p).f' → Λ = (Submodule.span (A.L p).O (Set.range fun i => (Pi.single i 1 : (G.S p).V)))) ∧ ∀ d Λ, (G.S p).IsTerm d Λ → ∃ h ∈ (G.S p).H0, d = h • d₀)}.Finite := by
  intro F E _ _ _ _ _ sig A r k G hk
  refine (GlobalTheory.T.globalHermitianFrames_good_almost_all_places A r k G).subset fun p hp hg => hp ?_
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  exact ⟨hg.gg, good_place (A.L p) r k (G.S p) hk hg⟩

end GlobalTheory.HL.StdPlace
