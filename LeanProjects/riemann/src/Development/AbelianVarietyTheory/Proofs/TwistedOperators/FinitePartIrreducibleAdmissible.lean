import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicUnitaryClosureLocalComponentsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesFactorLocalStableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetSumTranslatesFixedCompactSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrepStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FinPartIrrAdm

open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)

theorem mem_fixed_iff {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K : Subgroup G} {x : X} : x ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g x = x :=
  ⟨fun h g hg => by simpa using h ⟨g, hg⟩, fun h g => by simpa using h g g.2⟩

def stabGroup {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) (x : X) :
    Subgroup G :=
    { carrier := {g | ρ g x = x}
      mul_mem' := fun {a b} (ha : ρ a x = x) (hb : ρ b x = x) => by
        change ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by change ρ 1 x = x; simp
      inv_mem' := fun {a} (ha : ρ a x = x) => by
        change ρ a⁻¹ x = x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }

theorem isOpen_stab_of_fixed {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X]
    [Module ℂ X] (ρ : Representation ℂ G X) {K : Subgroup G} (hK : IsOpen (K : Set G)) {x : X}
    (hx : ∀ k ∈ K, ρ k x = x) : IsOpen {g | ρ g x = x} :=
  Subgroup.isOpen_mono (H₂ := stabGroup ρ x) (fun k hk => hx k hk) hK

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)}

theorem continuous_locFin' (v : HeightOneSpectrum (𝓞 D.host.F)) : Continuous (locFin V v) :=
  (continuous_emb D.sp.cm.sig V.gram v).subtype_mk _

theorem toFin_embV (v : HeightOneSpectrum (𝓞 D.host.F)) (k : Gv V v) : toFin V (embV V v k) = locFin V v k := by
  rw [← toFin_coe (locFin V v k)]; rfl

example (Φ : ContinuousMultilinearMap ℂ M.H H) (X : Submodule ℂ H) (h1 : ∀ y, Φ y ∈ X) (h2 : Φ ∈ homDS M π ⊤) : Φ ∈ homDS M π X :=
  ⟨h1, h2.2⟩

end GlobalTheory.FinPartIrrAdm

namespace GlobalTheory.FinPartIrrAdm
open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)}

theorem admissible (hF : GlobalTheory.Published.FlathFactorisation) (hπ : IsIrrUnitary π) (hD : HasDSComp M π)
    (hU : IsSubrep π ⊤) : IsAdmissible (finPartDSSm M hU) := by
  classical
  refine ⟨isSmooth_smoothRep _, fun K hKo hKc => ?_⟩
  obtain ⟨R, ξ, B, hR, hKξ⟩ := hF.exists_factorisation hπ
  haveI : Submodule.IsLattice D.host.E (frameLat V) := SelfDual.isLattice_frameLat V
  obtain ⟨S0, hS0⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig V.gram (frameLat V) (K.comap (toFin V))
    (hKo.preimage (continuous_toFin V))
  let Kp : ∀ v, Subgroup (Gv V v) := fun v => K.comap (locFin V v) ⊓ Kv V v
  have hKpeq : ∀ v ∉ S0, Kp v = Kv V v := fun v hv => inf_eq_right.2 fun k hk => by
    have h := hS0 (emb_mem_levelOff hv hk)
    change toFin V (embV V v k) ∈ K at h
    rw [toFin_embV] at h
    exact h
  have hKpo : ∀ v, IsOpen (Kp v : Set (Gv V v)) := fun v =>
    (hKo.preimage (continuous_locFin' v)).inter (isOpen_stabLoc _ _ _ v)
  have hKpc : ∀ v, IsCompact (Kp v : Set (Gv V v)) := fun v =>
    (isCompact_stabLoc _ _ (frameLat V) v).inter_left
      (Subgroup.isClosed_of_isOpen (K.comap (locFin V v)) (hKo.preimage (continuous_locFin' v)))
  let Q : ∀ v, Submodule ℂ (R (.inr v)).H := fun v =>
    (fixed (smRep (Flath.finFactor R v)) (Kp v)).map (smoothPart (toRep (Flath.finFactor R v))).subtype
  have hQfin : ∀ v, FiniteDimensional ℂ (Q v) := fun v => by
    haveI := (hR.2.1 v).2.2 (Kp v) (hKpo v) (hKpc v)
    infer_instance
  have hQmem : ∀ v (z : (R (.inr v)).H), (∀ k ∈ Kp v, (R (.inr v)).π k z = z) → z ∈ Q v := fun v z hz =>
    ⟨⟨z, isOpen_stab_of_fixed _ (hKpo v) hz⟩, mem_fixed_iff.2 fun k hk => Subtype.ext (hz k hk), rfl⟩
  have hQev : ∀ᶠ v in Filter.cofinite, Q v ≤ ℂ ∙ ξ (.inr v) := by
    have hS : ∀ᶠ v in Filter.cofinite, v ∉ S0 :=
      Filter.eventually_cofinite.2 (S0.finite_toSet.subset fun v hv => by simpa using hv)
    refine (hKξ.and hS).mono fun v hv => ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [← hv.1]
    refine mem_fixed_iff.2 fun k hk => ?_
    exact congrArg Subtype.val (mem_fixed_iff.1 hw k (by rw [hKpeq v hv.2]; exact hk))
  obtain ⟨X, hX⟩ : ∃ X : Submodule ℂ H,
      X = (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, y (.inr v) ∈ Q v) ∧ z = B y}).topologicalClosure := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ (homDS M π X) := hX ▸ GlobalTheory.T.finiteDimensional_homDS_closure_span_restricted D V S M H π hπ hD R ξ B hR.1 Q hQfin hQev
  have hval0 : ∀ Φ0 : ContinuousMultilinearMap ℂ M.H H, Φ0 ∈ homDS M π ⊤ →
      (∀ v, ∀ k ∈ Kp v, ∀ y, π (emb D.sp.cm.sig V.gram v k) (Φ0 y) = Φ0 y) → Φ0 ∈ homDS M π X := by
    intro Φ0 hΦ0m hfx
    refine ⟨fun y => ?_, hΦ0m.2⟩
    have hev : ∀ᶠ v in Filter.cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v) :=
      (hR.1.eventually_fixed (frameLat V)).mono fun v hv k hk => hv k hk.2
    have hx := GlobalTheory.T.factorisable_restricted_tensor_level D.sp.cm.sig V.rank V.gram H π hπ R ξ B hR.1 Kp hev (Φ0 y) (fun v k hk => hfx v k hk y)
    have hsub : {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y} ⊆
        {z | ∃ y, Restr ξ y ∧ (∀ v, y (.inr v) ∈ Q v) ∧ z = B y} := by
      rintro _ ⟨y', hy', hfix, rfl⟩
      exact ⟨y', hy', fun v => hQmem v _ (hfix v), rfl⟩
    rw [hX]
    exact Submodule.topologicalClosure_mono (Submodule.span_mono hsub) hx
  have hval : ∀ Φ : fixed (finPartDSSm M hU) K,
      (((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) ∈ homDS M π X :=
    fun Φ => hval0 _ ((Φ : smoothPart (finPartDS M hU)) : homDS M π ⊤).2 fun v k hk y =>
      congrArg (fun Ψ : smoothPart (finPartDS M hU) =>
        ((Ψ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y) (mem_fixed_iff.1 Φ.2 _ hk.1)
  let f : fixed (finPartDSSm M hU) K →ₗ[ℂ] homDS M π X :=
    LinearMap.codRestrict (homDS M π X)
      ((homDS M π ⊤).subtype ∘ₗ (smoothPart (finPartDS M hU)).subtype ∘ₗ (fixed (finPartDSSm M hU) K).subtype) hval
  have hf : Function.Injective f := fun a b e => by
    have e' := congrArg Subtype.val e
    exact Subtype.ext (Subtype.ext (Subtype.ext e'))
  exact Module.Finite.of_injective f hf

end GlobalTheory.FinPartIrrAdm

namespace GlobalTheory.FinPartIrrAdm
open GlobalTheory.PRep (fixed smoothPart smoothRep IsSmooth)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {H : Type} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] {π : GA D V →* (H →L[ℂ] H)}

noncomputable abbrev valMap (hU : IsSubrep π ⊤) : smoothPart (finPartDS M hU) →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
  (homDS M π ⊤).subtype ∘ₗ (smoothPart (finPartDS M hU)).subtype

theorem valMap_injective (hU : IsSubrep π ⊤) : Function.Injective (valMap (M := M) hU) := fun a b e =>
  Subtype.ext (Subtype.ext e)

set_option maxHeartbeats 1000000 in
theorem irreducible [CompleteSpace H] (hπ : IsIrrUnitary π) (hD : HasDSComp M π) (hU : IsSubrep π ⊤)
    (hadm : IsAdmissible (finPartDSSm M hU)) : (finPartDSSm M hU).IsIrreducible := by
  classical
  have hunit : IsUnitaryRep π := hπ.unitary
  haveI : Nontrivial H := hπ.irred.1
  let u : ∀ τ, M.H τ := fun τ => unitVec (M.H τ)
  obtain ⟨ev, hevd⟩ : ∃ ev : smoothPart (finPartDS M hU) →ₗ[ℂ] H,
      ev = (ContinuousMultilinearMap.apply ℂ M.H H u).toLinearMap ∘ₗ valMap hU := ⟨_, rfl⟩
  have hev : ∀ (g : GfC V) Φ, ev (finPartDSSm M hU g Φ) = π g (ev Φ) := fun g Φ => by subst hevd; rfl
  have hinner : ∀ (Φ Φ' : smoothPart (finPartDS M hU)) y y',
      ⟪valMap hU Φ' y', valMap hU Φ y⟫_ℂ = ⟪ev Φ', ev Φ⟫_ℂ * ∏ τ, ⟪y' τ, y τ⟫_ℂ := fun Φ Φ' y y' => by
    subst hevd
    exact inner_eq_bePi (fun τ => isIrrUnitary_dsRep M τ) hunit (Φ : homDS M π ⊤).2 (Φ' : homDS M π ⊤).2 y y'

  have hne : ∃ w : smoothPart (finPartDS M hU), w ≠ 0 := by
    obtain ⟨T, -, -, hTd⟩ := GlobalTheory.T.irreducibleUnitaryRep_eq_finiteSmoothPart_tensor_discreteSeries D V S M H π hπ hD hU
    by_contra hc
    push_neg at hc
    have h0 : Submodule.span ℂ {v | ∃ w y, v = T w y} = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro _ ⟨w, y, rfl⟩
      rw [hc w, map_zero]
      rfl
    have hb : (⊥ : Submodule ℂ H).topologicalClosure = ⊥ :=
      IsClosed.submodule_topologicalClosure_eq (by simp)
    rw [h0, hb] at hTd
    exact bot_ne_top hTd
  obtain ⟨w0, hw0⟩ := hne
  haveI : Nontrivial (smoothPart (finPartDS M hU)) := ⟨⟨w0, 0, hw0⟩⟩
  haveI : Nontrivial (Subrepresentation (finPartDSSm M hU)) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e :)⟩
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  refine Or.inr (Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun Φ _ => ?_))
  have hdense := GlobalTheory.T.span_values_dense_finitePartSubrep D V S M H π hπ hU N hN
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  have hΦo : IsOpen ((stabGroup (finPartDSSm M hU) Φ : Subgroup (GfC V)) : Set (GfC V)) := by
    have e : {g : GfC V | finPartDSSm M hU g Φ = Φ} = {g | finPartDS M hU g Φ = Φ} :=
      Set.ext fun _ => Subtype.ext_iff
    change IsOpen {g : GfC V | finPartDSSm M hU g Φ = Φ}
    rw [e]
    exact Φ.2
  obtain ⟨K, hKd⟩ : ∃ K : Subgroup (GfC V), K = K0 ⊓ stabGroup (finPartDSSm M hU) Φ := ⟨_, rfl⟩
  have hKo : IsOpen (K : Set (GfC V)) := hKd ▸ hK0o.inter hΦo
  have hKc : IsCompact (K : Set (GfC V)) := hKd ▸ hK0c.inter_right (Subgroup.isClosed_of_isOpen _ hΦo)
  have hKΦ : ∀ k ∈ K, finPartDSSm M hU k Φ = Φ := fun k hk => by
    rw [hKd] at hk
    exact hk.2
  haveI : FiniteDimensional ℂ (fixed (finPartDSSm M hU) K) := hadm.2 K hKo hKc
  obtain ⟨E, hEd⟩ : ∃ E : Submodule ℂ (smoothPart (finPartDS M hU)), E = N.toSubmodule ⊓ fixed (finPartDSSm M hU) K :=
    ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ E := hEd ▸ Submodule.finiteDimensional_of_le inf_le_right
  have hEN : ∀ x ∈ E, x ∈ N.toSubmodule := fun x hx => by rw [hEd] at hx; exact hx.1
  have hEK : ∀ x ∈ E, x ∈ fixed (finPartDSSm M hU) K := fun x hx => by rw [hEd] at hx; exact hx.2
  have hEmem : ∀ x ∈ N.toSubmodule, x ∈ fixed (finPartDSSm M hU) K → x ∈ E := fun x h1 h2 => by
    rw [hEd]; exact ⟨h1, h2⟩
  obtain ⟨Eh, hEhd⟩ : ∃ Eh : Submodule ℂ H, Eh = E.map ev := ⟨_, rfl⟩
  haveI : FiniteDimensional ℂ Eh := hEhd ▸ inferInstance
  haveI : CompleteSpace Eh := FiniteDimensional.complete ℂ Eh
  have hpm := Eh.starProjection_apply_mem (ev Φ)
  have hpo := Eh.sub_starProjection_mem_orthogonal (ev Φ)
  generalize Eh.starProjection (ev Φ) = p at hpm hpo
  rw [hEhd] at hpm
  obtain ⟨n0, hn0E, hn0⟩ := hpm
  have horth : ev (Φ - n0) ∈ Ehᗮ := by
    rw [map_sub, hn0]
    exact hpo
  have hΦ1fix : ∀ k ∈ K, finPartDSSm M hU k (Φ - n0) = Φ - n0 := fun k hk => by
    have h1 : finPartDSSm M hU k Φ = Φ := hKΦ k hk
    have h2 : finPartDSSm M hU k n0 = n0 := mem_fixed_iff.1 (hEK _ hn0E) k hk
    exact (map_sub (finPartDSSm M hU k) Φ n0).trans (congrArg₂ (· - ·) h1 h2)
  have hinv : ∀ k ∈ K, ∀ a, ⟪π k a, ev (Φ - n0)⟫_ℂ = ⟪a, ev (Φ - n0)⟫_ℂ := fun k hk a => by
    conv_lhs => rw [← hΦ1fix k hk, hev]
    exact inner_map_map hunit _ _ _
  have hall : ∀ n ∈ N.toSubmodule, ⟪ev n, ev (Φ - n0)⟫_ℂ = 0 := by
    intro n hn
    obtain ⟨s, hsK, hsne, hsfix⟩ := GlobalTheory.T.exists_finsetSum_translates_fixed_compactSubgroup (finPartDSSm M hU) K hKc n (isSmooth_smoothRep _ n)
    have hmem : ∑ g ∈ s, finPartDSSm M hU g n ∈ E :=
      hEmem _ (Submodule.sum_mem _ fun g _ => N.apply_mem_toSubmodule g hn) (mem_fixed_iff.2 hsfix)
    have h1 := (Submodule.mem_orthogonal _ _).1 horth (ev (∑ g ∈ s, finPartDSSm M hU g n))
      (by rw [hEhd]; exact ⟨_, hmem, rfl⟩)
    have hterm : ∀ g ∈ s, ⟪ev (finPartDSSm M hU g n), ev (Φ - n0)⟫_ℂ = ⟪ev n, ev (Φ - n0)⟫_ℂ := fun g hg => by
      rw [hev]; exact hinv g (hsK g hg) _
    rw [map_sum, sum_inner, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hsne))
  have hzero : ∀ y', valMap hU (Φ - n0) y' = 0 := by
    intro y'
    have hle : Submodule.span ℂ {z | ∃ Ψ ∈ N.toSubmodule, ∃ y,
        z = ((Ψ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y} ≤ (ℂ ∙ valMap hU (Φ - n0) y')ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨Ψ, hΨ, y, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      change ⟪valMap hU (Φ - n0) y', valMap hU Ψ y⟫_ℂ = 0
      rw [hinner Ψ (Φ - n0) y y', ← inner_conj_symm, hall Ψ hΨ, map_zero, zero_mul]
    have hcl := Submodule.topologicalClosure_minimal _ hle (Submodule.isClosed_orthogonal _)
    rw [hdense] at hcl
    exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
  have h0 : Φ - n0 = 0 := valMap_injective hU (by rw [map_zero]; exact ContinuousMultilinearMap.ext hzero)
  rw [sub_eq_zero.1 h0]
  exact hEN _ hn0E

end GlobalTheory.FinPartIrrAdm

namespace GlobalTheory.FinPartIrrAdm

theorem irreducible_admissible : GlobalTheory.Published.FlathFactorisation → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → HasDSComp M π → ∀ hU : IsSubrep π ⊤, (finPartDSSm M hU).IsIrreducible ∧ IsAdmissible (finPartDSSm M hU) := by
  intro hF D V S M H _ _ _ π hπ hD hU
  exact ⟨irreducible hπ hD hU (admissible hF hπ hD hU), admissible hF hπ hD hU⟩

end GlobalTheory.FinPartIrrAdm
