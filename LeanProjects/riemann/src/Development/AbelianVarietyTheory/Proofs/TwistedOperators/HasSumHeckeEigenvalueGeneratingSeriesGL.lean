import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSubquotientOfSameSphericalHeckeEigenvalues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

noncomputable section

open MeasureTheory ValuativeRel Matrix IsDedekindDomain NumberField Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.LocGL GlobalTheory.LGrp GlobalTheory.SplitWeil

open scoped Pointwise

namespace GlobalTheory.FinZeta.GLSeries

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def cyc (ρ : Representation ℂ G V) (x : V) : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => ρ g x)

theorem self_mem_cyc (ρ : Representation ℂ G V) (x : V) : x ∈ cyc ρ x :=
  Submodule.subset_span ⟨1, by simp⟩

theorem cyc_stable (ρ : Representation ℂ G V) (x : V) (g : G) (v : V) (hv : v ∈ cyc ρ x) : ρ g v ∈ cyc ρ x := by
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨h, rfl⟩ := hy
    exact Submodule.subset_span ⟨g * h, by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def quoRep (σ : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, σ g v ∈ M) :
    Representation ℂ G (V ⧸ M) where
  toFun g := M.mapQ M (σ g) fun v hv => hM g v hv
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem quoRep_mk (σ : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, σ g v ∈ M) (g : G) (v : V) :
    quoRep σ M hM g (M.mkQ v) = M.mkQ (σ g v) := rfl

theorem exists_coMax (σ : Representation ℂ G V) {y : V} (hy : y ≠ 0) :
    ∃ M : Submodule ℂ V, (∀ g, ∀ v ∈ M, σ g v ∈ M) ∧ y ∉ M ∧
      ∀ M' : Submodule ℂ V, M ≤ M' → (∀ g, ∀ v ∈ M', σ g v ∈ M') → y ∉ M' → M' = M := by
  let s : Set (Submodule ℂ V) := {U | (∀ g, ∀ v ∈ U, σ g v ∈ U) ∧ y ∉ U}
  have h0 : (⊥ : Submodule ℂ V) ∈ s := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero], by rwa [Submodule.mem_bot]⟩
  have ih : ∀ c ⊆ s, IsChain (· ≤ ·) c → ∀ z ∈ c, ∃ ub ∈ s, ∀ u ∈ c, u ≤ ub := by
    intro c hcs hc z hz
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun hmem => ?_⟩, fun u hu => le_sSup hu⟩
    · rw [Submodule.mem_sSup_of_directed ⟨z, hz⟩ hc.directedOn] at hv ⊢
      obtain ⟨u, hu, hvu⟩ := hv
      exact ⟨u, hu, (hcs hu).1 g v hvu⟩
    · rw [Submodule.mem_sSup_of_directed ⟨z, hz⟩ hc.directedOn] at hmem
      obtain ⟨u, hu, hyu⟩ := hmem
      exact (hcs hu).2 hyu
  obtain ⟨U, -, hU⟩ := zorn_le_nonempty₀ s ih ⊥ h0
  exact ⟨U, hU.prop.1, hU.prop.2, fun U' hle h1 h2 => (hU.eq_of_le ⟨h1, h2⟩ hle).symm⟩

theorem isIrreducible_quoRep (σ : Representation ℂ G V) {M : Submodule ℂ V} (hM : ∀ g, ∀ v ∈ M, σ g v ∈ M) {y : V}
    (hy : y ∉ M) (hmax : ∀ M' : Submodule ℂ V, M ≤ M' → (∀ g, ∀ v ∈ M', σ g v ∈ M') → y ∉ M' → M' = M)
    (hgen : ∀ S : Submodule ℂ V, (∀ g, ∀ v ∈ S, σ g v ∈ S) → y ∈ S → S = ⊤) : (quoRep σ M hM).IsIrreducible := by
  have hy0 : M.mkQ y ≠ 0 := by rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hy0 ?_⟩, eq_bot_or_eq_top := fun T => ?_ }
  · have h1 : M.mkQ y ∈ (⊤ : Subrepresentation (quoRep σ M hM)).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact h1
  · have hst : ∀ g, ∀ v ∈ T.toSubmodule.comap M.mkQ, σ g v ∈ T.toSubmodule.comap M.mkQ := fun g v hv =>
      T.apply_mem_toSubmodule g hv
    by_cases hyT : y ∈ T.toSubmodule.comap M.mkQ
    · right
      have e := hgen _ hst hyT
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      obtain ⟨u, rfl⟩ := M.mkQ_surjective v
      have : u ∈ T.toSubmodule.comap M.mkQ := e ▸ Submodule.mem_top
      exact this
    · left
      have hle : M ≤ T.toSubmodule.comap M.mkQ := fun v hv => by
        show M.mkQ v ∈ T.toSubmodule
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero M).2 hv]
        exact zero_mem _
      have e := hmax _ hle hst hyT
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      obtain ⟨u, rfl⟩ := M.mkQ_surjective v
      have : u ∈ M := e ▸ (show u ∈ T.toSubmodule.comap M.mkQ from hv)
      show M.mkQ u ∈ (⊥ : Submodule ℂ (V ⧸ M))
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact this

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem exists_irrSmooth_quot (ρ : Representation ℂ G V) {K : Subgroup G} (hK : IsOpen (K : Set G)) {x : V} (hx : x ≠ 0)
    (hxK : x ∈ fixed ρ K) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (π : Representation ℂ G W) (f : cyc ρ x →ₗ[ℂ] W),
      IsIrrSmooth π ∧ (∀ g y, f (sub ρ (cyc ρ x) (cyc_stable ρ x) g y) = π g (f y)) ∧
        f ⟨x, self_mem_cyc ρ x⟩ ≠ 0 := by
  set σ := sub ρ (cyc ρ x) (cyc_stable ρ x) with hσ
  set y : cyc ρ x := ⟨x, self_mem_cyc ρ x⟩ with hy
  have hy0 : y ≠ 0 := fun e => hx (congrArg Subtype.val e)
  obtain ⟨M, hM, hyM, hmax⟩ := exists_coMax σ hy0
  have hgen : ∀ S : Submodule ℂ (cyc ρ x), (∀ g, ∀ v ∈ S, σ g v ∈ S) → y ∈ S → S = ⊤ := by
    intro S hS hyS
    have hle : cyc ρ x ≤ S.map (cyc ρ x).subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      exact ⟨σ g y, hS g y hyS, rfl⟩)
    refine eq_top_iff.2 fun v _ => ?_
    obtain ⟨u, hu, e⟩ := hle v.2
    have : u = v := Subtype.ext e
    exact this ▸ hu
  have hxs : x ∈ smoothPart ρ := GlobalTheory.SmGL.mem_smoothPart_of_nhds
    (Filter.mem_of_superset (hK.mem_nhds (one_mem _)) fun g hg => mem_fixed.1 hxK g hg)
  have hsm : cyc ρ x ≤ smoothPart ρ := Submodule.span_le.2 (by
    rintro _ ⟨g, rfl⟩
    exact smoothPart_stable ρ g x hxs)
  refine ⟨_, inferInstance, inferInstance, quoRep σ M hM, M.mkQ, ⟨fun v => ?_, isIrreducible_quoRep σ hM hyM hmax hgen⟩,
    fun g u => rfl, ?_⟩
  · obtain ⟨u, rfl⟩ := M.mkQ_surjective v
    have h1 : IsOpen {g | ρ g u = u} := hsm u.2
    refine GlobalTheory.SmGL.mem_smoothPart_of_nhds (ρ := quoRep σ M hM) (Filter.mem_of_superset (h1.mem_nhds (by simp)) fun g hg => ?_)
    show quoRep σ M hM g (M.mkQ u) = M.mkQ u
    rw [quoRep_mk]
    congr 1
    exact Subtype.ext hg
  · rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

theorem exists_zonal {π : Representation ℂ G V} (hπ : IsSmooth π) {K : Subgroup G} (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) {y : V} (hy : y ∈ fixed π K) (hy0 : y ≠ 0) :
    ∃ ω : G → ℂ, GlobalTheory.SmGL.IsZonal π K ω ∧ ∀ (g : G) (a : ℂ), heckeVec π K (dosetInd ℂ K g) y = a • y →
      a = ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) * ω g := by
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Module.Dual ℂ V, l₀ y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
  let l : Module.Dual ℂ V := ((l₀ y)⁻¹ • l₀) ∘ₗ idem hπ hc
  have hl1 : l y = 1 := by
    simp [l, idem_of_mem hπ hc hy, hl₀]
  refine ⟨fun g => l (π g y), ⟨y, hy, l, mem_fixed.2 fun k hk => ?_, hl1, fun _ => rfl⟩, fun g a e => ?_⟩
  · ext v
    simp only [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, l]
    rw [idem_apply_mem hπ hc (inv_mem hk)]
  · rw [GlobalTheory.LGrp.Zonal.heckeVec_dosetInd hπ hc hK hy] at e
    have h1 := congrArg l e
    rw [map_smul, map_smul, hl1, smul_eq_mul, smul_eq_mul, mul_one] at h1
    have h2 : l (idem hπ hc (π g y)) = l (π g y) := by
      simp only [l, LinearMap.comp_apply]
      rw [idem_of_mem hπ hc (idem_mem hπ hc _)]
    rw [h2] at h1
    exact h1.symm

theorem real_doset_eq_card [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    {K : Subgroup G} (hKo : IsOpen (K : Set G)) (hμ : μ (K : Set G) = 1) (hK : IsCommensurated K) (g : G) :
    μ.real (DoubleCoset.doubleCoset g (K : Set G) (K : Set G)) = ((P.finite_cosets_in_doset hK g).toFinset.card : ℝ) := by
  set T := (P.finite_cosets_in_doset hK g).toFinset with hT
  have hmem : ∀ c : G ⧸ K, c ∈ T ↔ c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := fun c => by
    rw [hT, Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩
  have hmul : ∀ z ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G), ∀ k ∈ K,
      z * k ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) := fun z hz k hk => by
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hz
    exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * k, K.mul_mem hb hk, by group⟩
  have hU : DoubleCoset.doubleCoset g (K : Set G) (K : Set G) = ⋃ c ∈ T, (c.out • (K : Set G)) := by
    ext z
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K z
      refine ⟨(z : G ⧸ K), (hmem _).2 ?_, ?_⟩
      · rw [hu]
        exact hmul z hz u u.2
      · rw [hu]
        exact Set.mem_smul_set.2 ⟨(u : G)⁻¹, inv_mem u.2, by simp [smul_eq_mul]⟩
    · rintro ⟨c, hc, hz⟩
      obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hz
      exact hmul _ ((hmem c).1 hc) k hk
  have hd : (T : Set (G ⧸ K)).PairwiseDisjoint fun c => c.out • (K : Set G) := by
    intro c _ c' _ hne
    refine Set.disjoint_left.2 fun z hz hz' => hne ?_
    obtain ⟨k, hk, rfl⟩ := Set.mem_smul_set.1 hz
    obtain ⟨k', hk', e⟩ := Set.mem_smul_set.1 hz'
    have h1 : (c.out : G ⧸ K) = c'.out := by
      rw [QuotientGroup.eq]
      have e' : c'.out * k' = c.out * k := e
      have : c.out⁻¹ * c'.out = k * k'⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, e']
        group
      rw [this]
      exact K.mul_mem hk (inv_mem hk')
    simpa using h1
  have hm : ∀ c ∈ T, MeasurableSet (c.out • (K : Set G)) := fun c _ =>
    (hKo.smul c.out).measurableSet
  rw [Measure.real, hU, measure_biUnion_finset hd hm, Finset.sum_congr rfl fun c _ => by
    rw [measure_smul, hμ]]
  simp

end Abstract

section Analysis

open GlobalTheory.GLDoubling

theorem cpow_term {q a X : ℂ} (h : q ^ a = X) (m : ℤ) (hm : 0 ≤ m) : q ^ (a * (m : ℂ)) = X ^ m.toNat := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  have e : ((n : ℤ) : ℂ) = (n : ℂ) := by simp
  rw [e, mul_comm, Complex.cpow_nat_mul, h]
  simp

theorem rhs_eq {q r : ℕ} (hq : 1 < q) (α : Fin r → ℂˣ) (s X : ℂ) (hX : (q : ℂ) ^ (-((r : ℂ) / 2 + s)) = X) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q r s =
      eulerFac (Finset.univ.val.map α) ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
        eulerFac ((Finset.univ.val.map α).map (·⁻¹)) ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * X) *
          ∏ i ∈ Finset.range r, (1 - (q : ℂ) ^ i * X ^ 2) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have h1 : (q : ℂ) ^ (-(s + 1 / 2)) = (q : ℂ) ^ (((r : ℂ) - 1) / 2) * X := by
    rw [← hX, ← Complex.cpow_add _ _ hq0]
    congr 1
    ring
  have h2 : ∀ i ∈ Finset.Icc 1 r, (q : ℂ) ^ (-(2 * s + (i : ℂ))) = (q : ℂ) ^ (r - i) * X ^ 2 := by
    intro i hi
    obtain ⟨-, hir⟩ := Finset.mem_Icc.1 hi
    rw [← hX, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast [Nat.cast_sub hir]
    ring
  have e1 : lFactor q α (s + 1 / 2) = eulerFac (Finset.univ.val.map α) ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * X) := by
    rw [GlobalTheory.GLDoubling.lFactor, h1, eulerFac_map]
  have e2 : lFactor q α⁻¹ (s + 1 / 2) =
      eulerFac ((Finset.univ.val.map α).map (·⁻¹)) ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * X) := by
    rw [Multiset.map_map, GlobalTheory.GLDoubling.lFactor, h1]
    exact (eulerFac_map Finset.univ (fun i => (α i)⁻¹) _).symm
  have e3 : invNormFactor q r s = ∏ i ∈ Finset.range r, (1 - (q : ℂ) ^ i * X ^ 2) := by
    rw [invNormFactor, Finset.prod_congr rfl fun i hi => by rw [h2 i hi]]
    refine Finset.prod_nbij' (fun i => r - i) (fun i => r - i) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have := Finset.mem_Icc.1 hi
      exact Finset.mem_range.2 (by omega)
    · intro i hi
      have := Finset.mem_range.1 hi
      exact Finset.mem_Icc.2 (by omega)
    · intro i hi
      have := Finset.mem_Icc.1 hi
      show r - (r - i) = i
      omega
    · intro i hi
      have := Finset.mem_range.1 hi
      show r - (r - i) = i
      omega
    · intro i _
      rfl
  rw [e1, e2, e3]

end Analysis

section Main

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.GLDoubling GlobalTheory.SplitWeil ValuativeRel MeasureTheory

theorem hasSum_hecke_eigenvalues : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → ∀ ϖ, IsUnifV E w ϖ → ∀ t : (Fin r → ℤ) → GL (Fin r) (w.adicCompletion E), (∀ d, (t d).1 = Matrix.diagonal fun i => ϖ ^ d i) → ∀ c : (Fin r → ℤ) → ℂ, (∀ d, heckeVec ρ (KGL w r) (dosetInd ℂ (KGL w r) (t d)) x = c d • x) → ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℝ, 0 < X → X < δ → HasSum (fun d : {d : Fin r → ℤ // Antitone d} => c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) (eulerFac B ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * eulerFac (B.map (·⁻¹)) ((qV E w : ℂ) ^ (((r : ℂ) - 1) / 2) * X) * ∏ i ∈ Finset.range r, (1 - (qV E w : ℂ) ^ i * (X : ℂ) ^ 2)) := by
  intro H E _ _ w r V _ _ ρ x B hx ϖ hϖ t ht c hc
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ho, hcp⟩ := SatCompare.isOpen_isCompact_KGL w r
  have hcomm : IsCommensurated (KGL w r) := Formalism.UG.Final.GLintComm E w r
  have hKO : KO (w.adicCompletion E) (Fin r) = KGL w r := GlobalTheory.SmGL.SphCompletion.KO_completion w r
  obtain ⟨W, _, _, π, f, hirr, hf, hf0⟩ := exists_irrSmooth_quot ρ ho hx.1 hx.2.1
  have hx' : IsSatVecGL w (sub ρ (cyc ρ x) (cyc_stable ρ x)) ⟨x, self_mem_cyc ρ x⟩ B :=
    IsSatVecGL.of_map (cyc ρ x).subtype (fun _ _ => rfl) Subtype.val_injective hx
  have hy := hx'.map f hf hf0
  have hS := SatCompare.hasSatakeGL_of_isSatVecGL hirr hy
  obtain ⟨α, rfl, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π _).1 hS
  have hcy : ∀ d, heckeVec π (KGL w r) (dosetInd ℂ (KGL w r) (t d)) (f ⟨x, self_mem_cyc ρ x⟩) =
      c d • f ⟨x, self_mem_cyc ρ x⟩ := fun d => by
    have hm := Formalism.UG.Final.DosetIndMem _ (KGL w r) ℂ (t d)
    have e1 : heckeVec (sub ρ (cyc ρ x) (cyc_stable ρ x)) (KGL w r) (dosetInd ℂ (KGL w r) (t d))
        ⟨x, self_mem_cyc ρ x⟩ = c d • (⟨x, self_mem_cyc ρ x⟩ : cyc ρ x) := by
      refine Subtype.val_injective ?_
      have := map_heckeVec (ρ := sub ρ (cyc ρ x) (cyc_stable ρ x)) (ρ' := ρ) hcomm hm (cyc ρ x).subtype
        (fun _ _ => rfl) ⟨x, self_mem_cyc ρ x⟩
      exact this.trans (hc d)
    rw [← map_heckeVec hcomm hm f hf, e1, map_smul]
  obtain ⟨ω, hω, hval⟩ := exists_zonal hirr.1 hcp hcomm hy.2.1 hy.1
  letI : MeasurableSpace (GL (Fin r) (w.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin r) (w.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμ⟩ : ∃ μ : Measure (GL (Fin r) (w.adicCompletion E)), μ.IsHaarMeasure ∧ μ (KGL w r : Set _) = 1 := by
    let K₀ : TopologicalSpace.PositiveCompacts (GL (Fin r) (w.adicCompletion E)) :=
      ⟨⟨KGL w r, hcp⟩, by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
    exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩
  have hμ' : μ (KO (w.adicCompletion E) (Fin r) : Set _) = 1 := by rw [hKO]; exact hμ
  have hω' : GlobalTheory.SmGL.IsZonal π (KO (w.adicCompletion E) (Fin r)) ω := by rw [hKO]; exact hω
  let u : (w.adicCompletion E)ˣ := Units.mk0 ϖ (SatCompare.ne_zero_of_isUnifV hϖ)
  have hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = uniformizer (w.adicCompletion E) :=
    GlobalTheory.Orb.IsUnif.valuation_eq (ϖ := u) hϖ
  have htt : ∀ d, t d = torusElt (w.adicCompletion E) (Fin r) u d := fun d =>
    Units.ext ((ht d).trans (val_torusElt u d).symm)
  have hc2 : ∀ d, c d = (μ.real (cell (w.adicCompletion E) (Fin r) u d) : ℂ) *
      ω (torusElt (w.adicCompletion E) (Fin r) u d) := fun d => by
    have e1 := real_doset_eq_card μ ho hμ hcomm (t d)
    have e2 : cell (w.adicCompletion E) (Fin r) u d =
        DoubleCoset.doubleCoset (t d) (KGL w r : Set _) (KGL w r : Set _) := by
      rw [htt d, cell, hKO]
    rw [e2, e1, ← htt d, Complex.ofReal_natCast]
    exact hval (t d) (c d) (hcy d)
  obtain ⟨s₀, hs⟩ := GlobalTheory.Published.UnramifiedDoublingGL.hasSum H (w.adicCompletion E) r μ hμ' hu hα hω'
  have hq1 : 1 < qV E w := one_lt_absNorm w
  have hqr : resCard (w.adicCompletion E) = qV E w := GlobalTheory.LocLanglands.resCard_eq_normV w
  have hq0 : (0 : ℝ) < qV E w := by exact_mod_cast (by omega : 0 < qV E w)
  have hlq : 0 < Real.log (qV E w) := Real.log_pos (by exact_mod_cast hq1)
  refine ⟨Real.exp (-(s₀ + r / 2) * Real.log (qV E w)), Real.exp_pos _, fun X hX0 hXδ => ?_⟩
  obtain ⟨s, hsd⟩ : ∃ s : ℝ, s = -Real.log X / Real.log (qV E w) - r / 2 := ⟨_, rfl⟩
  have hss : s₀ < s := by
    have h1 := Real.log_lt_log hX0 hXδ
    rw [Real.log_exp] at h1
    rw [hsd, lt_sub_iff_add_lt, lt_div_iff₀ hlq]
    linarith
  have hXq : (qV E w : ℂ) ^ (-((r : ℂ) / 2 + (s : ℂ))) = (X : ℂ) := by
    have e : -((r : ℂ) / 2 + (s : ℂ)) = ((Real.log X / Real.log (qV E w) : ℝ) : ℂ) := by
      rw [hsd]
      push_cast
      ring
    have e' : ((qV E w : ℝ)) ^ (Real.log X / Real.log (qV E w)) = X := by
      rw [Real.rpow_def_of_pos hq0, mul_div_cancel₀ _ hlq.ne', Real.exp_log hX0]
    rw [e, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq0.le, e']
  have hsum := hs (s : ℂ) (by simpa using hss)
  rw [hqr, rhs_eq hq1 α (s : ℂ) (X : ℂ) hXq] at hsum
  have hfun : (fun d : {d : Fin r → ℤ // Antitone d} => c d.1 * (X : ℂ) ^ (∑ i, |d.1 i|).toNat) = fun e =>
      (μ.real (cell (w.adicCompletion E) (Fin r) u e.1) : ℂ) *
        ((qV E w : ℂ) ^ (-((r : ℂ) / 2 + (s : ℂ)) * ((∑ i, |e.1 i| : ℤ) : ℂ)) *
          ω (torusElt (w.adicCompletion E) (Fin r) u e.1)) := by
    funext e
    rw [hc2 e.1, cpow_term hXq _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    ring
  rw [hfun]
  exact hsum

end Main

end GlobalTheory.FinZeta.GLSeries
