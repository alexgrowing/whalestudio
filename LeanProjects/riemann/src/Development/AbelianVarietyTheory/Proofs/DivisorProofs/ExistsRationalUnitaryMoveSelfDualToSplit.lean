import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalUnitarySplitDenominator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryCongruentLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixDetNotMem

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SplitMove

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.UnRep.FullReps GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (v : Fin n → E) :
    (fun j => IsCMField.complexConj E (IsCMField.complexConj E (v j))) = v :=
  funext fun j => IsCMField.complexConj_apply_apply E (v j)

theorem unimod_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} (hU : Λ.Unimod) :
    (conjLat H Λ.La).Unimod := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range → IsCMField.complexConj E x ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨H.bar a, H.bar_eq a⟩
  intro v
  rw [mem_conjLat, hU]
  constructor
  · intro hv w hw
    have := hr _ (hv _ hw)
    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this
  · intro hv w hw
    have := hr _ (hv (fun j => IsCMField.complexConj E (w j)) (by rw [mem_conjLat, conj_conj]; exact hw))
    simpa only [map_sum, map_mul, IsCMField.complexConj_apply_apply] using this

theorem trivAt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {Λ : GenLat E n} {N : ℕ} (hT : Λ.TrivAt N) :
    (conjLat H Λ.La).TrivAt N := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk, conjLat_le H (by rw [← H.bar_eq, map_natCast])
    ⟨(Move.span_smul_le _ _ _).1 h1, (Move.span_smul_le _ _ _).1 h2⟩⟩

theorem congAt_of_congAtA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    {N M : ℕ} (hM : 0 < M) {γ : Matrix (Fin n) (Fin n) E} (h : CongAtA F L N M (fm F γ)) :
    GlobalTheory.UnRep.CongAt L N M γ := by
  obtain ⟨t, ht, h⟩ := h
  have hrat := (hat_rational_points_and_approx F E n L hfg hsp).1
  refine ⟨t, ht, fun v hv => ?_⟩
  obtain ⟨w, hw, e⟩ := h _ ((hrat v).2 hv)
  have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
  have key : t • (γ *ᵥ v - v) = M • ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) := by
    rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
  refine ⟨_, ?_, key⟩
  rw [← hrat]
  have e' : fv F ((M : E)⁻¹ • (t • (γ *ᵥ v - v))) = w := by
    refine Move.nsmul_cancel _ hM ?_
    rw [← cap_fv_nsmul, ← key, cap_fv_nsmul, Move.fv_sub, Move.fv_mulVec, e]
  rw [e']
  exact hw

theorem exists_move_matrix (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (N : ℕ) (hN : 0 < N) (Λ : GenLat E n)
    (hU : Λ.Unimod) (hT : Λ.TrivAt N) :
    ∃ (γ : Matrix (Fin n) (Fin n) E) (h : GL (Fin n) (RA (maximalRealSubfield E) E))
      (Lh : Submodule (𝓞 E) (Fin n → E)), IsUnitaryM γ ∧
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) ∧
      IsUnA (IsCMField.complexConj E) 1 h.1 ∧ SuppSplit (IsCMField.complexConj E) N h.1 ∧
      (Lh : Set (Fin n → E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield E) h.1 (stdLat E n) ∧
      actLat γ Λ = conjLat H Lh := by
  obtain ⟨hherm, hrk, hfg, hsp, -, -, -, hun⟩ := StdInhab.main E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate E H n N _ hN (unimod_conj H hU)
    (trivAt_conj H hT)
  obtain ⟨γ, h, k, hγ, hh, -, e, hs, hk, hk'⟩ := GlobalTheory.UnRep.exists_rep_suppSplit (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g N hg hN
  obtain ⟨Lh, hLh, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E n (stdLat E n) h hfg hsp
  have hu : adjM γ.1 * γ.1 = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← (hun _).1 hγ i j]
    rfl
  have hu' : γ.1 * adjM γ.1 = 1 := mul_eq_one_comm.1 hu
  have hδ : adjM γ.1ᵀ * γ.1ᵀ = 1 := by
    rw [show adjM γ.1ᵀ = (adjM γ.1)ᵀ from rfl, ← Matrix.transpose_mul, hu', Matrix.transpose_one]
  have hδ' : γ.1ᵀ * adjM γ.1ᵀ = 1 := mul_eq_one_comm.1 hδ
  have ck : CongAtA (maximalRealSubfield E) (stdLat E n) N N (k⁻¹).1 := by
    refine ⟨1, Nat.coprime_one_left _, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hk _ (hk' z hz)
    refine ⟨-w, neg_mem hw, ?_⟩
    rw [one_smul, smul_neg, ← e, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, neg_sub]
  have ch : CongAtA (maximalRealSubfield E) (stdLat E n) N N (h⁻¹).1 := by
    obtain ⟨ε, -, -, he, hcut⟩ := hs
    obtain ⟨t, ht, hb⟩ := (idempotent_adeles_small_matrices (maximalRealSubfield E) E n (stdLat E n) hfg hsp).2.2.2.1
      N N ε ((h⁻¹).1 - 1) hN fun v hv => by
        by_contra h0
        exact (he v h0).2 hv
    refine ⟨t, ht, fun z hz => ?_⟩
    obtain ⟨w, hw, e⟩ := hb z hz
    rw [cut_inv h _ hcut, Matrix.sub_mulVec, Matrix.one_mulVec] at e
    exact ⟨w, hw, e⟩
  have eγ : fm (maximalRealSubfield E) γ.1 = g.1 * (k⁻¹).1 * (h⁻¹).1 := by
    rw [e, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have cγ : GlobalTheory.UnRep.CongAt (stdLat E n) N N γ.1 := by
    refine congAt_of_congAtA (F := maximalRealSubfield E) _ hfg hsp hN ?_
    rw [eγ]
    exact LatForm.congAtA_mul _ _ _ _ _ (LatForm.congAtA_mul _ _ _ _ _ (hgc N hN) ck) ch
  have hmove : ∀ u, u ∈ Lh ↔ γ.1 *ᵥ u ∈ (conjLat H Λ.La).La := by
    intro u
    rw [← SetLike.mem_coe, ← SetLike.mem_coe (p := (conjLat H Λ.La).La), hΛ, hLh]
    constructor
    · rintro ⟨z, hz, ez⟩
      refine ⟨_, hk' z hz, ?_⟩
      rw [Move.fv_mulVec, ← ez, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Units.mul_inv_cancel_right]
    · rintro ⟨z, hz, ez⟩
      refine ⟨k.1 *ᵥ z, ?_, ?_⟩
      · obtain ⟨w, hw, e⟩ := hk z hz
        rw [sub_eq_iff_eq_add.1 e]
        exact add_mem (nsmul_mem hw _) hz
      · have := congrArg (fun x => fm (maximalRealSubfield E) (γ⁻¹).1 *ᵥ x) ez
        rw [← Move.fv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, e,
          ← mul_assoc, ← mul_assoc, ← FullReps.fm_mul, Units.inv_mul, FullReps.fm_one, one_mul] at this
        rw [Matrix.mulVec_mulVec, this]
  refine ⟨γ.1ᵀ, h, Lh, hδ, fun j => ?_, hh, hs, hLh, congrArg GenLat.mk (Submodule.ext fun v => ?_)⟩
  · obtain ⟨t, ht, hc⟩ := cγ
    refine ⟨t, ht, fun i => ?_⟩
    obtain ⟨w, hw, ew⟩ := hc _ (StdInhab.single_mem n i)
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hw j trivial)
    refine ⟨b, ?_⟩
    have := congrFun ew j
    rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul, ← hb, Pi.sub_apply,
      Matrix.mulVec_single_one] at this
    refine Eq.trans ?_ this
    congr 2
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Pi.single_apply, Ne.symm hij]
  · have hc : (fun j => IsCMField.complexConj E ((γ.1 *ᵥ fun j => IsCMField.complexConj E (v j)) j)) =
        adjM γ.1ᵀ *ᵥ v := by
      funext j
      simp [Matrix.mulVec, dotProduct, adjM]
    change v ∈ (actLat γ.1ᵀ Λ).La ↔ v ∈ (conjLat H Lh).La
    rw [mem_conjLat, hmove, mem_conjLat, hc]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change adjM γ.1ᵀ *ᵥ (γ.1ᵀ *ᵥ u) ∈ Λ.La
      rw [Matrix.mulVec_mulVec, hδ, Matrix.one_mulVec]
      exact hu
    · intro hv
      refine ⟨_, hv, ?_⟩
      change γ.1ᵀ *ᵥ (adjM γ.1ᵀ *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, hδ', Matrix.one_mulVec]

end General

open NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_move_to_split : ∀ (D : D7) (V : HSp D), V.gram = 1 → Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank → ∀ (H : Geo.Tor.Host D.host.E) (N : ℕ), 0 < N → ∀ Λ : GenLat D.host.E V.rank, Λ.Unimod → Λ.TrivAt N → ∃ (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (h : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.IsUnitaryM γ ∧ (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt N (fun i => γ i j) fun i => (((1 : Matrix (Fin V.rank) (Fin V.rank) (𝓞 D.host.E)) i j : 𝓞 D.host.E) : D.host.E)) ∧ h ∈ GfC V ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V h).1 ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.actLat γ Λ = GlobalTheory.UnRep.FullReps.conjLat H (Bridge.hLat V (fin V h)) := by
  intro D V hg hL H N hN Λ hU hT
  obtain ⟨γ, h', Lh, h1, h2, h3, h4, h5, h6⟩ := exists_move_matrix H N hN Λ hU hT
  have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨h, hh, eh⟩ := lift h' (by
    rw [show (HSpace.gram V)ᵀ = 1 by rw [hg, Matrix.transpose_one], hc]
    exact h3)
  refine ⟨γ, h, h1, h2, hh, ?_, ?_⟩
  · rw [eh, hc]; exact h4
  · rw [GlobalTheory.SplitReps.hLat_one] at hL
    rw [GlobalTheory.SplitReps.hLat_eq V (FWT.fin V h) Lh (by
      rw [hL]
      change _ = GlobalTheory.AdLat.latOf D.host.F (finHom V h).1 _
      rw [eh]
      exact h5)]
    exact h6

end GlobalTheory.SplitMove
