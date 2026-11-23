import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverThm
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.PtLocalEig

theorem jointKer_fin_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) (s : Finset G) :
    Module.finrank K ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let R : Matrix (↥s × ι) ι K := Matrix.of fun p b => Mg p.1.1 p.2 b
  have stack : ∀ {F : Type} [Field F] (N : G → Matrix ι ι F),
      (⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (N g))) =
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun (p : ↥s × ι) b => N p.1.1 p.2 b)) := by
    intro F _ N
    ext c
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro h
      funext p
      have := congrFun (h p.1.1 p.1.2) p.2
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
    · intro h g hg
      funext a
      have := congrFun h (⟨g, hg⟩, a)
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] using this
  have rn : ∀ {F : Type} [Field F] (N : Matrix (↥s × ι) ι F),
      N.rank + Module.finrank F (LinearMap.ker N.mulVecLin) = Fintype.card ι := by
    intro F _ N
    have := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at this
    exact this
  have h1 := rn R
  have h2 := rn (R.map φ)
  rw [GlobalTheory.Core.Rk.rank_map_field] at h2
  rw [stack Mg, stack (fun g => (Mg g).map φ)]
  have e : (Matrix.of fun (p : ↥s × ι) b => ((Mg p.1.1).map φ) p.2 b) = R.map φ := by
    ext p b
    rfl
  rw [e]
  change Module.finrank K ↥(LinearMap.ker (Matrix.mulVecLin R)) = _
  omega

theorem jointKer_finrank {K C : Type} [Field K] [Field C] (φ : K →+* C) {ι : Type} [Fintype ι] {G : Type}
    (Mg : G → Matrix ι ι K) :
    Module.finrank K ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) =
      Module.finrank C ↥(⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) := by
  classical
  let kK : Finset G → Submodule K (ι → K) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin (Mg g))
  let kC : Finset G → Submodule C (ι → C) := fun s => ⨅ g ∈ s, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))
  have heq : ∀ s, Module.finrank K (kK s) = Module.finrank C (kC s) := fun s => jointKer_fin_finrank φ Mg s
  have hex : ∃ m, ∃ s : Finset G, Module.finrank K (kK s) = m := ⟨_, ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin : ∀ s' : Finset G, Module.finrank K (kK s) ≤ Module.finrank K (kK s') := fun s' =>
    hs ▸ Nat.find_min' hex ⟨s', rfl⟩
  have hminC : ∀ s' : Finset G, Module.finrank C (kC s) ≤ Module.finrank C (kC s') := fun s' => by
    rw [← heq, ← heq]; exact hmin s'
  have hK : (⨅ g, LinearMap.ker (Matrix.mulVecLin (Mg g))) = kK s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kK (insert g s) = LinearMap.ker (Matrix.mulVecLin (Mg g)) ⊓ kK s := by
        simp only [kK, Finset.iInf_insert]
      have hle : kK (insert g s) ≤ kK s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hmin _)
      rw [← h, hins]
      exact inf_le_left
  have hC : (⨅ g, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ))) = kC s := by
    apply le_antisymm
    · exact le_iInf₂ fun g _ => iInf_le _ g
    · refine le_iInf fun g => ?_
      have hins : kC (insert g s) = LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) ⊓ kC s := by
        simp only [kC, Finset.iInf_insert]
      have hle : kC (insert g s) ≤ kC s := by rw [hins]; exact inf_le_right
      have h := Submodule.eq_of_le_of_finrank_le hle (hminC _)
      rw [← h, hins]
      exact inf_le_left
  rw [hK, hC]
  exact heq s

end GlobalTheory.PtLocalEig

namespace GlobalTheory.PtLocalEig

theorem eig_dim : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl) (μ : D.what₂.Tup) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), μ = D.what₂.muTw w → ∀ (φ : FractionRing (B.Oc j w) →+* ℂ), (∀ x, φ (B.ec j w x) = D.what₂.embLL x) → ∀ (κ : PlE D.host → ℕ → FractionRing (B.Oc j w)) (E : Submodule ℂ (D.what₂.Mt μ j)), (∀ v k, GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → ∀ (c : ℂ) (f f' : GAf D.host.E D.R.nV → (M μ j h1 h2).wt.W), NG.tN (M μ j h1 h2).J s ϖ k (c • f + f') = c • NG.tN (M μ j h1 h2).J s ϖ k f + NG.tN (M μ j h1 h2).J s ϖ k f') → (∀ y, y ∈ E ↔ ∀ v k (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ → NG.tN (M μ j h1 h2).J s ϖ k ((M μ j h1 h2).real y) = φ (κ v k) • (M μ j h1 h2).real y) → Module.finrank (FractionRing (B.Oc j w)) ↥(⨅ (v : PlE D.host) (k : ℕ) (_ : GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k), Module.End.eigenspace (B.hK j w v k) (κ v k)) = Module.finrank ℂ E := by
  intro D M B j w μ h1 h2 hμ φ hφ κ E hex hadd hE
  subst hμ
  classical
  haveI := Formalism.L2.finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
  let bC := Module.Basis.mk hjb.1 hjb.2.ge
  have hb := B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ a, bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := fun a => by simp [bC]
  have hbV : ∀ a, bV a = B.iV j w (b a) := fun a => by simp [bV]
  have rC : ∀ x r, bC.repr (D.what₂.jMt (D.what₂.muTw w) j x) r = D.what₂.embLL (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 x r
  have rV : ∀ x r, bV.repr (B.iV j w x) r = B.ec j w (b.repr x r) :=
    fun x r => Formalism.L2.NCov.repr_transport (B.ec j w) (B.iV j w) b hb.1 hb.2 x r
  let A : PlE D.host → ℕ → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) D.what₂.LL :=
    fun v k => LinearMap.toMatrix b b (B.hL j w v k)
  let G := {p : PlE D.host × ℕ // Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) p.1 p.2}
  let Mg : G → Matrix (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) (FractionRing (B.Oc j w)) :=
    fun g => (A g.1.1 g.1.2).map (B.ec j w) - κ g.1.1 g.1.2 • 1
  set Mw := M (D.what₂.muTw w) j h1 h2 with hMw

  have hV : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) c,
      B.hK j w v k (bV.equivFun.symm c) = κ v k • bV.equivFun.symm c ↔ Matrix.mulVec (Mg ⟨(v, k), hvk⟩) c = 0 := by
    intro v k hvk c
    have hmat : LinearMap.toMatrix bV bV (B.hK j w v k) = (A v k).map (B.ec j w) := by
      ext r c'
      rw [LinearMap.toMatrix_apply, Matrix.map_apply, hbV, B.hK_def, rV]
      simp only [A, LinearMap.toMatrix_apply]
    have hr := LinearMap.toMatrix_mulVec_repr bV bV (B.hK j w v k) (bV.equivFun.symm c)
    rw [hmat] at hr
    have hc : ⇑(bV.repr (bV.equivFun.symm c)) = c := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hc] at hr
    rw [← bV.equivFun.injective.eq_iff, map_smul, LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply, ← hr]
    simp only [Mg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have hPV : (⨅ (v : PlE D.host) (k : ℕ) (_ : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k),
      Module.End.eigenspace (B.hK j w v k) (κ v k)).map (bV.equivFun : B.V j w →ₗ[FractionRing (B.Oc j w)] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin (Mg g)) := by
    ext c
    rw [Submodule.mem_map_equiv]
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      exact (hV v k hvk c).1 (h v k hvk)
    · intro h v k hvk
      exact (hV v k hvk c).2 (h ⟨⟨v, k⟩, hvk⟩)

  have hCk : ∀ v k (hvk : Formalism.L2.GenAt D (D.what₂.places.resChar w) (B.Qc j w) v k) (y : D.what₂.Mt (D.what₂.muTw w) j),
      (∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y) = φ (κ v k) • Mw.real y) ↔
      Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
    intro v k hvk y
    obtain ⟨s0, ϖ0, hc0, hu0⟩ := hex v k hvk
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))
    have hagree : ∀ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
        IsConjPl D.host v s.w → Formalism.AUTREP.IsUnif D.host.E s.v ϖ →
        ∀ x, Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real x) = Mw.real (tC x) := by
      intro s ϖ hc hu
      have hadd' := hadd v k s ϖ hvk hc hu
      have htN0 : Formalism.L2.NG.tN Mw.J s ϖ k (0 : Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
        have := hadd' 1 0 0
        rw [one_smul, add_zero, one_smul] at this
        simpa using this
      let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (Formalism.AUTREP.GAf D.host.E D.R.nV → Mw.wt.W) :=
        { toFun := fun y => Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real y)
          map_add' := fun y y' => by
            have := hadd' 1 (Mw.real y) (Mw.real y')
            rw [one_smul, one_smul] at this
            simp only [map_add]
            exact this
          map_smul' := fun c y => by
            have := hadd' c (Mw.real y) 0
            rw [add_zero, htN0, add_zero] at this
            simp only [map_smul, RingHom.id_apply]
            exact this }
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) a
        show Formalism.L2.NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC a))
        rw [e, hbC a]
        exact (B.hL_def j w h1 h2 v k s ϖ hvk hc hu (b a)).symm
      intro x
      exact LinearMap.congr_fun hLt x
    have hmat : LinearMap.toMatrix bC bC tC = (A v k).map D.what₂.embLL := by
      ext r c
      rw [LinearMap.toMatrix_apply, Matrix.map_apply]
      have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) c
      show bC.repr ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (B.hL j w v k (b a))) (bC c)) r = _
      rw [e, rC]
      simp only [A, LinearMap.toMatrix_apply]
    have hMg : (Mg ⟨(v, k), hvk⟩).map φ = (A v k).map D.what₂.embLL - φ (κ v k) • 1 := by
      ext r c
      simp only [Mg, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp [hφ]
    have hvec : tC y = φ (κ v k) • y ↔ Matrix.mulVec ((Mg ⟨(v, k), hvk⟩).map φ) (bC.equivFun y) = 0 := by
      rw [hMg, Matrix.sub_mulVec, ← hmat, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero,
        Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr, ← Finsupp.coe_smul, ← map_smul]
      exact ⟨fun h => by rw [h], fun h => bC.repr.injective (DFunLike.coe_injective h)⟩
    constructor
    · intro h
      apply hvec.1
      apply Mw.real_inj
      rw [← hagree s0 ϖ0 hc0 hu0, h s0 ϖ0 hc0 hu0, map_smul]
    · intro h s ϖ hc hu
      rw [hagree s ϖ hc hu, hvec.2 h, map_smul]
  have hPC : E.map (bC.equivFun : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] _) =
      ⨅ g : G, LinearMap.ker (Matrix.mulVecLin ((Mg g).map φ)) := by
    ext d
    rw [Submodule.mem_map_equiv, hE]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · rintro h ⟨⟨v, k⟩, hvk⟩
      have := (hCk v k hvk (bC.equivFun.symm d)).1 (fun s ϖ hc hu => h v k s ϖ hvk hc hu)
      rwa [LinearEquiv.apply_symm_apply] at this
    · intro h v k s ϖ hvk hc hu
      refine (hCk v k hvk _).2 ?_ s ϖ hc hu
      rw [LinearEquiv.apply_symm_apply]
      exact h ⟨⟨v, k⟩, hvk⟩
  rw [← LinearEquiv.finrank_map_eq bV.equivFun, hPV, ← LinearEquiv.finrank_map_eq bC.equivFun E, hPC]
  exact jointKer_finrank φ Mg

end GlobalTheory.PtLocalEig
