import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChartStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSuccStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.KerSucc

theorem latK_of_renamed {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N n : ℕ} (h : N = n) (hr : n = N) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb Lb₁ : Submodule (𝓞 E) (Fin N → E))
    (J' : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb' : Submodule (𝓞 E) (Fin n → E))
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hy : x = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) y)
    (hLb : Lb' = Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E))) (h₁ : Lb₁ = Lb) :
    HEq ((latK sp J' a y Lb').map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a x Lb₁) := by
  have h1 := (GlobalTheory.reindex_rename_point_det_latK sp hr J' a y Lb').1
  have h3 := (GlobalTheory.reindex_rename_point_det_latK sp h J a x Lb).2.2
  have hy' : y = Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) x := by rw [hy]; exact h1.symm
  rw [hJ, hLb, h₁, hy']
  exact h3

section Unfold

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem gram_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).J (i + 1) La =
      (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr hr) (finCongr hr) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = _
  rw [chAt, dif_pos hi]

theorem base_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).Lb (i + 1) La =
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
        ((reE (E := D.host.E) hr).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = _
  rw [chAt, dif_pos hi]

end Unfold

end GlobalTheory.TwV.KerSucc

theorem GlobalTheory.TwV.Joint.kerN_succ_heq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  obtain ⟨hr, hx⟩ := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
  have hLb := (GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa).2.1
  have hJ : (J.cp std).J (j + 1) La = (gramN D (j + 1) hj).reindex (finCongr hr.symm) (finCongr hr.symm) :=
    GlobalTheory.TwV.KerSucc.gram_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  have hL : (J.cp std).Lb (j + 1) La = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb.map
      ((reE (E := D.host.E) hr.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) :=
    GlobalTheory.TwV.KerSucc.base_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  exact GlobalTheory.TwV.KerSucc.latK_of_renamed D.sp hr.symm hr _ J.a _ _ _ _ _ _ hJ hx hL hLb
