import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameOffOfIsPt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalModelLatticesAdmissibleSmall
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem bc_reGL_comm {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ} (e : Fin m ≃ Fin n) (x : GL (Fin m) A) :
    Formalism.UG.bc φ (Formalism.L2.PairingIndexBounds.F.reGL e x) = Formalism.L2.PairingIndexBounds.F.reGL e (Formalism.UG.bc φ x) := by
  apply Units.ext
  ext a b
  rfl

theorem sameOff_reGL_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {m n : ℕ} (e : Fin m ≃ Fin n) (x y : GL (Fin m) (AfE F E))
    (h : SameOff w x y) : SameOff w (Formalism.L2.PairingIndexBounds.F.reGL e x) (Formalism.L2.PairingIndexBounds.F.reGL e y) := fun w' hw => by
  rw [bc_reGL_comm, bc_reGL_comm, h w' hw]

theorem sameOff_eps_of_bases {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}
    {σ : E →ₐ[F] E} {Jm : Matrix (Fin n) (Fin n) E} {A : LocAt F E n G} (hG : LocGood σ Jm A) (i : G.comp)
    (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (v : Fin G.P.nV) (hgg : ∀ v', v' ≠ v → g v' = g' v') :
    SameOff (A.pl v).1 (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
      (Classical.epsilon fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F)) := by
  have ha := Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g, Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  have hb := Classical.epsilon_spec (p := fun x => A.IsPt i g' x ∧ x ∈ UPts σ Jm (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hG.isPt_sec i g', Subgroup.mul_mem _ (hG.yG_mem i) (hG.sec _).2⟩
  exact GlobalTheory.TwV.Xc.sameOff_of_isPt F E σ n p G A Jm hG i g g' ⟨_, ha.2⟩ ⟨_, hb.2⟩ ha.1 hb.1 v hgg

set_option maxHeartbeats 4000000 in

theorem sameOff_len_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameOff ((A0 J).pl v).1 (J.pt std j hj La).1 (J.pt std j hj Lb).1 ∧ ∀ v', v' ≠ v → len (sysS H X std) v' j La.2 = len (sysS H X std) v' j Lb.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb hab
  obtain ⟨hLa, hLb, h1, h2⟩ := hab
  have hent : ∀ v', v' ≠ v → La.2 ((sysS H X std).vJ j v') = Lb.2 ((sysS H X std).vJ j v') := by
    intro v' hv'
    have hne : (sysS H X std).vJ j v' ≠ (sysS H X std).vJ j v := by
      intro h
      apply hv'
      have := congrArg ((sysS H X std).vB j) h
      rwa [Formalism.L2.G.Pend.vB_vJ, Formalism.L2.G.Pend.vB_vJ] at this
    have := congrFun h2 ((sysS H X std).vJ j v')
    exact (Function.update_of_ne hne _ _).symm.trans (this.trans (Function.update_of_ne hne _ _))
  refine ⟨?_, fun v' hv' => by unfold len; rw [hent v' hv']⟩
  have hlat : ∀ v', v' ≠ v → (sysS H X std).latAt v' j La.2 = (sysS H X std).latAt v' j Lb.2 := by
    intro v' hv'
    have := hent v' hv'
    cases j <;> exact this
  obtain ⟨hr, hpa⟩ := (hD j hj La hLa).1
  obtain ⟨hr', hpb⟩ := (hD j hj Lb hLb).1
  rw [hpa, hpb]
  apply sameOff_reGL_of
  obtain ⟨c, a⟩ := La
  obtain ⟨c', b⟩ := Lb
  dsimp only at h1
  subst h1
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    apply sameOff_reGL_of
    apply sameOff_eps_of_bases J.one.good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]
  | succ i =>
    simp only [Joint.cp, cpAt]
    simp only [chAt, dif_pos hj]
    apply sameOff_reGL_of
    rw [show (A0 J).pl v = ((I.at' i hj).st.loc ((I.at' i hj).st.eC.symm c).1).pl v from (J.pl i hj _ v).symm]
    apply sameOff_eps_of_bases (H.core i hj _).good
    intro v' hv'
    have hl := hlat v' hv'
    dsimp only at hl
    unfold basesAt
    rw [hl]

end GlobalTheory.TwV.Xc
