import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPairMovedOfMultipliesLocalFunctional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjection

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.FvOff
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

set_option maxHeartbeats 1000000 in

theorem fT_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w.asIdeal)
    (y y' η κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hκ : κ ∈ S.U) (hη : bc (prV (E := E) w) η = 1)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = y * η * κ) (z' : Fin n → E)
    (hx : ((bc (prV (E := E) w) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.1 *ᵥ z') a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z' a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w hw ⟨_, hx'⟩ = S.fT w hw ⟨_, hx⟩ := by
  have hk : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = η * κ := by
    rw [mul_assoc, he]; group
  have hkw : bc (prV (E := E) w) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      bc (prV (E := E) w) κ := by
    rw [hk, map_mul, hη, one_mul]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec w y y' γ z'
  rw [hkw] at hm
  have hloc : bc (prV (E := E) w) κ ∈ S.Uloc w := ((S.U_eq κ).1 hκ).2 w
  rw [S.UlocAlt w hw] at hloc
  obtain ⟨hg, hf⟩ := (Subgroup.mem_inf.1 hloc).2
  rw [← hf ⟨_, hx'⟩]
  congr 1
  exact Subtype.ext hm

set_option maxHeartbeats 1000000 in

theorem fT_adStep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w w' : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w'.asIdeal) (hne : w' ≠ w)
    (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hA : Formalism.L2.Herm.AdStep σ J S.U y y' γ w) (z z' : Fin n → E) (hz : z = γ.1 *ᵥ z')
    (hx : ((bc (prV (E := E) w') y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w') y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z' a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w' hw ⟨_, hx'⟩ = S.fT w' hw ⟨_, hx⟩ := by
  obtain ⟨κ, hκ, η, -, hη, he⟩ := hA
  subst hz
  exact fT_move S w' hw y y' η κ γ hκ (hη _ hne) he z' hx hx'

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ld_loc_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi (cc c)) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  refine GlobalTheory.DualCompletion.dual_move D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi (cc c)) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) (bwB_clsCrd_lat D u i hi (cc c))
    ⟨Module.Finite.iff_fg.1 K.lev.Lb_fin, K.lev.Lb_span⟩
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ld_in {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi (cc c)) :
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (v.adicCompletion D.host.F) (z a)) ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
  (ld_loc_ch K v c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_off_cls {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi)
    (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) K.lev.U (K.y c).1 (K.y c').1 γ (A.eV v).1) (hv : v' ≠ v)
    (z : Ld D u i hi c) (z' : Ld D u i hi c') (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (P.pr v' c' z') = (D.fm u).fv i v' c (P.pr v' c z) := by
  have hw : (A.eV v').1 ≠ (A.eV v).1 := fun h => hv (A.eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c z.1 z.2
  have hx' := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c' z'.1 z'.2
  have e := fT_adStep K.lev (A.eV v).1 (A.eV v').1 (A.eV v').2 hw (K.y c).1 (K.y c').1 γ hA z.1 z'.1 hz hx hx'
  exact (hT v' c' z' hx').trans ((congrArg (fMe v') e).trans (hT v' c z hx).symm)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_off_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}
    {res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v}
    (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T res i hi (fun c => clsCrd D u i hi c))
    (eV : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTieG L eV K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (hβ : chOf c' = chOf c) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (K (chOf c)).lev.U ((K (chOf c)).y ⟨c, rfl⟩).1
      ((K (chOf c)).y ⟨c', hβ⟩).1 γ (eV v).1) (hv : v' ≠ v)
    (z : LdG D i hi (clsCrd D u i hi c)) (z' : LdG D i hi (clsCrd D u i hi c')) (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (L.pr v' c' z') = (D.fm u).fv i v' c (L.pr v' c z) := by
  have hw : (eV v').1 ≠ (eV v).1 := fun h => hv (eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c, rfl⟩ z.1 z.2
  have hx' := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c', hβ⟩ z'.1 z'.2
  have e := fT_adStep (K (chOf c)).lev (eV v).1 (eV v').1 (eV v').2 hw _ _ γ hA z.1 z'.1 hz hx hx'
  exact (hT v' (chOf c) ⟨c', hβ⟩ z' hx').trans ((congrArg (fMe (chOf c) v') e).trans (hT v' (chOf c) ⟨c, rfl⟩ z hx).symm)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem fv_eq_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  intro B X I hI hP l Z H F hF hC u i hi v v' c c' γ hA hv z z' hz
  by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
  · exact fv_off_cls ((F u).lv i hi) ((F u).cls i hi h) ((F u).fMe i hi h) ((F u).fv i hi h) v v' c c' γ (hA.1 h) hv z z' hz
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
    obtain ⟨hβ, hA'⟩ := hA.2 h1 h2
    have e := fv_off_ch ((F u).lvC i h1 h2) (F u).atT.eV ((F u).ch i h1 h2) ((F u).fMeC i h1 h2) ((F u).fvC i h1 h2)
      v v' c c' hβ γ hA' hv z z' hz
    have e1 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c).1 z z rfl
    have e2 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c').1 z' z' rfl
    exact (congrArg _ e2).symm.trans (e.trans (congrArg _ e1))

end GlobalTheory.Mem.Col2.HAt.FvOff
