import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.FvChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (J.reindex (finCongr h) (finCongr h)) (fun j => x ((finCongr h).symm j))
      (fun j => y ((finCongr h).symm j)) = hform σ J x y := by
  subst h
  simp [hform]

theorem mem_latS_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E)
    (Lb : Submodule (𝓞 E) (Fin a → E)) (w : HeightOneSpectrum (𝓞 F)) (t : Fin a → E ⊗[F] w.adicCompletion F)
    (ht : t ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb))) :
    (fun j => t ((finCongr h).symm j)) ∈ latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet σ (J.reindex (finCongr h) (finCongr h)) (reL h Lb))) := by
  subst h
  have hL : reL rfl Lb = Lb := by
    ext x
    simp [reL, reV]
  simpa [hL] using ht

theorem reGL_solve {a b : ℕ} (h : a = b) (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg' : g' = reGL h _ g) (t : Fin a → E ⊗[F] w.adicCompletion F) (z : Fin a → E)
    (ht : (bc (prV (E := E) w) g).1 *ᵥ t = fun j => inclE (F := F) (w.adicCompletion F) (z j)) :
    ((bc (prV (E := E) w) g')⁻¹).1 *ᵥ
      (fun j => inclE (F := F) (w.adicCompletion F) (z ((finCongr h).symm j))) =
      fun j => t ((finCongr h).symm j) := by
  subst h hg'
  have hg : reGL rfl _ g = g := by
    ext
    simp [reGL]
  simp only [hg, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem crdN_mem_LdG (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ LdG D i hi (clsCrd D u i hi c) := by
  apply Submodule.subset_span
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have h2 := hform_reindex (rankN D i hi) (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd (D.sp.X i) y) (Formalism.L2.Herm.crd (D.sp.X i) z.1)
  have h3 := Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) y z.1
  have hz := z.2
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hz
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hz y hy)
  refine ⟨r, ?_⟩
  change _ = hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) y ((finCongr (rankN D i hi)).symm j))
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) z.1 ((finCongr (rankN D i hi)).symm j))
  unfold gramN
  rw [h2]
  rw [hr]
  exact h3

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem exists_reindex_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ tr : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb)) →+
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' Lb')),
      ∀ t, (tr t).1 = fun j => t.1 ((finCongr h).symm j) := by
  subst hJ hL
  exact ⟨{ toFun := fun t => ⟨fun j => t.1 ((finCongr h).symm j), mem_latS_reindex h σ J Lb w t.1 t.2⟩
           map_zero' := rfl
           map_add' := fun _ _ => rfl }, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

set_option maxHeartbeats 1000000 in

theorem fvTie_of_car {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A)
    (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
      (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  have hc := hH.carC u i h1 h2 β
  have hw : (H.vT u v).1 = ((F u).atT.eV v).1 := congrArg (fun e => (e v).1) (hH.eV u).symm
  suffices hs : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
        (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) from hs _ hw
  intro w hw'
  subst hw'
  obtain ⟨tr, htr⟩ := exists_reindex_hom (F := D.host.F) (rankN D i (le_of_succ_m h2))
    (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram (gramN D i (le_of_succ_m h2)) rfl
    (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb hc.Lb_eq ((F u).atT.eV v).1
  refine ⟨⟨((F u).fMeC i h1 h2 β v).toAddMonoidHom.comp
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2).toAddMonoidHom.comp tr), ?_⟩⟩
  intro c z t ht
  have hmem := crdN_mem_LdG D u i (le_of_succ_m h2) c.1 z
  have hp := hT.prC u i h1 h2 v c.1 z ⟨_, hmem⟩ rfl
  refine (congrArg ((D.fm u).fv i v c.1) hp).symm.trans ?_
  have key : ((bc (prV (E := D.host.E) ((F u).atT.eV v).1) (((F u).ch i h1 h2 β).y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
        (crdN D i (le_of_succ_m h2) z.1 a)) = (tr t).1 :=
    (reGL_solve (rankN D i (le_of_succ_m h2)) ((F u).atT.eV v).1 ((H.cls u i h1 (le_of_succ_m h2) β).y c).1
      (((F u).ch i h1 h2 β).y c).1 (hc.y_eq c) t.1 (Formalism.L2.Herm.crd (D.sp.X i) z.1) ht).trans (htr t).symm
  have hz := (congrArg (fun x => x ∈ latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
    (intV D.host.E ((F u).atT.eV v).1)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E)
      (gramN D i (le_of_succ_m h2)) ((F u).ch i h1 h2 β).lev.Lb))) key).mpr (tr t).2
  refine ((F u).fvC i h1 h2 v β c ⟨_, hmem⟩ hz).trans ?_
  exact congrArg (fun x => ((F u).fMeC i h1 h2 β v)
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2) x)) (Subtype.ext key)

end GlobalTheory.Mem.Col2.TC.FvChart

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mem.Col2.TC.fvTie_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u i h1 h2 v β
  exact FvChart.fvTie_of_car H F A hH hT u i h1 h2 v β
