import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_refl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem fvTie_of_coords (hc : CMData F E) (S : HSpace E) {cls : Type}
    (y : cls → Formalism.L2.Herm.UAf hc S) (lat : cls → Submodule (𝓞 E) S.V)
    (w : HeightOneSpectrum (𝓞 F)) (k : Type) [AddCommGroup k]
    (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {b : ℕ} (h : S.rank = b)
    (J : Matrix (Fin b) (Fin b) E) (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ c, y' c = reGL h _ (y c).1)
    (fT : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb')) →+ k)
    (hfv : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c))
      (hz : ((bc (prV (E := E) w) (y' c))⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (reV h E (Formalism.L2.Herm.crd S z.1) a)) ∈
        latS (F := F) (w.adicCompletion F) (intV E w)
          (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb'))),
      fz c z = fT ⟨_, hz⟩) :
    Nonempty (Formalism.L2.Herm.FvTie hc S Lb y lat w k fz) := by
  subst h
  obtain rfl : J = S.gram := by rw [hJ]; ext i j; simp
  obtain rfl : Lb' = Lb := hL.trans (reL_refl Lb)
  obtain rfl : y' = fun c => (y c).1 := funext fun c => (hy c).trans (reGL_refl _ _)
  refine ⟨⟨fT, fun c z t ht => ?_⟩⟩
  have ht' : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) = t.1 := by
    have e : (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (Formalism.L2.Herm.crd S z.1 a) := rfl
    rw [e, ← ht, Matrix.mulVec_mulVec]
    simp
  have hz : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Lb')) := by
    rw [ht']; exact t.2
  rw [hfv c z hz]
  exact congrArg fT (Subtype.ext ht')

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩

set_option maxHeartbeats 4000000 in

theorem fvTie_top {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (h1 : 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u D.R.m) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl β).Lb (H.cls u D.R.m h1 le_rfl β).y
      (fun c => D.clsLat u D.R.m c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
  obtain rfl : β = chM H u := @Subsingleton.elim _ (@Unique.instSubsingleton _ (H.Ch_m u).some) _ _
  have key : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl (chM H u)).Lb
        (H.cls u D.R.m h1 le_rfl (chM H u)).y (fun c => D.clsLat u D.R.m c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
    intro w hw
    subst hw
    have hc := hH.carM u
    refine fvTie_of_coords D.sp.cm (D.sp.X D.R.m) _ _ _ _ _ _ (rankN D D.R.m le_rfl) (gramN D D.R.m le_rfl) rfl
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb hc.Lb_eq
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c.1).1) (fun c => hc.y_eq c.1)
      (((F u).fMe D.R.m le_rfl (Or.inr rfl) v).toAddMonoidHom.comp
        (((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.fT _ ((F u).atT.eV v).2).toAddMonoidHom) ?_
    intro c z hz
    have hz' := crdN_mem_Ld u D.R.m le_rfl c.1 z
    have e1 := (F u).fv D.R.m le_rfl (Or.inr rfl) v c.1 ⟨_, hz'⟩ hz
    have e2 := hT.pr u D.R.m le_rfl v c.1 z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv D.R.m v c.1 p) e2.symm).trans e1
  exact key _ (by rw [hH.eV u])

set_option maxHeartbeats 4000000 in

theorem fvTie_chart_top : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u h1 v β
  exact fvTie_top H F A hH hT u h1 v β

end GlobalTheory.Mem.Col2.TC
end
