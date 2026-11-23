import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.TiedTwJSym
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HermTransport

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

open scoped TensorProduct

theorem reGL_refl_apply' {n : ℕ} (R : Type) [CommRing R] (g : GL (Fin n) R) : reGL rfl R g = g := by
  ext a b
  simp [reGL]

theorem reGL_refl_hom' {n : ℕ} (R : Type) [CommRing R] :
    (reGL (rfl : n = n) R).toMonoidHom = MonoidHom.id _ := by
  ext1 g
  exact reGL_refl_apply' R g

omit [StarRing E] in
theorem reL_refl' {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) : reL rfl L = L := by
  ext x
  simp [reL, reV]

theorem classTie_of_reindex (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) {σ : E →ₐ[F] E}
    (hσ : σ = hc.sig) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ a b, J a b = S.gram (Fin.cast h.symm a) (Fin.cast h.symm b))
    {U' : Subgroup (GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))} {Lb' : Submodule (𝓞 E) (Fin n → E)}
    {cl cl' : Type} (e : cl' ≃ cl) {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) S.V)
    (y : cl → UPts σ J (Formalism.L2.Herm.Af F))
    (y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) :
      ClassSet ((ratPts σ J (Formalism.L2.Herm.Af F)).subgroupOf (UPts σ J (Formalism.L2.Herm.Af F)))
        (U'.subgroupOf (UPts σ J (Formalism.L2.Herm.Af F))))))
    (y_lat : ∀ c (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F),
      x ∈ Formalism.L2.Herm.hatL (F := F) (reL h (Formalism.L2.Herm.crdLat S (lat c))) ↔
        ((y c).1⁻¹).1 *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Lb')
    (stabI : ∀ c, stab c →* UJ (σ : E →+* E) J)
    (stabI_inj : ∀ c, Function.Injective (stabI c))
    (stabI_range : ∀ c (γ : UJ (σ : E →+* E) J), γ ∈ (stabI c).range ↔
      bc (inclE (F := F) (Formalism.L2.Herm.Af F)) γ.1 ∈ U'.map (MulAut.conj (y c).1).toMonoidHom)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) (U : Subgroup (GL (Fin S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)))
    (hLb : Lb' = reL h Lb) (hU : U' = U.map (reGL h _).toMonoidHom) :
    ∃ C : Formalism.L2.Herm.ClassTie hc S Lb U (fun c' => stab (e c')) (fun c' => lat (e c')),
      (∀ c', (y (e c')).1 = reGL h _ (C.y c').1) ∧ ∀ c' s, (stabI (e c') s).1 = reGL h _ (C.stabI c' s).1 := by
  subst h
  subst hσ
  obtain rfl : J = S.gram := by
    ext a b
    simpa using hJ a b
  subst hLb
  subst hU
  have hU0 : U.map (reGL (rfl : S.rank = S.rank) (E ⊗[F] Formalism.L2.Herm.Af F)).toMonoidHom = U := by
    rw [reGL_refl_hom', Subgroup.map_id]
  rw [hU0] at y_bij stabI_range
  simp only [reL_refl'] at y_lat
  refine ⟨⟨fun c' => y (e c'), y_bij.comp e.bijective, fun c' x => y_lat (e c') x, fun c' => stabI (e c'),
    fun c' => stabI_inj (e c'), fun c' γ => stabI_range (e c') γ⟩,
    fun c' => (reGL_refl_apply' _ _).symm, fun c' s => (reGL_refl_apply' _ _).symm⟩

end Gen

theorem latCrd_eq_reL (D : D7) (i : ℕ) (hi : i ≤ D.R.m) (L : Submodule (𝓞 D.host.E) (D.sp.X i).V) :
    latCrd D i hi L = reL (rankN D i hi) (Formalism.L2.Herm.crdLat (D.sp.X i) L) := by
  ext x
  simp [latCrd, reL, Formalism.L2.Herm.crdLat, reV, Formalism.L2.Herm.crd]

theorem classTie_of_chart : ∀ (D : D7) (i : ℕ) (hi : i ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {cl cl' : Type} (e : cl' ≃ cl)
  {stab : cl → Type} [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 D.host.E) (D.sp.X i).V)
  (K : LevelChart D T bad i hi stab (fun c => latCrd D i hi (lat c)))
  {T' f' : ℕ} (L : Formalism.L2.Herm.StepLevel D.sp.cm (D.sp.X i) D.host.g T' f'),
  K.lev.Lb = reL (rankN D i hi) L.Lb → K.lev.U = L.U.map (reGL (rankN D i hi) _).toMonoidHom →
  ∃ C : Formalism.L2.Herm.ClassTie D.sp.cm (D.sp.X i) L.Lb L.U (fun c' => stab (e c')) (fun c' => lat (e c')),
    (∀ c', (K.y (e c')).1 = reGL (rankN D i hi) _ (C.y c').1) ∧
    ∀ c' s, (K.stabI (e c') s).1 = reGL (rankN D i hi) _ (C.stabI c' s).1 := by
  intro D i hi T bad cl cl' e stab _ lat K T' f' L hLb hU
  exact classTie_of_reindex D.sp.cm (D.sp.X i) (rankN D i hi) rfl (fun a b => rfl) e lat K.y K.y_bij
    (fun c x => by rw [← latCrd_eq_reL]; exact K.y_lat c x) K.stabI K.stabI_inj K.stabI_range L.Lb L.U hLb hU

end GlobalTheory.HermTransport
