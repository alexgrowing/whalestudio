import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.VertCmp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp
open scoped Classical

private theorem fnMap_appLE {X Y : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens} (e : V ≤ j ⁻¹ᵁ U)
    (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (s : Γ(X, U)) :
    fnOf V h' ((j.appLE U V e).hom s) = SmallSec.fnMap j hη (fnOf U h s) := by
  rw [SmallSec.fnMap_fnOf j hη h (e h')]
  exact fnOf_resG e h' _

private theorem regAt_fnMap' {X Y : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] (j : Y ⟶ X)
    (hη : j (genericPoint Y) ⤳ genericPoint X) {y : Y} {t : X.functionField} (h : RegAt (j y) t) :
    RegAt y (SmallSec.fnMap j hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf j hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

private theorem unitAt_fnMap' {X Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨regAt_fnMap' g hη h.regAt, regAt_fnMap' g hη h.inv.regAt⟩

private theorem isRatSec_pull' {X Z : Scheme.{0}} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {L : LB X} {s : L.ι → X.functionFieldˣ} (hs : IsRatSec L s) :
    IsRatSec (L.pull g) (fun i => Units.map (SmallSec.fnMap g hη).toMonoidHom (s (i PUnit.unit))) := by
  intro i j hij
  have le : (L.pull g).U i ⊓ (L.pull g).U j ≤ g ⁻¹ᵁ (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) :=
    fun x hx => ⟨LB.pull_U_le g i hx.1, LB.pull_U_le g j hx.2⟩
  have h0 : genericPoint X ∈ L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit) := gen_mem (x := g (genericPoint Z)) (le hij)
  change SmallSec.fnMap g hη (s (i PUnit.unit)) = _ * SmallSec.fnMap g hη (s (j PUnit.unit))
  rw [hs _ _ h0, map_mul, ← fnMap_appLE g hη le h0 hij]
  congr 2
  exact (InducedPull.val_pull_g L g i j le).symm

theorem UpperTheory.vertical_model_match_compat :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (b : 𝓞 F →+* O) (B T : Vert.Model O) (μ : Match Y b B) (μ' : Match Y b T) (f : Vert.Model.Hom T B) (hf : f.f (genericPoint T.X) ⤳ genericPoint B.X) (f' : μ'.U.toScheme ⟶ μ.U.toScheme), f' ≫ μ.U.ι = μ'.U.ι ≫ f.f → f' ≫ μ.h = μ'.h → (∀ (v : HeightOneSpectrum (𝓞 F)) (L : LB B.X) (s : L.ι → B.X.functionFieldˣ) (l : Ext v → AlgPt Y → ℝ), Reads μ v L s l → Reads μ' v (L.pull f.f) (fun i => Units.map (SmallSec.fnMap f.f hf).toMonoidHom (s (i PUnit.unit))) l) ∧ (∀ (P : VertDiv B) (s : P.M.ι → B.X.functionFieldˣ), IsSecOf P s → IsSecOf (P.pull f.comp_str) (fun i => Units.map (SmallSec.fnMap f.f hf).toMonoidHom (s (i PUnit.unit)))) ∧ (SmallSec.fnMap f.f hf).comp (cst B) = cst T := by
  intro F _ _ Y O _ _ _ b B T μ μ' f hf f' h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rintro v L s l ⟨hs, W, hW, H⟩
    refine ⟨isRatSec_pull' f.f hf hs, W, hW, ?_⟩
    intro e y z zt i hy hz hzt hi
    have e1 : (z ≫ f') ≫ μ.U.ι = (z ≫ μ'.U.ι) ≫ f.f := by simp only [Category.assoc, h1]
    have H' := H e y (z ≫ f') (zt ≫ f.f) (i PUnit.unit) hy (by rw [Category.assoc, h2, hz])
      (by rw [e1, ← hzt, Category.assoc]) (fun x hx => LB.pull_U_le f.f i (hi hx))
    rw [e1] at H'
    have hU : UnitAt (f.f (below (z ≫ μ'.U.ι))) (s (i PUnit.unit) : B.X.functionField) := H'.1
    refine ⟨unitAt_fnMap' f.f hf hU, ?_⟩
    rw [← H'.2, ← SmallSec.valAt_fnMap f.f hf _ hU.regAt]
    rfl
  · intro P s hs i h
    have e : T.gen ⊓ (P.M.pull f.f).U i ≤ f.f ⁻¹ᵁ (B.gen ⊓ P.M.U (i ⟨⟩)) :=
      inf_le_inf (Vert.Model.preimage_gen f.comp_str).ge (LB.pull_U_le f.f i)
    have h0 : genericPoint B.X ∈ B.gen ⊓ P.M.U (i ⟨⟩) := gen_mem (x := f.f (genericPoint T.X)) (e h)
    change SmallSec.fnMap f.f hf (s (i PUnit.unit)) = _
    rw [hs _ h0, ← fnMap_appLE f.f hf e h0 h]
    exact congrArg _ (LB.resG_appLE f.f (LB.pull_inf_le f.f _ i) _ _).symm
  · ext a
    change SmallSec.fnMap f.f hf (fnOf ⊤ _ (B.const a)) = fnOf ⊤ _ (T.const a)
    rw [← Vert.Model.appTop_const f.comp_str]
    exact SmallSec.fnMap_fnOf f.f hf _ (TopologicalSpace.Opens.mem_top _) _
