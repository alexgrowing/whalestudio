import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPrimesOverLevelPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRelationClassesCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicConjugateCharacterStandardFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.UpMove

section G

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 4000000 in

theorem upCl_of_crd (A : AtTTied u) (P : ∀ i hi, LvTied u A i hi) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (hoff : ∀ q : HeightOneSpectrum (𝓞 D.host.E), q.asIdeal ≠ A.Pv v → q.asIdeal ≠ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) →
      Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ q.asIdeal (clsCrd D u i hi c))
    (h3 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c))
    (h4 : Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}))
    (h5 : ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((P i hi).pr v _ x) = (D.fm u).fv i v c ((P i hi).pr v c ⟨_, hx⟩))
    (h6 : ∀ v', v' ≠ v → ∀ (z : ↥(Formalism.L2.Forms.Ld D u i hi c))
        (z' : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH A P i v c y)))), z.1 = γ.1.1 *ᵥ z'.1 →
        (D.fm u).fv i v' _ ((P i hi).pr v' _ z') = (D.fm u).fv i v' c ((P i hi).pr v' c z)) :
    UpCl A P i v c y (gx i hi γ) := by

  let crdL := ((crdN D i hi : (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))
  have inj : Function.Injective crdL := (crdN D i hi).injective
  have eCls : ∀ c' : (D.mem u).C.cls i, (D.clsLat u i c').map crdL = clsCrd D u i hi c' := fun _ => rfl
  have eLd : ∀ c' : (D.mem u).C.cls i, (Formalism.L2.Herm.Ld D u i c').map crdL = Formalism.L2.Forms.Ld D u i hi c' := fun c' =>
    dual_co D.sp.cm (D.sp.X i) (rankN D i hi) (D.clsLat u i c')
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q hq hP hc
    haveI := hq.isPrime
    let q' : HeightOneSpectrum (𝓞 D.host.E) :=
      ⟨q, hq.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hq (RingOfIntegers.not_isField D.host.E)⟩
    apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eCls]
    exact hoff q' hP hc
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eCls, eLd]
    exact h3
  · apply Submodule.map_injective_of_injective inj
    rw [localization_map₂ hi, localization_map₂ hi, lc_gmap, eLd, Submodule.map_sup, eLd, Submodule.map_span, Set.image_singleton]
    convert h4 using 4
    simp [crdL, toLd]
  · intro z hz
    rw [prH_eq A P hi v _ z, prH_eq A P hi v c ⟨_, hz⟩]
    have key : crdN D i hi (((D.mem u).A.T : D.host.E) • (gx i hi γ).1 (z : (D.sp.X i).V)) =
        (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) := by
      rw [map_smul, crdN_gx]
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      rfl
    have hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ (toLd i hi _ z).1) ∈ Formalism.L2.Forms.Ld D u i hi c :=
      key ▸ (mem_Ld i hi c _).1 hz
    have e : toLd i hi c ⟨_, hz⟩ = ⟨_, hx⟩ := Subtype.ext key
    rw [e]
    exact h5 _ hx
  · intro v' hv' z hz
    rw [prH_eq A P hi v' _ z, prH_eq A P hi v' c ⟨_, hz⟩]
    exact h6 v' hv' (toLd i hi c ⟨_, hz⟩) (toLd i hi _ z) (crdN_gx i hi γ _)

end G

section S

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

set_option maxHeartbeats 4000000 in

theorem crd_up (T : FormsTiedSym D u Ch chOf) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT)
    (c : (D.mem u).C.cls i) (y : Formalism.L2.Herm.Ld D u i c)
    (hf : (D.fm u).fv i v c (prH T.atT T.lv i v c y) = 1)
    (hC : ∀ (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (c' : (D.mem u).C.cls i) (z : Formalism.L2.Forms.Ld D u i (le_of_succ_m h2) c')
      (z' : LdG D i (le_of_succ_m h2) (clsCrd D u i (le_of_succ_m h2) c')), z'.1 = z.1 →
        (T.lvC i h1 h2).pr v c' z' = (T.lv i (le_of_succ_m h2)).pr v c' z) :
    ∃ γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      AdC T i hi c ((D.fm u).up i v c (prH T.atT T.lv i v c y)) γ.1 (T.atT.eV v).1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y)))) =
        Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Formalism.L2.Forms.Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • (toLd i hi c y).1}) ∧
      ∀ (x : ↥(Formalism.L2.Forms.Ld D u i hi ((D.fm u).up i v c (prH T.atT T.lv i v c y))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Formalism.L2.Forms.Ld D u i hi c),
        (D.fm u).fv i v _ ((T.lv i hi).pr v _ x) = (D.fm u).fv i v c ((T.lv i hi).pr v c ⟨_, hx⟩) := by
  have e1 : (T.lv i hi).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y := (prH_eq T.atT T.lv hi v c y).symm
  rcases (show (i = 0 ∨ i = D.R.m) ∨ (1 ≤ i ∧ i + 1 ≤ D.R.m) by omega) with h | ⟨h1, h2⟩
  · have hz : (D.fm u).fv i v c ((T.lv i hi).pr v c (toLd i hi c y)) = 1 := by rw [e1]; exact hf
    have H0 := T.upN i hi h v c (toLd i hi c y) hz
    generalize (T.lv i hi).pr v c (toLd i hi c y) = t at H0 e1
    subst e1
    obtain ⟨γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h' => ⟨κ.1, κ.2, η.1, η.2, hη, hy⟩, fun h1 h2 => absurd h (by omega)⟩, h3, h4, h5⟩
  · have hl := le_of_succ_m h2
    have e0 : (T.lvC i h1 h2).pr v c (toLd i hi c y) = prH T.atT T.lv i v c y :=
      (hC h1 h2 c (toLd i hi c y) (toLd i hi c y) rfl).trans e1
    have hz : (D.fm u).fv i v c ((T.lvC i h1 h2).pr v c (toLd i hi c y)) = 1 := by rw [e0]; exact hf
    have H0 := T.upC i h1 h2 v (chOf i c) ⟨c, rfl⟩ (toLd i hi c y) hz
    generalize (T.lvC i h1 h2).pr v c (toLd i hi c y) = t at H0 e0
    subst e0
    obtain ⟨hβ, γ, η, κ, hη, hy, h3, h4, h5, -⟩ := H0
    refine ⟨γ, ⟨fun h => absurd h (by omega), fun h1' h2' => ⟨hβ, κ.1, κ.2, η.1, η.2, hη, hy⟩⟩, h3, h4, fun x hx => ?_⟩
    have := h5 x hx
    rwa [hC h1 h2 _ x x rfl, hC h1 h2 c ⟨_, hx⟩ ⟨_, hx⟩ rfl] at this

end S

end GlobalTheory.Mem.Col2.HAt.UpMove

open GlobalTheory.Mem.Col2.HAt.UpMove in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Col2.HAt.UpMove.up_move : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i v (c : ((I.rec7 l Z).mem u).C.cls i) (y : Formalism.L2.Herm.Ld (I.rec7 l Z) u i c), ∃ γ, i ≤ (I.rec7 l Z).R.m → ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1 → UpCl (F u).atT (F u).lv i v c y γ ∧ AdOf H u i c (((I.rec7 l Z).fm u).up i v c (prH (F u).atT (F u).lv i v c y)) γ v := by
  intro B X I hOk hPins l Z H F hStd hCar u i v c y
  by_cases hi : i ≤ (I.rec7 l Z).R.m
  swap
  · exact ⟨1, fun h => absurd h hi⟩
  by_cases hf : ((I.rec7 l Z).fm u).fv i v c (prH (F u).atT (F u).lv i v c y) = 1
  swap
  · exact ⟨1, fun _ h => absurd h hf⟩
  obtain ⟨γ, hAd, h3, h4, h5⟩ := crd_up (F u) i hi v c y hf
    (fun h1 h2 c' z z' e => (GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection I hOk hPins l Z H F hStd hCar u i h1 h2 v c').1 z z' e)
  refine ⟨gx i hi γ, fun _ _ => ⟨upCl_of_crd (F u).atT (F u).lv i hi v c y γ ?_ h3 h4 h5 ?_,
    GlobalTheory.T.adelic_relation_classes_coordinates I hOk hPins l Z H F hStd hCar u i hi v c _ γ hAd⟩⟩
  · intro q hP hc
    refine GlobalTheory.T.adelic_conjugate_character_standard_forms I hOk hPins l Z H F hStd hCar u i hi v c _ γ.1 hAd q fun hq => ?_
    rcases GlobalTheory.T.host_primes_over_level_place I hOk hPins l Z H F hStd hCar u v q hq with h | h
    · exact hP h
    · exact hc h
  · intro v' hv' z z' e
    exact GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place I hOk hPins l Z H F hStd hCar u i hi v v' c _ γ.1 hAd hv' z z' e
