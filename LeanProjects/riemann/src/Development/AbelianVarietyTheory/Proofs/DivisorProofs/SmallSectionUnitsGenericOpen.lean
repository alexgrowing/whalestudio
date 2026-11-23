import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegularStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue.PowGlue

open GlobalTheory.TrueGeo.SmallSec

theorem eq_gen_of_specializes {X : Scheme.{0}} [IsIntegral X] {x : X} (h : x ⤳ genericPoint X) :
    x = genericPoint X :=
  (h.antisymm (genericPoint_specializes x)).eq

theorem unitAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) :
    UnitAt x (f ^ n) := by
  induction n with
  | zero => simpa using unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem valAt_one' {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) :
    valAt y (1 : Z.functionField) = 1 := by
  have e := valAt_algebraMap (y := y) 1
  rwa [map_one, map_one] at e

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem gen_of_lies (V V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X)
    (g : V'.G ⟶ V.G) (hgj : g ≫ V.j = V'.j ≫ π) : g (genericPoint V'.G) = genericPoint V.G := by
  have := RootLine.isPreimmersion_j V
  apply V.j.isEmbedding.injective
  have e1 : V.j (g (genericPoint V'.G)) = π (V'.j (genericPoint V'.G)) := by
    rw [← Scheme.Hom.comp_apply, hgj, Scheme.Hom.comp_apply]
  rw [e1, eq_gen_of_specializes (RootLine.j_gen_specializes V'), eq_gen_of_specializes hπ,
    eq_gen_of_specializes (RootLine.j_gen_specializes V)]

end GlobalTheory.FrameGlue.PowGlue

open GlobalTheory.FrameGlue.PowGlue GlobalTheory.TrueGeo.SmallSec in

theorem GlobalTheory.FrameGlue.powOfFrames_of_normsAt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (p : ℕ), p.Prime →
  ∀ (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens)
    (c : ι → V.G.functionFieldˣ) (c' : ι → V.X.functionFieldˣ), genericPoint Y.X ∈ W →
    (∀ a, GlobalTheory.TrueGeo.SmallSec.fnMap V.j hη (c' a) = c a) →
    (∀ a (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt A.D (V.π z)) * c a)) →
    (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * (c a : V.G.functionField))))) →
    ∀ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), Lies V' V π →
    ∀ (L : LB V'.X) (m : ℕ), NormsAt V' L p ⊤ (fun x => genAt A.D x ^ m) (fun v e y => m * A.lg v e y) →
      GlobalTheory.FrameGlue.PowOfFrames p (fun a => π ⁻¹ᵁ U a) (fun a => Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c' a)) m L := by
  intro F _ _ Y C A p hp V hη W ι U c c' hW hc hunit hnorm V' π hπ hL L m hN
  obtain ⟨g, hgj, hgπ⟩ := hL
  have := RootLine.isPreimmersion_j V'
  have hη' := RootLine.j_gen_specializes V'
  have hg : g (genericPoint V'.G) ⤳ genericPoint V.G := specializes_of_eq (gen_of_lies V V' π hπ g hgj)
  obtain ⟨hηV, eV⟩ := V.φ_eq_fnMap
  obtain ⟨hηV', eV'⟩ := V'.φ_eq_fnMap
  have hφ : ∀ t, V'.φ t = fnMap g hg (V.φ t) := by
    intro t
    rw [eV', eV, ← ProjSpace.fnMap_comp g V.π hg hηV (ProjSpace.comp_genericPoint_specializes _ _ hg hηV) t]
    exact ProjSpace.fnMap_congr hgπ.symm _ _ _
  have hcc : ∀ a, fnMap V'.j hη' (fnMap π hπ (c' a)) = fnMap g hg (c a) := by
    intro a
    rw [← hc a, ← ProjSpace.fnMap_comp V'.j π hη' hπ (ProjSpace.comp_genericPoint_specializes _ _ hη' hπ),
      ← ProjSpace.fnMap_comp g V.j hg hη (ProjSpace.comp_genericPoint_specializes _ _ hg hη)]
    exact ProjSpace.fnMap_congr hgj.symm _ _ _
  obtain ⟨r, hr, hu, hn⟩ := hN
  choose s hs using fun k : L.ι => fnMap_surjective V'.j hη' (r fun _ => k : V'.G.functionField)
  have hs0 : ∀ k, s k ≠ 0 := fun k e => (r fun _ => k).ne_zero (by rw [← hs k, e, map_zero])
  refine ⟨fun k => Units.mk0 (s k) (hs0 k), ?_, ?_⟩
  · intro i k h
    apply (fnMap V'.j hη').injective
    have h' : genericPoint V'.G ∈ (L.pull V'.j).U (fun _ => i) ⊓ (L.pull V'.j).U (fun _ => k) :=
      ⟨Set.mem_iInter.2 fun _ => hη'.mem_open (L.U i).isOpen h.1,
        Set.mem_iInter.2 fun _ => hη'.mem_open (L.U k).isOpen h.2⟩
    have e := RootLine.fnOf_pull_g L V'.j hη' (fun _ => i) (fun _ => k) h' h
    have e2 := hr (fun _ => i) (fun _ => k) h'
    show fnMap V'.j hη' (s i) = fnMap V'.j hη' (fnOf _ h (L.g i k : Γ(V'.X, L.U i ⊓ L.U k)) * s k)
    rw [map_mul, hs, hs, e2]
    congr 1
  · intro a k x hxa hxk hpx
    have hf : (((Units.mk0 (s k) (hs0 k)) / (Units.map (fnMap π hπ).toMonoidHom (c' a)) ^ m :
        V'.X.functionFieldˣ) : V'.X.functionField) = s k / fnMap π hπ (c' a) ^ m := by
      simp
    rw [hf]
    set f : V'.X.functionField := s k / fnMap π hπ (c' a) ^ m with hfdef
    set q := fnMap V'.j hη' f with hqdef
    have hq : q = r (fun _ => k) / fnMap g hg (c a) ^ m := by
      rw [hqdef, hfdef, map_div₀, map_pow, hs, hcc]
    set O : V'.X.Opens := π ⁻¹ᵁ U a ⊓ L.U k with hO

    have key : ∀ z : V'.G, V'.j z ∈ O →
        UnitAt z (V'.φ (genAt A.D (V'.π z) ^ m) * r (fun _ => k)) ∧
        UnitAt z (V'.φ (genAt A.D (V'.π z)) * fnMap g hg (c a)) ∧
        q * (V'.φ (genAt A.D (V'.π z)) * fnMap g hg (c a)) ^ m = V'.φ (genAt A.D (V'.π z) ^ m) * r (fun _ => k) ∧
        UnitAt z q := by
      intro z hz
      have h1 : UnitAt z (V'.φ (genAt A.D (V'.π z) ^ m) * r (fun _ => k)) :=
        hu (fun _ => k) z (Set.mem_iInter.2 fun _ => hz.2)
      have hgz : V.j (g z) ∈ U a := by
        have : V.j (g z) = π (V'.j z) := by rw [← Scheme.Hom.comp_apply, hgj, Scheme.Hom.comp_apply]
        rw [this]; exact hz.1
      have hπz : V.π (g z) = V'.π z := by rw [← Scheme.Hom.comp_apply, hgπ]
      have h2 : UnitAt z (V'.φ (genAt A.D (V'.π z)) * fnMap g hg (c a)) := by
        have := RootLine.unitAt_fnMap g hg (hunit a (g z) hgz)
        rwa [map_mul, ← hφ, hπz] at this
      have h0 : V'.φ (genAt A.D (V'.π z)) ≠ 0 := fun e => h2.ne_zero (by rw [e, zero_mul])
      have hc0 : fnMap g hg (c a) ≠ 0 := fun e => h2.ne_zero (by rw [e, mul_zero])
      have h3 : q * (V'.φ (genAt A.D (V'.π z)) * fnMap g hg (c a)) ^ m =
          V'.φ (genAt A.D (V'.π z) ^ m) * r (fun _ => k) := by
        rw [hq, map_pow, mul_pow]
        field_simp
      refine ⟨h1, h2, h3, ?_⟩
      have h4 : q = V'.φ (genAt A.D (V'.π z) ^ m) * r (fun _ => k) *
          ((V'.φ (genAt A.D (V'.π z)) * fnMap g hg (c a)) ^ m)⁻¹ := by
        rw [← h3, mul_inv_cancel_right₀ (pow_ne_zero _ h2.ne_zero)]
      rw [h4]
      exact h1.mul (unitAt_pow h2 m).inv

    have hval : ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
        ∀ (z : Sp (AlgebraicClosure F) ⟶ V'.G) (yt : Sp e.O ⟶ V'.X), z ≫ V'.π = y.1 →
        spMap e.O.subtype ≫ yt = z ≫ V'.j → ⊤ ≤ yt ⁻¹ᵁ O →
        V'.j (below z) ∈ O ∧ e.w (valAt z q) = 1 := by
      intro v hv e y hy z yt e1 e2 hyt
      have hz : V'.j (below z) ∈ O := by
        have h1 : (z ≫ V'.j) (IsLocalRing.closedPoint _) ∈ O := by
          rw [← e2]
          exact hyt (Set.mem_univ _)
        exact h1
      refine ⟨hz, ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := key (below z) hz
      have hb : V'.π (below z) = below y.1 := by rw [← e1]; rfl
      rw [hb] at h1 h2 h3
      have e1' : (z ≫ g) ≫ V.π = y.1 := by rw [Category.assoc, hgπ, e1]
      have e2' : spMap e.O.subtype ≫ (yt ≫ π) = (z ≫ g) ≫ V.j := by
        rw [← Category.assoc, e2, Category.assoc, Category.assoc, hgj]
      have hUa : ⊤ ≤ (yt ≫ π) ⁻¹ᵁ U a := fun x hx => (hyt hx).1
      have HV := hnorm v hv e y hy (z ≫ g) (yt ≫ π) e1' e2' a hUa
      have hk : ⊤ ≤ yt ⁻¹ᵁ L.U k := fun x hx => (hyt hx).2
      have HV' := hn v hv e y trivial z yt (fun _ => k) e1 e2 hk
      have hgz : V.j (g (below z)) ∈ U a := by
        have : V.j (g (below z)) = π (V'.j (below z)) := by
          rw [← Scheme.Hom.comp_apply, hgj, Scheme.Hom.comp_apply]
        rw [this]; exact hz.1
      have hπz : V.π (g (below z)) = below y.1 := by rw [← Scheme.Hom.comp_apply, hgπ, hb]
      have hU := hunit a (g (below z)) hgz
      rw [hπz] at hU
      rw [← valAt_fnMap g hg z hU.regAt, map_mul, ← hφ] at HV
      have hv1 : valAt z (V'.φ (genAt A.D (below y.1) ^ m) * r (fun _ => k)) =
          valAt z q * valAt z (V'.φ (genAt A.D (below y.1)) * fnMap g hg (c a)) ^ m := by
        rw [← h3, valAt_mul h4.regAt (regAt_pow h2.regAt m), valAt_pow h2.regAt]
      have w1 : 0 < e.w (valAt z (V'.φ (genAt A.D (below y.1) ^ m) * r (fun _ => k))) :=
        e.w.pos (valAt_ne_zero h1)
      have w2 : 0 < e.w (valAt z (V'.φ (genAt A.D (below y.1)) * fnMap g hg (c a))) :=
        e.w.pos (valAt_ne_zero h2)
      have hlog : Real.log (e.w (valAt z (V'.φ (genAt A.D (below y.1) ^ m) * r (fun _ => k)))) =
          Real.log (e.w (valAt z (V'.φ (genAt A.D (below y.1)) * fnMap g hg (c a))) ^ m) := by
        rw [Real.log_pow, ← HV', ← HV]
      have heq := Real.log_injOn_pos w1 (pow_pos w2 m) hlog
      rw [hv1, map_mul, map_pow] at heq
      exact (mul_eq_right₀ (pow_ne_zero m w2.ne')).1 heq
    have hq1 : ∀ z : V'.G, V'.j z ∈ O → UnitAt z q := fun z hz => (key z hz).2.2.2
    have hreg : RegAt x f := by
      refine GlobalTheory.T.good_reduction_extends_regular F Y V' p hp W hW O f (fun z hz => (regAt_fnMap_iff V'.j hη').1 (hq1 z hz).regAt) ?_ x
        ⟨hxa, hxk⟩ hpx
      intro v hv e y hy z yt e1 e2 hyt
      obtain ⟨hz, h⟩ := hval v hv e y hy z yt e1 e2 hyt
      rw [← valAt_fnMap V'.j hη' z ((regAt_fnMap_iff V'.j hη').1 (hq1 _ hz).regAt), ← hqdef, h]
    have hreg' : RegAt x f⁻¹ := by
      have hq1' : ∀ z : V'.G, V'.j z ∈ O → RegAt (V'.j z) f⁻¹ := fun z hz =>
        (regAt_fnMap_iff V'.j hη').1 (by rw [map_inv₀, ← hqdef]; exact (hq1 z hz).inv.regAt)
      refine GlobalTheory.T.good_reduction_extends_regular F Y V' p hp W hW O f⁻¹ hq1' ?_ x ⟨hxa, hxk⟩ hpx
      intro v hv e y hy z yt e1 e2 hyt
      obtain ⟨hz, h⟩ := hval v hv e y hy z yt e1 e2 hyt
      rw [← valAt_fnMap V'.j hη' z (hq1' _ hz), map_inv₀, ← hqdef]
      have hm : valAt z q * valAt z q⁻¹ = 1 := by
        rw [← valAt_mul (hq1 _ hz).regAt (hq1 _ hz).inv.regAt, mul_inv_cancel₀ (hq1 _ hz).ne_zero, valAt_one']
      have := congrArg e.w hm
      rw [map_mul, h, one_mul, map_one] at this
      rw [this]
    have hf0 : f ≠ 0 := div_ne_zero (hs0 k) (pow_ne_zero _ ((map_ne_zero _).2 (Units.ne_zero _)))
    exact (unitAt_iff hf0).2 ⟨hreg, hreg'⟩
