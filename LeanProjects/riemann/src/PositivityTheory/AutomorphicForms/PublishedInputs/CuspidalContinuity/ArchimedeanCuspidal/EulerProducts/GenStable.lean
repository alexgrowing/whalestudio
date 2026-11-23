import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.GP

def wR : InfinitePlace ℚ := Rat.infinitePlace

theorem wR_isReal : wR.IsReal := Rat.isReal_infinitePlace

def eR : wR.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal wR_isReal

def gR (g : G3) : GL (Fin 3) ℝ := Units.map eR.toRingHom.mapMatrix.toMonoidHom (Reduction.infAt wR g)

abbrev psiF (v : Pl) : AddChar (Qv v) Circle := localAdelicChar ℚ v

abbrev sph (D : Dat) (v : Pl) : GL (Fin 3) (Qv v) → ℂ := sphW (psiF v) (D.ν v)

def pw (Wi : GL (Fin 3) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ) (g : G3) : ℂ :=
  Wi (gR g) * ∏ᶠ v, Wf v (Reduction.finAt v g)

structure Loc (D : Dat) where
  VF : ∀ v : Pl, Submodule ℂ (GL (Fin 3) (Qv v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VR : Submodule ℂ (GL (Fin 3) ℝ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VR
  hR : WhR D.k VR E

variable {D : Dat}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℝ → ℂ) (Wf : ∀ v : Pl, GL (Fin 3) (Qv v) → ℂ) : Prop where
  inf : Wi ∈ L.VR
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset Pl, ∀ v ∉ S, Wf v = sph D v

def Gen (L : Loc D) : Set (G3 → ℂ) := {W | ∃ Wi Wf, IsFac L Wi Wf ∧ W = pw Wi Wf}

def VA (L : Loc D) : Submodule ℂ (G3 → ℂ) := Submodule.span ℂ (Gen L)

def VorS (W : G3 → ℂ) : Prop :=
  Summable (fun a : ℚˣ => W (dia (dg a 1 1))) ∧
    (∀ b : ℚˣ, Integrable (fun u => W (dia (dg 1 1 b) * cyc u)) (adeleMeasure ℚ)) ∧
    Summable (fun b : ℚˣ => ∫ u, W (dia (dg 1 1 b) * cyc u) ∂adeleMeasure ℚ)

def StdChar : Prop := ∀ v : Pl, IsStd (psiF v)

def WhGen : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), WhA (VA L)

def VorGen : Prop := LocU → Mellin → ∀ (D : Dat) (L : Loc D), An D → ∀ W ∈ Gen L, Vor W ∧ VorS W

def VorSpan : Prop := ∀ s : Set (G3 → ℂ), (∀ W ∈ s, Vor W ∧ VorS W) → ∀ W ∈ Submodule.span ℂ s, Vor W

def CapGen : Prop := ∀ (D : Dat) (L : Loc D) (hV : WhA (VA L)), ∀ W (hW : W ∈ VA L) (u : ℂ),
  Formalism.REAL.qdet EA (u + 1) ⟨W, hV.arch W hW⟩ =
    ((u + (D.k - 1)) * u * (u - (D.k - 1))) • (⟨W, hV.arch W hW⟩ : archSmooth ℚ 3)

def TrGen : Prop := ∀ (D : Dat) (L : Loc D) (hV : WhA (VA L)), ∀ W (hW : W ∈ VA L),
  (∑ i, EA i i) ⟨W, hV.arch W hW⟩ = 0

def ExGen : Prop := ∀ (D : Dat) (L : Loc D), ∃ W ∈ VA L, W ≠ 0 ∧ IsKFinite W ∧ ∃ S : Finset Pl, ∀ v ∉ S, SphAt D v W

abbrev md (x : IdeleGroup ℚ) : ℝ := (IdeleGroup.ideleModule ℚ x : ℝ)

abbrev ιQ (a : ℚˣ) : IdeleGroup ℚ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a

def f1 (W : G3 → ℂ) (x : IdeleGroup ℚ) : ℂ := W (dg x 1 1) * ((md x : ℂ) ^ (-(1 / 2 : ℂ)))

def f2 (W : G3 → ℂ) (x : IdeleGroup ℚ) : ℂ :=
  (∫ u, W (mm x u) ∂adeleMeasure ℚ) * ((md x : ℂ) ^ ((1 / 2 : ℂ)))

def zv {v : Pl} (Wv : GL (Fin 3) (Qv v) → ℂ) (c : (Qv v)ˣ →* ℂˣ) (s : ℂ) : ℂ := ∫ a, zF Wv c s a ∂multHaar (Qv v)

def zv' {v : Pl} (Wv : GL (Fin 3) (Qv v) → ℂ) (c : (Qv v)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ p, zF' Wv c s p ∂((multHaar (Qv v)).prod (selfDualMeasure (psiF v)))

def zr (Wi : GL (Fin 3) ℝ → ℂ) (δ : Bool) (s : ℂ) : ℂ := ∫ a, Wi (dg a 1 1) * chR δ (s - 1) a ∂mulR

def zr' (Wi : GL (Fin 3) ℝ → ℂ) (δ : Bool) (s : ℂ) : ℂ :=
  ∫ p : ℝˣ × ℝ, Wi (mm p.1 p.2) * chR δ s p.1 ∂(mulR.prod volume)

def gz (W : G3 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ x, W (dg x 1 1) * (c.toIdele x : ℂ) * ((md x : ℂ) ^ (s - 1)) ∂ideleMeasure ℚ

def gz' (W : G3 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  ∫ x, (∫ u, W (mm x u) ∂adeleMeasure ℚ) * (c.toIdele x : ℂ) * ((md x : ℂ) ^ s) ∂ideleMeasure ℚ

def CharFac : Prop := ∀ x : 𝔸[ℚ], (adelicChar ℚ x : ℂ) = psiR (eR (x.1 wR)) * ∏ᶠ v : Pl, (psiF v (x.2 v) : ℂ)

def Gauge (W : G3 → ℂ) : Prop :=
  ∃ Ω : Set (FiniteAdeleRing (𝓞 ℚ) ℚ), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[ℚ])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup G3), ∀ w : InfinitePlace ℚ,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule ℚ a : ℝ) * IdeleGroup.ideleModule ℚ b) ^ T /
        ((1 + ‖(a : 𝔸[ℚ]).1 w‖) * (1 + ‖(b : 𝔸[ℚ]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[ℚ]).2 ∈ Ω ∧ (b : 𝔸[ℚ]).2 ∈ Ω)

def WhSpan : Prop := ∀ s : Set (G3 → ℂ),
  (∀ W ∈ s, ∀ h, (fun g => W (g * h)) ∈ Submodule.span ℂ s) →
  (∀ W ∈ s, ∀ x y z g, W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g) →
  (∀ W ∈ s, ∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g) →
  (∀ W ∈ s, IsArchSmooth W) →
  (∀ W ∈ s, ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∀ g, ∀ u ∈ U, W (g * finEmb ℚ 3 u) = W g) →
  (∀ W (hW : IsArchSmooth W), W ∈ s → ∀ i j, ((EA i j ⟨W, hW⟩ : archSmooth ℚ 3) : G3 → ℂ) ∈ Submodule.span ℂ s) →
  (∀ W ∈ s, Gauge W) → WhA (Submodule.span ℂ s)

def GenStable : Prop := StdChar → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, ∀ h, (fun g => W (g * h)) ∈ Gen L

def GenPsi : Prop := StdChar → CharFac → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, ∀ x y z g,
  W (uni x y z * g) = (adelicChar ℚ (x + z) : ℂ) * W g

def GenCen : Prop := ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, ∀ (a : (𝔸[ℚ])ˣ) g, W (dg a a a * g) = W g

def GenArch : Prop := StdChar → ∀ (D : Dat) (L : Loc D) Wi Wf, IsFac L Wi Wf → IsArchSmooth (pw Wi Wf)

def GenLevel : Prop := StdChar → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL ℚ 3), ∀ g, ∀ u ∈ U, W (g * finEmb ℚ 3 u) = W g

def GenLieF : Prop := ∀ (D : Dat) (L : Loc D) Wi Wf (h : IsFac L Wi Wf) (hA : IsArchSmooth (pw Wi Wf)) i j,
  ((EA i j ⟨pw Wi Wf, hA⟩ : archSmooth ℚ 3) : G3 → ℂ) = pw (L.E i j ⟨Wi, h.inf⟩ : GL (Fin 3) ℝ → ℂ) Wf

def GenGauge : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, Gauge W

def TrR : Prop := ∀ k V E, WhR k V E → ∀ W : V, (∑ i, E i i) W = 0

def QdetNat : Prop := ∀ (V₁ V₂ : Type) [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ)
  (E : Fin n → Fin n → Module.End ℂ V₁) (E' : Fin n → Fin n → Module.End ℂ V₂) (ι : V₁ →ₗ[ℂ] V₂),
  (∀ i j x, E' i j (ι x) = ι (E i j x)) → ∀ u x, Formalism.REAL.qdet E' u (ι x) = ι (Formalism.REAL.qdet E u x)

def IdQ : Prop := ∀ (W : G3 → ℂ) (a : ℚˣ), f1 W (ιQ a) = W (dia (dg a 1 1)) ∧
  f2 W (ιQ a) = ∫ u, W (dia (dg 1 1 a) * cyc u) ∂adeleMeasure ℚ

def AdmEx : Prop := ∀ (D : Dat) (c : HeckeCharacter ℚ), IsOfFinOrder c → ∀ S₀ : Finset Pl,
  ∃ δ S, S₀ ⊆ S ∧ admitted D c δ S

def EulA : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset Pl,
  (∀ v ∉ S, Wf v = sph D v) → ∀ c δ, admitted D c δ S → ∀ s : ℂ, 3 < s.re →
    gz (pw Wi Wf) c s = zr Wi δ s * (∏ v ∈ S, zv (Wf v) (localChar c v) s) * eul D c S s

def EulB : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset Pl,
  (∀ v ∉ S, Wf v = sph D v) → ∀ c δ, admitted D c δ S → ∀ s : ℂ, s.re < -2 →
    gz' (pw Wi Wf) c s = zr' Wi δ s * (∏ v ∈ S, zv' (Wf v) (localChar c v) s) * eul D c⁻¹ S (1 - s)

def IntA : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  Integrable (fun x => ‖f1 W x‖ * md x ^ (3 : ℝ)) (ideleMeasure ℚ)

def IntB : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  Integrable (fun x => ‖f2 W x‖ * md x ^ (-3 : ℝ)) (ideleMeasure ℚ)

def BndC : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L, Continuous (f1 W) ∧ Continuous (f2 W)

def BndI : Prop := StdChar → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  ∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ u ∈ U, ∀ x,
    f1 W (x * IdeleGroup.ofFinite u) = f1 W x ∧ f2 W (x * IdeleGroup.ofFinite u) = f2 W x

def BndS : Prop := StdChar → LocU → ∀ (D : Dat) (L : Loc D), ∀ W ∈ Gen L,
  (∀ x : IdeleGroup ℚ, Integrable (fun u => W (mm x u)) (adeleMeasure ℚ)) ∧
  ∀ K : Set (IdeleGroup ℚ), IsCompact K → ∃ b : ℚˣ → ℝ, Summable b ∧ ∀ a : ℚˣ, ∀ x ∈ K,
    ‖f1 W (ιQ a * x)‖ ≤ b a ∧ ‖f2 W (ιQ a * x)‖ ≤ b a

def Glue : Prop := StdChar → ∀ (D : Dat) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset Pl,
  (∀ v ∉ S, Wf v = sph D v) → ∀ c δ, admitted D c δ S → An D → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ Ord G (-5 / 2) ∧
    (∀ s : ℂ, 1 < s.re → G s = zr Wi δ s * (∏ v ∈ S, zv (Wf v) (localChar c v) s) * eul D c S s) ∧
    ∀ s : ℂ, s.re < 0 → G s = zr' Wi δ s * (∏ v ∈ S, zv' (Wf v) (localChar c v) s) * eul D c⁻¹ S (1 - s)

def VorAss : Prop := StdChar → IdQ → AdmEx → EulA → EulB → IntA → IntB → BndC → BndI → BndS → Glue → VorGen

end Ad3.GP
