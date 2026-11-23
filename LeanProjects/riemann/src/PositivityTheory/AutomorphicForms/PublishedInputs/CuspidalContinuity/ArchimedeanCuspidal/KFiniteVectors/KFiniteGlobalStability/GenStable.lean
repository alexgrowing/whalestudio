import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.ComplexMatrix3

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.GPK

def ShiftStd : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 → ∃ a : Fˣ, IsStd (ψ.mulShift (a : F))

def WhShift : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle), Continuous ψ → ψ ≠ 1 → ∀ (a : Fˣ) (ν : Fˣ →* ℂˣ) (V : Submodule ℂ (GL (Fin 3) F → ℂ)),
      IsUnit1 ν → WhF (ψ.mulShift (a : F)) ν V → ∃ V', WhF ψ ν V'

variable {K : Type} [Field K] [NumberField K]

variable (K) in

def wC : InfinitePlace K := Classical.arbitrary _

def gCx (g : G3K K) : GL (Fin 3) ℂ :=
  Units.map (InfinitePlace.Completion.extensionEmbedding (wC K)).mapMatrix.toMonoidHom (Reduction.infAt (wC K) g)

abbrev psiF (v : PlK K) : AddChar (Kv K v) Circle := localAdelicChar K v

abbrev sph (D : DatK K) (v : PlK K) : GL (Fin 3) (Kv K v) → ℂ := sphW (psiF v) (D.ν v)

def pw (Wi : GL (Fin 3) ℂ → ℂ) (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) (g : G3K K) : ℂ :=
  Wi (gCx g) * ∏ᶠ v, Wf v (Reduction.finAt v g)

structure Loc (D : DatK K) where
  VF : ∀ v : PlK K, Submodule ℂ (GL (Fin 3) (Kv K v) → ℂ)
  hF : ∀ v, WhF (psiF v) (D.ν v) (VF v)
  sp : ∀ v, v ∉ D.bad → sph D v ∈ VF v
  VC : Submodule ℂ (GL (Fin 3) ℂ → ℂ)
  E : Fin 3 → Fin 3 → Module.End ℂ VC
  E' : Fin 3 → Fin 3 → Module.End ℂ VC
  hC : WhC D.k VC E E'

variable {D : DatK K}

structure IsFac (L : Loc D) (Wi : GL (Fin 3) ℂ → ℂ) (Wf : ∀ v : PlK K, GL (Fin 3) (Kv K v) → ℂ) : Prop where
  inf : Wi ∈ L.VC
  fin : ∀ v, Wf v ∈ L.VF v
  ae : ∃ S : Finset (PlK K), ∀ v ∉ S, Wf v = sph D v

def Gen (L : Loc D) : Set (G3K K → ℂ) := {W | ∃ Wi Wf, IsFac L Wi Wf ∧ W = pw Wi Wf}

def VA (L : Loc D) : Submodule ℂ (G3K K → ℂ) := Submodule.span ℂ (Gen L)

variable (K) in

def VorS (W : G3K K → ℂ) : Prop :=
  Summable (fun a : Kˣ => W (diaK (K := K) (dg a 1 1))) ∧
    (∀ b : Kˣ, Integrable (fun u => W (diaK (K := K) (dg 1 1 b) * cyc u)) (adeleMeasure K)) ∧
    Summable (fun b : Kˣ => ∫ u, W (diaK (K := K) (dg 1 1 b) * cyc u) ∂adeleMeasure K)

def LocNe : Prop := ∀ (K : Type) [Field K] [NumberField K] (v : PlK K), Continuous (psiF v) ∧ psiF v ≠ 1

def WhGen : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), WhAK (VA L)

def VorGen : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU → MellinK K →
  ∀ (D : DatK K) (L : Loc D), AnK D → ∀ W ∈ Gen L, VorK W ∧ VorS K W

def VorSpan : Prop := ∀ (K : Type) [Field K] [NumberField K] (s : Set (G3K K → ℂ)),
  (∀ W ∈ s, VorK W ∧ VorS K W) → ∀ W ∈ Submodule.span ℂ s, VorK W

def CapGen : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D) (hV : WhAK (VA L)), ∀ W (hW : W ∈ VA L) (u : ℂ),
    Formalism.REAL.qdet EH (u + 1) ⟨W, hV.arch W hW⟩ = ((u + (D.k - 1)) * u * (u - (D.k - 1))) • (⟨W, hV.arch W hW⟩ : archSmooth K 3) ∧
    Formalism.REAL.qdet EA' (u + 1) ⟨W, hV.arch W hW⟩ = ((u + (D.k - 1)) * u * (u - (D.k - 1))) • (⟨W, hV.arch W hW⟩ : archSmooth K 3)

def ExGen : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∃ W ∈ VA L, W ≠ 0 ∧ IsKFinite W ∧ ∃ S : Finset (PlK K), ∀ v ∉ S, SphAtK D v W

abbrev md (x : IdeleGroup K) : ℝ := (IdeleGroup.ideleModule K x : ℝ)

abbrev ιK (a : Kˣ) : IdeleGroup K := Units.map (algebraMap K 𝔸[K]).toMonoidHom a

def f1 (W : G3K K → ℂ) (x : IdeleGroup K) : ℂ := W (dg x 1 1) * ((md x : ℂ) ^ (-(1 / 2 : ℂ)))

def f2 (W : G3K K → ℂ) (x : IdeleGroup K) : ℂ :=
  (∫ u, W (mm x u) ∂adeleMeasure K) * ((md x : ℂ) ^ ((1 / 2 : ℂ)))

def zv {v : PlK K} (Wv : GL (Fin 3) (Kv K v) → ℂ) (c : (Kv K v)ˣ →* ℂˣ) (s : ℂ) : ℂ := ∫ a, zF Wv c s a ∂multHaar (Kv K v)

def zv' {v : PlK K} (Wv : GL (Fin 3) (Kv K v) → ℂ) (c : (Kv K v)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ p, zF' Wv c s p ∂((multHaar (Kv K v)).prod (selfDualMeasure (psiF v)))

def zc (Wi : GL (Fin 3) ℂ → ℂ) (n : ℤ) (s : ℂ) : ℂ := ∫ a, Wi (dg a 1 1) * chC n (s - 1) a ∂mulC

def zc' (Wi : GL (Fin 3) ℂ → ℂ) (n : ℤ) (s : ℂ) : ℂ := ∫ p : ℂˣ × ℂ, Wi (mm p.1 p.2) * chC n s p.1 ∂(mulC.prod volC)

def gz (W : G3K K → ℂ) (c : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∫ x, W (dg x 1 1) * (c.toIdele x : ℂ) * ((md x : ℂ) ^ (s - 1)) ∂ideleMeasure K

def gz' (W : G3K K → ℂ) (c : HeckeCharacter K) (s : ℂ) : ℂ :=
  ∫ x, (∫ u, W (mm x u) ∂adeleMeasure K) * (c.toIdele x : ℂ) * ((md x : ℂ) ^ s) ∂ideleMeasure K

def κC : ℂ := 2

def Gauge (W : G3K K → ℂ) : Prop :=
  ∃ Ω : Set (FiniteAdeleRing (𝓞 K) K), IsCompact Ω ∧ ∃ T : ℕ, ∀ N : ℕ, ∃ C : ℝ, ∀ a b : (𝔸[K])ˣ,
    ∀ k ∈ (Reduction.maxCompact : Subgroup (G3K K)), ∀ w : InfinitePlace K,
      ‖W (dg (a * b) b 1 * k)‖ ≤ C / ((IdeleGroup.ideleModule K a : ℝ) * IdeleGroup.ideleModule K b) ^ T /
        ((1 + ‖(a : 𝔸[K]).1 w‖) * (1 + ‖(b : 𝔸[K]).1 w‖)) ^ N ∧
      (W (dg (a * b) b 1 * k) ≠ 0 → (a : 𝔸[K]).2 ∈ Ω ∧ (b : 𝔸[K]).2 ∈ Ω)

def CharFac : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ x : 𝔸[K], (adelicChar K x : ℂ) =
    psiC (InfinitePlace.Completion.extensionEmbedding (wC K) (x.1 (wC K))) * ∏ᶠ v : PlK K, (psiF v (x.2 v) : ℂ)

def WhSpan : Prop := ∀ (K : Type) [Field K] [NumberField K] (s : Set (G3K K → ℂ)),
  (∀ W ∈ s, ∀ h, (fun g => W (g * h)) ∈ Submodule.span ℂ s) →
  (∀ W ∈ s, ∀ x y z g, W (uni x y z * g) = (adelicChar K (x + z) : ℂ) * W g) →
  (∀ W ∈ s, ∀ (a : (𝔸[K])ˣ) g, W (dg a a a * g) = W g) →
  (∀ W ∈ s, IsArchSmooth W) →
  (∀ W ∈ s, ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K 3), ∀ g, ∀ u ∈ U, W (g * finEmb K 3 u) = W g) →
  (∀ W (hW : IsArchSmooth W), W ∈ s → ∀ X, ((EAK X ⟨W, hW⟩ : archSmooth K 3) : G3K K → ℂ) ∈ Submodule.span ℂ s) →
  (∀ W ∈ s, Gauge W) → WhAK (Submodule.span ℂ s)

def GenStable : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, ∀ h, (fun g => W (g * h)) ∈ Gen L

def GenPsi : Prop := CharFac → ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, ∀ x y z g, W (uni x y z * g) = (adelicChar K (x + z) : ℂ) * W g

def GenCen : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, ∀ (a : (𝔸[K])ˣ) g, W (dg a a a * g) = W g

def GenArch : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D) Wi Wf, IsFac L Wi Wf → IsArchSmooth (pw Wi Wf)

def GenLevel : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L,
    ∃ U : OpenSubgroup (AdelicGLn.FiniteAdelicGL K 3), ∀ g, ∀ u ∈ U, W (g * finEmb K 3 u) = W g

def GenLieX : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D) Wi Wf (_ : IsFac L Wi Wf) (hA : IsArchSmooth (pw Wi Wf)) X,
    ∃ Wi' ∈ L.VC, ((EAK X ⟨pw Wi Wf, hA⟩ : archSmooth K 3) : G3K K → ℂ) = pw Wi' Wf

def GenLieF : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  (∀ (D : DatK K) (L : Loc D) Wi Wf (h : IsFac L Wi Wf) (hA : IsArchSmooth (pw Wi Wf)) i j,
    ((EH i j ⟨pw Wi Wf, hA⟩ : archSmooth K 3) : G3K K → ℂ) = pw (L.E i j ⟨Wi, h.inf⟩ : GL (Fin 3) ℂ → ℂ) Wf ∧
    ((EA' i j ⟨pw Wi Wf, hA⟩ : archSmooth K 3) : G3K K → ℂ) = pw (L.E' i j ⟨Wi, h.inf⟩ : GL (Fin 3) ℂ → ℂ) Wf) ∨
  (∀ (D : DatK K) (L : Loc D) Wi Wf (h : IsFac L Wi Wf) (hA : IsArchSmooth (pw Wi Wf)) i j,
    ((EH i j ⟨pw Wi Wf, hA⟩ : archSmooth K 3) : G3K K → ℂ) = pw (L.E' i j ⟨Wi, h.inf⟩ : GL (Fin 3) ℂ → ℂ) Wf ∧
    ((EA' i j ⟨pw Wi Wf, hA⟩ : archSmooth K 3) : G3K K → ℂ) = pw (L.E i j ⟨Wi, h.inf⟩ : GL (Fin 3) ℂ → ℂ) Wf)

def GenGauge : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, Gauge W

def IdK : Prop := ∀ (K : Type) [Field K] [NumberField K] (W : G3K K → ℂ) (a : Kˣ),
  f1 W (ιK a) = W (diaK (dg a 1 1)) ∧ f2 W (ιK a) = ∫ u, W (diaK (dg 1 1 a) * cyc u) ∂adeleMeasure K

def AdmEx : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (c : HeckeCharacter K) (S₀ : Finset (PlK K)), ∃ n t S, S₀ ⊆ S ∧ AdmK D c n t S

def EulA : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset (PlK K),
    (∀ v ∉ S, Wf v = sph D v) → ∀ c n t, AdmK D c n t S → ∀ s : ℂ, 3 < s.re →
      gz (pw Wi Wf) c s = κC * zc Wi n (s + Complex.I * t) * (∏ v ∈ S, zv (Wf v) (localChar c v) s) * eulK D c S s

def EulB : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset (PlK K),
    (∀ v ∉ S, Wf v = sph D v) → ∀ c n t, AdmK D c n t S → ∀ s : ℂ, s.re < -2 →
      gz' (pw Wi Wf) c s = κC * zc' Wi n (s + Complex.I * t) * (∏ v ∈ S, zv' (Wf v) (localChar c v) s) *
        eulK D c⁻¹ S (1 - s)

def IntA : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, Integrable (fun x => ‖f1 W x‖ * md x ^ (3 : ℝ)) (ideleMeasure K)

def IntB : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, Integrable (fun x => ‖f2 W x‖ * md x ^ (-3 : ℝ)) (ideleMeasure K)

def BndC : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L, Continuous (f1 W) ∧ Continuous (f2 W)

def BndI : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L,
    ∃ U : OpenSubgroup (FiniteAdeleRing (𝓞 K) K)ˣ, ∀ u ∈ U, ∀ x,
      f1 W (x * IdeleGroup.ofFinite u) = f1 W x ∧ f2 W (x * IdeleGroup.ofFinite u) = f2 W x

def BndS : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K → LocU →
  ∀ (D : DatK K) (L : Loc D), ∀ W ∈ Gen L,
    (∀ x : IdeleGroup K, Integrable (fun u => W (mm x u)) (adeleMeasure K)) ∧
    ∀ C : Set (IdeleGroup K), IsCompact C → ∃ b : Kˣ → ℝ, Summable b ∧ ∀ a : Kˣ, ∀ x ∈ C,
      ‖f1 W (ιK a * x)‖ ≤ b a ∧ ‖f2 W (ιK a * x)‖ ≤ b a

def Glue : Prop := ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (D : DatK K) (L : Loc D) Wi Wf, IsFac L Wi Wf → ∀ S : Finset (PlK K),
    (∀ v ∉ S, Wf v = sph D v) → ∀ c n t, AdmK D c n t S → AnK D → ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ Ord G (-5 / 2) ∧
      (∀ s : ℂ, 1 < s.re → G s = zc Wi n (s + Complex.I * t) * (∏ v ∈ S, zv (Wf v) (localChar c v) s) * eulK D c S s) ∧
      ∀ s : ℂ, s.re < 0 → G s = zc' Wi n (s + Complex.I * t) * (∏ v ∈ S, zv' (Wf v) (localChar c v) s) * eulK D c⁻¹ S (1 - s)

end Ad3.K.GPK
