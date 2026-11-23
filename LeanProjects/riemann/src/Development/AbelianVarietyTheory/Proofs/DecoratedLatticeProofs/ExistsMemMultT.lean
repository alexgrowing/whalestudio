import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms GlobalTheory.Core.Rk GlobalTheory.Core.Rk.Top
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Core.Rk.TopLift

open GlobalTheory.Mem.ColAd Filter Topology

section Comp

variable {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem finN_mem_UPts (g : GA D V) : finN V hn g ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn))
    (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  exact GlobalTheory.PrincInLevel.swap_mem_UPts _ _ _ (GlobalTheory.UnitarySplit.finHom_mem V g)

theorem finN_eq (g : GA D V) (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (h : ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom V g)).1 i j = y.1 (finCongr hn i) (finCongr hn j)) : finN V hn g = y := by
  subst hn
  exact Units.ext (Matrix.ext h)

theorem exists_rat' (hθ : IsInfFam θ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ δ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)),
      finN V hn γ = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ ∧
      ∀ τ, (infN θ V hn (Equiv.refl _) γ τ : Matrix (Fin n) (Fin n) ℂ) = (δ : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) := by
  subst hn
  obtain ⟨δ, hδ, e⟩ := hγ
  refine ⟨δ, hδ, ?_, fun τ => ?_⟩
  · show Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ)) = _
    rw [show matHom V γ = _ from e.symm]
    rfl
  · show (Formalism.UG.bc _ (Formalism.UG.bc _ (matHom V γ))).1 = _
    rw [show matHom V γ = _ from e.symm]
    exact Matrix.ext fun i j => (hθ τ).1 _

theorem infN_atTau (hθ : IsInfFam θ) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (ρ : D.what₂.Tau) :
    (infN θ V hn (Equiv.refl _) (atTau θ V τ g) ρ : Matrix (Fin n) (Fin n) ℂ) =
      (Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  have h : IsAtTau θ V τ g (atTau θ V τ g) := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ hg
  show Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ ρ) (atTau θ V τ g) = Function.update (fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ)) τ g ρ
  by_cases c : ρ = τ
  · subst c
    rw [Function.update_self]
    exact h.2.1
  · rw [Function.update_of_ne c]
    exact h.2.2 ρ c

open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
open Formalism.L2.Col in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem continuous_finN : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    Continuous fun κ : GA D V =>
      (finN V hn κ : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  subst hn
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  letI := rlt_top D.host.F D.host.E
  haveI := rlt_isModTop D.host.F D.host.E
  haveI := rlt_topRing (F := D.host.F) (E := D.host.E)
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    ⟨rfl⟩
  have hs : Continuous (Lev.swapAE D) := by
    haveI := IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Lev.EAf D)
    refine (IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.ofBijective (rlt_comm (F := D.host.F) (E := D.host.E)) (TensorProduct.comm _ _ _).bijective).symm.toLinearMap).congr
      fun z => ?_
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    exact ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).symm_apply_apply z).symm
  have hf : Continuous fun κ : GA D V => (finN V rfl κ).1 :=
    (GlobalTheory.Mem.VolExists.continuous_finMat (σ := D.sp.cm.sig) V.gram).matrix_map hs
  refine Units.continuous_iff.2 ⟨hf, (hf.comp continuous_inv).congr fun κ => ?_⟩
  exact congrArg Units.val (map_inv (finN V rfl) κ)

end Comp

section Main

variable {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (θ : InfFam D)

def finPt (h : GA D D.sp.X') : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨finN D.sp.X' (rankP D) h, finN_mem_UPts D.sp.X' (rankP D) h⟩

theorem finPt_mul (h k : GA D D.sp.X') : (finPt (h * k)).1 = (finPt h).1 * (finPt k).1 := map_mul (finN D.sp.X' (rankP D)) h k

theorem finPt_one : (finPt (1 : GA D D.sp.X')) = 1 := Subtype.ext (map_one (finN D.sp.X' (rankP D)))

abbrev infPt : GA D D.sp.X' →* (D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ) := infN θ D.sp.X' (rankP D) (Equiv.refl _)

theorem finPt_of_hasMat {h : GA D D.sp.X'} {y} (hh : HasMat h y) : (finPt h).1 = y := finN_eq _ (rankP D) h y hh.2

variable {g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ}

theorem form_level (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h k : GA D D.sp.X') (κ : K.lev.U) (hk : (finPt k).1 = κ.1) :
    g (finPt (h * k)) = (K.lev.chi κ : ℂ) • g (finPt h) := by
  funext y
  refine hg.1 1 (one_mem _) (finPt h) (finPt (h * k)) κ ?_ y y fun τ => ?_
  · rw [map_one, one_mul, finPt_mul, hk]
  · show y.1 τ = (1 : Matrix _ _ D.host.E).map (embT D τ) * y.1 τ
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem form_left (hθ : IsInfFam θ) (hg : g ∈ AdForms K.lev (embT D) (sgT u)) {γ : GA D D.sp.X'} (hγ : γ ∈ GQ D.sp.X')
    (h : GA D D.sp.X') : lT _ (infPt θ γ) (g (finPt (γ * h))) = g (finPt h) := by
  obtain ⟨δ, hδ, e1, e2⟩ := exists_rat' θ D.sp.X' (rankP D) hθ hγ
  funext y
  have := hg.1 δ hδ (finPt h) (finPt (γ * h)) 1 (by
    rw [finPt_mul, ← e1]
    exact (mul_one _).symm) (frL _ (infPt θ γ) y) y fun τ => congrArg (· * y.1 τ) (e2 τ)
  rw [map_one, Units.val_one, one_mul] at this
  exact this

theorem form_locally (hK : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) |
        ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1})
    (hg : g ∈ AdForms K.lev (embT D) (sgT u)) :
    ∀ᶠ k in 𝓝 (1 : GA D D.sp.X'), ∀ h, g (finPt (h * k)) = g (finPt h) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  have hc : Continuous (finPt (D := D)) := (continuous_finN D.sp.X' (rankP D)).subtype_mk _
  have h1 := (hK.preimage hc).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, finPt_one]
    exact ⟨one_mem _, map_one K.lev.chi⟩)
  filter_upwards [h1] with k hk h
  obtain ⟨hx, e⟩ := hk
  rw [form_level hg h k ⟨_, hx⟩ rfl, e, Units.val_one, one_smul]

def valAt (g : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → FrP D → ℂ) (h : GA D D.sp.X') :
    FrP D → ℂ := lT _ (infPt θ h) (g (finPt h))

theorem finPt_mul_inf (h : GA D D.sp.X') {k : GA D D.sp.X'} (hk : k ∈ GinfC D.sp.X') : finPt (h * k) = finPt h := by
  refine Subtype.ext ?_
  rw [finPt_mul, show (finPt k).1 = 1 from finN_of_inf (rankP D) hk, mul_one]

theorem infPt_of_fin {k : GA D D.sp.X'} (hk : k ∈ GfC D.sp.X') : infPt θ k = 1 := infN_of_fin θ (rankP D) _ hk

theorem valAt_mem (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h : GA D D.sp.X') :
    valAt θ g h ∈ ValC (gramC (gramP D) (embT D)) (sgT u) := lT_mem _ _ _ (hg.2 _ (Set.mem_univ _))

theorem valAt_level (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (h : GA D D.sp.X') {k : GA D D.sp.X'} {κ : K.lev.U}
    (hk : HasMat k κ.1) : valAt θ g (h * k) = (K.lev.chi κ : ℂ) • valAt θ g h := by
  unfold valAt
  have e : infPt θ (h * k) = infPt θ h :=
    ((infPt θ).map_mul h k).trans ((congrArg (infPt θ h * ·) (infPt_of_fin θ hk.1)).trans (mul_one _))
  rw [form_level hg h k κ (finPt_of_hasMat hk), e]
  exact LinearMap.map_smul _ _ _

theorem valAt_of_hasMat {h : GA D D.sp.X'} {y : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hh : HasMat h y.1) : valAt θ g h = g y := by
  unfold valAt
  rw [infPt_of_fin θ hh.1, lT_one, show finPt h = y from Subtype.ext (finPt_of_hasMat hh)]

theorem valAt_atTau (hθ : IsInfFam θ) (h : GA D D.sp.X') (τ : D.what₂.Tau) {a : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ)) (y y' : FrP D)
    (hy : IsTr (fun ρ => (Function.update (fun _ => (1 : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ)) τ a ρ).reindex
      (finCongr (rankP D)) (finCongr (rankP D))) y' y) :
    valAt θ g h y = valAt θ g (h * atTau θ D.sp.X' τ a) y' := by
  have e : y = frL _ (infPt θ (atTau θ D.sp.X' τ a)) y' :=
    Subtype.ext (funext fun ρ => (hy ρ).trans (congrArg (· * y'.1 ρ) (infN_atTau θ _ (rankP D) hθ τ ha ρ).symm))
  unfold valAt
  rw [finPt_mul_inf h (GlobalTheory.PointAtPlaceHom.atTau_mem _ τ a), map_mul (infPt θ), lT_mul, e]
  rfl

variable (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ)

theorem isAutFunSm_pair (hθ : IsInfFam θ)
    (hK : letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) |
        ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1})
    (hg : g ∈ AdForms K.lev (embT D) (sgT u)) (f : FrP D → ℂ) :
    IsAutFunSm θ D.sp.X' fun h => Bf (valAt θ g h) f := by
  haveI : FiniteDimensional ℂ (ValC (gramC (gramP D) (embT D)) (sgT u)) :=
    GlobalTheory.Mem.Col2.valC_finiteDimensional (embT D) (RingHom.id ℂ) (sgT u)
  let l : (FrP D → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => star (Bf F f)
      map_add' := fun F F' => by rw [map_add, LinearMap.add_apply, star_add]
      map_smul' := fun c F => by simp }
  have h1 := isAutFunDef_of θ (rankP D) (Equiv.refl _) hθ (gramC (gramP D) (embT D)) (sgT u) (fun h => g (finPt h))
    (fun h => hg.2 _ (Set.mem_univ _)) (fun γ hγ h => form_left θ hθ hg hγ h) (form_locally hK hg)
    (fun k hk h => by rw [finPt_mul_inf h hk]) l
  have h2 := GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ _ _
    ((GlobalTheory.DefiniteForms.autFunDefIffSm D θ hθ _ D.sp.X'_sig (GlobalTheory.DefiniteEnd.end_definite D) _).1 h1)
  convert h2 using 1
  funext h
  exact (star_star _).symm

end Main

theorem exists_mem_multT : ∀ (D : D7) (u : D.what₂.Word) (K : ClsPTied u) (θ : InfFam D), IsInfFam θ → ∀ (S : D.what₂.Tau → SPar) (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)), IsJ u M j → ∀ (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ), TopLev K J χ → (letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F); IsOpen {x : Formalism.UG.UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) | ∃ hx : x.1 ∈ K.lev.U, K.lev.chi ⟨x.1, hx⟩ = 1}) → ∀ (Bf : (FrP D → ℂ) →ₗ⋆[ℂ] (FrP D → ℂ) →ₗ[ℂ] ℂ), (∀ a : D.what₂.Tau → Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) ℂ, (∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ)) → ∀ f f' f₁ f₁' : FrP D → ℂ, f ∈ ValC (gramC (gramP D) (embT D)) (sgT u) → f' ∈ ValC (gramC (gramP D) (embT D)) (sgT u) → (∀ y y' : FrP D, IsTr (fun τ => (a τ).reindex (finCongr (rankP D)) (finCongr (rankP D))) y' y → f₁ y = f y' ∧ f₁' y = f' y') → Bf f₁ f₁' = Bf f f') → ∀ g ∈ AdForms K.lev (embT D) (sgT u), ∃ T ∈ MultT θ M J χ, ∀ (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), HasMat h (K.y c).1 → T v h = Bf (g (K.y c)) (j v) := by
  intro D u K θ hθ S M j hj J χ hJ hK Bf hB g hg
  let T : SmT M →ₗ[ℂ] (GA D D.sp.X' → ℂ) := LinearMap.pi fun h => Bf (valAt θ g h) ∘ₗ j
  have hT : ∀ x h, T x h = Bf (valAt θ g h) (j x) := fun _ _ => rfl
  have hs := D.sp.X'_sig
  have hd := GlobalTheory.DefiniteEnd.end_definite D
  refine ⟨T, (mem_multT θ M J χ T).2 (Submodule.subset_span ⟨fun v => isAutFunSm_pair θ Bf hθ hK hg _,
    fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _, fun v k hk h => ?_, fun τ a ha v w hw => ?_, fun τ v x => ?_⟩),
    fun c v h hh => ?_⟩
  · obtain ⟨κ, hκ⟩ := (hJ.1 k).1 hk
    show Bf (valAt θ g (h * k)) _ = χ k * Bf (valAt θ g h) _
    rw [hJ.2 k κ hκ, valAt_level θ hg h hκ, LinearMap.map_smulₛₗ₂]
    rfl
  · funext h
    show Bf (valAt θ g h) (j _) = Bf (valAt θ g (h * atTau θ D.sp.X' τ a)) (j _)
    refine hB (Function.update (fun _ => 1) τ a) (fun ρ => ?_) _ _ _ _ (valAt_mem θ hg _)
      (hj.range ▸ LinearMap.mem_range_self j _) fun y y' hy => ⟨valAt_atTau θ hθ h τ ha y y' hy, hj.eqv τ a ha v w hw y y' fun ρ => ?_⟩
    · by_cases c : ρ = τ
      · subst c
        rwa [Function.update_self]
      · rw [Function.update_of_ne c]
        show (1 : Matrix _ _ ℂ).conjTranspose * _ * 1 = _
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    · refine (hy ρ).trans ?_
      by_cases c : ρ = τ
      · subst c
        simp only [Function.update_self]
      · simp only [Function.update_of_ne c, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  · haveI := GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd M τ
    exact GlobalTheory.DefiniteEnd.exists_sobCont M τ _ v x
  · rw [hT, valAt_of_hasMat θ hh]

end GlobalTheory.Core.Rk.TopLift

end
