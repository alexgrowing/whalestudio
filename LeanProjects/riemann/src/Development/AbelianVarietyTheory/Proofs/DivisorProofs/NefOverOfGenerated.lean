import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularSectionOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointPlaceConditionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen.Crit

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem nefOver_of_genOver : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l : ℕ),
    Norms V L f a φ → GenOver V f φ l → NefOver L l := by
  intro F _ _ Y V L f a φ l ⟨r, hr, hu, _, hf⟩ ⟨n, U, s, hUx, hreg, hgen⟩
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_gen_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ (y : Sp (AlgebraicClosure F) ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hrg : ∀ (z : V.G) (g : V.X.functionField), RegAt (V.j z) g ↔ RegAt z (ρ g) :=
    fun z g => (SmallSec.regAt_fnMap_iff V.j hη).symm
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr

  let R : L.B.ι → V.X.functionFieldˣ := fun i => Units.map ρ.symm.toMonoidHom (r fun _ => i)
  let s' : V.X → Fin n → V.X.functionField := fun x J => ρ.symm (s x J)
  have eR : ∀ (t : V.G.functionField) (i : L.B.ι), t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
      ρ (ρ.symm t * (R i : V.X.functionField)) := by
    intro t i
    rw [map_mul, ρ.apply_symm_apply]
    exact congrArg _ (ρ.apply_symm_apply _).symm
  have mem_pull : ∀ (z : V.G) (i : L.B.ι), V.j z ∈ L.B.U i → z ∈ (L.B.pull V.j).U (fun _ => i) :=
    fun z i h => Set.mem_iInter.2 fun _ => h

  have split : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i →
      t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) =
        t / V.φ (f (V.π z)) * (V.φ (f (V.π z)) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz
    have h0 : V.φ (f (V.π z)) ≠ 0 := left_ne_zero_of_mul (hu _ _ (mem_pull z i hz)).ne_zero
    field_simp
  have regG : ∀ (t : V.G.functionField) (i : L.B.ι) (z : V.G), V.j z ∈ L.B.U i → RegAt z (t / V.φ (f (V.π z))) →
      RegAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)) := by
    intro t i z hz ht
    rw [split t i z hz]
    exact ht.mul (hu _ _ (mem_pull z i hz)).regAt
  have valG : ∀ (t : V.G.functionField) (i : L.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (hz : z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F))),
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U i → RegAt (below z) (t / V.φ (f (V.π (below z)))) →
      e.w (valAt z (t * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) =
        e.w (valAt z (t / V.φ (f (V.π (below z))))) *
          Real.exp (φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩) := by
    intro t i v e z yt hz e₂ hU ht
    have hpt : V.j (below z) ∈ L.B.U i := by
      change (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have hun := hu _ _ (mem_pull _ i hpt)
    have H : φ v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ =
        Real.log (e.w (valAt z (V.φ (f (V.π (below z))) * ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))) :=
      hf v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt (fun _ => i) rfl e₂ hU
    rw [H, Real.exp_log (e.w.pos (SmallSec.valAt_ne_zero hun)), split t i _ hpt,
      SmallSec.valAt_mul ht hun.regAt, map_mul]
  refine GlobalTheory.T.regular_section_open_cover (𝓞 F) V.X V.p Y.dim V.ar L R hR l n U s' hUx ?_
  intro x i x₀ hx₀ hi₀ hl₀

  have regA : ∀ (J : Fin n) (c : V.X), c ∈ U x → c ∈ L.B.U i → (l : 𝓞 F) ∈ (V.p c).asIdeal →
      RegAt c (s' x J * R i) := by
    intro J c hc hic hlc
    refine GlobalTheory.T.integral_point_place_condition F Y V l (U x ⊓ L.B.U i) _ (fun z hz => ?_) (fun v e z yt hlv hz e₂ hU => ?_) c ⟨hc, hic⟩ hlc
    · rw [hrg, ← eR]
      exact regG _ i z hz.2 (hreg x J z hz.1)
    · have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
        rw [← e₂]
        exact hU (Set.mem_univ _)
      have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hU hw).1
      have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hU hw).2
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').1 J
  refine ⟨fun J => regA J x₀ hx₀ hi₀ hl₀, ?_, ?_⟩
  · obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ := GlobalTheory.T.integral_point_closure_extension F Y V l (U x ⊓ L.B.U i) x₀ ⟨hx₀, hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ U x ⊓ L.B.U i := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x ⊓ L.B.U i := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hlc : (l : 𝓞 F) ∈ (V.p (yt (IsLocalRing.closedPoint e.O))).asIdeal :=
      (PrimeSpectrum.le_iff_specializes _ _).2 (hsp.map V.p.continuous) hl₀
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2
    obtain ⟨J, hJ⟩ := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.1
    have hunit : UnitAt (yt (IsLocalRing.closedPoint e.O)) (s' x J * R i) := by
      refine (hiff _ (regA J _ hcW.1 hcW.2 hlc)).1 ?_
      rw [hv, ← eR, valG _ i v e z yt hz e₂ hUi (hreg x J _ hpt.1)]
      exact hJ
    obtain ⟨W', hW', hall⟩ := hunit.exists_nhds
    exact ⟨J, hall x₀ (hsp.mem_open W'.isOpen hW')⟩
  · intro x' hx₀' J hJ
    obtain ⟨W', hW', hall⟩ := hJ.exists_nhds
    obtain ⟨v, e, z, yt, hlv, hz, e₂, hW, hsp, hiff⟩ :=
      GlobalTheory.T.integral_point_closure_extension F Y V l (W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i))) x₀ ⟨hW', hx₀, hx₀', hi₀⟩ hl₀
    have hcW : yt (IsLocalRing.closedPoint e.O) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := hW (Set.mem_univ _)
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ W' ⊓ (U x ⊓ (U x' ⊓ L.B.U i)) := by
      rw [← e₂]
      exact hW (Set.mem_univ _)
    have hUx' : ⊤ ≤ yt ⁻¹ᵁ U x := fun w hw => (hW hw).2.1
    have hUx'' : ⊤ ≤ yt ⁻¹ᵁ U x' := fun w hw => (hW hw).2.2.1
    have hUi : ⊤ ≤ yt ⁻¹ᵁ L.B.U i := fun w hw => (hW hw).2.2.2
    have hc := hall _ hcW.1
    have h1 := (hiff _ hc.regAt).2 hc
    have hlt := (hgen v e ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩ z yt hlv rfl e₂ x hUx').2.2 x' hUx'' J
    have hd : RegAt (below z) ((s x J - s x' J) / V.φ (f (V.π (below z)))) := by
      have hm1 : RegAt (below z) (-1 : V.G.functionField) := ⟨-1, by simp⟩
      rw [show (s x J - s x' J) / V.φ (f (V.π (below z))) =
          s x J / V.φ (f (V.π (below z))) + (-1) * (s x' J / V.φ (f (V.π (below z)))) by ring]
      exact (hreg x J _ hpt.2.1).add (hm1.mul (hreg x' J _ hpt.2.2.1))
    have e₃ : s' x J - s' x' J = ρ.symm (s x J - s x' J) := (map_sub ρ.symm _ _).symm
    rw [e₃, hv, ← eR, valG _ i v e z yt hz e₂ hUi hd] at h1
    change e.w (valAt z ((s x J - s x' J) / V.φ (f (V.π (below z))))) * _ < 1 at hlt
    rw [h1] at hlt
    exact lt_irrefl _ hlt

end GlobalTheory.HtGen.Crit
