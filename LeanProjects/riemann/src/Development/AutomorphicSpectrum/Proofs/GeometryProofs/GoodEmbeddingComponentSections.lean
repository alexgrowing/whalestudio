import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

theorem eq_of_ratios {K A L M : Type} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L] [CommRing M]
    [IsDomain M] [Algebra K M] (ι : A →ₐ[K] L) (hι : Function.Injective ι) (ψ : A →ₐ[K] M) (φ : L →ₐ[K] M) {N : ℕ}
    (G : Fin (N + 1) → A) (h0 : ι (G 0) ≠ 0) (hψ0 : ψ (G 0) ≠ 0)
    (hrat : ∀ j, ψ (G j) * φ (ι (G 0)) = ψ (G 0) * φ (ι (G j)))
    (hgen : IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι (G 0)) = ⊤) (b : A) : ψ b = φ (ι b) := by
  set g₀ : A := G 0 with hg₀
  let S : Subalgebra K L :=
    { carrier := {x | ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a}
      mul_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * a', n + n', ?_, ?_⟩
        · rw [map_mul, ← h1, ← h1', pow_add]; ring
        · rw [map_mul, map_mul, ← h2, ← h2', pow_add]; ring
      add_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * g₀ ^ n' + a' * g₀ ^ n, n + n', ?_, ?_⟩
        · rw [map_add, map_mul, map_mul, map_pow, map_pow, ← h1, ← h1', pow_add]; ring
        · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← h2, ← h2', pow_add]; ring
      algebraMap_mem' := fun r => ⟨algebraMap K A r, 0, by simp, by simp⟩ }
  have hmem : ∀ x, x ∈ S ↔ ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a := fun x => Iff.rfl
  have hφ0 : φ (ι g₀) ≠ 0 := (map_ne_zero φ).2 h0
  have hρ : ∀ j, ι (G j) / ι g₀ ∈ S := by
    intro j
    refine (hmem _).2 ⟨G j, 1, by rw [pow_one, div_mul_cancel₀ _ h0], ?_⟩
    have e1 : φ (ι (G j) / ι g₀) * φ (ι g₀) = φ (ι (G j)) := by
      rw [← map_mul, div_mul_cancel₀ _ h0]
    refine mul_right_cancel₀ hφ0 ?_
    rw [pow_one, hrat j, ← e1]; ring
  have hpol : ∀ p : MvPolynomial (Fin (N + 1)) K, MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa using S.algebraMap_mem a
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p i hp => simpa using S.mul_mem hp (hρ i)
  have hb : ι b ∈ IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι g₀) := by
    rw [hgen]; exact IntermediateField.mem_top
  obtain ⟨p, q, e⟩ := (IntermediateField.mem_adjoin_range_iff K _ _).1 hb
  by_cases hq : MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q = 0
  · rw [hq, div_zero] at e
    have : b = 0 := hι (by rw [e, map_zero])
    rw [this, map_zero, map_zero, map_zero]
  obtain ⟨a₁, n₁, h1, h1'⟩ := (hmem _).1 (hpol q)
  obtain ⟨a₂, n₂, h2, h2'⟩ := (hmem _).1 (hpol p)
  set B := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q with hB
  set P := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p with hP
  have hbB : ι b * B = P := by rw [e, div_mul_cancel₀ _ hq]
  have key : b * a₁ * g₀ ^ n₂ = a₂ * g₀ ^ n₁ := by
    apply hι
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1, ← h2, ← hbB]; ring
  have key' := congrArg ψ key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1', ← h2', ← hbB, map_mul] at key'
  have hne : φ B * ψ g₀ ^ n₁ * ψ g₀ ^ n₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero φ).2 hq) (pow_ne_zero _ hψ0)) (pow_ne_zero _ hψ0)
  refine mul_right_cancel₀ hne ?_
  linear_combination key'

end GlobalTheory.CompanionTheory.Ar.SameFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_map (hL : GlobalTheory.Reg.EvLaws Xo c) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have key : ∀ {S' : Type} [CommRing S'] [Algebra c.F S'] (p : TRing c.F) (χ : p.R →ₐ[c.F] S') (y₀ : FrPt Xo c p.R)
      (w : FrPt Xo c S'), FrMap χ y₀ w → evR Xo c f w = χ (f p y₀) := by
    intro S' _ _ p χ y₀ w hw
    have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, χ, y₀, hw⟩
    unfold evR evalAt
    rw [dif_pos h]
    exact hL.wd f hf S' _ p _ χ _ y₀ w h.choose_spec.choose_spec.choose_spec hw
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [key q χ y₀ y hy₀, key q (φ.comp χ) y₀ z (PullbackSections.frMap_trans χ φ hy₀ hyz)]
  rfl

end Main

theorem frBor_of_proportional_readings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  intro E _ _ _ H Dw l Xo c r U h e hC σ hσ Z k hOver a N g hg hB φ x₀ y y₁ t hφ hb w hw hr
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  haveI hdom : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hrd : ∀ f : Rul Xo c, rdU (U σ) f k y.1 = toC (evR Xo c f ((U σ).un k y)) := by
    intro f
    classical
    show (if h : y.1 ∈ ((U σ).X k).dom then toC (evR Xo c f ((U σ).un k ⟨y.1, h⟩)) else 0) = _
    rw [dif_pos y.2]
  obtain ⟨C, ψ, z, t', hz, hbz⟩ : ∃ (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ))
      (t' : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z ∧ FrBor t' z ((U σ).un k y) := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    exact hA h (CAt σ) ((U σ).un k y)

  have hCZ : C.Z = Z := by
    by_contra hne
    have he := hC.e_sec Z
    have h0 : evC h C.Z (e Z) = 0 := (hC.e_val Z).2 _ hne
    have h1 : evR Xo c (e Z) C.yg = 0 := by
      rw [hL.wt 0 0 (e Z) he _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      unfold evC at h0
      rw [h0, mul_zero]
    have h2 : evR Xo c (e Z) C.y = 0 := by
      rw [evR_map hL he.1 C.R.val C.gen] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c (e Z) z = 0 := by rw [evR_map hL he.1 ψ hz, h2, map_zero]
    have h4 : evR Xo c (e Z) ((U σ).un k y) = 0 := by
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      rw [hL.wt 0 0 (e Z) he _ t' _ _ (hL.test _ _) (hL.test _ _) hbz, h3, mul_zero]
    have h5 := hOver y.1 y.2
    rw [hrd, h4] at h5
    exact zero_ne_one (α := ℂ) h5
  subst hCZ
  have hgA : ∀ j, g j ∈ GlobalTheory.AllWt.secZ Xo c (exZ Dw a) := fun j => by
    rw [← secZ_eq_allWt]; exact hg j
  set ex := exZ Dw a with hex

  let G : Fin (N + 1) → C.R := fun j => evR Xo c (g j) C.y
  have hιG : ∀ j, C.R.val (G j) = ((∏ i, C.t i ^ ex i : (Om C.Z)ˣ) : Om C.Z) * evC h C.Z (g j) := by
    intro j
    rw [← evR_map hL (hg j).1 C.R.val C.gen]
    exact GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (Om C.Z) C.t _ _ C.bor
  obtain ⟨wc, hwc⟩ : ∃ wc : CAt σ, toC wc = w := ⟨w, rfl⟩
  have hψG : ∀ j, ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * ψ (G j) = wc * φ (evC h C.Z (g j)) := by
    intro j
    have h1 : evR Xo c (g j) ((U σ).un k y) = ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * evR Xo c (g j) z :=
      GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (CAt σ) t' _ _ hbz
    have h2 : evR Xo c (g j) z = ψ (G j) := evR_map hL (hg j).1 ψ hz
    rw [← h2, ← h1]
    have h3 := hr j
    rw [hrd, ← hwc] at h3
    exact h3
  set T : (Om C.Z)ˣ := ∏ i, C.t i ^ ex i with hT
  set T' : (CAt σ)ˣ := ∏ i, t' i ^ ex i with hT'
  have hw' : wc ≠ 0 := fun h0 => hw (by rw [← hwc, h0]; rfl)
  have hE0 : φ (evC h C.Z (g 0)) ≠ 0 := (map_ne_zero_iff φ φ.toRingHom.injective).2 hB.1
  have hψ0 : ψ (G 0) ≠ 0 := by
    intro h0
    have h1 := hψG 0
    rw [h0, mul_zero] at h1
    exact mul_ne_zero hw' hE0 h1.symm
  have hι0 : C.R.val (G 0) ≠ 0 := by
    rw [hιG]
    exact mul_ne_zero T.ne_zero hB.1
  have hrat : ∀ j, ψ (G j) * φ (C.R.val (G 0)) = ψ (G 0) * φ (C.R.val (G j)) := by
    intro j
    have h1 := hψG j
    have h2 := hψG 0
    refine mul_left_cancel₀ T'.ne_zero ?_
    rw [hιG, hιG, map_mul, map_mul]
    linear_combination (φ (T : Om C.Z) * φ (evC h C.Z (g 0))) * h1 - (φ (T : Om C.Z) * φ (evC h C.Z (g j))) * h2
  have hgen : IntermediateField.adjoin c.F (Set.range fun j => C.R.val (G j) / C.R.val (G 0)) = ⊤ := by
    have e1 : (fun j => C.R.val (G j) / C.R.val (G 0)) = fun j => evC h C.Z (g j) / evC h C.Z (g 0) := by
      funext j
      rw [hιG, hιG, mul_div_mul_left _ _ T.ne_zero]
    rw [e1]
    exact hB.2
  have hψφ : ψ = φ.comp C.R.val :=
    AlgHom.ext fun b => eq_of_ratios C.R.val Subtype.val_injective ψ φ G hι0 hψ0 hrat hgen b

  obtain ⟨w₁, hw₁⟩ := hL.bc _ _ φ C.yg
  have h1 := PullbackSections.frMap_trans _ _ C.gen hw₁
  rw [← hψφ] at h1
  obtain rfl : z = w₁ := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz h1
  have hbc := GlobalTheory.SupGeneric.frBor_of_frMap φ C.bor hφ hw₁
  have hgp := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  exact ⟨_, hgp.2.1 _ _ _ _ _ (hgp.2.1 _ _ _ _ _ hb hbc) hbz⟩

end GlobalTheory.CompanionTheory.Ar.SameFlag
