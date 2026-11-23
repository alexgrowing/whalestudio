import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct nonZeroDivisors Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRefChar

open GlobalTheory.HeckeConj

theorem exists_transport_of_norm {G K : Type} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [Field K]
    (σ₀ σ : K →+* ℂ) (f : G →* Circle) (hy : ∀ x, ∃ y, ((f x : Circle) : ℂ) = σ₀ y)
    (hn : ∀ x y, ((f x : Circle) : ℂ) = σ₀ y → ‖σ y‖ = 1) (U : Set G) (hU : U ∈ 𝓝 (1 : G)) (h1 : ∀ x ∈ U, f x = 1) :
    ∃ ψ : G →* Circle, Continuous ψ ∧ ∀ x y, ((f x : Circle) : ℂ) = σ₀ y → ((ψ x : Circle) : ℂ) = σ y := by
  choose y hy using hy
  have hone : ∀ x, f x = 1 → y x = 1 := fun x h => σ₀.injective (by rw [← hy, h, map_one, Circle.coe_one])
  let ψ : G →* Circle :=
    { toFun := fun x => ⟨σ (y x), by simp [Submonoid.unitSphere, hn x _ (hy x)]⟩
      map_one' := Circle.ext (by
        show σ (y 1) = 1
        rw [hone 1 (map_one f), map_one])
      map_mul' := fun a b => Circle.ext (by
        show σ (y (a * b)) = σ (y a) * σ (y b)
        have : y (a * b) = y a * y b := σ₀.injective (by rw [map_mul, ← hy, ← hy, ← hy, map_mul, Circle.coe_mul])
        rw [this, map_mul]) }
  refine ⟨ψ, continuous_of_continuousAt_one ψ ?_, fun x z h => ?_⟩
  · refine (continuousAt_const (y := (1 : Circle))).congr ?_
    filter_upwards [hU] with x hx
    refine Circle.ext ?_
    show (1 : ℂ) = σ (y x)
    rw [hone x (h1 x hx), map_one]
  · show σ (y x) = σ z
    rw [σ₀.injective ((hy x).symm.trans h)]

open Classical in

theorem exists_pow_eq (L : Type) [Field L] [NumberField L] (t : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∃ e : Lˣ, ∀ v, Valued.v
      ((t ^ n * (FiniteAdeleRing.unitEmbedding (𝓞 L) L e)⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ).1 v) = 1 := by
  refine ⟨Fintype.card (ClassGroup (𝓞 L)), Fintype.card_pos, ?_⟩
  generalize ha : t ^ Fintype.card (ClassGroup (𝓞 L)) = a
  have h1 : ClassGroup.mk L ((GlobalTheory.Mem.UnitIndex.idealHom L).toHomUnits a) = 1 := by
    rw [← ha, map_pow, map_pow, pow_card_eq_one]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf a = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  refine ⟨Units.mk0 x hx0, (GlobalTheory.Idele.smul_eq_self_iff (R := 𝓞 L) (K := L) _ (I := 1) one_ne_zero).1 ?_⟩
  rw [GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, GlobalTheory.Idele.idealOf_unitEmbedding, hx']
  exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)

theorem exists_pow_mem (D : D7) (x : (AE D)ˣ) : ∃ n : ℕ, 0 < n ∧ ∃ e : D.host.Eˣ,
    x ^ n * (Units.map (incA D).toMonoidHom e)⁻¹ ∈ intIdeles D := by
  obtain ⟨ι, h1, h2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  let φ : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map (ι.toRingHom.comp (finPart D)).toMonoidHom
  obtain ⟨n, hn, e, he⟩ := exists_pow_eq D.host.E (φ x)
  have hφ : φ (Units.map (incA D).toMonoidHom e) = FiniteAdeleRing.unitEmbedding (𝓞 D.host.E) D.host.E e :=
    Units.ext (h1 e)
  rw [← hφ, ← map_pow, ← map_inv, ← map_mul] at he
  refine ⟨n, hn, e, ?_⟩
  generalize x ^ n * (Units.map (incA D).toMonoidHom e)⁻¹ = u at he
  refine ⟨(h2 _).2 fun P => (he P).le, (h2 _).2 fun P => ?_⟩
  have h3 : (φ u).1 P * (φ u⁻¹).1 P = 1 := by
    have : (φ u).1 * (φ u⁻¹).1 = 1 := by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) this
  have h4 := congrArg Valued.v h3
  rw [map_mul, he P, one_mul, map_one] at h4
  exact h4.le

theorem hasInfExp_of_type (D : D7) {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {χ : (AE D)ˣ →* Circle} {k : D.what₂.Tau → ℤ}
    (hk : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = ∏ τ, angle D (θ τ) x ^ k τ) (ρ : D.what₂.Tau) :
    HasInfExp D χ ρ (k ρ) := by
  refine ⟨2 * k ρ, by push_cast; rfl, (GlobalTheory.VolHeckeCompare.allSome_infFam_iff _).2 ⟨θ, hθ, fun x hx ho => ?_⟩⟩
  rw [hk x hx, Finset.prod_eq_single ρ (fun τ _ hτ => by
    rw [show angle D (θ τ) x = 1 from Circle.ext (by rw [angle_coe, ho τ hτ]; simp), one_zpow]) (by simp),
    Circle.coe_zpow, angle_coe, zpow_mul]
  congr 1
  have h : θ ρ (infPart D (x : AE D)) ≠ 0 := ((x.isUnit.map (infPart D)).map (θ ρ)).ne_zero
  generalize θ ρ (infPart D (x : AE D)) = z at h
  have h1 : (‖z‖ : ℂ) ^ 2 = z * starRingEnd ℂ z := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using h
  rw [zpow_ofNat, div_pow, h1]
  field_simp

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

set_option maxHeartbeats 2000000 in

theorem exists_conj (D : D7) (Q : Par D) (χ₀ : (AE D)ˣ →* Circle) (hH : IsHeckeChar D χ₀) (hF : ∀ a, χ₀ (idF D a) = 1)
    (hy : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y)
    (c : D.what₂.Tau → ℚ) (hc : ∀ τ, HasInfExp D χ₀ τ (c τ)) (σ : Q.c.F →+* ℂ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ (∀ a, χ (idF D a) = 1) ∧
      (∀ ℓ : D.what₂.Tau → D.what₂.Tau, (∀ ρ, relab Q.c σ (tauE D (ℓ ρ)) = tauE D ρ) → ∀ ρ, HasInfExp D χ ρ (c (ℓ ρ))) ∧
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : Q.c.F, ((χ₀ x : Circle) : ℂ) = Q.c.F.val.toRingHom y ∧
        ((χ x : Circle) : ℂ) = σ y := by
  obtain ⟨⟨θ, hθ⟩, hθ'⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨θc, θs, -⟩ := hθ' θ hθ
  have hfam : IsInfFam (fun τ => θ (tauE D τ)) := fun τ => hθ _
  obtain ⟨k, hk⟩ := exists_type D (fun τ => θ (tauE D τ)) hfam χ₀ hH.1 hF
  have hck : ∀ τ, c τ = k τ := fun τ => GlobalTheory.Mem.HeckeExp.hasInfExp_unique (hc τ) (hasInfExp_of_type D hfam hk τ)
  obtain ⟨hop, a, b, -, bc, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  obtain ⟨N, hN, hN1, m, hm, hm1⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ₀ hH.1
  have hbu : ∀ x ∈ intIdeles D, FinUnit (b x) := fun x hx =>
    ⟨(hb x).1, (hb x).2 ▸ hx.1, by rw [← map_inv, (hb _).2]; exact hx.2⟩
  let A : (AE D)ˣ →* Circle := ∏ τ, angle D (θ (relab Q.c σ (tauE D τ))) ^ k τ
  have hA : ∀ x, A x = ∏ τ, angle D (θ (relab Q.c σ (tauE D τ))) x ^ k τ := fun x => by
    simp only [A, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply]
  have Ac : Continuous A := by
    rw [show (A : _ → _) = _ from funext hA]
    exact continuous_finset_prod _ fun τ _ => (continuous_angle D (θc _)).zpow _
  have key : ∀ (e : D.host.Eˣ) (r : (AF D.host.F)ˣ) (x : (AE D)ˣ), Units.map (incA D).toMonoidHom e * idF D r = x →
      ∃ w : Q.c.F, ((χ₀ (b x) : Circle) : ℂ) = Q.c.F.val.toRingHom w⁻¹ ∧ ((A x : Circle) : ℂ) = σ w := by
    intro e r x hx
    have han : ∀ τ, ((angle D (θ τ) x : Circle) : ℂ) =
        τ ((e : D.host.E) / IsCMField.complexConj D.host.E (e : D.host.E)) := fun τ => by
      rw [← hx, map_mul, angle_idF D (θs τ), mul_one, angle_inc D (hθ τ)]
    generalize (e : D.host.E) / IsCMField.complexConj D.host.E (e : D.host.E) = w at han
    have h0 : χ₀ (a x) * χ₀ (b x) = 1 := by
      rw [← map_mul, ← hab, ← hx, map_mul, hH.2, hF, mul_one]
    have h1 : ((χ₀ (a x) : Circle) : ℂ) = Q.c.F.val.toRingHom (∏ τ, embF Q.c (tauE D τ) w ^ k τ) := by
      rw [hk _ (ha _).2, coe_prod_zpow, map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, angle_coe, (ha _).1, ← angle_coe, han]
      rfl
    refine ⟨∏ τ, embF Q.c (tauE D τ) w ^ k τ, ?_, ?_⟩
    · rw [map_inv₀, ← h1, ← Circle.coe_inv, ← eq_inv_of_mul_eq_one_right h0]
    · rw [hA, coe_prod_zpow, map_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [map_zpow₀, han]
      rfl
  obtain ⟨ψ, ψc, hψ⟩ := exists_transport_of_norm Q.c.F.val.toRingHom σ (χ₀.comp b) (fun x => hy _ (hb x).1)
    (fun x y hxy => by
      obtain ⟨n, hn, e, he⟩ := exists_pow_mem D x
      obtain ⟨w, hw1, hw2⟩ := key e 1 _ (by rw [map_one, mul_one])
      have h1 := hm1 _ (hbu _ he)
      rw [map_mul, map_mul, map_inv, map_inv, mul_pow, inv_pow, mul_inv_eq_one, map_pow, map_pow] at h1
      have h2 : (y ^ n) ^ m = w⁻¹ ^ m := Q.c.F.val.toRingHom.injective (by
        rw [map_pow, map_pow, map_pow, ← hxy, ← hw1, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_pow, ← h1]
        rfl)
      have h3 : ‖σ y‖ ^ (n * m) = 1 := by
        rw [← norm_pow, ← map_pow, pow_mul, h2, map_pow, map_inv₀, ← hw2, norm_pow, norm_inv, Circle.norm_coe, inv_one,
          one_pow]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.mul_pos hn hm).ne').1 h3) _
    ((hop N hN).mem_nhds
      ⟨(intIdeles D).one_mem.1, (intIdeles D).one_mem.2, 0, zero_mem _, by
        show finPart D 1 - 1 = _
        rw [RingHom.map_one, sub_self, nsmul_zero]⟩)
    (fun x hx => hN1 _ (hbu x ⟨hx.1, hx.2.1⟩) (by rw [(hb _).2]; exact hx.2.2))
  have triv : ∀ (e : D.host.Eˣ) (r : (AF D.host.F)ˣ) (x : (AE D)ˣ), Units.map (incA D).toMonoidHom e * idF D r = x →
      (A * ψ) x = 1 := fun e r x hx => by
    obtain ⟨w, hw1, hw2⟩ := key e r x hx
    refine Circle.ext ?_
    show ((A x : Circle) : ℂ) * ((ψ x : Circle) : ℂ) = 1
    rw [hψ x _ hw1, map_inv₀, ← hw2, mul_inv_cancel₀ (Circle.coe_ne_zero _)]
  refine ⟨A * ψ, ⟨Ac.mul ψc, fun e => triv e 1 _ (by rw [map_one, mul_one])⟩,
    fun r => triv 1 r _ (by rw [map_one, one_mul]), fun ℓ hℓ ρ => ?_, fun x hx => ?_⟩
  · rw [hck]
    refine hasInfExp_of_type D hfam (k := fun ρ => k (ℓ ρ)) (fun x hx => ?_) ρ
    have hl : Function.Bijective ℓ := Finite.injective_iff_bijective.1 fun ρ ρ' h =>
      tauE_injective D (by rw [← hℓ ρ, h, hℓ])
    have h1 : ψ x = 1 := by
      obtain ⟨y, hy1⟩ := hy _ (hb x).1
      have h2 : χ₀ (b x) = 1 := by
        rw [hk _ ((hb x).2.trans hx)]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [show angle D (θ (tauE D τ)) (b x) = 1 from Circle.ext (by rw [angle_coe, (hb x).1]; simp), one_zpow]
      exact Circle.ext ((hψ x 1 (by rw [MonoidHom.comp_apply, h2, map_one, Circle.coe_one])).trans (map_one σ))
    rw [MonoidHom.mul_apply, h1, mul_one, hA]
    exact (Fintype.prod_bijective ℓ hl _ _ fun ρ => by rw [hℓ]).symm
  · obtain ⟨y, hy⟩ := hy x hx
    have han : ∀ u : (AE D)ˣ, infPart D (u : AE D) = 1 → ∀ τ, angle D (θ τ) u = 1 := fun u hu τ =>
      Circle.ext (by rw [angle_coe, hu]; simp)
    have h1 : χ₀ (b x) = χ₀ x := by
      conv_rhs => rw [hab x, map_mul, hk _ (ha _).2]
      simp only [han _ ((ha x).1.trans hx), one_zpow, Finset.prod_const_one, one_mul]
    refine ⟨y, hy, ?_⟩
    have h3 : A x = 1 := by simp only [hA, han _ hx, one_zpow, Finset.prod_const_one]
    rw [MonoidHom.mul_apply, h3, one_mul]
    exact hψ x y ((congrArg _ h1).trans hy)

theorem reference_lift_character_exponent_neg_base {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} (hL : L.Is μ0) (i : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (L.mu0 ((i : ℕ) + 1)) τ (-(D.hc τ).e i) := by
  obtain ⟨n, hn, hi⟩ := (L.C.isMu0 i).inf
  refine GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => -(D.hc τ).e i) (hL.mu0 i)
    ⟨fun τ => n (D.eTau τ), fun τ => ?_, fun k => ?_⟩ τ
  · simp only [hn, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]
  · rw [hi k]
    exact (Equiv.prod_comp D.eTau (fun g => (Formalism.L2.Host.embPsi D.host g (k : D.host.E) /
      ((‖Formalism.L2.Host.embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ)) ^ n g)).symm

theorem exists_chiAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), T.Q.Pins → AlgTie T → R.toLevCh.Is A.μ0 → ValKs R → ∃ (chiW : ℕ → (T.Q.c.F →+* ℂ) → (AE D)ˣ →* Circle), (∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ChiAt R i σ (chiW ((i : ℕ) + 1) (res T σ))) ∧ ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → IsHeckeChar D (chiW j σ) ∧ (∀ a, chiW j σ (idF D a) = 1) ∧ MuConj T.σ₀ σ (chiW j T.σ₀) (chiW j σ) := by
  intro D G _ _ Pl0 T0 A T _ R hp ha hL hv
  classical
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hp.2.2.1
  have e1 : ∀ y : T.Q.c.F, D.what₂.embLL (algebraMap T.Q.c.F D.what₂.LL y) = T.σ₀ y := RingHom.congr_fun e0
  have key : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ χ : (AE D)ˣ →* Circle, ∀ i : Fin D.R.m, j = (i : ℕ) + 1 →
      (IsHeckeChar D χ ∧ (∀ a, χ (idF D a) = 1) ∧
      (∀ ℓ : D.what₂.Tau → D.what₂.Tau, (∀ ρ, relab T.Q.c σ (tauE D (ℓ ρ)) = tauE D ρ) →
        ∀ ρ, HasInfExp D χ ρ (-(D.hc (ℓ ρ)).e i)) ∧
      ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∃ y : T.Q.c.F, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = T.σ₀ y ∧
        ((χ x : Circle) : ℂ) = σ y) ∧ (σ = T.σ₀ → χ = R.mu0 ((i : ℕ) + 1)) := by
    intro j σ
    by_cases hj : ∃ i : Fin D.R.m, j = (i : ℕ) + 1
    swap
    · exact ⟨1, fun i hi => absurd ⟨i, hi⟩ hj⟩
    obtain ⟨i, rfl⟩ := hj
    have hH : IsHeckeChar D (R.mu0 ((i : ℕ) + 1)) := (hL.mu0 i).1
    have hF : ∀ a, R.mu0 ((i : ℕ) + 1) (idF D a) = 1 := GlobalTheory.GridWeil.triv_base (hL.mu0 i) (R.C.isMu0 i).triv
    have hy : ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 →
        ∃ y : T.Q.c.F, ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = T.σ₀ y := fun x hx =>
      (hv i x hx).imp fun y h => h.trans (e1 y)
    by_cases hσ : σ = T.σ₀
    · subst hσ
      refine ⟨R.mu0 ((i : ℕ) + 1), fun i' hi => ?_⟩
      obtain rfl : i = i' := Fin.ext (Nat.succ_injective hi)
      refine ⟨⟨hH, hF, fun ℓ hℓ ρ => ?_, fun x hx => (hy x hx).imp fun y h => ⟨h, h⟩⟩, fun _ => rfl⟩
      rw [show ℓ ρ = ρ from tauE_injective D ((RingHom.ext fun _ => rfl).trans (hℓ ρ))]
      exact reference_lift_character_exponent_neg_base hL i ρ
    · obtain ⟨χ, hχ⟩ := exists_conj D T.Q _ hH hF hy (fun τ => -(D.hc τ).e i) (reference_lift_character_exponent_neg_base hL i) σ
      refine ⟨χ, fun i' hi => ?_⟩
      obtain rfl : i = i' := Fin.ext (Nat.succ_injective hi)
      exact ⟨hχ, fun h => absurd h hσ⟩
  choose χ hχ using key
  refine ⟨χ, fun i σ hσ => ?_, fun j hj σ _ => ?_⟩
  · obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := hχ _ (res T σ) i rfl
    refine ⟨h1, h2, h3 (lab σ) fun ρ => ?_, fun x hx => (h4 x hx).imp fun y h => ⟨h.1.trans (e1 y).symm, h.2⟩,
      fun h => h5 (h.trans e0)⟩
    refine Eq.trans (RingHom.ext fun x => ?_) ((GlobalTheory.ConjReading.branch_of_pins T ha hp σ ρ).1 hσ)
    refine congrArg σ (D.what₂.embLL.injective ((e1 _).trans ?_))
    exact (RingHom.congr_fun (embV_spec (RingHom.id _) D.what₂.embLL rfl (lab σ ρ)) x).symm
  · obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 :=
      ⟨⟨j - 1, by have := hj.1; have := hj.2; omega⟩, by have := hj.1; show j = j - 1 + 1; omega⟩
    obtain ⟨⟨h1, h2, -, h4⟩, -⟩ := hχ _ σ i rfl
    refine ⟨h1, h2, fun x hx => ?_⟩
    rw [(hχ _ T.σ₀ i rfl).2 rfl]
    exact h4 x hx.1

end GlobalTheory.ConjRefChar
