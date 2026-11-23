import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PropZStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLocalOfKernelAtPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericStatementOfCanonicalExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftingOfComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseOfTateValueBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessStatementHoldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluingOfConnectednessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PackingStatementHoldsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Local

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem exists_unit (hG : GenSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {ξ : Sp R ⟶ Y.X} [IsOpenImmersion ξ] {β : c'.V W →+* R}
    (hβ : ξ ≫ Y.s = spMap β) (hξ : ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Xw) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {U₁ U₂ : Fin g → Fin g → R}
    (h₁ : EigFam Y.t ξ (β.comp (embV c' W τ.1)) e U₁) (h₂ : EigFam Y.t ξ (β.comp (embV c' W (conjEmb τ.1))) e U₂)
    (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g) (a₁ : Fin (Dw.mult τ.1) → Fin g → R)
    (a₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → R) (ε : ℤˣ) :
    ∃ u : (Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))))ˣ,
      ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))) →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap (ψ.comp (algebraMap R _)) ≫ ξ → ∃ fv : k,
          GVal Y r ν τ.1 s.sig yy (bcV Y.t (ψ.comp (algebraMap R _)) e) (fun i b => ψ (algebraMap R _ (U₁ (K₁ i) b)))
            (fun i b => ψ (algebraMap R _ (U₂ (K₂ i) b))) fv ∧
          ψ u = fv * ((ε : ℤ) : k) * ψ (algebraMap R _ (pairDet a₁ (U₁ ∘ K₁))) / ψ (algebraMap R _ (pairDet a₂ (U₂ ∘ K₂))) := by
  set q : R := (p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂)) with hq
  have hu : IsUnit (algebraMap R (Localization.Away q) q) := IsLocalization.Away.algebraMap_isUnit q
  by_cases h0 : q = 0
  · refine ⟨1, fun k _ _ ψ _ _ => ?_⟩
    have := hu.map ψ
    rw [show algebraMap R (Localization.Away q) q = 0 from (congrArg _ h0).trans (map_zero _), map_zero] at this
    exact absurd this not_isUnit_zero
  have hle' : Submonoid.powers q ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away q) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R (Localization.Away q)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R (Localization.Away q)
  have hu' : IsUnit ((p : Localization.Away q) * (ρ (pairDet a₁ (U₁ ∘ K₁)) * ρ (pairDet a₂ (U₂ ∘ K₂)))) := by
    rw [← map_natCast ρ, ← map_mul, ← map_mul]; exact hu
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu')
  have mp : ∀ {m : ℕ} (a V : Fin m → Fin g → R), ρ (pairDet a V) = pairDet (fun i b => ρ (a i b)) fun i b => ρ (V i b) :=
    fun a V => by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext i j
      simp [map_sum]
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization q
  obtain ⟨f, hf⟩ := hG E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw Fact.out hc (Localization.Away q)
    (spMap ρ ≫ ξ) (ρ.comp β) inferInstance (by rw [Category.assoc, hβ, spMap_spMap]) (isUnit_of_mul_isUnit_left hu')
    (by rw [bot_map hinj]; exact hξ) g (bcV Y.t ρ e) (fun i b => ρ (U₁ (K₁ i) b)) (fun i b => ρ (a₁ i b))
    (fun i b => ρ (U₂ (K₂ i) b)) (fun i b => ρ (a₂ i b)) (isTanBasis_bc he ρ)
    (fun S _ φ => by
      rw [sp_sp, bcV_bcV]
      exact ⟨fun i => (h₁ S (φ.comp ρ)).1 (K₁ i), fun i => (h₂ S (φ.comp ρ)).1 (K₂ i)⟩)
    (mp a₁ _ ▸ u₁) (mp a₂ _ ▸ u₂)
  refine ⟨f * Units.map (Int.castRingHom _).toMonoidHom ε * u₁.unit * u₂.unit⁻¹, fun k _ _ ψ yy hy => ⟨ψ f, ?_, ?_⟩⟩
  · have := hf k ψ yy (by rw [sp_sp]; exact hy)
    rwa [bcV_bcV] at this
  · rw [eq_div_iff (u₂.map ψ).ne_zero, ← map_mul]
    change ψ (_ * (u₂.unit : Localization.Away q)) = _
    rw [← Units.val_mul, inv_mul_cancel_right]
    simp [ρ]

end Local

section Charts

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens} [StarRing (𝓞 E)]

variable (Y r ν) in

def kapSet (τ : E →+* ℂ) (f : Rul Xo c) (n : ℕ) {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ → Fin N → c'.V W)
    (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) : Set ℂ_[p] :=
  {κ | ∃ (_ : Algebra c.F ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ ∧ KapSpec Y r ν τ f n a T S yb yy P π ψ κ}

theorem chartAt (hC : ChartSt) (hP : ProjSt) (hT : HTLocSt) (hG : GenSt) (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw) {n : ℕ} (hn : l'.A = p ^ n)
    {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ.1 → Fin N → c'.V W)
    (hK : ∀ yb, IsTest p Xw yb → (kapSet Y r ν τ.1 s.sig n a T S yb).Nonempty) {z : Y.X}
    (hz : z ∈ closure (Xw : Set Y.X)) : ChartAt p n Xw (kapSet Y r ν τ.1 s.sig n a T S) z := by
  obtain ⟨R₀, _, _, _, ξ₀, g, e₀, hξ₀, ⟨z₀, rfl⟩, he₀⟩ := hC E H Dw l' Xo' c' W Y p Fact.out hc.2.2.1 z
  obtain ⟨_, ⟨z₁, rfl⟩, hz₁⟩ := mem_closure_iff.1 hz _ ξ₀.isOpenEmbedding.isOpen_range ⟨z₀, rfl⟩
  have hb₀ := bot_mem ξ₀ hz₁
  let β₀ : c'.V W →+* R₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have hβ₀ : ξ₀ ≫ Y.s = spMap β₀ := (Spec.map_preimage _).symm
  obtain ⟨V₁, hV₁⟩ := hP E H l' c' W Y.X Y.t R₀ ξ₀ β₀ g e₀ he₀ τ.1
  obtain ⟨V₂, hV₂⟩ := hP E H l' c' W Y.X Y.t R₀ ξ₀ β₀ g e₀ he₀ (conjEmb τ.1)
  obtain ⟨f, h, hf, hh⟩ := hT E H Dw l' Xo' c' W Y p n hs hc.2.2.1 hn R₀ ξ₀ (hc.2.2.2.2.1 hb₀) g e₀ he₀ N a
    (PrimeSpectrum.asIdeal z₀) (PrimeSpectrum.isPrime z₀)
  have h0 : f ≠ 0 := by rintro rfl; exact hf (Ideal.zero_mem _)
  have hle' : Submonoid.powers f ≤ nonZeroDivisors R₀ := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away f) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R₀ (Localization.Away f)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R₀ (Localization.Away f)
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization f
  let U₁ : Fin g → Fin g → Localization.Away f := fun k b => ρ (V₁ k b)
  let U₂ : Fin g → Fin g → Localization.Away f := fun k b => ρ (V₂ k b)
  have hU₁ : EigFam Y.t (spMap ρ ≫ ξ₀) ((ρ.comp β₀).comp (embV c' W τ.1)) (bcV Y.t ρ e₀) U₁ := fun S _ φ => by
    rw [sp_sp, bcV_bcV]; exact hV₁ S (φ.comp ρ)
  have hU₂ : EigFam Y.t (spMap ρ ≫ ξ₀) ((ρ.comp β₀).comp (embV c' W (conjEmb τ.1))) (bcV Y.t ρ e₀) U₂ := fun S _ φ => by
    rw [sp_sp, bcV_bcV]; exact hV₂ S (φ.comp ρ)
  have hβ : (spMap ρ ≫ ξ₀) ≫ Y.s = spMap (ρ.comp β₀) := by rw [Category.assoc, hβ₀, spMap_spMap]
  have he := isTanBasis_bc he₀ ρ
  let J : Type := Equiv.Perm (Ind Dw τ.1) × (Fin (Dw.mult τ.1) → Fin g) × (Fin (Dw.mult (conjEmb τ.1)) → Fin g)
  choose u hu using fun j : J => exists_unit (ν := ν) hG hL s hc hβ (by rw [bot_map hinj]; exact hb₀) he hU₁ hU₂
    j.2.1 j.2.2 (covec (ρ.comp β₀) T h (j.1 ∘ Sum.inl)) (covec (ρ.comp β₀) S h (j.1 ∘ Sum.inr)) (Equiv.Perm.sign j.1)
  refine ⟨Localization.Away f, inferInstance, spMap ρ ≫ ξ₀, J, inferInstance, _, u, inferInstance, ?_, fun φ ht => ?_⟩
  · obtain ⟨z', hz'⟩ : z₀ ∈ Set.range (PrimeSpectrum.comap ρ) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact hf
    exact ⟨z', (Scheme.Hom.comp_apply _ _ _).trans (congrArg ξ₀ hz')⟩
  have hA : ∀ {yy P π ψ}, PtOn Y (spMap φ ≫ spMap ρ ≫ ξ₀) yy P π ψ →
      HTApprox Y n yy P π ψ a (bcV Y.t φ (bcV Y.t ρ e₀)) fun m k => φ (h m k) := fun {yy P π ψ} hPt => by
    rw [bcV_bcV]
    exact hh φ yy P π ψ (by rw [← sp_sp]; exact hPt)
  have hφ : (spMap φ ≫ spMap ρ ≫ ξ₀) ≫ Y.s = spMap (φ.comp (ρ.comp β₀)) := by rw [Category.assoc, hβ, spMap_spMap]
  constructor
  · obtain ⟨κ, alg, yy, P, π, ψ, hPt, hκ⟩ := hK _ ht
    obtain ⟨⟨σ, K₁, K₂, hj⟩, -⟩ := hκ _ hφ g _ _ _ _ (isTanBasis_bc he φ) (hU₁ _ φ) (hU₂ _ φ) (hA hPt)
    refine ⟨(σ, K₁, K₂), ?_⟩
    rw [map_mul, map_pairDet_covec, map_pairDet_covec]
    exact hj
  · rintro ⟨σ, K₁, K₂⟩ hj ψ hψ κ ⟨alg, yy, P, π, ψ', hPt, hκ⟩
    obtain ⟨-, hv⟩ := hκ _ hφ g _ _ _ _ (isTanBasis_bc he φ) (hU₁ _ φ) (hU₂ _ φ) (hA hPt)
    rw [map_mul, map_pairDet_covec, map_pairDet_covec] at hj
    obtain ⟨fv, hfv, hu'⟩ := hu (σ, K₁, K₂) ℂ_[p] ψ yy (by rw [hψ, ← hPt.1, sp_sp])
    have hψ' : ∀ b, ψ (algebraMap _ _ b) = (φ b : ℂ_[p]) := fun b => RingHom.congr_fun hψ b
    simp only [hψ'] at hfv hu'
    rw [hψ, ← bcV_bcV] at hfv
    rw [hu', map_pairDet_covec, map_pairDet_covec]
    exact hv σ K₁ K₂ hj fv hfv

end Charts

section Top

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem evR_ne_zero [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {yb yy} {P : PtP E p} {π ψ y} (ht : IsTest p Xw yb) (h : HTAt Y r ν yb yy P π ψ y) : evR Xo c s.sig y ≠ 0 := by
  have hZ : LiesOn Z y := fun z => by
    rw [h.2.2.1, Scheme.Hom.comp_apply]
    refine hc.2.2.2.2.2.2.1 _ (ht.2 ⟨z, ?_⟩)
    rw [h.1.1, Scheme.Hom.comp_apply]
  have h1 : evR Xo c s.sig y * evR Xo c s.inv y = 1 := by
    rw [← CompSplitPfB.cspB_evR_mul, s.mul_inv, evR_idem hZ h.2.1]
  exact left_ne_zero_of_mul_eq_one h1

theorem exists_norm (hCov : CoverSt) (hC : ChartSt) (hP : ProjSt) (hLat : LatSt) (hT : HTLocSt) (hG : GenSt) (hEx : ExSt)
    (hLift : LiftSt) (hPt : PtSt) (hGl : GlueSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ))
    (hp : (p : 𝓞 c.F) ∈ la.asIdeal) : ∃ ρ : ℝ, ∀ [Algebra c.F ℂ_[p]] (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
      (y₀ : IntFr Xo c T io), OverLa la T.V io e → algOn Z T io y₀ →
      ∀ (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p]), IsHTFrameCp p y₀ k y →
        evR Xo c s.sig y ≠ 0 ∧ ‖evR Xo c s.sig y‖ = ρ := by
  letI := H.starRing
  have hs : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  obtain ⟨n, hn⟩ := hPt E H Dw τ p hs
  obtain ⟨l', Xo', c', W, Y, r, ν, hle, Xw, hA, hc⟩ := hCov E H Dw l Xo c hL.pos hL.lev hL.good hL.geo Z la p n Fact.out hp
  obtain ⟨N, a, T, S, hTS⟩ := hLat E H Dw l' c' W p Fact.out hc.2.2.1 τ
  have hk : ∀ [Algebra c.F ℂ_[p]] {yb yy} {P : PtP E p} {π ψ y}, IsTest p Xw yb → HTAt Y r ν yb yy P π ψ y →
      ∃ κ ∈ kapSet Y r ν τ.1 s.sig n a T S yb, ‖κ‖ = ‖evR Xo c s.sig y‖ := fun {alg yb yy P π ψ y} ht h => by
    obtain ⟨κ, h1, h2⟩ := hn l l' Xo Xo' c c' W Y r ν hle hc.1 hA N a T S hTS s.sig yb yy P π ψ y h (evR_ne_zero s hc ht h)
    exact ⟨κ, ⟨alg, yy, P, π, ψ, h.1, h2⟩, h1⟩
  have hK : ∀ yb, IsTest p Xw yb → (kapSet Y r ν τ.1 s.sig n a T S yb).Nonempty := fun yb ht => by
    obtain ⟨alg, yy, y, P, π, ψ, h⟩ := hEx E H Dw l l' Xo Xo' c c' W Y r ν hle hL.pos hL.lev hL.good Z la p Xw hc yb ht
    obtain ⟨κ, hκ, -⟩ := hk ht h
    exact ⟨κ, hκ⟩
  obtain ⟨ρ, hρ⟩ := hGl c'.F (c'.V W) p hc.2.2.2.1 Y.X Y.s Xw Y.normal Y.proj Y.flat hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.1 n _
    hK fun z hz => chartAt hC hP hT hG hs hL s hc hA a T S hK hz
  refine ⟨ρ, fun T₀ io e y₀ ho hZ k y hy => ?_⟩
  obtain ⟨yb, yy, ht, P, π, ψ, h⟩ := hLift E H Dw l l' Xo Xo' c c' W Y r ν hle Z la p Xw hc T₀ io e y₀ ho hZ k y hy
  obtain ⟨κ, hκ, h1⟩ := hk ht h
  exact ⟨evR_ne_zero s hc ht h, h1 ▸ hρ yb ht κ hκ⟩

end Top

theorem exists_prime_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ la.asIdeal ∧ ∀ q : ℕ, q.Prime → (q : 𝓞 K) ∈ la.asIdeal → q = p := by
  haveI := la.isPrime
  haveI : Finite (𝓞 K ⧸ la.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ la.ne_bot
  haveI : Nontrivial (𝓞 K ⧸ la.asIdeal) := Ideal.Quotient.nontrivial_iff.2 la.isPrime.ne_top
  have hp : (ringChar (𝓞 K ⧸ la.asIdeal)).Prime := CharP.char_prime_of_ne_zero (𝓞 K ⧸ la.asIdeal) (CharP.ringChar_ne_zero_of_finite _)
  refine ⟨_, hp, Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_natCast]; exact ringChar.Nat.cast_ringChar), fun q hq h => ?_⟩
  have := Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_natCast, ringChar.spec] at this
  exact ((Nat.prime_dvd_prime_iff_eq hp hq).1 this).symm

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

theorem model_of_steps (hCov : CoverSt) (hC : ChartSt) (hP : ProjSt) (hLat : LatSt) (hT : HTLocSt) (hG : GenSt) (hEx : ExSt)
    (hLift : LiftSt) (hPt : PtSt) (hGl : GlueSt) (hPk : PackSt) :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s la
  obtain ⟨p, hp, hm, huniq⟩ := exists_prime_mem la
  haveI := Fact.mk hp
  obtain ⟨ρ, hρ⟩ := exists_norm hCov hC hP hLat hT hG hEx hLift hPt hGl hL s hm
  have hw : ∀ w ∈ htValOn Z la, ∃ z : ℂ_[p], z ≠ 0 ∧ ‖z‖ = ρ ∧
      w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) z := by
    rintro w ⟨T, io, e, y₀, ho, hZ, q, hq, alg, k, y, hy, rfl⟩
    obtain rfl := huniq q hq.out (hy.mem ho)
    exact ⟨_, (hρ T io e y₀ ho hZ k y hy).1, (hρ T io e y₀ ho hZ k y hy).2, rfl⟩
  obtain ⟨z₀, hz₀, h₀⟩ : ∃ z₀ : ℂ_[p], z₀ ≠ 0 ∧ ∀ w ∈ htValOn Z la, ‖z₀‖ = ρ := by
    by_cases h : (htValOn Z la).Nonempty
    · obtain ⟨z, h1, h2, -⟩ := hw _ h.choose_spec
      exact ⟨z, h1, fun _ _ => h2⟩
    · exact ⟨1, one_ne_zero, fun w hw => absurd ⟨w, hw⟩ h⟩
  obtain ⟨O, i1, i2, i3, i4, ϖ, hϖ, Zs, f, D, a1, a2, a3, a4, a5, a6, sig, hsig, φ, hφ, hloc, ybar, y, e, cc, b1, b2, b3, b4,
    b5⟩ := hPk p z₀ hz₀
  have hne : algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ ϖ) ≠ 0 := fun h =>
    hϖ.ne_zero (hφ (by rw [map_zero]; exact Subtype.ext h))
  refine ⟨O, i1, i2, i3, i4, ϖ, hϖ, Zs, f, D, a1, a2, a3, a4, a5, a6, sig, _, hsig, fun w hw' => ⟨p, inferInstance, 𝓞_ℂ_[p],
    inferInstance, inferInstance, φ, PadicComplexInt.integers p, hφ, hloc, ybar, y, e, cc, b1, b2, b3, b4, ?_,
    val_vw_of_ne la p _ hne⟩⟩
  obtain ⟨z, h1, h2, h3⟩ := hw w hw'
  rw [h3, val_vw_of_ne la p _ h1, val_vw_of_ne la p _ cc.ne_zero, coe_valued p z, coe_valued p cc, b5, h₀ w hw', h2]

open Module Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits in

theorem exists_model : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.DeRhamCanonicalExtension →
  GlobalTheory.Published.PrismaticDieudonneHodge →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x →
  ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)),
  ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ) (Zs : Scheme.{0})
    (f : Zs ⟶ Spec (.of O)) (D : LB Zs),
    IsIntegral Zs ∧ (∀ z : Zs, IsIntegrallyClosed (Zs.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧ D.IsLB ∧
    (∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen) ∧
    ∃ (sig : (D.pull (genericι f)).Gen) (κ : ℝ), sig.IsGen ∧
      ∀ w ∈ htValOn Z la, ∃ (p : ℕ) (_ : Fact p.Prime) (R : Type) (_ : CommRing R) (_ : Algebra R ℂ_[p])
        (φ : O →+* R), (Valued.v : Valuation ℂ_[p] NNReal).Integers R ∧ Function.Injective φ ∧ IsLocalHom φ ∧
        ∃ (ybar : Spec (.of R) ⟶ Zs) (y : Spec (.of ℂ_[p]) ⟶ genericFibre f) (e : (D.pull ybar).Gen)
          (cc : ℂ_[p]ˣ),
          ybar ≫ f = Spec.map (CommRingCat.ofHom φ) ∧
          y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R ℂ_[p])) ≫ ybar ∧
          e.IsGen ∧ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord f D sig ybar y e cc ∧
          w s.sig = val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (cc : ℂ_[p]) ∧
          val_vw la p (Valued.v : Valuation ℂ_[p] NNReal) (algebraMap R ℂ_[p] (φ ϖ)) = (κ : EReal) := fun hP h₂ h₃ _ =>
  model_of_steps GlobalTheory.T.cover_statement_holds GlobalTheory.T.chart_statement_holds GlobalTheory.T.projection_statement_holds GlobalTheory.T.lattice_statement_holds (GlobalTheory.T.hodge_tate_local_of_kernel_at_point (GlobalTheory.T.hodge_tate_kernel_at_point hP)) (GlobalTheory.T.generic_statement_of_canonical_extension hP h₂ h₃)
    (GlobalTheory.T.existence_of_comparison GlobalTheory.T.comparison_statement_holds) (GlobalTheory.T.lifting_of_comparison GlobalTheory.T.comparison_statement_holds)
    (GlobalTheory.T.pointwise_of_tate_value_bound (GlobalTheory.T.hodge_tate_kernel_at_point hP) GlobalTheory.T.tate_statement_holds GlobalTheory.T.value_statement_holds GlobalTheory.T.bound_statement_holds)
    (GlobalTheory.T.gluing_of_connectedness (GlobalTheory.T.connectedness_statement_holds hP) GlobalTheory.T.prop_z_statement) GlobalTheory.T.packing_statement_holds

end GlobalTheory.FlatModel

end
