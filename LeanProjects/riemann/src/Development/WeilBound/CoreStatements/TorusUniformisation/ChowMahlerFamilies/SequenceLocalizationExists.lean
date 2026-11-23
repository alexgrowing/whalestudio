import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsHTAtIff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualBC
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsFunctionAtPoint
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.StalkPointFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RangeExtension
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceLocalization

theorem mem_range {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {U : X.Opens} (hU : IsAffineOpen U) {R : Type} [CommRing R] (φ : R →+* Ω) (x : Spec (CommRingCat.of R) ⟶ X)
    (hx : spMap φ ≫ x = ξ) (hxU : ∀ z, x z ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U) (hsub : ∀ a, φ a ∈ regAt ξ q) :
    q.1 ∈ Set.range x :=
  _root_.UpperTheory.Reformulated.B.RangeExtension.mem_range hξ hU φ x hx hxU q hq hsub

theorem isFractionRing {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [Algebra R Ω] (hk : Function.Injective (algebraMap R Ω))
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap (algebraMap R Ω) ≫ x = ξ) (q : Cpt ξ) (hq : q.1 ∈ Set.range x)
    (hsub : ∀ a, algebraMap R Ω a ∈ regAt ξ q) : IsFractionRing R Ω := by
  obtain ⟨P, hP⟩ : ∃ P : PrimeSpectrum R, x P = q.1 := hq
  have hf := GlobalTheory.CompanionTheory.HtLink.regAt_frac hξ hk hx P q hP hsub
  haveI : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2 hk
  refine IsFractionRing.of_field R Ω fun z => ?_
  obtain ⟨u, v, hv, rfl⟩ : ∃ u v : X.presheaf.stalk q.1, genMap ξ q v ≠ 0 ∧ z = genMap ξ q u / genMap ξ q v := by
    obtain ⟨b, c, hc, e⟩ := GlobalTheory.CompanionTheory.Ar.exists_frac_genMap ξ hξ q z
    exact ⟨b, c, hc, eq_div_of_mul_eq hc e⟩
  obtain ⟨s, a, hs, ha⟩ := hf.2 _ ⟨u, rfl⟩
  obtain ⟨t, b, ht, hb⟩ := hf.2 _ ⟨v, rfl⟩
  have h1 := (hf.1 s hs).1
  have h2 := (hf.1 t ht).1
  refine ⟨t * a, s * b, ?_⟩
  rw [map_mul, map_mul, ← ha, ← hb]
  field_simp

end PositivityTheory.Xgn.SequenceLocalization

set_option maxHeartbeats 1600000 in
open PositivityTheory.Xgn.SequenceLocalization in
theorem PositivityTheory.Xgn.sequence_localization_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li)) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ p hp hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ G c' hc' P q hq hO
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.separated
  haveI := 𝔐.t.semi.comm
  haveI := P.fin
  have hn : p ^ 𝔐.R p ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  have hsub : ∀ a : CR O y c', algebraMap (CR O y c') Ω a ∈ regAt 𝔐.ξ q := fun a =>
    GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt O y c' q hq hO a.2
  have hr : q.1 ∈ Set.range P.x := by
    obtain ⟨U, hU, hmem⟩ := 𝔐.tie.affine c' hc'
    exact mem_range hξ hU _ P.x P.x_gen (fun z => (hmem _).2 ⟨𝔐.all _,
      (PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV p hpS A m hpm O G c' hc' P z).1⟩)
      q ((hmem _).2 ⟨q.2, hq⟩) hsub
  haveI : IsFractionRing (CR O y c') Ω := isFractionRing hξ hinj P.x P.x_gen q hr hsub
  let κ : FractionRing (CR O y c') ≃+* Ω := (FractionRing.algEquiv (CR O y c') Ω).toRingEquiv
  have hκ : ∀ a, κ (algebraMap (CR O y c') _ a) = algebraMap (CR O y c') Ω a :=
    (FractionRing.algEquiv (CR O y c') Ω).commutes
  have hκ' : κ.toRingHom.comp (algebraMap (CR O y c') (FractionRing (CR O y c'))) = algebraMap (CR O y c') Ω :=
    RingHom.ext hκ
  have hκf : fracToField (CR O y c') = κ.toRingHom :=
    IsLocalization.ringHom_ext (nonZeroDivisors (CR O y c')) (by
      rw [hκ']
      exact RingHom.ext fun a => IsFractionRing.lift_algebraMap (g := algebraMap (CR O y c') Ω) hinj a)
  have hx' : spMap (κ.toRingHom.comp (algebraMap (CR O y c') (FractionRing (CR O y c')))) ≫ P.x = 𝔐.ξ := by
    rw [hκ', P.x_gen]
  have hsurj : ∀ s : TorsT E (D.p + D.q) (p ^ 𝔐.R p), ∃ v, qmk (p ^ 𝔐.R p) v = s := fun s => by
    choose v hv using fun j => Ideal.Quotient.mk_surjective (Multiplicative.toAdd s j)
    exact ⟨v, congrArg Multiplicative.ofAdd (funext hv)⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {((p ^ 𝔐.R p : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 hn)
  have hom := fun w => GlobalTheory.CompanionTheory.HtLink.mem_omLat_iff 𝔐.M P.M hξ hinj P.x_gen P.toLi P.toLi_pt q hr hsub w
  have h3 : ∀ w ∈ P.Dh.om, w ∈ 𝔐.M.omLat q := by
    rw [P.isHT.1]
    rintro _ ⟨w₀, rfl⟩
    exact (hom _).2 fun b => by rw [P.j_apply]; exact hsub _
  have h4 : ∀ w ∈ 𝔐.M.omLat q, w ∈ Submodule.span (regAt 𝔐.ξ q) (P.Dh.om : Set (Module.Dual Ω 𝔐.Li)) := by
    intro w hw
    obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (CR O y c'), P.x Q = q.1 := hr
    have hf := GlobalTheory.CompanionTheory.HtLink.regAt_frac hξ hinj P.x_gen Q q hQ hsub
    obtain ⟨v, w₀, h1, h2, h3⟩ := GlobalTheory.CompanionTheory.HtLink.clear_denom hinj (regAt 𝔐.ξ q) (fun b hb => by
      obtain ⟨s, a, hs, hsa⟩ := hf.2 b hb
      exact ⟨s, a, (hf.1 s hs).1, (hf.1 s hs).2, hsa⟩) (w.restrictScalars (CR O y c') ∘ₗ P.toLi) ((hom w).1 hw)
    have : w = (⟨_, h2⟩ : regAt 𝔐.ξ q) • P.j w₀ := P.toLi_bc.algHom_ext _ _ fun b => by
      show _ = (algebraMap (CR O y c') Ω v)⁻¹ * P.j w₀ (P.toLi b)
      rw [P.j_apply, h3, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
      rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by rw [P.isHT.1]; exact ⟨w₀, rfl⟩))
  have h5 : ∀ z w', 𝔐.M.IsHTAt 𝔐.t.PP.L (p ^ 𝔐.R p) (G.t₂.pt (qmk _ z)) q w' ↔
      ∃ v ∈ 𝔐.M.omLat q, w' = P.Dh.h z + (p ^ 𝔐.R p) • v := by
    intro z w'
    obtain ⟨χ, w₀, hχ, hh, hHT⟩ := P.isHT.2.2 z
    refine GlobalTheory.CompanionTheory.HtLink.isHTAt_iff GlobalTheory.T.lie_model_finite_base_change GlobalTheory.T.section_eq_zero_of_values hξ 𝔐.t.PP.L hn (𝔐.tors p hpS) 𝔐.M P.x κ hx' P.Γ₂
      P.i₂ P.tors₂ P.M P.toLi (by rw [hκ']; exact P.toLi_pt) _ χ w₀ _ (fun s k _ _ a xk gk u h1 h2 => ?_) hHT
      (fun b => by rw [hh, P.j_apply, hκ]) q hr (fun a => by rw [hκ]; exact hsub a) w'
    obtain ⟨z', rfl⟩ := hsurj s
    have e1 : χ (qmk (p ^ 𝔐.R p) z') = P.ζ ^ (P.Dh.e z z').val := hχ z'
    have e2 := G.weil z z' k a xk gk u h1 (by rw [h2, P.pts₂, hκf])
    have e3 : κ (algebraMap (CR O y c') _ (χ (qmk (p ^ 𝔐.R p) z') : CR O y c')) = G.ζ ^ (G.e z z').val := by
      rw [e1, hκ, P.Dh_e, Units.val_pow_eq_pow_val, ← P.ζ_eq, map_pow (algebraMap (CR O y c') Ω)]
      rfl
    rw [e3, Nat.cast_pow]
    exact e2
  have hpow : ∀ w : Module.Dual Ω 𝔐.Li, ((p : CR O y c') ^ 𝔐.R p) • w = (p ^ 𝔐.R p) • w := fun w => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hmem : ∀ z, ∀ v ∈ 𝔐.M.omLat q, P.Dh.h z + (p ^ 𝔐.R p) • v ∈ HT.omP 𝔐 p q := fun z v hv =>
    Submodule.subset_span ⟨_, (G.t₂.onto _).2 ⟨_, rfl⟩, (h5 z _).2 ⟨v, hv, rfl⟩⟩
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun w hw => ?_)
  · rintro w ⟨g, hg, hw⟩
    obtain ⟨s, rfl⟩ := (G.t₂.onto g).1 hg
    obtain ⟨z, rfl⟩ := hsurj s
    obtain ⟨v, hv, rfl⟩ := (h5 z w).1 hw
    refine add_mem (Submodule.subset_span (Submodule.mem_sup_left (Submodule.subset_span ⟨z, rfl⟩))) ?_
    replace hv := h4 v hv
    clear hw
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (Submodule.mem_sup_right ⟨v, hv, hpow v⟩)
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ _ h
  · obtain ⟨w₁, hw₁, _, ⟨w₂, hw₂, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hw
    refine add_mem ?_ ?_
    · clear hw
      induction hw₁ using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨z, rfl⟩ := hv
        have := hmem z 0 (zero_mem _)
        rwa [smul_zero, add_zero] at this
      | zero => exact zero_mem _
      | add v v' _ _ h h' => exact add_mem h h'
      | smul r v _ h => exact Submodule.smul_mem (HT.omP 𝔐 p q) ⟨_, hsub r⟩ h
    · have := hmem 0 w₂ (h3 w₂ hw₂)
      rw [map_zero, zero_add, ← hpow] at this
      exact this
