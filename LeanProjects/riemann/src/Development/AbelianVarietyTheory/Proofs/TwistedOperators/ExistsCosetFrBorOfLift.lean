import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetOfSelfDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKerLatticeBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSimilitudeTriangularPeriodsOfHeckePoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection

set_option autoImplicit false

noncomputable section

section Adelic

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckePointIdent

set_option maxHeartbeats 800000 in

theorem levG_cong {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0)
    (i : Fin D.R.m) (κ : GA D (Wc D i)) (hκ : κ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) :
    ∀ z ∈ latHat (Wc D i), ∃ y ∈ latHat (Wc D i),
      (finHom (Wc D i) κ).1.mulVec z - z = (D.host.g 0 * D.host.g 1) • y := by
  have hκ' : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 κ :=
    ⟨hκ.1, hκ.2.1, Subgroup.mem_bot.1 hκ.2.2⟩
  obtain ⟨-, h2, h3⟩ := (GlobalTheory.LiftLevel.isLift_one_iff (R.βW i) (R.datWp i R.triv)
    (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).le rfl κ).1 hκ'
  have hβ := hL.βW i
  have hfr := hβ.choose_spec.1
  have hsd := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβ
  have hred : ∀ PP : Pl D.host.E, Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)} ≤ PP.asIdeal →
      redFn (R.βW i) PP (Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul] at hP
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rcases PP.isPrime.mem_or_mem hP with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    rcases GlobalTheory.StepLaw.div_or_isConjPl_div D R.C.P k PP hk with h | ⟨PP', h, hc⟩
    · exact h3 PP ((hL.Pg PP).2 ⟨k, h⟩)
    · exact GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj D _ _ hsd _ hfr κ h2 PP PP' hc (h3 PP' ((hL.Pg PP').2 ⟨k, h⟩))
  intro z hz
  obtain ⟨w, hw, e⟩ := GlobalTheory.LiftLevel.cong_of_redFn' hfr h2 (GlobalTheory.CoverHalf.squarefree_span_g D) (J := ⊤)
    (Ideal.mul_top _) hred (b := 1) Submodule.mem_top _ ((GlobalTheory.LiftLevel.latHat_iff_frame hβ z).1 hz)
  simp only [map_one, OneMemClass.coe_one, one_mul] at e
  obtain ⟨y, rfl⟩ := GlobalTheory.LiftLevel.swap_surj w
  exact ⟨y, (GlobalTheory.LiftLevel.latHat_iff_frame hβ y).2 hw, (GlobalTheory.LiftLevel.swap_cong_iff _ κ _ _ y).2 e⟩

theorem nsmul_mem_latGHat {D : D7} (V : HSp D) (p : ℕ) (g g' : GA D V) (h : ∀ v ∈ latG V g, p • v ∈ latG V g') :
    ∀ z ∈ latGHat V g, p • z ∈ latGHat V g' := by
  intro z hz
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1] at hz
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g').2.2.2.2.1]
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, p • x, h x hx, ?_⟩
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, TensorProduct.tmul_smul]
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem smul_mulVec_eq {A : Type} [CommRing A] {n : ℕ} (k : Matrix (Fin n) (Fin n) A) (a : A)
    (h : ∀ i j, a * (k - 1) i j = (k - 1) i j) (u : Fin n → A) : (1 - a) • (k *ᵥ u) = (1 - a) • u := by
  rw [← sub_eq_zero, ← smul_sub]
  have : k *ᵥ u - u = (k - 1) *ᵥ u := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [this]
  funext i
  rw [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [← mul_assoc, sub_mul, h, one_mul, sub_self, zero_mul]

theorem map_sub_one {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (k : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    f ((k - 1) i j) = (k.map f - 1) i j := by
  rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 800000 in

theorem exists_split_of_suppAt {D : D7} (V : HSp D) {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {a : GA D V} (ha : SuppAt e V a) {M : ℕ} (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ c d : Af D.host.F, (∀ v, c v ∈ v.adicCompletionIntegers D.host.F) ∧ (∀ v, d v ∈ v.adicCompletionIntegers D.host.F) ∧
      c + M * d = 1 ∧ ∀ u : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E,
        (c ⊗ₜ[D.host.F] (1 : D.host.E)) • ((finHom V a).1 *ᵥ u) = (c ⊗ₜ[D.host.F] (1 : D.host.E)) • u := by
  obtain ⟨v, ε, hε, h3⟩ := he.1.2.2
  have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D e P v ε he hε h3
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have hMv : (M : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro h
    apply hM
    rw [← hv] at h
    have h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (M : 𝓞 D.host.F) ∈ P.asIdeal := h
    rwa [map_natCast] at h'
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hMv
    have : M = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
    exact zero_mem _
  refine ⟨1 - α, α * algebraMap D.host.F (Af D.host.F) (M : D.host.F)⁻¹, fun w => ?_, fun w => ?_, ?_, fun u => ?_⟩
  · show evalV D.host.F w (1 - α) ∈ _
    rw [map_sub, map_one]
    by_cases hw : w = v
    · subst hw
      rw [h1, sub_self]; exact zero_mem _
    · rw [h0 w hw, sub_zero]; exact one_mem _
  · show evalV D.host.F w (α * algebraMap D.host.F (Af D.host.F) (M : D.host.F)⁻¹) ∈ _
    rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
      have e1 : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (M : D.host.F)⁻¹) =
          w.valuation D.host.F (M : D.host.F)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      have e2 : w.valuation D.host.F (M : D.host.F) = 1 := by
        have := (HeightOneSpectrum.valuation_eq_one_iff_notMem w (K := D.host.F) (r := (M : 𝓞 D.host.F))).2 hMv
        rwa [map_natCast] at this
      exact (e1.trans (by rw [map_inv₀, e2, inv_one])).le
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  · rw [mul_left_comm, ← map_natCast (algebraMap D.host.F (Af D.host.F)), ← map_mul, mul_inv_cancel₀ hM0, map_one, mul_one,
      sub_add_cancel]
  · have hent : ∀ i j, (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((finHom V a).1 - 1) i j = ((finHom V a).1 - 1) i j := by
      intro i j
      have h4 := congrArg (finPart D) (ha i j)
      rw [h3, (finPart D).map_mul, map_sub_one (finPart D)] at h4
      exact h4
    have := smul_mulVec_eq _ _ hent u
    rw [TensorProduct.sub_tmul]
    exact this

set_option maxHeartbeats 800000 in

theorem mark_keep {D : D7} (V : HSp D) {e : AE D} {P : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e P)
    {a a₀ : GA D V} (ha : SuppAt e V a₀) {M p p' : ℕ} (hp : (p : 𝓞 D.host.E) ∈ P.asIdeal) (hpp : p * p' ≡ 1 [MOD M])
    (hκ : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V (a⁻¹ * a₀)).1.mulVec z - z = M • y) (g : GA D V)
    (hlat : latG V (g * a₀) = latG V (g * a)) (hincl : ∀ v ∈ latG V g, p • v ∈ latG V (g * a))
    (y x w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hy : y ∈ latGHat V 1)
    (hx : ∃ x₁ ∈ latGHat V g, x - (finHom V g).1 *ᵥ y = M • x₁)
    (hw : ∃ w₁ ∈ latGHat V (g * a), w - (finHom V (g * a)).1 *ᵥ y = M • w₁) :
    ∃ s ∈ latGHat V (g * a), w - (p * p') • x = M • s := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (1 : ℤ) - (p * p' : ℕ) = M * n := (Nat.modEq_iff_dvd.1 hpp)
  have hM : (M : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have e1 : (1 : 𝓞 D.host.E) = p * p' + M * n := by
      have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hn
      push_cast at this
      linear_combination this
    rw [e1]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_right _ hp) (P.asIdeal.mul_mem_right _ h)
  obtain ⟨c, d, hc, hd, hcd, hca⟩ := exists_split_of_suppAt V he ha hM
  obtain ⟨x₁, hx₁, ex⟩ := hx
  obtain ⟨w₁, hw₁, ew⟩ := hw
  have hsm : ∀ (b : Af D.host.F), (∀ v, b v ∈ v.adicCompletionIntegers D.host.F) → ∀ z ∈ latGHat V 1,
      (b ⊗ₜ[D.host.F] (1 : D.host.E)) • z ∈ latGHat V 1 := by
    intro b hb z hz
    rw [(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at hz ⊢
    exact GlobalTheory.Member.AALev.hat_smul_adele _ b hb hz
  have hP := nsmul_mem_latGHat V p g (g * a) hincl
  have hP₀ := nsmul_mem_latGHat V p g (g * a₀) (hlat ▸ hincl)
  have hlin : ∀ (k : GA D V) (m : ℕ) z, (finHom V k).1 *ᵥ (m • z) = m • (finHom V k).1 *ᵥ z := fun k m z =>
    map_nsmul (finHom V k).1.mulVecLin.toAddMonoidHom m z
  obtain ⟨u, hu, eu⟩ := ((GlobalTheory.MarkCoset.latG_spec D V (g * a₀)).2 _).1
    (hP₀ _ (((GlobalTheory.MarkCoset.latG_spec D V g).2 _).2 ⟨y, hy, rfl⟩))
  have eu' : (finHom V a₀).1 *ᵥ u = p • y := by
    have := congrArg (fun z => (finHom V g⁻¹).1 *ᵥ z) eu
    simp only [← hlin, ← GlobalTheory.Member.LatMove.fin_mul, inv_mul_cancel_left, inv_mul_cancel,
      GlobalTheory.Member.LatMove.fin_one] at this
    exact this
  obtain ⟨s, hs, es⟩ := GlobalTheory.MarkCoset.level_latGHat V M _ hκ u hu
  have hcu : (c ⊗ₜ[D.host.F] (1 : D.host.E)) • u = (c ⊗ₜ[D.host.F] (1 : D.host.E)) • (p • y) := by rw [← eu', hca]
  have hone : (c ⊗ₜ[D.host.F] (1 : D.host.E)) + (M : Af D.host.F ⊗[D.host.F] D.host.E) * (d ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    have := congrArg (Algebra.TensorProduct.includeLeftRingHom (R := D.host.F) (A := Af D.host.F) (B := D.host.E)) hcd
    rwa [map_add, map_mul, map_natCast, map_one] at this
  have hn' : (1 : Af D.host.F ⊗[D.host.F] D.host.E) - p * p' = M * n := by
    have := congrArg (Int.cast : ℤ → Af D.host.F ⊗[D.host.F] D.host.E) hn
    push_cast at this
    exact this
  obtain ⟨r, hr, er⟩ : ∃ r ∈ latGHat V 1, y - p' • u = M • r := by
    refine ⟨n • (c ⊗ₜ[D.host.F] (1 : D.host.E)) • y + (d ⊗ₜ[D.host.F] (1 : D.host.E)) • (y - p' • u),
      add_mem (zsmul_mem (hsm c hc y hy) n) (hsm d hd _ (sub_mem hy (nsmul_mem hu p'))), ?_⟩
    generalize (c ⊗ₜ[D.host.F] (1 : D.host.E)) = C at *
    generalize (d ⊗ₜ[D.host.F] (1 : D.host.E)) = Dd at *
    funext i
    have h1 := congrFun hcu i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, nsmul_eq_mul, zsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply, Pi.intCast_apply] at h1 ⊢
    linear_combination (-(y i - p' * u i)) * hone + (C * y i) * hn' - p' * h1
  have e1 : (finHom V (g * a)).1 *ᵥ (u + M • s) = p • (finHom V g).1 *ᵥ y := by
    rw [← es, ← GlobalTheory.Member.LatMove.fin_mul, mul_assoc, mul_inv_cancel_left, eu]
  refine ⟨w₁ + (finHom V (g * a)).1 *ᵥ (r - p' • s) - p' • p • x₁, sub_mem (add_mem hw₁
    (((GlobalTheory.MarkCoset.latG_spec D V (g * a)).2 _).2 ⟨_, sub_mem hr (nsmul_mem hs p'), rfl⟩)) (nsmul_mem (hP _ hx₁) p'), ?_⟩
  have e2 : (finHom V (g * a)).1 *ᵥ y - p' • (finHom V (g * a)).1 *ᵥ u = M • (finHom V (g * a)).1 *ᵥ r := by
    rw [← hlin, ← hlin, ← er, Matrix.mulVec_sub]
  rw [Matrix.mulVec_add, hlin] at e1
  rw [Matrix.mulVec_sub, hlin, sub_eq_iff_eq_add.1 ex, sub_eq_iff_eq_add.1 ew, sub_eq_iff_eq_add.1 e2,
    eq_sub_of_add_eq e1]
  module

end GlobalTheory.HeckePointIdent

end Adelic

section Family

open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G
  ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.HeckePointIdent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem frBor_one_of_eq {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x)
    (hu : y'.u = y.u) : ∃ t : Ix Dw → Sˣ, (∀ j, j ≠ none → t j = 1) ∧ FrBor t y y' := by
  classical
  obtain ⟨t, h1, -, h3⟩ := GlobalTheory.CongrOrbit.frBor_of_eq y y' hx hu
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu' : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  refine ⟨fun o => match o with
    | none => t none
    | some _ => 1, fun j hj => ?_, h1,
      fun τ i => ⟨Pi.single i 1, by simp, fun j hj => Pi.single_eq_of_ne hj.ne' _, ?_⟩, h3⟩
  · cases j with
    | none => exact absurd rfl hj
    | some _ => rfl
  · rw [hu, hu' τ, hcomb]
    simp [Pi.single_apply]

set_option maxHeartbeats 800000 in

theorem exists_lift_all {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (i j : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (P' : (F.Di j).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di j) ty P') {𝔓 : Ideal (𝓞 E)} {p k : ℕ}
    (hp : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p)
    {y y'' : Sp ℂ ⟶ Xo.X} (hy : y = F.u i P) (hy'' : y'' = F.u j P') (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G))
    (ψ : pullback Xo.univ.t.G.hom y ⟶ pullback Xo.univ.t.G.hom y'')
    (ψp : (Over.mk y ⟶ Xo.univ.t.G) →* (Over.mk y'' ⟶ Xo.univ.t.G))
    (hK : Xo.univ.t.HeckeKer (Over.mk y) Dw 𝔓 p k C) (hI : IsHkIsog p y y'' C ψ ψp) :
    ∃ (gam : (F.Di i).La →ₗ[𝓞 E] (F.Di j).La) (θ : (F.Di j).La →ₗ[𝓞 E] (F.Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a, θ (gam a) = (p ^ 2) • a) ∧ (∀ a b, (F.Di i).EF (θ a) (θ b) = (p : ℤ) ^ 2 * (F.Di j).EF a b) ∧
      (∀ b, h (P (θ b)) = (p ^ 2) • P' b) ∧
      ((Ideal.span {(p : 𝓞 E)} * 𝔓) • (⊤ : Submodule (𝓞 E) (F.Di i).La) ≤ LinearMap.range θ ∧
        𝔓.map (H.bar : 𝓞 E →+* 𝓞 E) • LinearMap.range θ ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La) ∧
        Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)) ⧸
          (LinearMap.range θ).comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) (F.Di i).La)).subtype) =
            Ideal.absNorm 𝔓 ^ k) ∧
      (∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ x, F.t j a = gam (F.t i (p' • a)) + l.M • x) ∧
      ∀ (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ pullback Xo.univ.t.G.hom y),
        v ≫ pullback.snd _ _ = spMap (algebraMap ℂ (DualNumber ℂ)) →
        IsDerivAt0 (fun z => (F.ex i P z).left) w (v ≫ pullback.fst _ _) →
        IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) (v ≫ ψ ≫ pullback.fst _ _) := by
  subst hy hy''
  have hpp : p.Prime := hp.2.2.2.1
  have hC : ∀ a ∈ C, a ^ p ^ 2 = 1 := fun a ha => GlobalTheory.HkPts.pow_eq_one hp.2.2.2.2 hK ha
  obtain ⟨gam, h, h1, h2, h3, h4, h5, -⟩ := GlobalTheory.HeckeKerLat.exists_lift_ker _ H Dw l Xo σ' g ty F i j P P' p C ψ ψp
    hP hP' hpp hC hI
  have hinj : Function.Injective gam := fun a b e => hP.2.1 (h.injective (by rw [← h2, ← h2, e]))
  choose θ₀ hθ₀ using h3
  let θ : (F.Di j).La →ₗ[𝓞 E] (F.Di i).La :=
    { toFun := θ₀
      map_add' := fun a b => hinj (by rw [map_add, hθ₀, hθ₀, hθ₀, smul_add])
      map_smul' := fun s a => hinj (by rw [map_smul, hθ₀, hθ₀, smul_comm]; rfl) }
  have hθ : ∀ b, gam (θ b) = (p ^ 2) • b := hθ₀
  have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hpp.ne_zero)
  refine ⟨gam, θ, h, fun a => hinj (by rw [hθ, map_nsmul]), fun a b => ?_, fun b => by rw [← h2, hθ, map_nsmul],
    GlobalTheory.heckeKer_lattice_bounds E H Dw l Xo σ' g ty F i P 𝔓 p k C _ hP hp hK fun a => (h5 a).trans
      ⟨fun ⟨b, hb⟩ => ⟨b, hinj (by rw [hθ, hb])⟩, fun ⟨b, hb⟩ => ⟨b, by rw [← hb, hθ]⟩⟩,
    fun p' hp' a ha => ?_, fun w v hvs hd => ?_⟩
  · apply mul_left_cancel₀ hp0
    rw [← h1, hθ, hθ, map_nsmul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  · have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    refine (GlobalTheory.UnifPoint.div_eq_iff hP'.2.1 (F.ex_add j P' hP') (F.ex_ker j P' hP') hM0 _ _).1 ?_
    rw [← F.ex_eta j P' hP' a ha, ← (hI.2.2.2.2.2.2.2 p' hp' a).1, F.ex_eta i P hP _ (nsmul_mem ha p'), ← h4, h2,
      map_smul h]
  · have hfst : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ pullback.fst _ _ = (F.ex i P z).left := fun z =>
      pullback.lift_fst _ _ _
    have d0 : IsDerivAt0 (fun z => fibPt Xo.univ.t.G (F.ex i P z)) w v := by
      refine FibreDeriv.isDerivAt0_of_isPullback (IsPullback.of_hasPullback Xo.univ.t.G.hom (F.u i P))
        (fun z => pullback.lift_snd _ _ _) ?_ hvs ?_
      · convert ExpChain.isHolTo_ex F i P hP using 2 with z
        exact hfst z
      · convert hd using 2 with z
        exact hfst z
    have d1 := FibreDeriv.isDerivAt0_comp d0 (ψ ≫ pullback.fst _ _)
    have e1 : ∀ z, fibPt Xo.univ.t.G (F.ex i P z) ≫ ψ ≫ pullback.fst _ _ = (F.ex j P' (h z)).left := fun z => by
      rw [← Category.assoc, hI.2.2.1, h4]
      exact pullback.lift_fst _ _ _
    simp only [e1] at d1
    exact (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F j P' hP') h.toLinearMap w _).1 d1

theorem point_deriv_eq {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty)
    (hr : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty) (hA : l.A = 1)
    {j m : Fin F.n} {P' : (F.Di j).La →+ (Fin g → ℂ)} {Pa : (F.Di m).La →+ (Fin g → ℂ)}
    (hP' : IsPeriod (F.Di j) ty P') (hPa : IsPeriod (F.Di m) ty Pa) {p : ℕ} (hp : p ≠ 0)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gm : (F.Di j).La ≃ₗ[𝓞 E] (F.Di m).La)
    (hEF : ∀ a b, (F.Di m).EF (gm a) (gm b) = (F.Di j).EF a b)
    (hM : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gm (F.t j a) = F.t m a + l.M • x)
    (hper : ∀ b, h (p • Pa (gm b)) = (p ^ 2) • P' b) :
    F.u j P' = F.u m Pa ∧ ∀ w v v', IsDerivAt0 (fun z => (F.ex j P' z).left) (h w) v →
      IsDerivAt0 (fun z => (F.ex m Pa z).left) w v' → spMap (epsMul ((p : ℂ)⁻¹)) ≫ v = v' := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
  let L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := h.symm.trans (LinearEquiv.smulOfNeZero ℂ _ (p : ℂ) hp0)
  have hL : ∀ z, L z = (p : ℂ) • h.symm z := fun z => rfl
  obtain ⟨k₁, k₂⟩ := GlobalTheory.ArcCM.point_exp_eq_of_isometry GlobalTheory.ArcCM.known_holds E H Dw l Xo σ' g ty F j m P' Pa gm L
    hr hσ hty hA hP' hPa hEF hM fun b => by
      rw [hL]
      apply h.injective
      apply smul_right_injective _ hp0
      have := hper b
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at this
      show (p : ℂ) • h (Pa (gm b)) = (p : ℂ) • h ((p : ℂ) • h.symm (P' b))
      rw [this, map_smul, h.apply_symm_apply, smul_smul]
      push_cast
      rw [sq]
  refine ⟨k₁, fun w v v' d d' => ?_⟩
  have d1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_smul d ((p : ℂ)⁻¹)
  simp only [← k₂] at d1
  have d2 := (ExpChain.isDerivAt0_comp_linear _ (ExpChain.isHolTo_ex F m Pa hPa) L.toLinearMap _ _).1 d1
  have e : L.toLinearMap ((p : ℂ)⁻¹ • h w) = w := by
    show L _ = w
    rw [hL, map_smul, h.symm_apply_apply, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  rw [e] at d2
  exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F _ Pa hPa).2.1 _).unique d2 d'

def trForm {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (ξ : E) : (Fin n → E) →+ (Fin n → E) →+ ℚ :=
  AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (fun y => Algebra.trace ℚ E (ξ * herm G v y)) fun y y' => by
      rw [← map_add, ← mul_add]
      congr 2
      simp [herm, cc, mul_add, Finset.sum_add_distrib]) fun v v' => by
    ext y
    show Algebra.trace ℚ E _ = Algebra.trace ℚ E _ + Algebra.trace ℚ E _
    rw [← map_add, ← mul_add]
    congr 2
    simp [herm, add_mul, Finset.sum_add_distrib]

theorem trForm_apply {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (ξ : E) (v y : Fin n → E) :
    trForm G ξ v y = Algebra.trace ℚ E (ξ * herm G v y) := rfl

set_option maxHeartbeats 800000 in

theorem exists_quot_lattice {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (ξ : E) (A A' : Datum H)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (φ : A.La ≃ₗ[𝓞 E] Λ)
    (hE : ∀ a b, ((A.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm G (φ a : Fin n → E) (φ b)))
    (hsd : ∀ v : Fin n → E, (∀ y ∈ Λ, ∃ m : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = m) ↔ v ∈ Λ)
    {p : ℕ} (hp : p ≠ 0) (gam : A.La →ₗ[𝓞 E] A'.La) (θ : A'.La →ₗ[𝓞 E] A.La) (hθ : ∀ a, θ (gam a) = (p ^ 2) • a)
    (hEF : ∀ a b, A.EF (θ a) (θ b) = (p : ℤ) ^ 2 * A'.EF a b) (P Q : Ideal (𝓞 E)) (N : ℕ)
    (h1 : (Ideal.span {(p : 𝓞 E)} * P) • (⊤ : Submodule (𝓞 E) A.La) ≤ LinearMap.range θ)
    (h2 : Q • LinearMap.range θ ≤ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) A.La))
    (h3 : Nat.card (↥(Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) A.La)) ⧸
      (LinearMap.range θ).comap (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) A.La)).subtype) = N) :
    ∃ j : A'.La →ₗ[𝓞 E] (Fin n → E), Function.Injective j ∧ (∀ b, p • j b = (φ (θ b) : Fin n → E)) ∧
      (∀ a, j (gam a) = p • (φ a : Fin n → E)) ∧
      (∀ a b, ((A'.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm G (j a) (j b))) ∧
      P • Λ ≤ LinearMap.range j ∧ Q • LinearMap.range j ≤ Λ ∧
      (∀ v : Fin n → E, (∀ y ∈ LinearMap.range j, ∃ m : ℤ, Algebra.trace ℚ E (ξ * herm G v y) = m) ↔
        v ∈ LinearMap.range j) ∧
      (LinearMap.range j ⊓ Λ).toAddSubgroup.relIndex Λ.toAddSubgroup = N := by
  have hp0 : (p : E) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hpQ : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp
  let j : A'.La →ₗ[𝓞 E] (Fin n → E) := (p : E)⁻¹ • (Λ.subtype ∘ₗ φ.toLinearMap ∘ₗ θ)
  have hj : ∀ b, p • j b = (φ (θ b) : Fin n → E) := fun b => by
    show p • ((p : E)⁻¹ • (φ (θ b) : Fin n → E)) = _
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  have hc : ∀ {u v : Fin n → E}, p • u = p • v → u = v := fun {u v} h => by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at h
    exact smul_right_injective _ hp0 h
  have hφn : ∀ (m : ℕ) a, (φ (m • a) : Fin n → E) = m • (φ a : Fin n → E) := fun m a => by rw [map_nsmul]; rfl
  have hφs : ∀ (s : 𝓞 E) a, (φ (s • a) : Fin n → E) = s • (φ a : Fin n → E) := fun m a => by rw [map_smul]; rfl
  have hps : ∀ a : A.La, (p : 𝓞 E) • a = p • a := fun a => Nat.cast_smul_eq_nsmul _ _ _
  have hjg : ∀ a, j (gam a) = p • (φ a : Fin n → E) := fun a => hc (by rw [hj, hθ, hφn, smul_smul, sq])
  have hiso : ∀ a b, ((A'.EF a b : ℤ) : ℚ) = trForm G ξ (j a) (j b) := fun a b => by
    have e := hE (θ a) (θ b)
    rw [hEF, ← trForm_apply, ← hj, ← hj, map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, nsmul_eq_mul] at e
    push_cast at e
    apply mul_left_cancel₀ (pow_ne_zero 2 hpQ)
    rw [e]; ring
  have hmemp : ∀ a : A.La, a ∈ Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) A.La) ↔ ∃ b, p • b = a := fun a => by
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨b, _, e⟩ => ⟨b, (hps b).symm.trans e⟩, fun ⟨b, e⟩ => ⟨b, trivial, (hps b).trans e⟩⟩
  have hrange : ∀ a, (φ a : Fin n → E) ∈ LinearMap.range j ↔ p • a ∈ LinearMap.range θ := fun a =>
    ⟨fun ⟨b, e⟩ => ⟨b, φ.injective (Subtype.ext (by rw [← hj, e, hφn]))⟩,
      fun ⟨b, e⟩ => ⟨b, hc (by rw [hj, e, hφn])⟩⟩
  refine ⟨j, fun a b e => ?_, hj, hjg, hiso, ?_, ?_, fun v => ⟨fun hv => ?_, ?_⟩, ?_⟩
  · apply A'.unimod.1
    ext x
    have : ((A'.EF a x : ℤ) : ℚ) = A'.EF b x := by rw [hiso, hiso, e]
    exact_mod_cast this
  · refine Submodule.smul_le.2 fun s hs v hv => ?_
    obtain ⟨a, ha⟩ := φ.surjective ⟨v, hv⟩
    rw [show v = (φ a : Fin n → E) by rw [ha], ← hφs, hrange, ← hps, smul_smul]
    exact h1 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hs) Submodule.mem_top)
  · refine Submodule.smul_le.2 fun s hs v ⟨b, hb⟩ => ?_
    obtain ⟨a, ha⟩ := (hmemp _).1 (h2 (Submodule.smul_mem_smul hs (LinearMap.mem_range_self θ b)))
    have : s • v = (φ a : Fin n → E) := hc (by rw [← hφn, ha, hφs, ← hj, hb, smul_comm])
    rw [this]
    exact (φ a).2
  · choose f hf using fun b => hv (j b) (LinearMap.mem_range_self j b)
    have hf' : ∀ b, (f b : ℚ) = trForm G ξ v (j b) := fun b => (hf b).symm
    let f' : A'.La →+ ℤ := AddMonoidHom.mk' f fun a b => by
      have : ((f (a + b) : ℤ) : ℚ) = f a + f b := by rw [hf', hf', hf', map_add, map_add]
      exact_mod_cast this
    obtain ⟨b₀, hb₀⟩ := A'.unimod.2 f'.toIntLinearMap
    have hz : ∀ a, trForm G ξ (v - j b₀) (φ a : Fin n → E) = 0 := fun a => by
      apply mul_left_cancel₀ hpQ
      rw [mul_zero, ← nsmul_eq_mul, ← map_nsmul, ← hjg, map_sub, AddMonoidHom.sub_apply, ← hf', ← hiso, hb₀]
      exact sub_self _
    have hm : v - j b₀ ∈ Λ := (hsd _).1 fun y hy => by
      obtain ⟨a, ha⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨0, by rw [show y = (φ a : Fin n → E) by rw [ha], Int.cast_zero]; exact hz a⟩
    obtain ⟨a₀, ha₀⟩ := φ.surjective ⟨_, hm⟩
    have e0 : v - j b₀ = (φ a₀ : Fin n → E) := by rw [ha₀]
    have : a₀ = 0 := by
      apply A.unimod.1
      ext x
      have : ((A.EF a₀ x : ℤ) : ℚ) = 0 := by rw [hE, ← e0]; exact hz x
      rw [map_zero]
      exact_mod_cast this
    rw [this, map_zero] at e0
    exact ⟨b₀, (sub_eq_zero.1 e0).symm⟩
  · rintro ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨_, (hiso a b).symm⟩
  · let f : A.La →+ (Fin n → E) := (Λ.subtype ∘ₗ φ.toLinearMap).toAddMonoidHom
    let m : A.La →+ A.La := nsmulAddMonoidHom p
    have e1 : Λ.toAddSubgroup = (⊤ : AddSubgroup A.La).map f := by
      ext v
      exact ⟨fun hv => ⟨φ.symm ⟨v, hv⟩, trivial, congrArg Subtype.val (φ.apply_symm_apply ⟨v, hv⟩)⟩,
        fun ⟨a, _, e⟩ => e ▸ (φ a).2⟩
    have e2 : (Ideal.span {(p : 𝓞 E)} • (⊤ : Submodule (𝓞 E) A.La)).toAddSubgroup = (⊤ : AddSubgroup A.La).map m := by
      ext v
      exact (hmemp v).trans ⟨fun ⟨b, e⟩ => ⟨b, trivial, e⟩, fun ⟨b, _, e⟩ => ⟨b, e⟩⟩
    have e3 : (LinearMap.range j ⊓ Λ).toAddSubgroup.comap f = (LinearMap.range θ).toAddSubgroup.comap m := by
      ext a
      exact ⟨fun h => (hrange a).1 h.1, fun h => ⟨(hrange a).2 h, (φ a).2⟩⟩
    rw [e1, ← AddSubgroup.relIndex_comap, e3, AddSubgroup.relIndex_comap, ← e2, ← h3]
    rfl

end GlobalTheory.HeckePointIdent

end Family

section Point

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open Formalism.IndefR.FWT (castDict)
open scoped TensorProduct Matrix MonObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.HeckeEx.fieldCAt GlobalTheory.HeckeEx.algClosedCAt

namespace GlobalTheory.HeckePointIdent

set_option maxHeartbeats 1600000 in

theorem exists_frBor_of_dictLat {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {V W : HSp D} (hV : V = W)
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (hr : V.rank = r) {U : Unf Xo c σ r}
    {dict : GA D V → Σ k, Frame (U.X k).Ψ r} (io : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hio : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io))
    (hL : DictLat U V hr dict (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ io) e F ik φ th x₀)
    (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) (hdom : ∀ h, (dict h).2 ∈ (U.X (dict h).1).dom)
    {𝔓 : Ideal (𝓞 D.host.E)} {p k : ℕ} (hp : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l 𝔓 p) (Rc : Finset (GA D W))
    (hcos : ∀ (g : GA D W) (L' : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)),
      𝔓 • latG W g ≤ L' → 𝔓.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • L' ≤ latG W g →
      (∀ v : Fin W.rank → D.host.E, (∀ y ∈ L', ∃ n : ℤ,
        Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-W.gram.transpose) v y) = n) ↔ v ∈ L') →
      (L' ⊓ latG W g).toAddSubgroup.relIndex (latG W g).toAddSubgroup = Ideal.absNorm 𝔓 ^ k →
      ∃ a ∈ Rc, latG W (g * a) = L' ∧ a ∈ GfC W ∧ ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M] →
        ∀ y x w : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E, y ∈ latGHat W 1 →
          (∃ x₁ ∈ latGHat W g, x - (finHom W g).1 *ᵥ y = l.M • x₁) →
          (∃ w₁ ∈ latGHat W (g * a), w - (finHom W (g * a)).1 *ᵥ y = l.M • w₁) →
          ∃ s ∈ latGHat W (g * a), w - (p * p') • x = l.M • s)
    (h : GA D W) (hx : (castDict hV dict h).2 ∈ (U.X (castDict hV dict h).1).dom)
    (C : Subgroup (Over.mk (U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).x ⟶ Xo.univ.t.G))
    (hK : Xo.univ.t.HeckeKer (Over.mk (U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).x) Dw 𝔓 p k C)
    (z : FrPt Xo c (CAt σ))
    (ψ : pullback Xo.univ.t.G.hom (U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).x ⟶
      pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk (U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).x ⟶ Xo.univ.t.G) →*
      (Over.mk z.x ⟶ Xo.univ.t.G))
    (hI : IsHkIsog p (U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).x z.x C ψ ψp)
    (hLie : ∀ τ j, IsLieImageH p ψ ((U.un (castDict hV dict h).1 ⟨(castDict hV dict h).2, hx⟩).u τ j) (z.u τ j)) :
    ∃ a ∈ Rc, ∃ (hx' : (castDict hV dict (h * a)).2 ∈ (U.X (castDict hV dict (h * a)).1).dom) (t : Ix Dw → (CAt σ)ˣ),
      (∀ j, j ≠ none → t j = 1) ∧
        FrBor t (U.un (castDict hV dict (h * a)).1 ⟨(castDict hV dict (h * a)).2, hx'⟩) z := by
  subst hV
  subst hr
  change DictLat U V rfl dict io e F ik φ th x₀ at hL
  change LatEmb V io at hio
  change ∃ a ∈ Rc, ∃ (hx' : (dict (h * a)).2 ∈ (U.X (dict (h * a)).1).dom) (t : Ix Dw → (CAt σ)ˣ),
      (∀ j, j ≠ none → t j = 1) ∧ FrBor t (U.un (dict (h * a)).1 ⟨(dict (h * a)).2, hx'⟩) z
  have hG : ∀ k, (U.X k).Gm = -V.gramᵀ := fun k => (hW k).1
  have hξ : ∀ k, (U.X k).ξ0 = -D.host.xi0 := fun k => (hW k).2
  have hEF : ∀ k a b, (((F.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E
      (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k a : Fin V.rank → D.host.E) (φ k b)) := fun k a b => by
    rw [hL.1.1, hG, hξ]
  have hty := (GlobalTheory.Relab.relab_good _ H l c σ hσ).2.2.2 Dw g e
  obtain ⟨θa, hθa⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  obtain ⟨hAr, -, -⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V θa hθa
  have hp0 : p ≠ 0 := hp.2.2.2.1.ne_zero
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨p', hp'⟩ : ∃ p', p * p' ≡ 1 [MOD l.M'] := by
    have hc : p.Coprime l.M' :=
      (Nat.Prime.coprime_iff_not_dvd hp.2.2.2.1).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hp).2.2.2.2
    have h0 : 0 < l.M'.totient := Nat.totient_pos.2 (Nat.lcm_pos (Nat.pos_of_ne_zero hM0) l.A_pos)
    refine ⟨p ^ (l.M'.totient - 1), ?_⟩
    rw [← pow_succ', Nat.sub_add_cancel h0]
    exact Nat.ModEq.pow_totient hc

  obtain ⟨P, hPe, hP, hy, hd⟩ := hL.1.2 (dict h).1 ⟨(dict h).2, hx⟩
  obtain ⟨j, P', hP', hz⟩ := F.onto z.x z.x_over
  obtain ⟨gam, θ, hl, hθ, hθE, hθP, ⟨b1, b2, b3⟩, hmk, hder⟩ :=
    exists_lift_all F (ik (dict h).1) j P P' hP hP' hp hy hz.symm C ψ ψp hK hI
  obtain ⟨γ₁, hγ₁, hΛ₁, hm₁, hf₁⟩ := hL.2 h
  have hΛ₁' : (U.X (dict h).1).Λ = latG V (γ₁ * h) := SetLike.coe_injective (hΛ₁.trans (Set.image_id _))
  obtain ⟨jm, hjinj, hjθ, hjg, hjE, c1, c2, c3, c4⟩ := exists_quot_lattice (-V.gramᵀ) (-(-D.host.xi0)) _ _ _ (φ (dict h).1)
    (hEF _) (hΛ₁' ▸ (GlobalTheory.Member.latG_selfDual D V (γ₁ * h) _ rfl).2.2) hp0 gam θ hθ hθE _ _ _ b1 b2 b3
  rw [hΛ₁'] at c1 c2 c4

  obtain ⟨a, ha, hlat, haf, hkeep⟩ := hcos (γ₁ * h) _ c1 c2 c3 c4
  obtain ⟨γ₂, hγ₂, hΛ₂, hm₂, hf₂⟩ := hL.2 (h * a)
  have hΛ₂' : (U.X (dict (h * a)).1).Λ = latG V (γ₂ * (h * a)) := SetLike.coe_injective (hΛ₂.trans (Set.image_id _))
  have e₀ : γ₂ * (h * a) = γ₂ * γ₁⁻¹ * (γ₁ * h * a) := by group
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix V (γ₂ * γ₁⁻¹) (mul_mem hγ₂ (inv_mem hγ₁))
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hmove : ∀ v, v ∈ LinearMap.range jm ↔ δ.1 *ᵥ v ∈ (U.X (dict (h * a)).1).Λ := fun v => by
    rw [← hlat, hΛ₂', e₀, GlobalTheory.Member.LatMove.mem_lat_iff, GlobalTheory.Member.LatMove.mem_lat_iff, ← hδf]
    exact GlobalTheory.Member.LatMove.move_iff V _ _ _
  let g₀ : (F.Di j).La →ₗ[𝓞 D.host.E] (U.X (dict (h * a)).1).Λ :=
    { toFun := fun b => ⟨δ.1 *ᵥ jm b, (hmove _).1 (LinearMap.mem_range_self jm b)⟩
      map_add' := fun u v => Subtype.ext (by
        show δ.1 *ᵥ jm (u + v) = δ.1 *ᵥ jm u + δ.1 *ᵥ jm v
        rw [map_add, Matrix.mulVec_add])
      map_smul' := fun s v => Subtype.ext (by
        show δ.1 *ᵥ jm (s • v) = s • δ.1 *ᵥ jm v
        rw [map_smul]
        exact Matrix.mulVec_smul δ.1 s _) }
  have hg₀ : Function.Bijective g₀ := by
    refine ⟨fun u v e => hjinj ?_, fun v => ?_⟩
    · have : δ.1 *ᵥ jm u = δ.1 *ᵥ jm v := congrArg Subtype.val e
      rw [← hli (jm u), this, hli]
    · obtain ⟨b, hb⟩ := (hmove ((δ⁻¹).1 *ᵥ v.1)).2 (by rw [hri]; exact v.2)
      exact ⟨b, Subtype.ext (by show δ.1 *ᵥ jm b = v.1; rw [hb, hri])⟩
  obtain ⟨gm, hgm⟩ : ∃ gm : (F.Di j).La ≃ₗ[𝓞 D.host.E] (F.Di (ik (dict (h * a)).1)).La,
      ∀ b, (φ _ (gm b) : Fin V.rank → D.host.E) = δ.1 *ᵥ jm b :=
    ⟨(LinearEquiv.ofBijective g₀ hg₀).trans (φ _).symm, fun b => by
      rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]; rfl⟩
  have hδn : ∀ (m : ℕ) v, δ.1 *ᵥ (m • v) = m • δ.1 *ᵥ v := fun m v => map_nsmul δ.1.mulVecLin.toAddMonoidHom m v
  obtain ⟨Pa, hPae, hPa, hya, hda⟩ := hL.1.2 (dict (h * a)).1 ⟨(dict (h * a)).2, hdom _⟩
  obtain ⟨k₁, k₂⟩ := point_deriv_eq F hpq hσ hty hA hP' hPa hp0 hl gm
    (fun u v => by
      have h1 := hEF _ (gm u) (gm v)
      rw [hgm, hgm, hδu, ← hjE] at h1
      exact_mod_cast h1)
    (fun v hv => by
      obtain ⟨x, hx⟩ := hmk p' hp' v hv
      have hy1 : finVec V (io v) ∈ latGHat V 1 :=
        ((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1 (hio.2 ▸ LinearMap.mem_range_self io v)
      obtain ⟨w₂, hw₂, ew₂⟩ := hm₂ v hv
      obtain ⟨s, hs, es⟩ := hkeep p' (hp'.of_dvd (Nat.dvd_lcm_left _ _)) (finVec V (io v))
        (finVec V (φ _ (F.t (ik (dict h).1) v) : Fin V.rank → D.host.E))
        (finVec V ((δ⁻¹).1 *ᵥ (φ _ (F.t (ik (dict (h * a)).1) v) : Fin V.rank → D.host.E))) hy1 (hm₁ v hv) (by
          have e₁ : γ₁ * h * a = (γ₂ * γ₁⁻¹)⁻¹ * (γ₂ * (h * a)) := by group
          refine ⟨(finHom V (γ₂ * γ₁⁻¹)⁻¹).1 *ᵥ w₂, e₁ ▸ GlobalTheory.Member.LatMove.move_mem V _ _ _ hw₂, ?_⟩
          have h2 := congrArg (fun u => (finHom V (γ₂ * γ₁⁻¹)⁻¹).1 *ᵥ u) ew₂
          have h3 : (finHom V (γ₂ * γ₁⁻¹)⁻¹).1 *ᵥ (l.M • w₂) = l.M • (finHom V (γ₂ * γ₁⁻¹)⁻¹).1 *ᵥ w₂ :=
            map_nsmul (finHom V (γ₂ * γ₁⁻¹)⁻¹).1.mulVecLin.toAddMonoidHom l.M w₂
          have h4 : ∀ u, (finHom V (γ₂ * γ₁⁻¹)⁻¹).1 *ᵥ finVec V u = finVec V ((δ⁻¹).1 *ᵥ u) := fun u => by
            conv_lhs => rw [← hri u, ← hδf, ← GlobalTheory.Member.LatMove.fin_mul, inv_mul_cancel, GlobalTheory.Member.LatMove.fin_one]
          rw [← h3, ← h4, e₁, GlobalTheory.Member.LatMove.fin_mul, ← Matrix.mulVec_sub]
          exact h2)
      obtain ⟨w, hw, e'⟩ := GlobalTheory.MarkCoset.finVec_div V l.M hM0
        ((δ⁻¹).1 *ᵥ (φ _ (F.t (ik (dict (h * a)).1) v) : Fin V.rank → D.host.E) -
          (p * p') • (φ _ (F.t (ik (dict h).1) v) : Fin V.rank → D.host.E)) s (by
          rw [← es]
          funext i
          exact (TensorProduct.tmul_sub _ _ _).trans (congrArg _ (map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) (p * p') _)))
      obtain ⟨b, hb⟩ : w ∈ LinearMap.range jm := by
        rw [← hlat, GlobalTheory.Member.LatMove.mem_lat_iff, hw]
        exact hs
      refine ⟨gm (x - b), (φ _).injective (Subtype.ext ?_)⟩
      have h5 : (φ _ (F.t (ik (dict (h * a)).1) v) : Fin V.rank → D.host.E) =
          δ.1 *ᵥ ((p * p') • (φ _ (F.t (ik (dict h).1) v) : Fin V.rank → D.host.E) + l.M • jm b) := by
        rw [hb, ← sub_eq_iff_eq_add'.1 e', hri]
      rw [hgm, map_add, map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, hgm, h5, ← hδn, ← Matrix.mulVec_add,
        hx, map_add, hjg, map_nsmul, map_nsmul, map_nsmul, map_sub, Submodule.coe_smul_of_tower, smul_smul, smul_sub,
        add_add_sub_cancel])
    (fun b => by
      rw [← hθP, ← map_nsmul, ← map_nsmul]
      refine congrArg hl (funext fun n => ?_)
      rw [hPe, hPae, hgm, map_nsmul, hjθ]
      refine GlobalTheory.TwistTie.perFr_of_unitary _ _ (fun τ => ((hU.2.1 _).2 τ).trans ((hU.2.1 _).2 τ).symm)
        (by rw [hG, hG]) (by rw [(hU.2.1 _).1, (hU.2.1 _).1]) (by rw [hG]; exact hδu) (fun τ h₁ h₂ => ?_) _ _ _
      rw [hf₁ ⟨τ, h₁⟩, hf₂ ⟨τ, h₂⟩, GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h₁⟩) (hθa τ),
        GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth _ ⟨τ, h₂⟩) (hθa τ), e₀, (hAr τ).2.1, (hAr τ).2.1 (γ₁ * h) a,
        (hAr τ).2.2.1 a haf, hδa τ _ (hθa τ), Matrix.mul_one, ← Matrix.mul_assoc]
      rfl)
  refine ⟨a, ha, hdom _, frBor_one_of_eq _ _ (hz.symm.trans (k₁.trans hya.symm)) (funext fun τ => funext fun n => ?_)⟩
  obtain ⟨wv, hw1, hw2, hw3⟩ := hLie τ n
  have d2 := hder (Pi.single (e.symm ⟨τ, n⟩) 1) wv hw2 ((congrArg (IsDerivAt0 (fun z => (F.ex (ik (dict h).1) P z).left)
    (Pi.single (e.symm ⟨τ, n⟩) 1)) hw1).mpr (hd τ n))
  exact hw3.trans (k₂ _ _ _ d2 (hda τ n))

end GlobalTheory.HeckePointIdent

end Point

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField

namespace GlobalTheory.HeckePointIdent

theorem conjP_asIdeal {D : D7} (Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (P : Formalism.L2.DIV.Pl D.host.E) :
    (Formalism.L2.Col.conjPrime₂ P).asIdeal = P.asIdeal.map (Hh.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  rw [← Formalism.L2.Col.conjIdeal_asIdeal]
  unfold Formalism.HermitianLatticesTheory.conjIdeal
  rw [Ideal.map]
  congr 1
  ext r
  constructor
  · rintro ⟨s, hs, e⟩
    refine ⟨s, hs, ?_⟩
    apply RingOfIntegers.coe_injective
    show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = (r : D.host.E)
    rw [Hh.bar_eq]
    exact e.symm
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s, hs, ?_⟩
    show ((Hh.bar s : 𝓞 D.host.E) : D.host.E) = _
    rw [Hh.bar_eq]
    rfl

set_option maxHeartbeats 1000000 in

theorem exists_coset_frBor : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → LawsJ T →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∃ a ∈ Rc, ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  intro D G _ _ Pl0 T0 A T _ R hLv hFam hL i σ hσ hV P p k α Rc hS h hx C z hz
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hSp, hp, hpP, hM, -, hα, hRc⟩ := hS
  obtain ⟨_, _, -, hd⟩ := hL.dictU _ hj σ hσ
  obtain ⟨hr, g₀, e, F, ik, φ, th, hio, -, hth, hD⟩ := hL.adPin _ hj σ hσ
  obtain ⟨_, hW⟩ := hL.modelW _ hj σ hσ
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hL.pins
  have hU := hL.unf _ hj σ hσ
  have hpq := hU.1 ▸ (show 1 ≤ D.R.r from (hnum _ hj).2.1)
  have hc := conjP_asIdeal T.Q.H P
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, ?_, hp, hpP, hM⟩
    rw [← hc]
    refine Ideal.IsMaximal.coprime_of_ne P.isMaximal (Formalism.L2.Col.conjPrime₂ P).isMaximal fun h => hSp.1 ?_
    rw [Formalism.L2.Col.conjIdeal_asIdeal, ← h]
  obtain ⟨ψ, ψp, hI, hLie, -⟩ := hz
  refine exists_frBor_of_dictLat hV hr (T.iota _) hσ hU hpq hA hW hio hD hth hd.2.2.2.1 hP Rc
    (fun g L' h1 h2 h3 h4 => ?_) h hx C.1 C.2 z ψ ψp hI hLie
  obtain ⟨a, ha, hlat, e', a₀, he, hs, hκ, hlat₀⟩ := GlobalTheory.HeckeLatCoset.exists_coset_of_selfDual D R hLv hFam i P k α Rc
    hSp hα hRc g L' h1 (hc ▸ h2) h3 h4
  refine ⟨a, ha, hlat, ?_, fun p' hp' y x w hy hx hw => ?_⟩
  · have h5 : a₀ * (a⁻¹ * a₀)⁻¹ ∈ GfC (Wc D i) :=
      mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt he.1 hs) (inv_mem hκ.1)
    rwa [show a₀ * (a⁻¹ * a₀)⁻¹ = a by group] at h5
  · refine mark_keep (Wc D i) he hs hpP hp' ?_ g (hlat₀.trans hlat.symm) (fun v hv => ?_) y x w hy hx hw
    · rw [hL.pins.2.1.1]
      exact levG_cong R hLv i _ hκ
    · rw [hlat, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
      exact h1 (Submodule.smul_mem_smul hpP hv)

set_option maxHeartbeats 1000000 in

theorem exists_coset_frBor_of_lift : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (k' : (T.U ((i : ℕ) + 1) σ).Comp) (x' : ((T.U ((i : ℕ) + 1) σ).X k').dom) (t' : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          FrBor t' ((T.U ((i : ℕ) + 1) σ).un k' x') z →
        ∀ (gam : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ →ₗ[𝓞 D.host.E] ((T.U ((i : ℕ) + 1) σ).X k').Λ) (A : (D.host.E →+* ℂ) → ℕ → ℕ → ℂ),
          (∀ u v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ, Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X k').ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X k').Gm (gam u : Fin D.R.r → D.host.E) (gam v : Fin D.R.r → D.host.E)) =
            (p : ℚ) ^ 2 * Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Gm (u : Fin D.R.r → D.host.E) (v : Fin D.R.r → D.host.E))) →
          (∀ w : ((T.U ((i : ℕ) + 1) σ).X k').Λ, ∃ v, gam v = (p ^ 2) • w) →
          (∀ τ a b, b < a → A τ a b = 0) →
          (∀ τ, ∀ n < (T.Q.Dw ((i : ℕ) + 1)).mult τ, ∀ v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ,
            perFr ((T.U ((i : ℕ) + 1) σ).X k') x'.1 (gam v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) n =
              p * ∑ b ∈ Finset.range ((T.Q.Dw ((i : ℕ) + 1)).mult τ), A τ n b * perFr ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 (v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) b) →
          (∀ τ (n : Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ)), A τ n n = toC (t' (some ⟨τ, n⟩) : CAt σ)) →
          ∃ a ∈ Rc, ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z := by
  intro D _ _ _ G _ _ Pl0 T0 A T _ R F κ v₀ hLv _ hFam _ _ hTie i σ hσ hV _ P p k α Rc hS h hx C z hz _ _ _ _ _ _ _ _ _ _ _
  exact exists_coset_frBor D G Pl0 T0 A T R hLv hFam hTie.laws i σ (hσ ▸ T.toCore.good_σ₀) hV P p k α Rc hS h hx C z hz

end GlobalTheory.HeckePointIdent

end Main
