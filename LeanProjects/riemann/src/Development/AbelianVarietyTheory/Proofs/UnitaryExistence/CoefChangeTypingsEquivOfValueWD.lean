import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ComplexResidueRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReducedFiniteTypeIffTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChangeStatement

set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.CoefChangeCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing TensorProduct

section Algebra

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [Algebra K K']

theorem exists_testRing_ext (p : TRing K) :
    ∃ (q : TRing K') (α : p.R →+* q.R), (∀ a, α (algebraMap K p.R a) = algebraMap K' q.R (algebraMap K K' a)) ∧
      (∀ (S : Type) [CommRing S] [Algebra K' S] (φ : p.R →+* S),
        (∀ a, φ (algebraMap K p.R a) = algebraMap K' S (algebraMap K K' a)) →
        ∃ β : q.R →ₐ[K'] S, ∀ v, β (α v) = φ v) ∧
      ∀ (m : ℕ) (b : Fin m → K') (v : Fin m → p.R), ∑ i, algebraMap K' q.R (b i) * α (v i) = 0 →
        ∀ lam : K' →ₗ[K] K, ∑ i, lam (b i) • v i = 0 := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K).2 p
  have hred' : IsReduced (K' ⊗[K] p.R) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  obtain ⟨q, ⟨e⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K').1 (K' ⊗[K] p.R) inferInstance hred'
  refine ⟨q, e.symm.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := p.R)).toRingHom,
    fun a => ?_, fun S _ _ φ hφ => ?_, fun m b v hv lam => ?_⟩
  · show e.symm (Algebra.TensorProduct.includeRight (algebraMap K p.R a)) = _
    rw [AlgHom.commutes, ← e.symm.commutes]
    rfl
  · letI : Algebra K S := ((algebraMap K' S).comp (algebraMap K K')).toAlgebra
    haveI : IsScalarTower K K' S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ' : p.R →ₐ[K] S := { φ with commutes' := hφ }
    refine ⟨(Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)).comp e.toAlgHom,
      fun v => ?_⟩
    show Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)
      (e (e.symm ((1 : K') ⊗ₜ[K] v))) = _
    rw [e.apply_symm_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have h1 : ∑ i, b i ⊗ₜ[K] v i = (0 : K' ⊗[K] p.R) := by
      have h2 := congrArg e hv
      rw [map_zero, map_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = e (algebraMap K' q.R (b i) * e.symm ((1 : K') ⊗ₜ[K] v i))
      rw [map_mul, e.commutes, e.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
    have h3 := congrArg (fun w => TensorProduct.lid K p.R (lam.rTensor p.R w)) h1
    simpa [map_sum] using h3

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l}

section First

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD

variable (c c') (hle : c.F ≤ c'.F)

abbrev inclF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def Compat (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (inclF c c' hle a) = algebraMap c.F S a

variable {c c'}

theorem embK_inclF (τ : E →+* ℂ) (a : 𝓞 E) : inclF c c' hle (embK c τ a) = embK c' τ a :=
  Subtype.ext rfl

theorem sOf_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : Compat c c' hle S) :
    sOf c' S = sOf c S := by
  unfold sOf
  congr 1
  ext a
  simp only [RingHom.comp_apply]
  rw [← h]
  rfl

theorem isEigAt_res {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : Compat c c' hle S)
    (τ : E →+* ℂ) (v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsEigAt (Xo := Xo) c' τ v ↔ IsEigAt (Xo := Xo) c τ v := by
  have h' : ∀ a : c.F, algebraMap c'.F S (inclF c c' hle a) = algebraMap c.F S a := h
  unfold IsEigAt
  simp only [← embK_inclF hle τ, h']

def ptRes {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : Compat c c' hle S)
    (y : FrPt Xo c' S) : FrPt Xo c S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h)
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).1 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).2 he)
  s := y.s
  gen := y.gen

def ptExt {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : Compat c c' hle S)
    (y : FrPt Xo c S) : FrPt Xo c' S where
  x := y.x
  x_over := y.x_over.trans (sOf_res hle h).symm
  u := y.u
  tan := y.tan
  eig τ i := (isEigAt_res hle h τ _).2 (y.eig τ i)
  basis τ w ht he := y.basis τ w ht ((isEigAt_res hle h τ w).1 he)
  s := y.s
  gen := y.gen

variable {r : ℕ}

def unifExt (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := (σ'.comp (inclF c c' hle)).toAlgebra
  { Comp := (U (σ'.comp (inclF c c' hle))).Comp
    fin := (U (σ'.comp (inclF c c' hle))).fin
    X := (U (σ'.comp (inclF c c' hle))).X
    un := fun k x => ptExt hle (S := CAt σ') (fun _ => rfl) ((U (σ'.comp (inclF c c' hle))).un k x) }

def IsSum {m : ℕ} (f' : Rul Xo c') (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : Compat c c' hle S) (y : FrPt Xo c' S),
    evR Xo c' f' y = ∑ i, algebraMap c'.F S (as i) * evR Xo c (fs i) (ptRes hle h y)

def CuspSums (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f' ∈ cusp Xo c' (unifExt hle U) a n,
    ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ cusp Xo c U a n) ∧ IsSum hle f' as fs

def ActSums {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c') :
    Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ sec Xo c' a n → (∀ i, fs i ∈ sec Xo c a n) →
    IsSum hle f' as fs → IsSum hle (act' g f') as (fun i => act g (fs i))

end First

abbrev Natural (c : Coeff l) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f

abbrev FromT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

variable (Xo c) in

abbrev ValueWD : Prop := EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)

variable (Xo c) in

abbrev HasBC : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z

theorem map_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w :=
  frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h₁ h₂

theorem hasBC_of (hS : Out.SecBaseChangeSt) : HasBC Xo c :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c

theorem evR_spec {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : FromT y) :
    ∃ (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : FrPt Xo c p.R), FrMap φ y₀ y ∧
      ∀ f : Rul Xo c, evR Xo c f y = φ (f p y₀) :=
  ⟨_, _, _, hy.choose_spec.choose_spec.choose_spec, fun f => by unfold evR evalAt; rw [dif_pos hy]⟩

theorem evR_not {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : ¬ FromT y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt; rw [dif_neg hy]

theorem evR_test {f : Rul Xo c} (hf : Natural c f) (p : TRing c.F) (y : FrPt Xo c p.R) : evR Xo c f y = f p y := by
  obtain ⟨q, φ, y₀, h, e⟩ := evR_spec (y := y) ⟨p, AlgHom.id _ _, y, GlobalTheory.Frames.frMapUniq_refl y⟩
  rw [e, hf q p φ y₀ y h]

theorem evR_of_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S] [Algebra c.F S]
    {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y₀ : FrPt Xo c p.R} {y : FrPt Xo c S} (h : FrMap φ y₀ y) :
    evR Xo c f y = φ (f p y₀) := by
  obtain ⟨q, ψ, y₁, h₁, e⟩ := evR_spec (y := y) ⟨p, φ, y₀, h⟩
  rw [e]
  exact hWD f hf S q p ψ φ y₁ y₀ y h₁ h

theorem evR_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S T : Type} [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y)
    (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, ψ, y₀, h₀, e⟩ := evR_spec hy
  rw [e, evR_of_map hWD hf (map_trans ψ φ h₀ h)]
  rfl

theorem map_cancel (hBC : HasBC Xo c) {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {α : R →ₐ[c.F] S} {β : S →ₐ[c.F] T} {φ : R →ₐ[c.F] T} (hc : β.comp α = φ)
    {y : FrPt Xo c R} {z : FrPt Xo c S} {w : FrPt Xo c T} (h₁ : FrMap α y z) (h₂ : FrMap φ y w) : FrMap β z w := by
  obtain ⟨w', hw'⟩ := hBC S T β z
  have h₃ : FrMap φ y w' := hc ▸ map_trans α β h₁ hw'
  rwa [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c R T φ y).1 w w' h₂ h₃]

theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hb : FrBor t y y') (h : FrMap φ y z)
    (h' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, g1, g2, hg⟩ := (GlobalTheory.Frames.Model.frBor_iff t y y').1 hb
  refine (GlobalTheory.Frames.Model.frBor_iff _ z z').2 ⟨fun τ => (g τ).map φ, fun τ i => ?_, fun τ i j hij => ?_, ?_⟩
  · simp [g1]
  · simp [g2 τ i j hij]
  · exact (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg h).1 h'

variable (hle : c.F ≤ c'.F)

def resHom {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T) :
    Res hle S →ₐ[c.F] Res hle T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (incl hle a) }

theorem frMap_down {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (resHom hle φ) (ptDown hle y) (ptDown hle z) ↔ FrMap φ y z := Iff.rfl

theorem finite_incl : letI := (incl hle).toAlgebra; Module.Finite c.F c'.F := by
  letI := (incl hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  exact Module.Finite.of_restrictScalars_finite ℚ c.F c'.F

theorem exists_testRing_res (q : TRing c'.F) : ∃ p : TRing c.F, Nonempty (p.R ≃ₐ[c.F] Res hle q.R) := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c'.F).2 q
  letI := (incl hle).toAlgebra
  haveI := finite_incl hle
  letI : Algebra c'.F (Res hle q.R) := inferInstanceAs (Algebra c'.F q.R)
  haveI : IsScalarTower c.F c'.F (Res hle q.R) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType c'.F (Res hle q.R) := hft
  exact (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 _ (Algebra.FiniteType.trans (S := c'.F) inferInstance this) hred

theorem fromT_down_test (hBC : HasBC Xo c) (q : TRing c'.F) (y : FrPt Xo c' q.R) : FromT (ptDown hle y) := by
  obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
  obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
  exact ⟨p, e, z, map_cancel hBC (by ext; simp) hz (GlobalTheory.Frames.frMapUniq_refl _)⟩

theorem fromT_down_iff (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FromT (ptDown hle y) ↔ FromT y := by
  constructor
  · rintro ⟨p, φ, y₀, h⟩
    letI := (incl hle).toAlgebra
    obtain ⟨q, α, hα, hu, -⟩ := exists_testRing_ext (K' := c'.F) p
    obtain ⟨β, hβ⟩ := hu S φ.toRingHom φ.commutes
    let α' : p.R →ₐ[c.F] Res hle q.R := { α with commutes' := hα }
    obtain ⟨z, hz⟩ := hBC _ _ α' y₀
    exact ⟨q, β, ptUp hle z, map_cancel hBC (β := resHom hle β) (AlgHom.ext hβ) hz h⟩
  · rintro ⟨q, φ, y₀, h⟩
    obtain ⟨p, ψ, z, hz⟩ := fromT_down_test hle hBC q y₀
    exact ⟨p, _, z, map_trans ψ (resHom hle φ) hz h⟩

theorem evR_ruleUp (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S]
    [Algebra c'.F S] (y : FrPt Xo c' S) : evR Xo c' (ruleUp hle f) y = unRes (evR Xo c f (ptDown hle y)) := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, h, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_down_test hle hBC q y₀) ((frMap_down hle φ y₀ y).2 h)]
    rfl
  · rw [evR_not hy, evR_not (fun h => hy ((fromT_down_iff hle hBC y).1 h)), map_zero]

theorem ruleUp_mem_sec (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : ruleUp hle f ∈ sec Xo c' a n := by
  refine ⟨fun p q φ y z h => ?_, fun q t y y' h => ?_⟩
  · exact evR_map hWD hf.1 (fromT_down_test hle hBC p y) ((frMap_down hle φ y z).2 h)
  · obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
    obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
    obtain ⟨z', hz'⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y')
    have he : (e : p.R →ₐ[c.F] Res hle q.R).comp (e.symm : Res hle q.R →ₐ[c.F] p.R) = AlgHom.id _ _ := by
      ext; simp
    have hb : FrBor (c := c) (S := Res hle q.R) t (ptDown hle y) (ptDown hle y') := h
    have hw := hf.2 p _ z z' (frBor_map hb hz hz')
    have e1 := evR_of_map hWD hf.1 (map_cancel hBC he hz (GlobalTheory.Frames.frMapUniq_refl _))
    have e2 := evR_of_map hWD hf.1 (map_cancel hBC he hz' (GlobalTheory.Frames.frMapUniq_refl _))
    have e3 : evR Xo c f (ptDown hle y') = wchar (S := Res hle q.R) (ex Dw a n) t * evR Xo c f (ptDown hle y) := by
      rw [e1, e2, hw, map_mul]
      congr 1
      unfold wchar
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow]
      exact congrArg (· ^ _) (e.apply_symm_apply _)
    exact e3

variable {r : ℕ}

def ActSumsOn {G : Type} [Group G] (act : G → Rul Xo c →ₗ[c.F] Rul Xo c) (act' : G → Rul Xo c' →ₗ[c'.F] Rul Xo c')
    (W : Submodule c.F (Rul Xo c)) (W' : Submodule c'.F (Rul Xo c')) : Prop :=
  ∀ (g : G) (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c) (f' : Rul Xo c'),
    f' ∈ W' → (∀ i, fs i ∈ W) → IsSum hle f' as fs → IsSum hle (act' g f') as (fun i => act g (fs i))

def ExtendsOn {G : Type} [Group G] {W : Submodule c.F (Rul Xo c)} {W' : Submodule c'.F (Rul Xo c')}
    (ρ : G →* Module.End c.F W) (ρ' : G →* Module.End c'.F W') : Prop :=
  ∀ (g : G) (m : ℕ) (b : Fin m → c'.F) (f : Fin m → W) (f' : W'),
    IsComb hle b (fun i => (f i : Rul Xo c)) (f' : Rul Xo c') →
      IsComb hle b (fun i => (ρ g (f i) : Rul Xo c)) (ρ' g f' : Rul Xo c')

end GlobalTheory.CoefChangeCompare
