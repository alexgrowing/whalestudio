import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SecFieldChange

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD HasBC map_trans evR_spec evR_not evR_test evR_of_map evR_map
  map_cancel frBor_map hasBC_of)

section Algebra

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

def coord (lam : K' →ₗ[K] K) (R : Type) [CommRing R] [Algebra K R] : K' ⊗[K] R →ₗ[K] R :=
  (TensorProduct.lid K R).toLinearMap ∘ₗ lam.rTensor R

theorem coord_tmul (lam : K' →ₗ[K] K) {R : Type} [CommRing R] [Algebra K R] (a : K') (r : R) :
    coord lam R (a ⊗ₜ r) = lam a • r := by simp [coord]

theorem coord_map (lam : K' →ₗ[K] K) {R T : Type} [CommRing R] [Algebra K R] [CommRing T] [Algebra K T]
    (ψ : R →ₐ[K] T) (v : K' ⊗[K] R) :
    coord lam T (Algebra.TensorProduct.map (AlgHom.id K' K') ψ v) = ψ (coord lam R v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a r => simp [coord_tmul]
  | add x y hx hy => simp [hx, hy]

theorem coord_mul (lam : K' →ₗ[K] K) {R : Type} [CommRing R] [Algebra K R] (r : R) (v : K' ⊗[K] R) :
    coord lam R (((1 : K') ⊗ₜ[K] r) * v) = r * coord lam R v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a s => simp [coord_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [mul_add, hx, hy]

theorem sum_coord {d : ℕ} (B : Module.Basis (Fin d) K K') {R : Type} [CommRing R] [Algebra K R] (v : K' ⊗[K] R) :
    v = ∑ j, B j ⊗ₜ[K] coord (B.coord j) R v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a r =>
    simp only [coord_tmul, Module.Basis.coord_apply, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, B.sum_repr]
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← hx, ← hy]

def Ext (K K' R : Type) [Field K] [Field K'] [Algebra K K'] [CommRing R] [Algebra K R] : Type := K' ⊗[K] R

variable {R T : Type} [CommRing R] [Algebra K R] [CommRing T] [Algebra K T]

instance : CommRing (Ext K K' R) := inferInstanceAs (CommRing (K' ⊗[K] R))
instance algBig : Algebra K' (Ext K K' R) := inferInstanceAs (Algebra K' (K' ⊗[K] R))
instance algSmall : Algebra K (Ext K K' R) := inferInstanceAs (Algebra K (K' ⊗[K] R))

theorem ext_tower (x : K) : algebraMap K' (Ext K K' R) (algebraMap K K' x) = algebraMap K (Ext K K' R) x :=
  (IsScalarTower.algebraMap_apply K K' (K' ⊗[K] R) x).symm

theorem ext_reduced [CharZero K] (p : TRing K) : IsReduced (Ext K K' p.R) := by
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing K).2 p).2
  haveI := ((GlobalTheory.reduced_finiteType_iff_testRing K).2 p).1
  exact GlobalTheory.ReducedAlg.isReduced_field_tensor _ _

def inR (K' : Type) [Field K'] [Algebra K K'] (R : Type) [CommRing R] [Algebra K R] : R →ₐ[K] Ext K K' R :=
  Algebra.TensorProduct.includeRight

def crd (lam : K' →ₗ[K] K) (v : Ext K K' R) : R := coord lam R v

theorem exists_map (ψ : R →ₐ[K] T) : ∃ (Ψ : Ext K K' R →ₐ[K'] Ext K K' T) (Ψ₀ : Ext K K' R →ₐ[K] Ext K K' T),
    (∀ x, Ψ₀ x = Ψ x) ∧ Ψ₀.comp (inR K' R) = (inR K' T).comp ψ ∧ ∀ lam v, crd lam (Ψ v) = ψ (crd lam v) :=
  ⟨Algebra.TensorProduct.map (AlgHom.id K' K') ψ,
    (Algebra.TensorProduct.map (AlgHom.id K' K') ψ).restrictScalars K, fun _ => rfl,
    AlgHom.ext fun v => by
      show Algebra.TensorProduct.map (AlgHom.id K' K') ψ ((1 : K') ⊗ₜ[K] v) = (1 : K') ⊗ₜ[K] ψ v
      simp,
    fun lam v => coord_map lam ψ v⟩

theorem crd_mul (lam : K' →ₗ[K] K) (r : R) (v : Ext K K' R) : crd lam (inR K' R r * v) = r * crd lam v :=
  coord_mul lam r v

theorem exists_lift {S : Type} [CommRing S] [Algebra K S] [Algebra K' S]
    (h : ∀ x, algebraMap K' S (algebraMap K K' x) = algebraMap K S x) (φ : R →ₐ[K] S) :
    ∃ (Φ : Ext K K' R →ₐ[K'] S) (Φ₀ : Ext K K' R →ₐ[K] S), (∀ x, Φ₀ x = Φ x) ∧ Φ₀.comp (inR K' R) = φ ∧
      ∀ (d : ℕ) (B : Module.Basis (Fin d) K K') (v : Ext K K' R),
        Φ v = ∑ j, algebraMap K' S (B j) * φ (crd (B.coord j) v) := by
  haveI : IsScalarTower K K' S := IsScalarTower.of_algebraMap_eq fun x => (h x).symm
  let Φ : K' ⊗[K] R →ₐ[K'] S := Algebra.TensorProduct.lift (Algebra.ofId K' S) φ (fun _ _ => Commute.all _ _)
  refine ⟨Φ, Φ.restrictScalars K, fun _ => rfl, AlgHom.ext fun v => ?_, fun d B v => ?_⟩
  · show Φ ((1 : K') ⊗ₜ[K] v) = φ v
    simp [Φ]
  · have e := congrArg Φ (sum_coord B (R := R) v)
    rw [map_sum] at e
    refine e.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Φ, Algebra.TensorProduct.lift_tmul]
    rfl

theorem wchar_inR {ι : Type} [Fintype ι] (e : ι → ℕ) (t : ι → Rˣ) :
    wchar e (fun i => Units.map ((inR K' R : R →ₐ[K] Ext K K' R) : R →* Ext K K' R) (t i)) =
      (inR K' R : R →ₐ[K] Ext K K' R) (wchar e t) := by
  simp only [wchar, map_prod, map_pow]
  rfl

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

theorem frMap_ext {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (φ : S →ₐ[c.F] T) (Φ : S →ₐ[c'.F] T)
    (e : ∀ x, φ x = Φ x) {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    FrMap Φ (y.ext hle hS) (z.ext hle hT) := by
  have e' : φ.toRingHom = Φ.toRingHom := RingHom.ext e
  unfold FrMap at h ⊢
  rw [e'] at h
  exact h

theorem frMap_res {S T : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] [CommRing T] [Algebra c.F T]
    [Algebra c'.F T] (hS : AlgOver c c' hle S) (hT : AlgOver c c' hle T) (φ : S →ₐ[c.F] T) (Φ : S →ₐ[c'.F] T)
    (e : ∀ x, φ x = Φ x) {y : FrPt Xo c' S} {z : FrPt Xo c' T} (h : FrMap Φ y z) :
    FrMap φ (y.res hle hS) (z.res hle hT) := by
  have e' : φ.toRingHom = Φ.toRingHom := RingHom.ext e
  unfold FrMap at h ⊢
  rw [← e'] at h
  exact h

theorem frBor_ext {S : Type} [CommRing S] [Algebra c.F S] [Algebra c'.F S] (hS : AlgOver c c' hle S)
    {t : Ix Dw → Sˣ} {y z : FrPt Xo c S} (h : FrBor t y z) : FrBor t (y.ext hle hS) (z.ext hle hS) := h

theorem section_base_change_of_basis [Algebra c.F c'.F] (halg : ∀ x, algebraMap c.F c'.F x = incF c c' hle x) {d : ℕ}
    (B : Module.Basis (Fin d) c.F c'.F) (hWD : ValueWD Xo c) (hWD' : ValueWD Xo c') (hBC : HasBC Xo c)
    (hA : AllTest Xo c) (hA' : AllTest Xo c') (hB' : BorChartF Xo c') : Formalism.L2.Pj.SecBC Xo hle := by
  classical
  intro a n f' hf'
  have hov : ∀ p : TRing c.F, AlgOver c c' hle (Ext c.F c'.F p.R) := fun p x => by
    rw [← halg]; exact ext_tower x
  choose z hz using fun (p : TRing c.F) (y : FrPt Xo c p.R) => hBC p.R (Ext c.F c'.F p.R) (inR c'.F p.R) y
  have hT : ∀ (p : TRing c.F) (y : FrPt Xo c p.R), FromT ((z p y).ext hle (hov p)) := fun p y => by
    haveI := ext_reduced (K' := c'.F) p
    exact hA' _ _
  obtain ⟨fs, hfs⟩ : ∃ fs : Fin d → Rul Xo c, ∀ j p y,
      fs j p y = crd (B.coord j) (evR Xo c' f' ((z p y).ext hle (hov p))) := ⟨fun j p y => _, fun _ _ _ => rfl⟩
  have hnat : ∀ j, Natural c (fs j) := by
    intro j p q ψ y w h
    have h' : FrMap ψ y w := h
    obtain ⟨Ψ, Ψ₀, e₁, e₂, e₃⟩ := exists_map (K' := c'.F) ψ
    have h0 := map_trans ψ (inR c'.F q.R) h' (hz q w)
    have h1 := map_cancel hBC e₂ (hz p y) h0
    have h2 := frMap_ext hle (hov p) (hov q) Ψ₀ Ψ e₁ h1
    rw [hfs, hfs, evR_map hWD' hf'.1 (hT p y) h2, e₃]
  refine ⟨d, fun j => B j, fs, fun j => ⟨hnat j, ?_⟩, ?_⟩
  · intro p t y y' h
    have h' : FrBor t y y' := h
    have h2 := frBor_ext hle (hov p) (frBor_map h' (hz p y) (hz p y'))
    have h3 : evR Xo c' f' ((z p y').ext hle (hov p)) = _ * evR Xo c' f' ((z p y).ext hle (hov p)) :=
      wtAll_of_borChart hB' (ex Dw a n) hf'.1 hf'.2 _ _ _ _ (hT p y) (hT p y') h2
    rw [hfs, hfs, h3, wchar_inR, crd_mul]
  · intro S _ _ _ h y
    by_cases hy : FromT (y.res hle h)
    · obtain ⟨p, φ, y₀, hy₀'⟩ := hy
      have hy₀ : FrMap φ y₀ (y.res hle h) := hy₀'
      obtain ⟨Φ, Φ₀, e₁, e₂, e₃⟩ := exists_lift (K' := c'.F) (fun x => by rw [halg]; exact h x) φ
      have h1 := map_cancel hBC e₂ (hz p y₀) hy₀
      have h2 : FrMap Φ ((z p y₀).ext hle (hov p)) y := frMap_ext hle (hov p) h Φ₀ Φ e₁ h1
      rw [evR_map hWD' hf'.1 (hT p y₀) h2, e₃ d B]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [evR_of_map hWD (hnat j) hy₀, hfs]
    · have hy' : ¬ FromT y := by
        rintro ⟨q, ψ, y₁, hy₁⟩
        letI : Algebra c.F q.R := ((algebraMap c'.F q.R).comp (incF c c' hle)).toAlgebra
        have hq : AlgOver c c' hle q.R := fun _ => rfl
        haveI := ((GlobalTheory.reduced_finiteType_iff_testRing c'.F).2 q).2
        obtain ⟨p, φ, y₀, hy₀'⟩ := hA q.R (y₁.res hle hq)
        have hy₀ : FrMap φ y₀ (y₁.res hle hq) := hy₀'
        let ψ' : q.R →ₐ[c.F] S := { ψ.toRingHom with commutes' := fun x => (ψ.commutes _).trans (h x) }
        have h1 : FrMap ψ' (y₁.res hle hq) (y.res hle h) := frMap_res hle hq h ψ' ψ (fun _ => rfl) hy₁
        exact hy ⟨p, _, y₀, map_trans φ ψ' hy₀ h1⟩
      rw [evR_not hy']
      simp [evR_not hy]

theorem secBC_of_laws (hWD : ValueWD Xo c) (hWD' : ValueWD Xo c') (hBC : HasBC Xo c) (hA : AllTest Xo c)
    (hA' : AllTest Xo c') (hB' : BorChartF Xo c') : Formalism.L2.Pj.SecBC Xo hle := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  exact section_base_change_of_basis hle (fun _ => rfl) (Module.finBasis c.F c'.F) hWD hWD' hBC hA hA' hB'

theorem secBC_holds : Formalism.L2.Pj.SecBC Xo hle :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c
  secBC_of_laws hle (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) (hasBC_of hS)
    (GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c) (GlobalTheory.Frames.allTest_of_secBaseChange hS E H Dw l Xo c')
    (borChartF_of_cover (hc c'))

theorem cuspBC_holds {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) : Formalism.L2.Pj.CuspBC hle U :=
  cuspBC_of hle U (secBC_holds hle)

theorem val_of_isBC {m : ℕ} {f' : Rul Xo c'} (hf' : Natural c' f') {as : Fin m → c'.F} {fs : Fin m → Rul Xo c}
    (h : IsBC hle f' as fs) (q : TRing c'.F) [Algebra c.F q.R] (hq : AlgOver c c' hle q.R) (y : FrPt Xo c' q.R) :
    f' q y = ∑ i, algebraMap c'.F q.R (as i) * evR Xo c (fs i) (y.res hle hq) := by
  rw [← evR_test hf' q y, h q.R hq y]

end GlobalTheory.SecFieldChange
