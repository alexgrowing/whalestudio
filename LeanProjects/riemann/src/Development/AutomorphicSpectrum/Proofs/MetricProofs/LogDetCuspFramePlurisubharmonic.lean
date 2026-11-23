import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicFamilySmoothEntriesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicEigencomponentConjugateFormStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocal
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentPolynomialInActionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicQuotientStructureStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicLocalQuotientMapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.QuotientFamilyEigenFrameStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicSpanCoefficientsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpanStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosIffLinearIndependentStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PhiI

open ReciprocityTheory.AnForm.A (IsPsh)

theorem isPsh_add {d : ℕ} {U : Set (Fin d → ℂ)} {φ ψ : (Fin d → ℂ) → ℝ} (hφ : IsPsh U φ) (hψ : IsPsh U ψ) :
    IsPsh U (fun z => φ z + ψ z) := by
  refine ⟨hφ.1.add hψ.1, fun z w hd => ?_⟩
  obtain ⟨h1, h2⟩ := hφ.2 z w hd
  obtain ⟨h3, h4⟩ := hψ.2 z w hd
  refine ⟨h1.add h3, ?_⟩
  have e := Real.circleAverage_fun_add h1 h3
  show φ z + ψ z ≤ Real.circleAverage (fun ζ : ℂ => φ (z + ζ • w) + ψ (z + ζ • w)) 0 1
  rw [e]
  linarith

theorem isPsh_zero {d : ℕ} (U : Set (Fin d → ℂ)) (c : ℝ) : IsPsh U (fun _ => c) := by
  refine ⟨upperSemicontinuousOn_const, fun z w _ => ⟨circleIntegrable_const c 0 1, ?_⟩⟩
  rw [Real.circleAverage_const]

theorem isPsh_sum {d : ℕ} {U : Set (Fin d → ℂ)} {ι : Type} (S : Finset ι) {f : ι → (Fin d → ℂ) → ℝ}
    (h : ∀ i ∈ S, IsPsh U (f i)) : IsPsh U (fun z => ∑ i ∈ S, f i z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isPsh_zero U 0
  | insert a S ha ih =>
    have := isPsh_add (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun z _ => ?_) this
    simp [Finset.sum_insert ha]

theorem hol_apply {n g g' : ℕ} {V : Set (Fin n → ℂ)} {q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)}
    (hq : ∀ x, DifferentiableOn ℂ (fun t => q t x) V) {z : (Fin n → ℂ) → Fin g → ℂ}
    (hz : DifferentiableOn ℂ z V) : DifferentiableOn ℂ (fun t => q t (z t)) V := by
  have e : (fun t => q t (z t)) = fun t => ∑ i, z t i • q t (fun j => if i = j then 1 else 0) := by
    funext t
    exact LinearMap.pi_apply_eq_sum_univ (q t) (z t)
  rw [e]
  refine DifferentiableOn.fun_sum fun i _ => ?_
  exact ((differentiableOn_pi.1 hz) i).smul (hq _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
  {n : ℕ}

theorem hol_eig {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hP : ∀ x, DifferentiableOn ℂ (fun t => (R t).P x) U)
    (s : 𝓞 E →+* ℂ) (x : Λ) : DifferentiableOn ℂ (fun t => eigComp (R t).B s ((R t).P x)) U := by
  obtain ⟨N, a, c, h⟩ := GlobalTheory.T.eigen_component_polynomial_in_action E s
  have e : (fun t => eigComp (R t).B s ((R t).P x)) = fun t => ∑ i, c i • (R t).P (a i • x) := by
    funext t
    rw [h g Λ (R t)]
    simp only [(R t).act]
  rw [e]
  exact DifferentiableOn.fun_sum fun i _ => (hP _).const_smul (c i)

theorem isHolFam_mono {g' : ℕ} {Λ' : Type} [AddCommGroup Λ'] [Module (𝓞 E) Λ'] {W V : Set (Fin n → ℂ)}
    {R' : (Fin n → ℂ) → RiemLat E g' Λ'} (h : IsHolFam W R') (hV : V ⊆ W) : IsHolFam V R' :=
  ⟨fun t ht t' ht' => h.1 t (hV ht) t' (hV ht'), fun x => (h.2 x).mono hV⟩

theorem perEmb {U W : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hHol : IsHolFam U R)
    {g' : ℕ} {Λ' : Type} [AddCommGroup Λ'] [Module (𝓞 E) Λ'] (hW : IsOpen W) (hWU : W ⊆ U) {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ W)
    {R' : (Fin n → ℂ) → RiemLat E g' Λ'} (hR' : IsHolFam W R')
    {q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hq : ∀ x, DifferentiableOn ℂ (fun t => q t x) W)
    {I : Submodule (𝓞 E) Λ} (hker : ∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I))
    (hcomp : ∀ t ∈ W, ∀ y z, (∀ u ∈ I, (R t).ip ((R t).P u) y = 0) → (R' t).ip (q t y) (q t z) = (R t).ip y z)
    (hiso : ∀ t ∈ U, IsIsoSub (R t).form I) (s : 𝓞 E →+* ℂ) {r : ℕ} {v : Fin r → Λ} (hv : IsNzFamily I r v)
    {m : ℕ} {b : Fin m → (Fin n → ℂ) → Fin g → ℂ} (hb : ∀ i, DifferentiableOn ℂ (b i) U)
    (hbl : ∀ t ∈ U, LinearIndependent ℂ fun i => b i t)
    (hbs : ∀ t ∈ U, Submodule.span ℂ (Set.range fun i => b i t) = eigSp (R t).B s) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧
      IsPsh V (fun t => Real.log ((R t).gram fun i => b i t).det.re -
        Real.log ((R t).gram fun a => eigComp (R t).B s ((R t).P (v a))).det.re) := by
  obtain ⟨hr1, hvI, hvli, hvidx⟩ := hv
  have hv : IsNzFamily I r v := ⟨hr1, hvI, hvli, hvidx⟩
  set w : Fin r → (Fin n → ℂ) → Fin g → ℂ := fun a t => eigComp (R t).B s ((R t).P (v a)) with hw
  have hwh : ∀ a, DifferentiableOn ℂ (w a) U := fun a => hol_eig hHol.2 s (v a)
  have hwl : ∀ t ∈ U, LinearIndependent ℂ fun a => w a t := fun t ht =>
    (GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit (R t) I (hiso t ht) s).2 r v hvI hvli
  have hwe : ∀ t, ∀ a, w a t ∈ eigSp (R t).B s := fun t a =>
    ((GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit (R t)).2.2.1 s).1 _
  have ht₀U := hWU ht₀
  obtain ⟨k, J, rfl, hli⟩ := GlobalTheory.T.exists_extend_linearIndependent_of_span g m r (fun a => w a t₀) (fun i => b i t₀) (hwl _ ht₀U) (hbl _ ht₀U)
    (fun a => by rw [hbs _ ht₀U]; exact hwe _ a)
  set c : Fin (r + k) → (Fin n → ℂ) → Fin g → ℂ := fun i t => Fin.append (fun a => w a t) (fun j => b (J j) t) i with hc
  have hch : ∀ i, DifferentiableOn ℂ (c i) W := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · simp only [hc, Fin.append_left]; exact (hwh a).mono hWU
    · simp only [hc, Fin.append_right]; exact (hb _).mono hWU
  have hcs : ∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t) := by
    intro t ht i
    refine Fin.addCases (fun a => ?_) (fun j => ?_) i
    · simp only [hc, Fin.append_left]; rw [hbs t (hWU ht)]; exact hwe t a
    · simp only [hc, Fin.append_right]; exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨V, hVo, ht₀V, hVW, G, hG, hGl⟩ := GlobalTheory.T.holomorphic_span_coefficients E g Λ n (r + k) W R b c t₀ hW ht₀
    (fun i => (hb i).mono hWU) hch (fun t ht => hbl t (hWU ht)) hcs hli
  have hSc : ∀ t ∈ V, ((R t).gram fun i => c i t).det =
      ((R t).gram fun a => w a t).det * ((R' t).gram fun j => q t (b (J j) t)).det := by
    intro t ht
    have htW := hVW ht
    exact GlobalTheory.T.quotient_family_eigen_frame E g g' Λ Λ' (R t) (R' t) (q t) I s r k v (fun j => b (J j) t) (hiso t (hWU htW)) hv
      (hker t htW) (hcomp t htW) (fun j => by rw [← hbs t (hWU htW)]; exact Submodule.subset_span ⟨_, rfl⟩)
  have hcpos : ∀ t ∈ V, 0 < ((R t).gram fun i => c i t).det.re ∧ ((R t).gram fun i => c i t).det.im = 0 :=
    fun t ht => (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1 (hGl t ht).1
  have hwpos : ∀ t ∈ V, 0 < ((R t).gram fun a => w a t).det.re ∧ ((R t).gram fun a => w a t).det.im = 0 :=
    fun t ht => (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1 (hwl t (hWU (hVW ht)))
  have hul : ∀ t ∈ V, LinearIndependent ℂ fun j => q t (b (J j) t) := by
    intro t ht
    refine (GlobalTheory.T.gram_det_pos_iff_linearIndependent E g' Λ' (R' t) _ _).2 fun h0 => ?_
    have := hSc t ht
    rw [h0, mul_zero] at this
    have h1 := (hcpos t ht).1
    rw [this] at h1
    simp at h1
  have hup : IsPsh V (fun t => Real.log ((R' t).gram fun j => q t (b (J j) t)).det.re) :=
    (GlobalTheory.T.holomorphic_family_smooth_entries E g' Λ' Unit n V R' hVo (isHolFam_mono hR' hVW)).2.2 k (fun j t => q t (b (J j) t))
      (fun j => hol_apply (fun x => (hq x).mono hVW) (((hb _).mono hWU).mono hVW)) hul
  have hneg : DifferentiableOn ℂ (fun t => - G t) V := hG.neg
  have hfin := GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hVo hup hneg 0
  refine ⟨V, hVo, ht₀V, hVW, GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun t ht => ?_) hfin⟩
  have e1 := (hGl t ht).2
  have e2 := hSc t ht
  have hc1 := hcpos t ht
  have hw1 := hwpos t ht
  have hre : ((R t).gram fun i => c i t).det.re =
      ((R t).gram fun a => w a t).det.re * ((R' t).gram fun j => q t (b (J j) t)).det.re := by
    rw [e2, Complex.mul_re, hw1.2]; ring
  have hupos : ((R' t).gram fun j => q t (b (J j) t)).det.re ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hre
    rw [hre] at hc1
    exact lt_irrefl _ hc1.1
  rw [hre, Real.log_mul hw1.1.ne' hupos] at e1
  simp only [Complex.neg_re, add_zero]
  linarith

theorem localQuot {U : Set (Fin n → ℂ)} {R : (Fin n → ℂ) → RiemLat E g Λ} (hU : IsOpen U) (hHol : IsHolFam U R)
    {t₀ : Fin n → ℂ} (ht₀ : t₀ ∈ U) {I : Submodule (𝓞 E) Λ} (hsat : IsSaturated I) (hiso : IsIsoSub (R t₀).form I) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧ t₀ ∈ W ∧ W ⊆ U ∧ ∃ (g' : ℕ) (Λ' : Type) (_ : AddCommGroup Λ') (_ : Module (𝓞 E) Λ')
      (R' : (Fin n → ℂ) → RiemLat E g' Λ') (q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)),
      IsHolFam W R' ∧ (∀ x, DifferentiableOn ℂ (fun t => q t x) W) ∧
      (∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I)) ∧
      ∀ t ∈ W, ∀ y z, (∀ u ∈ I, (R t).ip ((R t).P u) y = 0) → (R' t).ip (q t y) (q t z) = (R t).ip y z := by
  obtain ⟨g', k, Λ', i1, i2, e, form', π, hk, hπ, hall⟩ := GlobalTheory.T.isotropic_quotient_structure E g Λ (R t₀) I hsat hiso
  have hform : ∀ t ∈ U, (R t).form = (R t₀).form := fun t ht => hHol.1 t ht t₀ ht₀
  obtain ⟨W, hWo, ht₀W, hWU, q, hq, hqs⟩ := GlobalTheory.T.holomorphic_local_quotient_map g' k g n U (fun i t => (R t).P (e i)) t₀ hU ht₀ hk
    (fun i => hHol.2 (e i)) (hall (R t₀) rfl).1
  have hker : ∀ t ∈ W, LinearMap.ker (q t) = Submodule.span ℂ ((R t).P '' I) := fun t ht => by
    rw [(hqs t ht).2, (hall (R t) (hform t (hWU ht))).2.1]
  have hex : ∀ t ∈ W, ∃ R' : RiemLat E g' Λ', R'.form = form' ∧
      (∀ x, (∀ y ∈ I, (R t).form x y = 0) → R'.P (π x) = q t ((R t).P x)) ∧
      ∀ x y, (∀ v ∈ I, (R t).ip ((R t).P v) x = 0) → R'.ip (q t x) (q t y) = (R t).ip x y := fun t ht =>
    (hall (R t) (hform t (hWU ht))).2.2 (q t) (hqs t ht).1 (hker t ht)
  have hex' : ∀ t, ∃ R' : RiemLat E g' Λ', t ∈ W → (R'.form = form' ∧
      (∀ x, (∀ y ∈ I, (R t).form x y = 0) → R'.P (π x) = q t ((R t).P x)) ∧
      ∀ x y, (∀ v ∈ I, (R t).ip ((R t).P v) x = 0) → R'.ip (q t x) (q t y) = (R t).ip x y) := by
    intro t
    by_cases ht : t ∈ W
    · obtain ⟨R', h⟩ := hex t ht
      exact ⟨R', fun _ => h⟩
    · obtain ⟨R', _⟩ := hex t₀ ht₀W
      exact ⟨R', fun h => absurd h ht⟩
  choose R' hR' using hex'
  refine ⟨W, hWo, ht₀W, hWU, g', Λ', i1, i2, R', q, ⟨fun t ht t' ht' => ?_, fun x' => ?_⟩, hq, hker,
    fun t ht => (hR' t ht).2.2⟩
  · rw [(hR' t ht).1, (hR' t' ht').1]
  · obtain ⟨x, hx, rfl⟩ := hπ x'
    have e1 : Set.EqOn (fun t => (R' t).P (π x)) (fun t => q t ((R t).P x)) W := fun t ht =>
      (hR' t ht).2.1 x (fun y hy => by rw [hform t (hWU ht)]; exact hx y hy)
    exact (hol_apply hq ((hHol.2 x).mono hWU)).congr e1

end GlobalTheory.CompanionTheory.Ar.Cusp.PhiI

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open GlobalTheory.CompanionTheory.Ar.Cusp.PhiI
open ReciprocityTheory.AnForm.A (IsPsh)

theorem phi_isPsh_continuous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) (I : Submodule (𝓞 E) Λ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → (∀ t ∈ U, (R t).IsCusp I) → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I)) ∧ ContinuousOn (fun t => (R t).nz σ I) U := by
  intro E _ _ _ g Λ _ _ Ψ _ n U R σ m b I hU hHol hCM hB hC
  have hcusp : ∀ t ∈ U, I ≠ ⊥ ∧ IsIsoSub (R t).form I := fun t ht => ⟨(hC t ht).1, (hC t ht).2.2⟩
  rcases U.eq_empty_or_nonempty with rfl | ⟨t₁, ht₁⟩
  · refine ⟨GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n _ _ isOpen_empty (fun z hz => absurd hz (Set.notMem_empty z)),
      continuousOn_empty _⟩
  obtain ⟨⟨r, v, hv⟩, -⟩ := GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t₁) σ I hCM (hcusp t₁ ht₁).2 (hcusp t₁ ht₁).1
  have hnz : ∀ t ∈ U, (R t).nz σ I = (R t).nzOf σ I v ∧ 0 < (R t).nz σ I := fun t ht => by
    have := ((GlobalTheory.T.isotropic_sublattice_covolume_positive E g Λ Ψ (R t) σ I hCM (hcusp t ht).2 (hcusp t ht).1).2 r v hv)
    exact ⟨this.1, this.2.1⟩
  set w : Ψ → Fin r → (Fin n → ℂ) → Fin g → ℂ := fun τ a t => eigComp (R t).B (σ τ) ((R t).P (v a)) with hw
  set idx : ℝ := ((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ) with hidx
  have hidx0 : idx ≠ 0 := by
    rw [hidx]; exact_mod_cast hv.2.2.2
  have hwpos : ∀ t ∈ U, ∀ τ, 0 < ((R t).gram fun a => w τ a t).det.re := fun t ht τ =>
    ((GlobalTheory.T.gram_det_pos_iff_linearIndependent E g Λ (R t) _ _).1
      ((GlobalTheory.T.isotropic_eigencomponent_conjugate_form E g Λ Unit (R t) I (hcusp t ht).2 (σ τ)).2 r v hv.2.1 hv.2.2.1)).1
  have hlog : ∀ t ∈ U, (R t).logDet (fun τ i => b τ i t) - Real.log ((R t).nz σ I) =
      (∑ τ, (Real.log ((R t).gram fun i => b τ i t).det.re - Real.log ((R t).gram fun a => w τ a t).det.re)) +
        Real.log idx := by
    intro t ht
    rw [(hnz t ht).1]
    unfold RiemLat.nzOf RiemLat.logDet
    rw [Real.log_div (Finset.prod_ne_zero_iff.2 fun τ _ => (hwpos t ht τ).ne') hidx0,
      Real.log_prod (fun τ _ => (hwpos t ht τ).ne'), Finset.sum_sub_distrib]
    ring
  refine ⟨GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_of_locally n U _ hU fun t₀ ht₀ => ?_, ?_⟩
  · obtain ⟨W, hWo, ht₀W, hWU, g', Λ', i1, i2, R', q, hR', hq, hker, hcomp⟩ :=
      localQuot hU hHol ht₀ (hC t₀ ht₀).2.1 (hcusp t₀ ht₀).2
    have hloc : ∀ τ, ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧
        IsPsh V (fun t => Real.log ((R t).gram fun i => b τ i t).det.re -
          Real.log ((R t).gram fun a => w τ a t).det.re) := fun τ =>
      perEmb hHol hWo hWU ht₀W hR' hq hker hcomp (fun t ht => (hcusp t ht).2) (σ τ) hv (hB.1 τ)
        (fun t ht => (hB.2 t ht τ).1) (fun t ht => (hB.2 t ht τ).2)
    choose V hVo ht₀V hVW hVp using hloc
    classical
    let V₀ : Set (Fin n → ℂ) := W ∩ ⋂ τ, V τ
    have hV₀o : IsOpen V₀ := hWo.inter (isOpen_iInter_of_finite hVo)
    have hV₀ : ∀ τ, V₀ ⊆ V τ := fun τ x hx => Set.mem_iInter.1 hx.2 τ
    refine ⟨V₀, hV₀o, ⟨ht₀W, Set.mem_iInter.2 ht₀V⟩, ?_⟩
    have hs := isPsh_add (isPsh_sum Finset.univ fun τ _ => GlobalTheory.CompanionTheory.AnForm.PshLocal.isPsh_mono (hV₀ τ) (hVp τ))
      (isPsh_zero V₀ (Real.log idx))
    exact GroundTheory.Heights₂.Heights.NineStatements.isPsh_congr' (fun t ht => (hlog t (hWU ht.1)).symm) hs
  · have hHm : ∀ i j, ContinuousOn (fun t => (R t).Hm i j) U := by
      intro i j
      obtain ⟨h1, h2⟩ := (GlobalTheory.T.holomorphic_family_smooth_entries E g Λ Ψ n U R hU hHol).1 i j
      have e : (fun t => (R t).Hm i j) = fun t => (((R t).Hm i j).re : ℂ) + (((R t).Hm i j).im : ℂ) * Complex.I := by
        funext t; exact (Complex.re_add_im _).symm
      rw [e]
      exact (Complex.continuous_ofReal.comp_continuousOn h1.continuousOn).add
        ((Complex.continuous_ofReal.comp_continuousOn h2.continuousOn).mul continuousOn_const)
    have hwc : ∀ τ a, ContinuousOn (w τ a) U := fun τ a => (hol_eig hHol.2 (σ τ) (v a)).continuousOn
    have hip : ∀ τ a c, ContinuousOn (fun t => (R t).ip (w τ a t) (w τ c t)) U := by
      intro τ a c
      unfold RiemLat.ip
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      refine continuousOn_finset_sum _ fun i _ => ((continuousOn_pi.1 (hwc τ c) i)).mul ?_
      refine continuousOn_finset_sum _ fun j _ => (hHm i j).mul ?_
      exact (continuous_star.comp_continuousOn (continuousOn_pi.1 (hwc τ a) j))
    have hdet : ∀ τ, ContinuousOn (fun t => ((R t).gram fun a => w τ a t).det.re) U := by
      intro τ
      have hm : ContinuousOn (fun t => (R t).gram fun a => w τ a t) U :=
        continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => hip τ a c
      exact Complex.continuous_re.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hm)
    have hc : ContinuousOn (fun t => (∏ τ, ((R t).gram fun a => w τ a t).det.re) / idx) U :=
      (continuousOn_finset_prod _ fun τ _ => hdet τ).div_const _
    refine hc.congr fun t ht => ?_
    rw [(hnz t ht).1]
    rfl

end GlobalTheory.CompanionTheory.Ar.Cusp
