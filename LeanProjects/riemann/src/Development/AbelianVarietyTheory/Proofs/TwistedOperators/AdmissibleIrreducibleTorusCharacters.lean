import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.IwahoriRel

open GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep

section General

variable {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]

theorem isIntegralOp_mem_fixed [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant] {π : Representation ℂ G W}
    {f : G → ℂ} {A : W →ₗ[ℂ] W} (hA : IsIntegralOp μ π f A) {K : Subgroup G} (hf : ∀ k ∈ K, ∀ g, f (k * g) = f g)
    (v : W) : A v ∈ fixed π K := by
  refine GlobalTheory.OpTrace.mem_fixed.2 fun k hk => ?_
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, sub_eq_zero]
  have h1 := (hA v (l ∘ₗ π k)).2
  have h2 := (hA v l).2
  simp only [LinearMap.comp_apply] at h1
  rw [h1, h2]
  refine Eq.trans ?_ (integral_mul_left_eq_self (fun g => f g * l (π g v)) k)
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only [hf k hk, map_mul, Module.End.mul_apply]

theorem hasTrace_eq_zero [MeasurableMul G] {μ : Measure G} [μ.IsMulLeftInvariant] {π : Representation ℂ G W}
    {f : G → ℂ} {K : Subgroup G} (hf : ∀ k ∈ K, ∀ g, f (k * g) = f g) (hK : fixed π K = ⊥) {c : ℂ}
    (h : HasTrace μ π f c) : c = 0 := by
  obtain ⟨A, hA, -, rfl⟩ := h
  have h0 : A = 0 := LinearMap.ext fun v => by
    have := isIntegralOp_mem_fixed hA hf v
    rw [hK] at this
    exact (Submodule.mem_bot ℂ).1 this
  subst h0
  have e : ((0 : W →ₗ[ℂ] W).restrict (p := LinearMap.range (0 : W →ₗ[ℂ] W)) (q := LinearMap.range (0 : W →ₗ[ℂ] W))
      fun v _ => LinearMap.mem_range_self (0 : W →ₗ[ℂ] W) v) = 0 := LinearMap.ext fun x => Subtype.ext (by simp)
  rw [e, map_zero]

theorem hasTrace_eq_of_equiv {W' : Type} [AddCommGroup W'] [Module ℂ W'] {μ : Measure G} {π : Representation ℂ G W}
    {π' : Representation ℂ G W'} (e : π.Equiv π') {f : G → ℂ} {c c' : ℂ} (h : HasTrace μ π f c)
    (h' : HasTrace μ π' f c') : c = c' := by
  obtain ⟨A, hA, hfd, rfl⟩ := h
  obtain ⟨A', hA', -, rfl⟩ := h'
  let E := e.toLinearEquiv
  have he : ∀ g w, E (π g w) = π' g (E w) := fun g w => LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) w
  let T : W' →ₗ[ℂ] W' := (E : W →ₗ[ℂ] W') ∘ₗ A ∘ₗ (E.symm : W' →ₗ[ℂ] W)
  have hT : IsIntegralOp μ π' f T := by
    intro v l
    have h1 := hA (E.symm v) (l ∘ₗ (E : W →ₗ[ℂ] W'))
    have h2 : ∀ g, f g * (l ∘ₗ (E : W →ₗ[ℂ] W')) (π g (E.symm v)) = f g * l (π' g v) := fun g => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, he, LinearEquiv.apply_symm_apply]
    simp only [h2] at h1
    exact ⟨h1.1, h1.2⟩
  obtain rfl := hA'.unique hT
  haveI := hfd.1
  have key := GlobalTheory.OpTrace.finRankTrace_eq_of_equiv E (T := A) (T' := T) fun v => by
    simp [T]
  exact key.2.symm

end General

section Transport

variable {G H W : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H] [AddCommGroup W] [Module ℂ W]

theorem hasTrace_map_iff (φ : G ≃ₜ* H) (μ : Measure G) (π : Representation ℂ G W) (f : G → ℂ) (c : ℂ) :
    HasTrace (μ.map φ) (π.comp φ.symm.toMulEquiv.toMonoidHom) (f ∘ φ.symm) c ↔ HasTrace μ π f c := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  have hm : μ.map φ = μ.map e := rfl
  have key : ∀ A : W →ₗ[ℂ] W,
      IsIntegralOp (μ.map φ) (π.comp φ.symm.toMulEquiv.toMonoidHom) (f ∘ φ.symm) A ↔ IsIntegralOp μ π f A := by
    intro A
    refine forall_congr' fun v => forall_congr' fun l => ?_
    have hc : (fun x => (f ∘ φ.symm) x * l ((π.comp φ.symm.toMulEquiv.toMonoidHom) x v)) ∘ e =
        fun g => f g * l (π g v) := by
      funext g
      show f (φ.symm (φ g)) * l (π (φ.symm (φ g)) v) = f g * l (π g v)
      rw [φ.symm_apply_apply]
    rw [hm, integrable_map_equiv e, integral_map_equiv e, hc]
    refine and_congr Iff.rfl ?_
    rw [← hc]
    exact Iff.rfl
  exact exists_congr fun A => and_congr_left fun _ => key A

end Transport

section Core

open GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r : ℕ}

theorem cosetInd_mul (t : Fin r → kˣ) {x : GL (Fin r) k} (hx : x ∈ iwahori k (Fin r)) (g : GL (Fin r) k) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd t (x * g) = GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd t g := by
  have key : x * g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.iwahoriCoset t ↔ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.iwahoriCoset t := by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      refine ⟨x⁻¹ * a, mul_mem (inv_mem hx) ha, b, hb, ?_⟩
      rw [show g = x⁻¹ * (x * g) by group, e]
      simp only [mul_assoc]
    · rintro ⟨a, ha, b, hb, e⟩
      refine ⟨x * a, mul_mem hx ha, b, hb, ?_⟩
      rw [e]
      simp only [mul_assoc]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd
  by_cases h : g ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.iwahoriCoset t
  · rw [indicator_of_mem h, indicator_of_mem (key.2 h)]
  · rw [indicator_of_notMem h, indicator_of_notMem fun h' => h (key.1 h')]

variable (k r) in

theorem relation_gl (hI : IwahoriTrace) (hE : ExponentsSeparate) (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    [MeasurableSpace (GL (Fin r) k)] [BorelSpace (GL (Fin r) k)] (μ : Measure (GL (Fin r) k)) [μ.IsHaarMeasure]
    (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]
    (π : ∀ i, Representation ℂ (GL (Fin r) k) (N i)) (hirr : ∀ i, (π i).IsIrreducible)
    (hadm : ∀ i, IsAdmissible (π i)) (d : Fin n → ℂ)
    (hd : ∀ t ∈ strictCone ϖ r, ∀ b : Fin n → ℂ,
      (∀ i, HasTrace μ (π i) (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd t) (b i)) → ∑ i, d i * b i = 0)
    (f : GL (Fin r) k → ℂ) (hf : ∀ x ∈ iwahori k (Fin r), ∀ g, f (x * g) = f g)
    (b : Fin n → ℂ) (hb : ∀ i, HasTrace μ (π i) f (b i)) : ∑ i, d i * b i = 0 := by
  classical
  obtain ⟨hDom, hTF⟩ := hI k r
  have hex := fun i => hTF μ (N i) (π i) (hadm i)
  choose hfd htr E hEx hEtr using hex

  let P : Finset (Fin n) := Finset.univ.filter fun i => fixed (π i) (iwahori k (Fin r)) ≠ ⊥
  let iso : Fin n → Fin n → Prop := fun i j => Nonempty ((π i).Equiv (π j))
  have iso_symm : ∀ {i j}, iso i j → iso j i := fun ⟨e⟩ => ⟨e.symm⟩
  have iso_trans : ∀ {i j l}, iso i j → iso j l → iso i l := fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩
  have hne : ∀ i ∈ P, (P.filter fun j => iso j i).Nonempty := fun i hi =>
    ⟨i, Finset.mem_filter.2 ⟨hi, ⟨Representation.Equiv.refl _⟩⟩⟩
  let rep : Fin n → Fin n := fun i => if hi : i ∈ P then (P.filter fun j => iso j i).min' (hne i hi) else i
  have rep_spec : ∀ i ∈ P, rep i ∈ P ∧ iso (rep i) i := fun i hi => by
    have := Finset.min'_mem _ (hne i hi)
    simp only [rep, dif_pos hi]
    exact Finset.mem_filter.1 this
  have rep_eq : ∀ i ∈ P, ∀ j ∈ P, iso i j → rep i = rep j := fun i hi j hj h => by
    have e : (P.filter fun l => iso l i) = P.filter fun l => iso l j :=
      Finset.filter_congr fun l _ => ⟨fun h' => iso_trans h' h, fun h' => iso_trans h' (iso_symm h)⟩
    simp only [rep, dif_pos hi, dif_pos hj]
    congr 1
  let R : Finset (Fin n) := P.image rep
  have hRP : ∀ j ∈ R, j ∈ P ∧ rep j = j := fun j hj => by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    obtain ⟨h1, h2⟩ := rep_spec i hi
    exact ⟨h1, rep_eq _ h1 _ hi h2⟩
  let D : Fin n → ℂ := fun j => ∑ i ∈ P with rep i = j, d i

  have hsum : ∀ w : Fin n → ℂ, (∀ i ∉ P, w i = 0) → (∀ i ∈ P, w i = w (rep i)) →
      ∑ i, d i * w i = ∑ j ∈ R, D j * w j := by
    intro w h0 h1
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun i _ hi => by rw [h0 i hi, mul_zero]),
      Finset.sum_congr rfl (g := fun i => d i * w (rep i)) fun i hi => by rw [h1 i hi],
      ← Finset.sum_fiberwise_of_maps_to (g := rep) (t := R) (fun i hi => Finset.mem_image_of_mem rep hi)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [D, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hcontr : ∀ t ∈ strictCone ϖ r, Contracts t := by
    rintro t ⟨a, ha, rfl⟩
    exact hDom ϖ hϖ a ha.antitone
  have hvol : (μ.real (iwahori k (Fin r) : Set (GL (Fin r) k)) : ℂ) ≠ 0 := by
    have h1 := (GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori k (Fin r)).measure_pos μ ⟨1, one_mem _⟩
    have h2 := (GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori k (Fin r)).measure_ne_top (μ := μ)
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'

  have hrel : ∀ t ∈ strictCone ϖ r, ∑ j ∈ R, D j * charSum (E j) t = 0 := by
    intro t ht
    have hc0 : (μ.real (iwahori k (Fin r) : Set (GL (Fin r) k)) : ℂ) * ((deltaB t : ℂ))⁻¹ ≠ 0 :=
      mul_ne_zero hvol (inv_ne_zero (by exact_mod_cast (deltaB_pos t).ne'))
    have htr' : ∀ i, HasTrace μ (π i) (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd t)
        ((μ.real (iwahori k (Fin r) : Set (GL (Fin r) k)) : ℂ) * ((deltaB t : ℂ))⁻¹ * charSum (E i) t) :=
      fun i => hEtr i t (hcontr t ht)
    have h0 := hd t ht _ htr'
    rw [hsum _ (fun i hi => hasTrace_eq_zero (fun x hx g => cosetInd_mul t hx g) (by simpa [P] using hi) (htr' i))
      (fun i hi => hasTrace_eq_of_equiv (rep_spec i hi).2.some.symm (htr' i) (htr' (rep i)))] at h0
    rw [← mul_right_inj' hc0, mul_zero, ← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

  have hD : ∀ j ∈ R, D j = 0 := by
    let σ : Fin R.card → Fin n := fun l => (R.equivFin.symm l).1
    have hσR : ∀ l, σ l ∈ R := fun l => (R.equivFin.symm l).2
    have hσinj : Function.Injective σ := fun l l' h => R.equivFin.symm.injective (Subtype.ext h)
    have key := hE k ϖ hϖ r R.card (fun l => N (σ l)) (fun l => π (σ l)) (fun l => hirr _) (fun l => hadm _)
      (fun l l' hll' => ⟨fun e => hll' (hσinj (by
          rw [← (hRP _ (hσR l)).2, ← (hRP _ (hσR l')).2]
          exact rep_eq _ (hRP _ (hσR l)).1 _ (hRP _ (hσR l')).1 ⟨e⟩))⟩)
      (fun l => by simpa [P] using (hRP _ (hσR l)).1)
      (fun l => E (σ l)) (fun l χ => ((hEx (σ l)).2 χ).symm) (fun l => D (σ l)) (fun t ht => by
        have := hrel t ht
        rw [← Finset.sum_coe_sort R, ← Equiv.sum_comp R.equivFin.symm] at this
        exact this)
    intro j hj
    have := key (R.equivFin ⟨j, hj⟩)
    simpa [σ] using this
  rw [hsum b (fun i hi => hasTrace_eq_zero hf (by simpa [P] using hi) (hb i))
    (fun i hi => hasTrace_eq_of_equiv (rep_spec i hi).2.some.symm (hb i) (hb (rep i)))]
  exact Finset.sum_eq_zero fun j hj => by rw [hD j hj, zero_mul]

end Core

end GlobalTheory.IwahoriRel

namespace GlobalTheory.IwahoriRel

open GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep

theorem relation_of_iwahoriTrace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → ∀ (D : D7) (V : HSp D) (U : AuxiliaryPlaceHermitianSpace V) (μ : Measure (Gv V U.u)), μ.IsHaarMeasure → ∀ (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (π : ∀ i, Representation ℂ (Gv V U.u) (N i)), (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) → ∀ d : Fin n → ℂ, (∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) (U.frame.cosetFn t) (b i)) → ∑ i, d i * b i = 0) → ∀ f ∈ CcLoc D.sp.cm.sig V.gram U.u, (∀ k ∈ U.frame.iwahori, ∀ g, f (k * g) = f g) → ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) f (b i)) → ∑ i, d i * b i = 0 := by
  intro hI hE D V U μ hμ n N _ _ π hirr hadm d hd f hf hfI b hb
  letI := GlobalTheory.LocalData.complRel U.u
  haveI := GlobalTheory.LocalData.isLocalField U.u
  letI : MeasurableSpace (GL (Fin V.rank) (Fv D.host.F U.u)) := borel _
  haveI : BorelSpace (GL (Fin V.rank) (Fv D.host.F U.u)) := ⟨rfl⟩
  haveI : (μ.map U.frame.equiv).IsHaarMeasure :=
    U.frame.equiv.toMulEquiv.isHaarMeasure_map μ U.frame.equiv.continuous U.frame.equiv.symm.continuous
  have hcos : ∀ t, U.frame.cosetFn t ∘ U.frame.equiv.symm = GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd t := fun t => funext fun x => by
    have key : U.frame.equiv.symm x ∈ U.frame.iwahoriCoset t ↔ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.iwahoriCoset t := by
      rw [U.frame.mem_iwahoriCoset, ContinuousMulEquiv.apply_symm_apply]
      rfl
    simp only [Function.comp_apply, GlobalTheory.Orb.SplitAt.cosetFn, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd]
    by_cases h : x ∈ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.iwahoriCoset t
    · rw [indicator_of_mem (key.2 h), indicator_of_mem h]
      rfl
    · rw [indicator_of_notMem (fun h' => h (key.1 h')), indicator_of_notMem h]
  refine relation_gl (Fv D.host.F U.u) V.rank hI hE U.ϖ U.unif.valuation_eq (μ.map U.frame.equiv) n N
    (fun i => (π i).comp U.frame.equiv.symm.toMulEquiv.toMonoidHom)
    (fun i => GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv _ _ (hirr i))
    (fun i => GlobalTheory.CuspMult.isAdmissible_comp_equiv _ U.frame.equiv.symm (hadm i)) d ?_ (f ∘ U.frame.equiv.symm) ?_ b
    (fun i => (hasTrace_map_iff U.frame.equiv μ (π i) f (b i)).2 (hb i))
  · intro t ht b' hb'
    exact hd t ht b' fun i => (hasTrace_map_iff U.frame.equiv μ (π i) _ (b' i)).1 (by rw [hcos]; exact hb' i)
  · intro x hx g
    simp only [Function.comp_apply, map_mul]
    refine hfI _ (Subgroup.mem_comap.2 ?_) _
    show U.frame.equiv (U.frame.equiv.symm x) ∈ GlobalTheory.SmGL.iwahori (Fv D.host.F U.u) (Fin V.rank)
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact hx

end GlobalTheory.IwahoriRel
