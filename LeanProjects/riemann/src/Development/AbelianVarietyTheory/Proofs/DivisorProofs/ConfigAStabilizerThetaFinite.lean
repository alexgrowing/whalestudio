import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanCommutingIsometriesBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedNormCompactPreimage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionStableBaseChange

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XTermFinParts

section Group

variable {Y : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

theorem eventually_add_eq {g : Y → ℂ} (hg : g ∈ SB Y) : ∀ᶠ t in 𝓝 (0 : Y), ∀ y, g (y + t) = g y := by
  have hc : IsCompact (tsupport g) := hg.2
  have hl : IsLocallyConstant g := hg.1
  have key : ∀ s : Y → Y, Continuous s → s 0 = 0 → ∀ᶠ t in 𝓝 (0 : Y), ∀ y ∈ tsupport g, g (y + s t) = g y := by
    intro s hs hs0
    refine hc.eventually_forall_of_forall_eventually fun y _ => ?_
    have h1 : IsLocallyConstant fun p : Y × Y => g (p.2 + s p.1) :=
      hl.comp_continuous (continuous_snd.add (hs.comp continuous_fst))
    have h2 : IsLocallyConstant fun p : Y × Y => g p.2 := hl.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (0, y), h2.eventually_eq (0, y)] with p a b
    rw [a, b]; simp [hs0]
  filter_upwards [key id continuous_id rfl, key (fun t => -t) continuous_neg neg_zero] with t h1 h2 y
  by_cases hy : y ∈ tsupport g
  · exact h1 y hy
  by_cases hy' : y + t ∈ tsupport g
  · have := h2 _ hy'
    simp only [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy']

theorem exists_cosets [T2Space Y] (L : AddSubgroup Y) (ho : IsOpen (L : Set Y)) (hc : IsCompact (L : Set Y)) {Ω : Set Y}
    (hΩ : IsCompact Ω) : ∃ (m : ℕ) (c : Fin m → Y) (φ : Fin m → Y → ℂ), (∀ j, φ j ∈ SB Y) ∧
      ∀ d : Y → ℂ, (∀ y, ∀ t ∈ L, d (y + t) = d y) → (∀ y, y ∉ Ω → d y = 0) → ∀ y, d y = ∑ j, d (c j) * φ j y := by
  haveI : DiscreteTopology (Y ⧸ L) := QuotientAddGroup.discreteTopology ho
  have hq : Continuous (QuotientAddGroup.mk : Y → Y ⧸ L) := QuotientAddGroup.continuous_mk
  have hfin : ((QuotientAddGroup.mk : Y → Y ⧸ L) '' Ω).Finite := (hΩ.image hq).finite_of_discrete
  set S := hfin.toFinset
  let q : Fin S.card → Y ⧸ L := fun j => (S.equivFin.symm j).1
  refine ⟨S.card, fun j => (q j).out, fun j y => if (y : Y ⧸ L) = q j then 1 else 0, fun j => ⟨?_, ?_⟩, ?_⟩
  · exact (IsLocallyConstant.of_discrete fun s : Y ⧸ L => if s = q j then (1 : ℂ) else 0).comp_continuous hq
  · refine HasCompactSupport.intro (hc.image (continuous_const.add continuous_id : Continuous fun t => (q j).out + t)) ?_
    intro y hy
    beta_reduce
    rw [if_neg]
    intro h
    refine hy ⟨-(q j).out + y, ?_, by simp⟩
    exact QuotientAddGroup.eq.1 (by rw [h, QuotientAddGroup.out_eq'])
  · intro d hd h0 y
    beta_reduce
    have hinv : ∀ a b : Y, (a : Y ⧸ L) = b → d a = d b := fun a b h => by
      have := hd a _ (QuotientAddGroup.eq.1 h)
      rw [add_neg_cancel_left] at this
      exact this.symm
    by_cases hy : (y : Y ⧸ L) ∈ S
    · rw [Finset.sum_eq_single (S.equivFin ⟨_, hy⟩)]
      · have e : q (S.equivFin ⟨_, hy⟩) = y := by simp [q]
        rw [e, if_pos rfl, mul_one]
        exact hinv _ _ (QuotientAddGroup.out_eq' _).symm
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        apply hj
        rw [← Equiv.symm_apply_eq]
        exact Subtype.ext h.symm
      · simp
    · rw [h0 y fun h => hy (hfin.mem_toFinset.2 ⟨y, h, rfl⟩)]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hy (h ▸ (S.equivFin.symm j).2)

end Group

section Fin

variable {F : Type} [Field F] [NumberField F]

variable (F) in

def intA : AddSubgroup (Af F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem _
  neg_mem' ha v := neg_mem (ha v)

theorem isOpen_intA : IsOpen (intA F : Set (Af F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intA : IsCompact (intA F : Set (Af F)) := GlobalTheory.AdeleCocompact.isCompact_integral F

theorem exists_factorial {N : Set (Af F)} (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ n : ℕ, ∀ z ∈ intA F, ((n.factorial : ℕ) : Af F) * z ∈ N := by
  have hev : ∀ᶠ t in 𝓝 (0 : Af F), ∀ z ∈ (intA F : Set (Af F)), t * z ∈ N := by
    refine isCompact_intA.eventually_forall_of_forall_eventually fun z _ => ?_
    refine (continuous_mul.continuousAt (x := ((0 : Af F), z))).preimage_mem_nhds ?_
    simpa using hN
  exact ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hev).exists

theorem isCompact_mul_mem {x : F} (hx : x ≠ 0) : IsCompact {y : Af F | algebraMap F (Af F) x * y ∈ intA F} := by
  have h := isCompact_intA.image (continuous_const_mul (algebraMap F (Af F) x⁻¹))
  convert h using 1
  ext y
  constructor
  · intro hy
    exact ⟨_, hy, by beta_reduce; rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul]⟩
  · rintro ⟨z, hz, rfl⟩
    show algebraMap F (Af F) x * (algebraMap F (Af F) x⁻¹ * z) ∈ intA F
    rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul]

theorem exists_openCompact {κ : Type} [Fintype κ] {N : Set (κ → Af F)} (hN : N ∈ 𝓝 (0 : κ → Af F)) :
    ∃ L : AddSubgroup (κ → Af F), IsOpen (L : Set (κ → Af F)) ∧ IsCompact (L : Set (κ → Af F)) ∧ (L : Set _) ⊆ N := by
  rw [nhds_pi, Filter.mem_pi'] at hN
  obtain ⟨I, t, ht, hsub⟩ := hN
  obtain ⟨n, hn⟩ := exists_factorial (F := F) (N := ⋂ i, t i) (Filter.iInter_mem.2 ht)
  have hx : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  let L₀ : AddSubgroup (Af F) := (intA F).comap (AddMonoidHom.mulLeft (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹))
  refine ⟨AddSubgroup.pi Set.univ fun _ => L₀, ?_, ?_, fun y hy => hsub fun i _ => ?_⟩
  · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intA.preimage (continuous_const_mul _)
  · exact isCompact_univ_pi fun _ => isCompact_mul_mem (inv_ne_zero hx)
  · have := Set.mem_iInter.1 (hn _ (hy i trivial)) i
    rwa [AddMonoidHom.coe_mulLeft, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hx,
      map_one, one_mul] at this

variable {ψ : AddChar (AF F) ℂ}

theorem psi_intA (hψ : IsStd ψ) {a : Af F} (ha : a ∈ intA F) : ψ (pairA F 0 a) = 1 := by
  have h := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ) (algebraMap F (Af F) 1)).1
    ((GlobalTheory.Idele.algebraMap_mem_adelicIdeal GlobalTheory.StdDual.codiff_ne_zero 1).2
      (GlobalTheory.StdDual.one_le_codiff (FractionalIdeal.one_mem_one _))) a ha
  rwa [map_one, mul_one] at h

theorem exists_compact_annihilator (hψ : IsStd ψ) {N : Set (Af F)} (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ C : Set (Af F), IsCompact C ∧ ∀ y, (∀ a ∈ N, ψ (pairA F 0 (y * a)) = 1) → y ∈ C := by
  obtain ⟨n, hn⟩ := exists_factorial hN
  have hx : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  have hI : (GlobalTheory.StdDual.codiff F)⁻¹ ≠ 0 := inv_ne_zero GlobalTheory.StdDual.codiff_ne_zero
  obtain ⟨a, ha, ha0⟩ : ∃ a : F, a ∈ (GlobalTheory.StdDual.codiff F)⁻¹ ∧ a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hI (FractionalIdeal.eq_zero_iff.2 h)
  refine ⟨_, isCompact_mul_mem (mul_ne_zero ha0 hx), fun y hy v => ?_⟩
  have h1 := (GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1 (GlobalTheory.LatVacArith.psi_fin_rat hψ)
    (((n.factorial : ℕ) : Af F) * y)).2 fun α hα => by
      have := hy _ (hn α hα)
      rwa [show y * (((n.factorial : ℕ) : Af F) * α) = α * (((n.factorial : ℕ) : Af F) * y) by ring] at this
  have h2 := (GlobalTheory.Idele.mem_adelicIdeal_iff GlobalTheory.StdDual.codiff_ne_zero).1 h1 v
  have h3 := (GlobalTheory.Idele.mem_adelicIdeal_iff hI).1 ((GlobalTheory.Idele.algebraMap_mem_adelicIdeal hI a).2 ha) v
  rw [FractionalIdeal.count_inv, neg_neg] at h3
  rw [map_mul, map_natCast, mul_assoc, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.adele_mul_apply, map_mul]
  refine (mul_le_mul' h3 h2).trans ?_
  rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

end Fin

section Heis

variable {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ]

variable (F) in

def infOne : AF F := pairA F 1 0

theorem fst_eq_zero {a : AF F} (h : infOne F * a = 0) : a.1 = 0 :=
  (one_mul a.1).symm.trans (congrArg Prod.fst h)

theorem infOne_mul_pairA (a : Af F) : infOne F * pairA F 0 a = 0 :=
  Prod.ext (mul_zero (1 : Ainf F)) (zero_mul a)

theorem eq_pairA {a : AF F} (h : infOne F * a = 0) : a = pairA F 0 (sndA F a) := Prod.ext (fst_eq_zero h) rfl

theorem eventually_schr_eq (hψ : IsStd ψ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∀ᶠ w in 𝓝 (0 : (κ → AF F) × (κ → AF F)), infOne F • w = 0 → schr ψ w Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Eventually.of_forall fun w _ => funext fun x => by simp [schr]
  | add a b _ _ ha hb =>
    filter_upwards [ha, hb] with w h1 h2 hw
    funext x
    have e1 := congrFun (h1 hw) x
    have e2 := congrFun (h2 hw) x
    simp only [schr, Pi.add_apply] at e1 e2 ⊢
    rw [mul_add, e1, e2]
  | smul c a _ ha =>
    filter_upwards [ha] with w h1 hw
    funext x
    have e1 := congrFun (h1 hw) x
    simp only [schr, Pi.smul_apply, smul_eq_mul] at e1 ⊢
    rw [mul_left_comm, e1]
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    have hs : Continuous (sndA F) := continuous_snd
    have c1 : Continuous fun w : (κ → AF F) × (κ → AF F) => fun i => sndA F (w.1 i) :=
      continuous_pi fun i => hs.comp ((continuous_apply i).comp continuous_fst)
    have c2 : Continuous fun w : (κ → AF F) × (κ → AF F) => fun i => sndA F (w.2 i) :=
      continuous_pi fun i => hs.comp ((continuous_apply i).comp continuous_snd)
    have t1 : Tendsto (fun w : (κ → AF F) × (κ → AF F) => fun i => sndA F (w.1 i)) (𝓝 0) (𝓝 0) :=
      c1.tendsto' 0 0 (funext fun i => map_zero _)
    have h2 : ∀ᶠ w in 𝓝 (0 : (κ → AF F) × (κ → AF F)), ∀ y ∈ tsupport g,
        y ⬝ᵥ (fun i => sndA F (w.2 i)) + sndA F (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ∈ intA F := by
      refine IsCompact.eventually_forall_of_forall_eventually hg.2 fun y _ => ?_
      have c3 : Continuous fun p : ((κ → AF F) × (κ → AF F)) × (κ → Af F) =>
          p.2 ⬝ᵥ (fun i => sndA F (p.1.2 i)) + sndA F (⅟(2 : AF F) * (p.1.1 ⬝ᵥ p.1.2)) :=
        (continuous_snd.dotProduct (c2.comp continuous_fst)).add
          (hs.comp (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd)))
      refine c3.continuousAt.preimage_mem_nhds (isOpen_intA.mem_nhds ?_)
      simp [dotProduct]
    filter_upwards [t1.eventually (eventually_add_eq hg), h2] with w h1 h2 hw
    have hw1 : ∀ i, infOne F * w.1 i = 0 := fun i => congrFun (congrArg Prod.fst hw) i
    have hw2 : ∀ i, infOne F * w.2 i = 0 := fun i => congrFun (congrArg Prod.snd hw) i
    funext x
    have e1 : pureA F f g (x + w.1) = pureA F f g x := by
      unfold pureA
      congr 1
      · congr 1
        funext i
        congr 1
        exact (congrArg (fun t => (x i).1 + t) (fst_eq_zero (hw1 i))).trans (add_zero _)
      · exact h1 fun i => sndA F (x i)
    rw [schr, e1]
    by_cases hx : (fun i => sndA F (x i)) ∈ tsupport g
    · have e2 : infOne F * (x ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) = 0 := by
        have e3 : ∀ z : κ → AF F, infOne F * (z ⬝ᵥ w.2) = 0 := fun z => by
          rw [dotProduct, Finset.mul_sum]
          exact Finset.sum_eq_zero fun i _ => by rw [mul_left_comm, hw2, mul_zero]
        rw [mul_add, mul_left_comm, e3, e3, mul_zero, add_zero]
      rw [eq_pairA e2, psi_intA hψ, one_mul]
      have := h2 _ hx
      rwa [map_add, dotProduct, map_sum, Finset.sum_congr rfl fun i _ => map_mul (sndA F) (x i) (w.2 i)]
    · have : pureA F f g x = 0 := by
        unfold pureA
        exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hx)
      rw [this, mul_zero]

theorem exists_parts (hψ : IsStd ψ) {N : Set ((κ → AF F) × (κ → AF F))} (hN : N ∈ 𝓝 0) :
    ∃ (m : ℕ) (c : Fin m → κ → Af F) (φ : Fin m → (κ → Af F) → ℂ), (∀ j, φ j ∈ SB _) ∧
      ∀ D : (κ → AF F) → ℂ, (∀ w ∈ N, infOne F • w = 0 → schr ψ w D = D) →
        ∀ x, D x = ∑ j, D (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  let up : (κ → Af F) → κ → AF F := fun t i => pairA F 0 (t i)
  have hup : Continuous up := continuous_pi fun i => continuous_const.prodMk (continuous_apply i)
  have hup0 : ∀ t, infOne F • up t = 0 := fun t => funext fun i => infOne_mul_pairA _
  have t1 : Tendsto (fun t => (up t, (0 : κ → AF F))) (𝓝 0) (𝓝 0) := (hup.prodMk continuous_const).tendsto' 0 0 rfl
  have t2 : ∀ i : κ, Tendsto (fun a : Af F => ((0 : κ → AF F), up (Pi.single i a))) (𝓝 0) (𝓝 0) := fun i =>
    (continuous_const.prodMk (hup.comp (continuous_single i))).tendsto' 0 0 (by
      show ((0 : κ → AF F), up (Pi.single i 0)) = 0
      rw [Pi.single_zero]; rfl)
  obtain ⟨L, hLo, hLc, hLN⟩ := exists_openCompact (t1 hN)
  obtain ⟨C, hC, hCN⟩ := exists_compact_annihilator hψ (Filter.iInter_mem.2 fun i => t2 i hN)
  obtain ⟨m, c, φ, hφ, H⟩ := exists_cosets L hLo hLc (isCompact_univ_pi fun _ : κ => hC)
  refine ⟨m, c, φ, hφ, fun D hD x => H (fun y => D fun q => ((x q).1, y q)) (fun y t ht => ?_) (fun y hy => ?_) _⟩
  · have h := congrFun (hD _ (hLN ht) (Prod.ext (hup0 t) (smul_zero _))) fun q => pairA F (x q).1 (y q)
    simp only [schr, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul] at h
    refine Eq.trans (congrArg D (funext fun q => ?_)) h
    exact Prod.ext (add_zero _).symm rfl
  · by_contra h0
    refine hy fun i _ => hCN _ fun a ha => ?_
    have h := congrFun (hD _ (Set.mem_iInter.1 ha i) (Prod.ext (smul_zero _) (hup0 _))) fun q => pairA F (x q).1 (y q)
    simp only [schr, zero_dotProduct, mul_zero, add_zero] at h
    have h1 := (mul_left_eq_self₀.1 h).resolve_right h0
    rw [← h1, dotProduct, Finset.sum_eq_single i]
    · congr 1
      refine Prod.ext (mul_zero _).symm ?_
      show y i * a = y i * Pi.single (M := fun _ => Af F) i a i
      rw [Pi.single_eq_same]
    · intro j _ hj
      refine Prod.ext (mul_zero _) ?_
      show y j * Pi.single (M := fun _ => Af F) i a j = 0
      rw [Pi.single_eq_of_ne hj, mul_zero]
    · simp

end Heis

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem rho_comm {R W κ : Type} [CommRing R] [Invertible (2 : R)] [AddCommGroup W] [Module R W] [Fintype κ] {Bf : W → W → R}
    (d : Darboux Bf κ) (ψ : AddChar R ℂ) {u s : W} (h : Bf u s = 0) (Φ : (κ → R) → ℂ) :
    d.rho ψ u (d.rho ψ s Φ) = d.rho ψ s (d.rho ψ u Φ) := by
  rw [d.form, sub_eq_zero] at h
  funext x
  simp only [Darboux.rho, schr, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, h]
  congr 2
  · ring
  · abel

theorem symp_eq_zero {B : Base F E} {n n₁ d : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B X X₁ i₀ i₁) (JB : Matrix (Fin d) (Fin d) (AE F E)) (z : Matrix (Fin n₁) (Fin d) (AE F E))
    (l : AE F E) (y : Fin d → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.x) y) = 0 := by
  have h0 : ∀ a, ∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.x k) = 0 := fun a => by
    have h := congrArg (inclR (F := F) (AF F)) (hH.orth (Pi.single a 1)).1
    rw [map_zero, Matrix.mulVec_single_one] at h
    rw [← h]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, mul_assoc]
    rfl
  have h1 : hTens (cA σ) (incM F X.J) JB (incM F H.ι * z) (l • Matrix.vecMulVec (incV F H.x) y) =
      ∑ a, ∑ j, ∑ m, (∑ i, ∑ k, incM F H.ι i a * incM F X.J i k * cA σ (incV F H.x k)) *
        (z a j * JB j m * cA σ l * cA σ (y m)) := by
    simp only [hTens, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, map_mul, Finset.sum_mul]
    simp only [← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv ⟨fun p => (p.2.2.2.2, p.2.1, p.2.2.2.1, p.1, p.2.2.1),
      fun p => (p.2.2.2.1, p.2.1, p.2.2.2.2, p.2.2.1, p.1), fun _ => rfl, fun _ => rfl⟩ _ _ fun p => ?_
    simp only [Equiv.coe_fn_mk]
    ring
  rw [symp, h1]
  simp [h0]

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have e : compInf F E w (cA σ z) = sigR w.Completion σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  simp only [piInf, RingHom.comp_apply, e]
  exact (infEmb_sigR h τ _).symm

theorem exists_compact_entries {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) :
    ∃ C : Set (AE F E), IsCompact C ∧ ∀ g ∈ K, ∀ i j, mat g i j ∈ C := by
  have hcm : IsCMExt F E σ := hB.cm
  choose Rw hRw using fun w => GlobalTheory.isCartan_entries_bounded _ _ (hX.cartan w)
  set R : ℝ := ∑ w, |Rw w|
  have hlat := hX.lat
  obtain ⟨Cf, hCf, hCfe⟩ := GlobalTheory.StabCompact.exists_compact_entries F E X.L hlat.fg hlat.span_eq_top
  obtain ⟨C, hC, hCe⟩ := GlobalTheory.AdeleBoundedCompact.exists_compact_of_bounded F E σ hcm B.emb Cf hCf R
  refine ⟨C, hC, fun g hg i j => hCe _ ?_ ?_⟩
  · exact hCfe _ (GlobalTheory.FinPartLat.finite_part F E n X (mat g) fun z hz => (((hK g).1 hg).2 z hz).1) i j
  · intro w
    have hu : ((mat g).map (piInf (B.emb w))).transpose * X.J.map (B.emb w).1 *
        ((mat g).map (piInf (B.emb w))).map star = X.J.map (B.emb w).1 := by
      have h2 := congrArg (fun Y : Matrix (Fin n) (Fin n) (AE F E) => Y.map (piInf (B.emb w)))
        (show (mat g).transpose * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2)
      simp only [Matrix.map_mul] at h2
      have e1 : (incM F X.J).map (piInf (B.emb w)) = X.J.map (B.emb w).1 := by
        ext i j
        simp [incM, piInf, compInf, inclR, infEmb_tmul]
      have e2 : ((mat g).map (cA σ)).map (piInf (B.emb w)) = ((mat g).map (piInf (B.emb w))).map star := by
        ext i j
        simp only [Matrix.map_apply]
        exact piInf_cA hcm _ _
      rw [e1] at h2
      rw [← e2, ← Matrix.transpose_map]
      exact h2
    have hb := hRw w _ hu (((hK g).1 hg).1 w).eq i j
    calc ‖piInf (B.emb w) (mat g i j)‖ = ‖(mat g).map (piInf (B.emb w)) i j‖ := rfl
      _ ≤ Rw w := hb
      _ ≤ |Rw w| := le_abs_self _
      _ ≤ R := Finset.single_le_sum (f := fun w => |Rw w|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)

theorem eventually_rho_om_eq {B : Base F E} {n d r s : ℕ} {X : Spc F E n} {W : Spc F E d} (hB : B.IsGood σ)
    (hX : X.IsHerm σ B r s) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (M : Model σ X W) {χ χ' : Chr F E}
    {om : Rep σ X W} (hom : M.IsWeil B.ψ χ χ' om) {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (h : UA σ W.J) :
    ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)), infOne F • u = 0 →
      ∀ k ∈ K, M.co.rho B.ψ u (om (k, h) Φ) = om (k, h) Φ := by
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous (M.co.e : Matrix (Fin n) (Fin d) (AE F E) → _) :=
    IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  obtain ⟨C, hC, hCK⟩ := exists_compact_entries hB hX hK
  have hC' : IsCompact (X := Matrix (Fin n) (Fin n) (AE F E)) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have h1 : ∀ᶠ u in 𝓝 (0 : Matrix (Fin n) (Fin d) (AE F E)),
      ∀ m : Matrix (Fin n) (Fin n) (AE F E), m ∈ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C) →
        infOne F • M.co.e (m * u * (mat h⁻¹)ᵀ) = 0 → schr B.ψ (M.co.e (m * u * (mat h⁻¹)ᵀ)) Φ = Φ := by
    refine hC'.eventually_forall_of_forall_eventually fun m _ => ?_
    have c : Continuous fun p : Matrix (Fin n) (Fin d) (AE F E) × Matrix (Fin n) (Fin n) (AE F E) =>
        M.co.e (p.2 * p.1 * (mat h⁻¹)ᵀ) :=
      he.comp ((continuous_snd.matrix_mul continuous_fst).matrix_mul continuous_const)
    exact (c.tendsto' (0, m) 0 (by simp)).eventually (eventually_schr_eq hB.std hΦ)
  filter_upwards [h1] with u hu h0 k hk
  have h2 := hu (mat k⁻¹) (fun i _ j _ => hCK _ (K.inv_mem hk) i j) (by
    rw [← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul, map_zero])
  have h3 := (IsUWeilPair.isUSplitting hom).impl (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) Φ hΦ
  have h4 : actAB (cA σ) (k, h) (mat k⁻¹ * u * (mat h⁻¹)ᵀ) = u := by
    show mat k * (mat k⁻¹ * u * (mat h⁻¹)ᵀ) * (mat h)ᵀ = u
    have a1 : mat k * mat k⁻¹ = 1 := by
      show mat (k * k⁻¹) = 1
      rw [mul_inv_cancel]; rfl
    have a2 : mat h * mat h⁻¹ = 1 := by
      show mat (h * h⁻¹) = 1
      rw [mul_inv_cancel]; rfl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, a2,
      Matrix.transpose_one, Matrix.mul_one]
  rw [h4] at h3
  rw [← h3]
  exact congrArg _ h2

end Main

theorem finite_parts : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ Φ ∈ PolData B G.M, ∀ h, ∃ (m : ℕ) (c : Fin m → Fin b × Fin (b + a') → Af F) (φ : Fin m → (Fin b × Fin (b + a') → Af F) → ℂ),
      (∀ j, φ j ∈ SB _) ∧ ∀ k ∈ K, ∀ (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F),
        e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) x = ∑ j, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k, h) Φ)) (fun q => ((x q).1, c j q)) * φ j (fun q => (x q).2) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC K hK e he X om om' hT Φ hΦ h
  have hψ := hT.base.std
  have hΦ' : Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := by
    refine (Submodule.span_le.2 ?_ : PolData B G.M ≤ _) hΦ
    rintro _ ⟨f, -, φ, hφ, hv, rfl⟩
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hφ ((hv.and hT.geo.hM.std).mono fun v h => h.1.trans h.2)
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  have hs : Continuous (G₁.M.co.e.symm : _ → Matrix (Fin b) (Fin (b + a')) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap G₁.M.co.e.symm.toLinearMap
  have c : Continuous fun w => incM F H.ι * G₁.M.co.e.symm w * (incM F H'.ι)ᵀ :=
    (continuous_const.matrix_mul hs).matrix_mul continuous_const
  have hN := (c.tendsto' 0 0 (by simp)).eventually (eventually_rho_om_eq hT.base hT.geo.hV hK G.M hT.weil hΦ' h)
  obtain ⟨m, c, φ, hφ, hD⟩ := exists_parts hψ hN
  refine ⟨m, c, φ, hφ, fun k hk l => hD _ fun w hw h0 => ?_⟩
  have hΨ : om (k, h) Φ ∈ schA F _ := (IsUWeilPair.isUSplitting hT.weil).pres (k, h) Φ hΦ'
  have h1 := hw (by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← map_smul, h0, map_zero, Matrix.mul_zero, Matrix.zero_mul]) k hk
  have h2 := he.Heisenberg₂ (G₁.M.co.e.symm w) _ (GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hψ (shiftA H H' l) _ hΨ)
  rw [rho_comm G.M.co B.ψ (by rw [Matrix.mul_assoc]; exact symp_eq_zero hC.hH _ _ _ _), h1,
    show G₁.M.co.rho B.ψ (G₁.M.co.e.symm w) = schr B.ψ w from congrArg (schr B.ψ) (G₁.M.co.e.apply_symm_apply w)] at h2
  exact h2.symm

end GlobalTheory.XTermFinParts

end
