import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AddCharTrivialIntegralFiniteAdeleMul
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField
open IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitCharCond

variable {D : D7}

theorem mul_int {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem conj_int {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    sigR (Af D.host.F) D.sp.cm.sig z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨a, ha, ⟨D.sp.cm.sig (o : D.host.E),
      (show IsIntegral ℤ (o : D.host.E) from o.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom⟩, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem trace_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CommRing R] [Algebra F R]
    (a : R) (e : E) : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

theorem snd_trace (z : AE D) : sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) z) =
    Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [RingHom.map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : finPart D (a ⊗ₜ[D.host.F] x) = sndA D.host.F a ⊗ₜ[D.host.F] x := rfl
    rw [e, trace_tmul, trace_tmul, map_mul, AlgHom.commutes]

theorem coe_mem_intAf {F : Type} [Field F] [NumberField F] (r : 𝓞 F) : algebraMap F (Af F) (r : F) ∈ intAf F := by
  intro v
  rw [AlgHom.commutes]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v r

theorem trace_int {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    Algebra.trace (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) z ∈ intAf D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, o, rfl⟩ := hw
    intro v
    rw [trace_tmul, map_mul]
    exact mul_mem (ha v) (coe_mem_intAf (⟨Algebra.trace D.host.F D.host.E (o : D.host.E),
      Algebra.isIntegral_trace (show IsIntegral ℤ (o : D.host.E) from o.2)⟩ : 𝓞 D.host.F) v)
  | zero => intro v; rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro v; rw [map_add, map_add]; exact add_mem (hx v) (hy v)
  | neg x _ hx => intro v; rw [map_neg, map_neg]; exact neg_mem (hx v)

theorem char_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (z : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) z)) = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ D.host.F z = n := by
  rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
  exact_mod_cast Iff.rfl

theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    ψ (pairA D.host.F 0 β) = 1 := by
  have := GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 1 (fun a => by
    rw [mul_one, char_rat hψ]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (L := ℚ) (show IsIntegral ℤ (a : D.host.F) from a.2))
    exact ⟨z, by rw [← hz]; simp⟩) β hβ
  rwa [map_one, mul_one] at this

theorem pair_mul {F : Type} [Field F] [NumberField F] (α : Af F) (c : AF F) :
    pairA F 0 α * c = pairA F 0 (α * sndA F c) := Prod.ext (zero_mul _) rfl

theorem pair_add {F : Type} [Field F] [NumberField F] (α β : Af F) :
    pairA F 0 (α + β) = pairA F 0 α + pairA F 0 β := Prod.ext (add_zero _).symm rfl

theorem trace_tower {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (a : F) (c : E) :
    Algebra.trace ℚ E (algebraMap F E a * c) = Algebra.trace ℚ F (a * Algebra.trace F E c) := by
  rw [← Algebra.trace_trace (S := F) (T := E), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem one_tmul_eq {F E A : Type} [Field F] [Field E] [CommRing A] [Algebra F E] [Algebra F A] (a : F) :
    (1 : A) ⊗ₜ[F] algebraMap F E a = algebraMap F A a ⊗ₜ[F] (1 : E) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem mem_datum (a : D.host.F) (h : ∀ r : 𝓞 D.host.F, ∃ n : ℤ, Algebra.trace ℚ D.host.F (a * r) = n) :
    algebraMap D.host.F D.host.E a ∈
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar := by
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [eq_inv_of_mul_eq_one_left h1, Host.ddE, coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E), inv_inv,
    FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
  intro b hb
  obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
  obtain ⟨n, hn⟩ := h ⟨Algebra.trace D.host.F D.host.E (c : D.host.E),
      Algebra.isIntegral_trace (show IsIntegral ℤ (c : D.host.E) from c.2)⟩
  refine ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans ?_⟩
  rw [← hn, Algebra.traceForm_apply, trace_tower]
  rfl

section Pt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem sec_one : p.sec 1 = p.e := by
  have h := p.sec_pr 1
  rwa [map_one, mul_one] at h

theorem pr_e : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]

theorem e_mul_sec (x : k) : p.e * p.sec x = p.sec x := by
  have h := p.sec_pr (p.sec x)
  rw [p.pr_sec] at h
  exact h.symm

theorem pr_int {z : AE D} (hz : finPart D z ∈ intAE D) : p.pr z ∈ 𝒪[k] := by
  rw [p.int_iff, p.sec_pr, RingHom.map_mul]
  refine mul_int ?_ hz
  rw [← sec_one]
  exact (p.int_iff 1).1 (one_mem _)

theorem pr_cA_e : p.pr (cA D p.e) = 0 := by
  have h := congrArg p.pr p.split.2.1
  rwa [map_mul, pr_e, one_mul, map_zero] at h

theorem pr_trace (x : k) :
    p.pr (algebraMap (AF D.host.F) (AE D) (Algebra.trace (AF D.host.F) (AE D) (p.sec x))) = x := by
  rw [GlobalTheory.FockCompare.SymplVal.trace_AE, map_add, p.pr_sec, ← e_mul_sec, RingHom.map_mul, map_mul, pr_cA_e, zero_mul,
    add_zero]

theorem exists_idem : ∃ η : Af D.host.F, η ∈ intAf D.host.F ∧ (∀ v, ¬ v = p.v → evalV D.host.F v η = 0) ∧
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 η) * p.e = p.e := by
  obtain ⟨ε, ⟨η, rfl, h1, h0⟩, he⟩ := p.above
  refine ⟨η, fun v => ?_, h0, ?_⟩
  · by_cases h : v = p.v
    · subst h; rw [h1]; exact one_mem _
    · rw [h0 v h]; exact zero_mem _
  · rw [← he, add_mul, p.split.1, mul_comm, p.split.2.1, add_zero]

theorem trace_sec (x : k) : Algebra.trace (AF D.host.F) (AE D) (p.sec x) =
    pairA D.host.F 0 (sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (p.sec x))) := by
  obtain ⟨η, -, -, h⟩ := exists_idem p
  have e : p.sec x = pairA D.host.F 0 η • p.sec x := by
    rw [Algebra.smul_def, ← e_mul_sec, ← mul_assoc, h]
  rw [e, map_smul, smul_eq_mul, pair_mul]
  rfl

theorem pr_pair_tmul {η : Af D.host.F} (h : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 η) * p.e = p.e)
    (a : D.host.E) : p.pr (pairA D.host.F 0 η ⊗ₜ[D.host.F] a) = p.pr (incA D a) := by
  have h1 := congrArg p.pr h
  rw [map_mul, pr_e, mul_one] at h1
  have e : (pairA D.host.F 0 η ⊗ₜ[D.host.F] a : AE D) =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 η) * incA D a := by
    change _ = (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e, map_mul, h1, one_mul]

theorem xi_zero_projection_integral (hU : p.UnitAA) : p.pr (incA D D.host.xi0) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := pr_int p (hU.1 _ hm).1.2
  rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this

theorem AA_tmul_int (hU : p.UnitAA) {η : Af D.host.F} (hη : η ∈ intAf D.host.F)
    (h0 : ∀ v, ¬ v = p.v → evalV D.host.F v η = 0) {a : D.host.E} (ha : a ∈ D.host.AA) :
    η ⊗ₜ[D.host.F] a ∈ intAE D := by
  let S : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1
  let L : Lat S := Submodule.span (𝓞 D.host.E) {fun _ => 1}
  let i : Fin S.rank := (0 : Fin 1)
  have h1 : (fun i => (pairA D.host.F 0 η) ⊗ₜ[D.host.F] (a * (fun _ : Fin S.rank => (1 : D.host.E)) i)) ∈
      latA S L (· = p.v) :=
    AddSubgroup.subset_closure ⟨η, hη, h0, a, ha, _, Submodule.mem_span_singleton_self _, rfl⟩
  rw [hU.2 S L] at h1
  have h2 : ∀ y ∈ latV S L (· = p.v), finPart D (y i) ∈ intAE D := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, b, hb, x, hx, rfl⟩ := hw
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain rfl : b = 1 := hb
      refine AddSubgroup.subset_closure ⟨α, hα, r, ?_⟩
      change α ⊗ₜ[D.host.F] ((1 : D.host.E) * (r • (1 : D.host.E))) = _
      rw [one_mul, Algebra.smul_def, mul_one]
    | zero => rw [Pi.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [Pi.add_apply, RingHom.map_add]; exact add_mem hx hy
    | neg x _ hx => rw [Pi.neg_apply, RingHom.map_neg]; exact neg_mem hx
  have h3 := h2 _ h1
  change η ⊗ₜ[D.host.F] (a * 1) ∈ intAE D at h3
  rwa [mul_one] at h3

theorem datum_int (hU : p.UnitAA) {z : D.host.E} (hz : z ∈
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) :
    p.pr (incA D z) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  refine FractionalIdeal.mul_induction_on (C := fun z => p.pr (incA D z) ∈ 𝒪[k]) hz (fun u hu b hb => ?_)
    (fun u w hu hw => by rw [map_add, map_add]; exact add_mem hu hw)
  rw [map_mul, map_mul]
  refine mul_mem ?_ ?_
  · refine FractionalIdeal.mul_induction_on (C := fun z => p.pr (incA D z) ∈ 𝒪[k]) hu (fun s hs a ha => ?_)
      (fun u w hu hw => by rw [map_add, map_add]; exact add_mem hu hw)
    rw [map_mul, map_mul]
    refine mul_mem ?_ ?_
    · obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
      rw [Algebra.smul_def, map_mul, map_mul]
      refine mul_mem ?_ (xi_zero_projection_integral p hU)
      rw [← pr_pair_tmul p h]
      exact pr_int p (AddSubgroup.subset_closure ⟨η, hη, r, rfl⟩)
    · rw [← pr_pair_tmul p h]
      exact pr_int p (AA_tmul_int p hU hη h0 ha)
  · rw [← pr_pair_tmul p h]
    have h1 := conj_int (AA_tmul_int p hU hη h0 (Formalism.L2.Pj.conj_mem_AA D hb))
    change η ⊗ₜ[D.host.F] star (D.host.conj b) ∈ intAE D at h1
    rw [bridge_star_holds D.R D.host, Formalism.L2.Pj.conj_conj] at h1
    exact pr_int p h1

theorem sec_mul_pr (x : k) (z : AE D) : p.sec (x * p.pr z) = z * p.sec x := by
  conv_lhs => rw [← p.pr_sec x, ← map_mul, p.sec_pr, ← mul_assoc, e_mul_sec, mul_comm]

theorem pr_pair_int {u : Af D.host.F} (hu : u ∈ intAf D.host.F) :
    p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 u)) ∈ 𝒪[k] :=
  pr_int p (AddSubgroup.subset_closure ⟨u, hu, 1, rfl⟩)

end Pt

theorem hasConductor_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (χ : AddChar k Circle), IsStdChar D ψ (-1) → p.IsChar ψ χ → p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1 := by
  intro D k _ _ _ _ p ψ χ hψ hχ hU x
  rw [Units.val_one, map_one]
  constructor
  · intro h
    have hα := trace_sec p x
    generalize sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (p.sec x)) = α at hα
    have key : ∀ u ∈ intAf D.host.F, ψ (pairA D.host.F 0 (u * α)) = 1 := by
      intro u hu
      have h1 := h (x * p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 u))) (by
        rw [map_mul]
        exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (pr_pair_int p hu)))
      have h2 := hχ (x * p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 u)))
      rw [h1, sec_mul_pr, GlobalTheory.MixPer.psiE, ← Algebra.smul_def, map_smul, hα, smul_eq_mul, pair_mul] at h2
      exact h2.symm
    obtain ⟨a, β, hβ, hab⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F 1 one_pos).1 α
    rw [one_smul] at hab
    have hβ' : β ∈ intAf D.host.F := hβ
    have ha := datum_int p hU (mem_datum a fun r => by
      have h1 := key _ (coe_mem_intAf r)
      rw [hab, mul_add, pair_add, ψ.map_add_eq_mul, char_int hψ (β := _ * β)
        (fun v => by rw [map_mul]; exact mul_mem (coe_mem_intAf r v) (hβ' v)), mul_one, ← map_mul, mul_comm] at h1
      exact (char_rat hψ _).1 h1)
    obtain ⟨η, -, -, hη⟩ := exists_idem p
    have h1 : p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 η)) = 1 := by
      have h1 := congrArg p.pr hη
      rwa [map_mul, pr_e, mul_one] at h1
    have h2 : p.pr (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a))) =
        p.pr (incA D (algebraMap D.host.F D.host.E a)) := by
      have e : incA D (algebraMap D.host.F D.host.E a) =
          algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) a) := one_tmul_eq a
      have e2 : pairA D.host.F 0 η * pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) =
          pairA D.host.F 0 η * algebraMap D.host.F (AF D.host.F) a := by
        rw [pair_mul, pair_mul]; rfl
      have e3 := congrArg (fun c => p.pr (algebraMap (AF D.host.F) (AE D) c)) e2
      simp only [map_mul, h1, one_mul] at e3
      rw [e, e3]
    have h3 := pr_trace p x
    rw [hα, hab, pair_add, map_add, map_add, h2] at h3
    rw [← h3]
    exact (Valuation.mem_integer_iff _ _).1 (add_mem ha (pr_pair_int p hβ'))
  · intro hx y hy
    have hy' : y ∈ 𝒪[k] := (Valuation.mem_integer_iff _ _).2 (hy.trans hx)
    have h1 := hχ y
    rw [GlobalTheory.MixPer.psiE, trace_sec, snd_trace, char_int hψ (trace_int ((p.int_iff y).1 hy'))] at h1
    exact Circle.ext h1

end GlobalTheory.SplitCharCond

end
