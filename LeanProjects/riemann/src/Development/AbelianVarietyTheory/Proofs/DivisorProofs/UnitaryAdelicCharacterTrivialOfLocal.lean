import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalGlobalChar

open Filter Topology GlobalTheory.IdemSupport

section Adele

variable {F : Type} [Field F] [NumberField F]

open Classical in

def ind (S : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun u => if u ∈ S then 1 else 0, Eventually.of_forall fun u => by
    by_cases h : u ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem ev_ind (S : Finset (HeightOneSpectrum (𝓞 F))) (u : HeightOneSpectrum (𝓞 F)) :
    evalV F u (ind S) = if u ∈ S then 1 else 0 := rfl

theorem fin_ext {a b : Af F} (h : ∀ u, evalV F u a = evalV F u b) : a = b := Subtype.ext (funext h)

theorem tendsto_ind_mul (α : Af F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => ind S * α) atTop (𝓝 α) := by
  classical
  let T : Set (HeightOneSpectrum (𝓞 F)) := {u | α u ∈ (u.adicCompletionIntegers F : Set (u.adicCompletion F))}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.2 α.2
  let f : Finset (HeightOneSpectrum (𝓞 F)) → RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) :=
    fun S => ⟨fun u => if u ∈ S then α u else 0, fun u hu => by
      by_cases h : u ∈ S
      · simp only [Set.mem_setOf_eq, h, if_true]; exact hu
      · simp only [Set.mem_setOf_eq, h, if_false]; exact zero_mem _⟩
  let a : RestrictedProduct
      (fun u : HeightOneSpectrum (𝓞 F) => u.adicCompletion F)
      (fun u => (u.adicCompletionIntegers F : Set (u.adicCompletion F))) (𝓟 T) := ⟨fun u => α u, fun u hu => hu⟩
  have hf : Tendsto f atTop (𝓝 a) := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({u} : Finset _)] with S hS
    exact (if_pos (hS (Finset.mem_singleton_self u))).symm
  have h2 := ((RestrictedProduct.continuous_inclusion hT).tendsto a).comp hf
  refine Tendsto.congr (fun S => fin_ext fun u => ?_) h2
  rw [map_mul, ev_ind]
  change (if u ∈ S then α u else 0) = _
  split_ifs
  · exact (one_mul _).symm
  · exact (zero_mul _).symm

def eps (S : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 1 (ind S)

theorem tendsto_eps_mul (a : AF F) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => eps S * a) atTop (𝓝 a) := by
  have := (tendsto_const_nhds (x := a.1)).prodMk_nhds (tendsto_ind_mul a.2)
  refine Tendsto.congr (f₁ := fun S => ((a.1, ind S * a.2) : Ainf F × Af F)) (fun S => ?_) this
  exact Prod.ext (one_mul _).symm rfl

theorem ind_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : ind S * ind S = ind S :=
  fin_ext fun u => by rw [map_mul, ev_ind]; split_ifs <;> simp

theorem eps_mul_self (S : Finset (HeightOneSpectrum (𝓞 F))) : eps S * eps S = eps S :=
  Prod.ext (one_mul _) (ind_mul_self S)

theorem pl_mul_self (v : HeightOneSpectrum (𝓞 F)) :
    pairA F 0 (ind {v}) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) :=
  Prod.ext (mul_zero _) (ind_mul_self _)

theorem eps_cons (S : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    eps (S.cons v hv) * pairA F 0 (ind {v}) = pairA F 0 (ind {v}) ∧
    eps (S.cons v hv) * (1 - pairA F 0 (ind {v})) = eps S := by
  refine ⟨Prod.ext (mul_zero _) (fin_ext fun u => ?_), Prod.ext ?_ (fin_ext fun u => ?_)⟩
  · change evalV F u (ind (S.cons v hv) * ind {v}) = evalV F u (ind {v})
    rw [map_mul, ev_ind, ev_ind]
    by_cases h : u = v <;> simp [h]
  · change (1 : Ainf F) * (1 - 0) = 1
    simp
  · change evalV F u (ind (S.cons v hv) * (1 - ind {v})) = evalV F u (ind S)
    rw [map_mul, map_sub, map_one, ev_ind, ev_ind, ev_ind]
    by_cases h : u = v
    · subst h; simp [hv]
    · have hm : u ∈ S.cons v hv ↔ u ∈ S := by rw [Finset.mem_cons]; exact or_iff_right h
      by_cases h' : u ∈ S
      · rw [if_pos (hm.2 h'), if_pos h', if_neg (by simpa using h)]; simp
      · rw [if_neg (fun x => h' (hm.1 x)), if_neg h', zero_mul]

variable {E : Type} [Field E] [Algebra F E]

theorem tendsto_eps_tens (x : AF F ⊗[F] E) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) * x)
      atTop (𝓝 x) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousSMul (AF F) (AF F ⊗[F] E) := IsModuleTopology.toContinuousSMul (AF F) _
  induction x using TensorProduct.induction_on with
  | zero => simpa only [mul_zero] using tendsto_const_nhds
  | tmul a e =>
    have h := (tendsto_eps_mul a).smul_const ((1 : AF F) ⊗ₜ[F] e)
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
    refine h.congr fun S => ?_
    rw [← Algebra.smul_def, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simpa only [mul_add] using hx.add hy

theorem tendsto_mix {n : ℕ} (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) => algebraMap (AF F) (AF F ⊗[F] E) (eps S) • M +
      (1 - algebraMap (AF F) (AF F ⊗[F] E) (eps S)) • (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem tendsto_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {ι : Type} {l : Filter ι}
    {p : ι → HA R σ J} {g : HA R σ J}
    (h1 : Tendsto (fun i => (HA.mat R σ J (p i)).1) l (𝓝 (HA.mat R σ J g).1))
    (h2 : Tendsto (fun i => (HA.mat R σ J (p i)⁻¹).1) l (𝓝 (HA.mat R σ J g⁻¹).1)) : Tendsto p l (𝓝 g) := by
  refine (IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

variable {D : D7}

theorem mem_GinfC (V : HSp D) {g : GA D V} (hg : SuppPl (eps ∅) V g) : g ∈ GinfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hf : finPart D (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps ∅)) = 0 := by
    have h0 : ind (∅ : Finset (HeightOneSpectrum (𝓞 D.host.F))) = 0 := fin_ext fun u => by
      rw [ev_ind, map_zero, if_neg (Finset.notMem_empty u)]
    change ind ∅ ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [h0, TensorProduct.zero_tmul]
  have h := congrArg (finPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change finPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem isPlaceIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (pairA D.host.F 0 (ind {v})) :=
  ⟨ind {v}, rfl, by rw [ev_ind, if_pos (Finset.mem_singleton_self v)],
    fun w hw => by rw [ev_ind, if_neg (by simpa using hw)]⟩

theorem alg_idem {a : AF D.host.F} (h : a * a = a) :
    algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a * algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) a := by rw [← map_mul, h]

theorem triv_eps (V : HSp D) (ν : GA D V →* Circle) (hinf : ∀ g ∈ GinfC V, ν g = 1)
    (hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∀ g, SuppPl (eps S) V g → ν g = 1 := by
  induction S using Finset.cons_induction with
  | empty => exact fun g hg => hinf g (mem_GinfC V hg)
  | cons v S hv ih =>
    intro g hg
    obtain ⟨h1, h2⟩ := eps_cons S v hv
    have h1' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h1
    have h2' := congrArg (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)) h2
    rw [map_mul] at h1' h2'
    rw [map_sub, map_one] at h2'
    obtain ⟨g₁, g₂, s₁, s₂, e⟩ := exists_split V (alg_idem (pl_mul_self v)) (cA_algebraMap _) g
    have t₁ : g₁ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := fun i j => by
      rw [← s₁ i j, ← mul_assoc, h1']
    have t : g ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := hg
    have t₂ : g₂ ∈ suppGroup V (algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (eps (S.cons v hv))) := by
      have := mul_mem (inv_mem t₁) t
      rwa [e, inv_mul_cancel_left] at this
    have u₂ : SuppPl (eps S) V g₂ := fun i j => by
      rw [← h2', mul_assoc, s₂ i j, t₂ i j]
    rw [e, map_mul, hpl v g₁ s₁, ih g₂ u₂, mul_one]

theorem exists_approx (V : HSp D) (g : GA D V) :
    ∃ p : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ S, SuppPl (eps S) V (p S)) ∧ Tendsto p atTop (𝓝 g) := by
  choose p hp using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g
  choose q hq using fun S : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    exists_piece V (alg_idem (eps_mul_self S)) (cA_algebraMap _) g⁻¹
  have hpq : ∀ S, (p S)⁻¹ = q S := fun S => by
    refine inv_eq_of_mul_eq_one_right (mt_inj V ?_)
    rw [mt_mul, hp, hq, mix_mul (alg_idem (eps_mul_self S)), ← mt_mul, mul_inv_cancel, mt_one, one_mul, mix_self]
  refine ⟨p, fun S => (suppF_iff V _ (p S)).2 (smul_mix (alg_idem (eps_mul_self S)) (hp S)), ?_⟩
  have a1 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)) atTop (𝓝 (Formalism.L2.Theta.mt V g)) :=
    (tendsto_mix _).congr fun S => (hp S).symm
  have a2 : Tendsto (fun S => Formalism.L2.Theta.mt V (p S)⁻¹) atTop (𝓝 (Formalism.L2.Theta.mt V g⁻¹)) :=
    (tendsto_mix _).congr fun S => by rw [hpq, hq]
  exact tendsto_HA _ _ _ a1 a2

theorem eq_one_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  intro D V ν hν hinf hs hn g
  have hpl : ∀ v g, SuppPl (pairA D.host.F 0 (ind {v})) V g → ν g = 1 := fun v g hg => by
    by_cases h : ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D)
        (pairA D.host.F 0 (ind {v}))
    · obtain ⟨e, he, h⟩ := h
      exact hs e he g fun i j => by rw [h]; exact hg i j
    · exact hn v _ ⟨isPlaceIdem v, h⟩ g hg
  obtain ⟨p, hp', hlim⟩ := exists_approx V g
  have hp : ∀ S, ν (p S) = 1 := fun S => triv_eps V ν hinf hpl S _ (hp' S)
  have h1 := (hν.tendsto g).comp hlim
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun S => (hp S).symm)

end GlobalTheory.LocalGlobalChar

end
