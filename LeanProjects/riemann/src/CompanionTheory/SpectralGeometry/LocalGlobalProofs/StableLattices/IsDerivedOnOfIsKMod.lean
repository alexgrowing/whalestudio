import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOnePOf
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.SopNegComm

open Matrix Finset WithLp
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.DSUniq

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight Cas)
open PI.UpqRep (lowK IsURepOn IsIrredOn UJset IsDS)
open CompanionTheory.D.DSIC (KUnit KStab)
open CompanionTheory.D.LK (Cyc LocFin IsMin IsKMod MultAlg KModExists OrthCyc mem_cyc cyc_stab ev)
open ReciprocityTheory.ChartRestriction.DS (genSub IsDerivedOn)
open ReciprocityTheory.ChartRestriction.DS.USum (sD sE sσ ofP toP lift)

variable {n : ℕ}

theorem equiv_of_graph {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    {G : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hI : IsIrredOn G σ) (hI' : IsIrredOn G σ')
    (Y : Submodule ℂ (WithLp 2 (H × H'))) (hc : IsClosed (Y : Set (WithLp 2 (H × H'))))
    (hst : ∀ g ∈ G, ∀ y ∈ Y, sσ σ σ' g y ∈ Y) (hn : ∀ y ∈ Y, ‖(ofLp y).1‖ = ‖(ofLp y).2‖)
    {y₀ : WithLp 2 (H × H')} (hy₀ : y₀ ∈ Y) (h0 : y₀ ≠ 0) :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ G, ∀ x, U (σ g x) = σ' g (U x) := by
  have : CompleteSpace Y := hc.completeSpace_coe
  have hs : ‖((√2 : ℝ) : ℂ)‖ = √2 := by simp
  have hnorm : ∀ y : Y, √2 * ‖(ofLp (y : WithLp 2 (H × H'))).1‖ = ‖y‖ := fun y => by
    show _ = ‖(y : WithLp 2 (H × H'))‖
    rw [WithLp.prod_norm_eq_of_L2]
    show _ = √(‖(ofLp (y : WithLp 2 (H × H'))).1‖ ^ 2 + ‖(ofLp (y : WithLp 2 (H × H'))).2‖ ^ 2)
    rw [← hn y y.2, ← two_mul, Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
  let f₁ : Y →ₗᵢ[ℂ] H :=
    { toFun := fun y => ((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).1
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [smul_comm c]
      norm_map' := fun y => by
        show ‖((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).1‖ = _
        rw [norm_smul, hs, hnorm] }
  let f₂ : Y →ₗᵢ[ℂ] H' :=
    { toFun := fun y => ((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).2
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp [smul_comm c]
      norm_map' := fun y => by
        show ‖((√2 : ℝ) : ℂ) • (ofLp (y : WithLp 2 (H × H'))).2‖ = _
        rw [norm_smul, hs, ← hn y y.2, hnorm] }
  have e₁ : ∀ g (hg : g ∈ G) (y : Y), f₁ ⟨_, hst g hg y y.2⟩ = σ g (f₁ y) := fun g hg y =>
    ((σ g).map_smul _ _).symm
  have e₂ : ∀ g (hg : g ∈ G) (y : Y), f₂ ⟨_, hst g hg y y.2⟩ = σ' g (f₂ y) := fun g hg y =>
    ((σ' g).map_smul _ _).symm
  have hy : (⟨y₀, hy₀⟩ : Y) ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have s₁ : Function.Surjective f₁ := by
    refine LinearMap.range_eq_top.1 ((hI (LinearMap.range f₁.toLinearMap) f₁.isometry.isClosedEmbedding.isClosed_range
      ?_).resolve_left fun h => hy ?_)
    · rintro g hg _ ⟨y, rfl⟩
      exact ⟨_, e₁ g hg y⟩
    · have : f₁ ⟨y₀, hy₀⟩ ∈ LinearMap.range f₁.toLinearMap := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact f₁.injective (by rw [this, map_zero])
  have s₂ : Function.Surjective f₂ := by
    refine LinearMap.range_eq_top.1 ((hI' (LinearMap.range f₂.toLinearMap) f₂.isometry.isClosedEmbedding.isClosed_range
      ?_).resolve_left fun h => hy ?_)
    · rintro g hg _ ⟨y, rfl⟩
      exact ⟨_, e₂ g hg y⟩
    · have : f₂ ⟨y₀, hy₀⟩ ∈ LinearMap.range f₂.toLinearMap := ⟨_, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact f₂.injective (by rw [this, map_zero])
  let u₁ := LinearIsometryEquiv.ofSurjective f₁ s₁
  let u₂ := LinearIsometryEquiv.ofSurjective f₂ s₂
  have key : ∀ y : Y, (u₁.symm.trans u₂) (f₁ y) = f₂ y := fun y => by
    have : u₁.symm (f₁ y) = y := u₁.symm_apply_apply y
    rw [LinearIsometryEquiv.trans_apply, this]
    rfl
  refine ⟨u₁.symm.trans u₂, fun g hg x => ?_⟩
  obtain ⟨y, rfl⟩ := s₁ x
  rw [← e₁ g hg, key, key, e₂ g hg]

section Alg

variable {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}

theorem self_mem_cyc (v : V) : v ∈ Cyc E v := by
  rw [mem_cyc]
  exact ⟨1, by simp⟩

theorem cyc_le {v : V} {T : Submodule ℂ V} (hT : ∀ a b, ∀ x ∈ T, E a b x ∈ T) (hv : v ∈ T) : Cyc E v ≤ T := by
  intro w hw
  obtain ⟨a, rfl⟩ := mem_cyc.1 hw
  clear hw
  suffices h : ∀ x ∈ T, ev E a x ∈ T from h v hv
  induction a using FreeAlgebra.induction
  next r =>
    intro x hx
    rw [AlgHom.commutes, Module.algebraMap_end_apply]
    exact T.smul_mem r hx
  next p =>
    intro x hx
    simp only [ev, FreeAlgebra.lift_ι_apply]
    exact hT p.1 p.2 x hx
  next a b ha hb =>
    intro x hx
    rw [map_mul, Module.End.mul_apply]
    exact ha _ (hb x hx)
  next a b ha hb =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact T.add_mem (ha x hx) (hb x hx)

theorem cas_comm (ε : Fin n → Bool) (hgl : GlRel E) (a b : Fin n) (x : V) : E a b (Cas E x) = Cas E (E a b x) := by
  have key : E a b * Cas E - Cas E * E a b = 0 := by
    have h : ∀ c d, E a b * (E c d * E d c) - E c d * E d c * E a b =
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E d c +
        E c d * ((if b = d then E a c else 0) - (if c = a then E d b else 0)) := by
      intro c d
      rw [← hgl a b c d, ← hgl a b d c]
      noncomm_ring
    have A1 : ∑ c, ∑ d, (if b = c then E a d else 0) * E d c = ∑ d, E a d * E d b := by
      rw [Finset.sum_comm]
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have A2 : ∑ c, ∑ d, (if d = a then E c b else 0) * E d c = ∑ c, E c b * E a c := by
      simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have A3 : ∑ c, ∑ d, E c d * (if b = d then E a c else 0) = ∑ c, E c b * E a c := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have A4 : ∑ c, ∑ d, E c d * (if c = a then E d b else 0) = ∑ d, E a d * E d b := by
      rw [Finset.sum_comm]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    calc E a b * Cas E - Cas E * E a b
        = ∑ c, ∑ d, (E a b * (E c d * E d c) - E c d * E d c * E a b) := by
          simp only [Cas, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      _ = 0 := by
          simp only [h, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, A1, A2, A3, A4]
          abel
  have := congrArg (fun T : Module.End ℂ V => T x) (sub_eq_zero.1 key)
  simpa only [Module.End.mul_apply] using this

end Alg

section Unit

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
  {ε : Fin n → Bool}

theorem cas_symm (hU : IsUnitary ε E) (x y : V) : ⟪Cas E x, y⟫_ℂ = ⟪x, Cas E y⟫_ℂ := by
  have hs : ∀ a b : Fin n, ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) * (Formalism.REAL.sgn ε b a : ℂ) = 1 := by
    intro a b
    by_cases h : ε a = ε b
    · simp [Formalism.REAL.sgn, h]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp [Formalism.REAL.sgn, h, h']
  have h1 : ∀ a b, ⟪(E a b * E b a) x, y⟫_ℂ = ⟪x, (E a b * E b a) y⟫_ℂ := by
    intro a b
    rw [Module.End.mul_apply, Module.End.mul_apply, hU a b, hU b a, ← mul_assoc, hs, one_mul]
  simp only [Cas, LinearMap.sum_apply, sum_inner, inner_sum, h1]

theorem orth_spread (hU : IsUnitary ε E) (J : Module.End ℂ V) (hJ : ∀ a b x, J (E a b x) = E a b (J x)) {v : V}
    (hv : ∀ m ∈ Cyc E v, ⟪m, J v⟫_ℂ = 0) : ∀ x ∈ Cyc E v, ∀ m ∈ Cyc E v, ⟪m, J x⟫_ℂ = 0 := by
  let S : Submodule ℂ V :=
    { carrier := {x | ∀ m ∈ Cyc E v, ⟪m, J x⟫_ℂ = 0}
      add_mem' := fun {x y} hx hy m hm => by
        rw [map_add, inner_add_right, hx m hm, hy m hm, add_zero]
      zero_mem' := fun m _ => by rw [map_zero, inner_zero_right]
      smul_mem' := fun c x hx m hm => by rw [map_smul, inner_smul_right, hx m hm, mul_zero] }
  have hS : Cyc E v ≤ S := by
    refine cyc_le (fun c d x hx m hm => ?_) hv
    show ⟪m, J (E c d x)⟫_ℂ = 0
    have h1 := hU d c m (J x)
    rw [hJ]
    have h2 : ⟪E d c m, J x⟫_ℂ = 0 := hx _ (cyc_stab d c hm)
    rw [h2] at h1
    have hs : ((Formalism.REAL.sgn ε d c : ℝ) : ℂ) ≠ 0 := by
      unfold Formalism.REAL.sgn; split_ifs <;> norm_num
    exact (mul_eq_zero.1 h1.symm).resolve_left hs
  intro x hx m hm
  exact hS hx m hm

end Unit

theorem exists_closed_stable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hU : IsUnitary ε E) (hF : LocFin ε E) {v : D} {c : ℂ}
    (hv0 : v ≠ 0) (hc : Cas E v = c • v) :
    ∃ Y : Submodule ℂ H, IsClosed (Y : Set H) ∧ (∀ g ∈ UJset ε, ∀ y ∈ Y, σ g y ∈ Y) ∧ (v : H) ∈ Y ∧
      Y ≤ ((Cyc E v).map D.subtype).topologicalClosure := by
  have hcreal : c = ((c.re : ℝ) : ℂ) := by
    have h1 : ⟪Cas E v, v⟫_ℂ = ⟪v, Cas E v⟫_ℂ := cas_symm hU v v
    rw [hc, inner_smul_left, inner_smul_right] at h1
    have hv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
    have h2 := mul_right_cancel₀ hv h1
    exact (Complex.conj_eq_iff_re.1 h2).symm
  obtain ⟨S, hSf, hSK, hvS⟩ := hF v
  let V : Submodule ℂ D := (S ⊓ LinearMap.ker (Cas E - c • 1)) ⊓ Cyc E v
  have hVf : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
  have hVK : ReciprocityTheory.ChartRestriction.DS.IsKStableSub ε E V := by
    intro a b hab w hw
    obtain ⟨⟨hwS, hwK⟩, hwC⟩ := hw
    refine ⟨⟨hSK a b hab w hwS, ?_⟩, cyc_stab a b hwC⟩
    have hwK' : (Cas E - c • 1) w = 0 := hwK
    show (Cas E - c • 1) (E a b w) = 0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hwK' ⊢
    rw [← cas_comm ε hD.glRep, ← map_smul, ← map_sub, hwK', map_zero]
  have hVc : ∀ w ∈ V, ReciprocityTheory.ChartRestriction.DS.casimir E w = ((c.re : ℝ) : ℂ) • w := by
    intro w hw
    have h3 : (Cas E - c • 1) w = 0 := hw.1.2
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h3
    show Cas E w = _
    rw [← hcreal]
    exact sub_eq_zero.1 h3
  have hvV : v ∈ V := by
    refine ⟨⟨hvS, ?_⟩, self_mem_cyc v⟩
    show (Cas E - c • 1) v = 0
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hc, sub_self]
  have hsub : ReciprocityTheory.ChartRestriction.DS.genSub E V ≤ Cyc E v :=
    sInf_le ⟨(inf_le_right : V ≤ Cyc E v), fun a b w hw => cyc_stab a b hw⟩
  have hvGen : v ∈ ReciprocityTheory.ChartRestriction.DS.genSub E V := Submodule.mem_sInf.2 (fun T hT => hT.1 hvV)
  refine ⟨(Submodule.map D.subtype (ReciprocityTheory.ChartRestriction.DS.genSub E V)).topologicalClosure,
    Submodule.isClosed_topologicalClosure _, ?_, ?_, ?_⟩
  · intro g hg y hy
    exact ReciprocityTheory.ChartRestriction.DS.closure_genSub_stable hσ hD hVf hVK hVc g hg y hy
  · exact Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hvGen)
  · exact Submodule.topologicalClosure_mono (Submodule.map_mono hsub)

theorem isDerivedOn_of_isKMod {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hK : IsKMod ε σ D E) : IsDerivedOn ε σ D E := by
  refine ⟨hK.gl, ?_, ?_⟩
  · intro k hk v hv
    obtain ⟨S, hSf, hvS, hSK⟩ := (hK.mem v).1 hv
    exact (hK.mem _).2 ⟨S, hSf, hSK k hk v hvS, hSK⟩
  · intro X hX v
    have h := hK.real X hX v
    have e : ((ReciprocityTheory.ChartRestriction.DS.actM E X v : D) : H) = ∑ a, ∑ b, X a b • ((E a b v : D) : H) := by
      simp [ReciprocityTheory.ChartRestriction.DS.actM]
    rw [e]
    exact h

section Sum

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {D : Submodule ℂ H} {D' : Submodule ℂ H'} {E : Fin n → Fin n → Module.End ℂ D}
  {E' : Fin n → Fin n → Module.End ℂ D'} {ε : Fin n → Bool}

theorem inner_sD (x y : sD D D') : ⟪x, y⟫_ℂ = ⟪(toP x).1, (toP y).1⟫_ℂ + ⟪(toP x).2, (toP y).2⟫_ℂ := rfl

theorem toProd_prodMap (a b : Fin n) (x : sD D D') : toP (sE E E' a b x) = (E a b (toP x).1, E' a b (toP x).2) := rfl

theorem toProd_injective₂ {x y : sD D D'} (h : toP x = toP y) : x = y := by
  have h1 : ((toP x).1 : H) = (toP y).1 := congrArg (fun p => (p.1 : H)) h
  have h2 : ((toP x).2 : H') = (toP y).2 := congrArg (fun p => (p.2 : H')) h
  apply Subtype.ext
  apply (WithLp.linearEquiv 2 ℂ (H × H')).injective
  exact Prod.ext h1 h2

theorem isUnitary_sE (hU : IsUnitary ε E) (hU' : IsUnitary ε E') : IsUnitary ε (sE E E') := by
  intro a b x y
  simp only [inner_sD, toProd_prodMap, hU a b, hU' a b, mul_add]

theorem locFin_sE (hF : LocFin ε E) (hF' : LocFin ε E') : LocFin ε (sE E E') := by
  intro x
  obtain ⟨S₁, hf₁, hk₁, hx₁⟩ := hF (toP x).1
  obtain ⟨S₂, hf₂, hk₂, hx₂⟩ := hF' (toP x).2
  refine ⟨(S₁.prod S₂).map ofP, ?_, ?_, ?_⟩
  · haveI : FiniteDimensional ℂ (S₁.prod S₂) := by
      first
        | infer_instance
        | (rw [← Submodule.range_subtype S₁, ← Submodule.range_subtype S₂, ← LinearMap.range_prodMap]
           infer_instance)
        | (rw [← Submodule.range_subtype S₁, ← Submodule.range_subtype S₂, ← LinearMap.range_prod_map]
           infer_instance)
    infer_instance
  · intro a b hab w hw
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hw
    refine Submodule.mem_map.2 ⟨(E a b p.1, E' a b p.2), ⟨hk₁ a b hab _ hp.1, hk₂ a b hab _ hp.2⟩, ?_⟩
    rfl
  · exact Submodule.mem_map.2 ⟨toP x, ⟨hx₁, hx₂⟩, toProd_injective₂ rfl⟩

theorem kHighest_sE_iff {μ : Fin n → ℝ} {x : sD D D'} :
    KHighest ε (sE E E') μ x ↔ KHighest ε E μ (toP x).1 ∧ KHighest ε E' μ (toP x).2 := by
  have key : ∀ (x y : sD D D'), x = y ↔ (toP x).1 = (toP y).1 ∧ (toP x).2 = (toP y).2 := fun x y =>
    ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => toProd_injective₂ (Prod.ext h.1 h.2)⟩
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  simp only [key, toProd_prodMap, map_smul, map_zero, Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun a => (h1 a).1, fun a b hab he => (h2 a b hab he).1⟩,
      ⟨fun a => (h1 a).2, fun a b hab he => (h2 a b hab he).2⟩⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h1', h2'⟩⟩
    exact ⟨fun a => ⟨h1 a, h1' a⟩, fun a b hab he => ⟨h2 a b hab he, h2' a b hab he⟩⟩

theorem isMin_sE {lam : Fin n → ℝ} (hm : IsMin ε E lam) (hm' : IsMin ε E' lam) : IsMin ε (sE E E') lam := by
  intro μ x hx hk
  rw [kHighest_sE_iff] at hk
  by_cases h1 : (toP x).1 = 0
  · have h2 : (toP x).2 ≠ 0 := by
      intro h2
      apply hx
      apply toProd_injective₂
      rw [map_zero]
      exact Prod.ext h1 h2
    exact hm' μ _ h2 hk.2
  · exact hm μ _ h1 hk.1

end Sum

theorem kHighest_smul {V : Type} [AddCommGroup V] [Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}
    {ε : Fin n → Bool} {μ : Fin n → ℝ} {v : V} (c : ℂ) (hv : KHighest ε E μ v) : KHighest ε E μ (c • v) := by
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hv ⊢
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [map_smul, hv.1 a, smul_comm]
  · rw [map_smul, hv.2 a b hab he, smul_zero]

theorem core (hM : MultAlg) (hO : OrthCyc) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) (hgl : GlRel E)
    (hun : IsUnitary ε E) (hF : LocFin ε E) (hm : IsMin ε E lam) {y : V} (hy0 : y ≠ 0)
    (hyK : KHighest ε E (lowK ε lam) y) (J : Module.End ℂ V) (hJ : ∀ a b x, J (E a b x) = E a b (J x))
    (hy : ⟪y, J y⟫_ℂ = 0) : (∃ c : ℂ, Cas E y = c • y) ∧ ∀ x ∈ Cyc E y, ⟪x, J x⟫_ℂ = 0 := by
  have hKU : KUnit ε E := fun a b hab x y => by simp [hun a b, Formalism.REAL.sgn, hab]
  have hmult : ∀ w ∈ Cyc E y, KHighest ε E (lowK ε lam) w → ∃ c, w = c • y :=
    fun w hw hwK => hM n ε lam V E hlam hgl hKU hF hm y w hy0 hyK hwK hw
  have hyK' := hyK
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight at hyK'
  have hCas : KHighest ε E (lowK ε lam) (Cas E y) := by
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [cas_comm ε hgl, hyK'.1 a, map_smul]
    · rw [cas_comm ε hgl, hyK'.2 a b hab he, map_zero]
  have hCasMem : Cas E y ∈ Cyc E y := by
    simp only [Cas, LinearMap.sum_apply, Module.End.mul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      cyc_stab a b (cyc_stab b a (self_mem_cyc y))
  refine ⟨hmult _ hCasMem hCas, ?_⟩
  have hJK : KHighest ε E (lowK ε lam) (J y) := by
    unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hJ, hyK'.1 a, map_smul]
    · rw [← hJ, hyK'.2 a b hab he, map_zero]
  have horth := hO n ε V E (lowK ε lam) y (J y) hgl hKU hF hmult hJK hy
  intro x hx
  exact orth_spread hun J hJ horth x hx x hx

theorem ds_unique (hM : MultAlg) (hE : KModExists) (hO : OrthCyc) (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hσ' : IsDS ε lam σ') :
    ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UJset ε, ∀ x, U (σ g x) = σ' g (U x) := by
  obtain ⟨hc, -, hU, hI, -, ⟨S, hS⟩, hmin⟩ := hσ
  obtain ⟨hc', -, hU', hI', -, ⟨S', hS'⟩, hmin'⟩ := hσ'
  obtain ⟨D, E, hK⟩ := hE n ε H σ hU hI
  obtain ⟨D', E', hK'⟩ := hE n ε H' σ' hU' hI'
  have hm : IsMin ε (sE E E') lam := isMin_sE
    (fun μ x hx0 hx => (hK.ty μ x hx0 hx).elim fun T hT => hmin μ T hT)
    (fun μ x hx0 hx => (hK'.ty μ x hx0 hx).elim fun T hT => hmin' μ T hT)
  obtain ⟨v, hv0, -, hv⟩ := hK.hw _ S hS
  obtain ⟨v', hv0', -, hv'⟩ := hK'.hw _ S' hS'
  have hD := ReciprocityTheory.ChartRestriction.DS.USum.isDerivedOn_sσ (isDerivedOn_of_isKMod hK) (isDerivedOn_of_isKMod hK')
  have hR : IsURepOn (UJset ε) (sσ σ σ') := ReciprocityTheory.ChartRestriction.DS.USum.isURepOn_sσ hU hU'
  have hgl : GlRel (sE E E') := hD.glRep
  have hun := isUnitary_sE hK.unit hK'.unit
  have hF := locFin_sE hK.locFin hK'.locFin
  set w : D := ((‖v'‖ : ℝ) : ℂ) • v with hw
  set w' : D' := ((‖v‖ : ℝ) : ℂ) • v' with hw'
  have hw0 : w ≠ 0 := smul_ne_zero (by simpa using hv0') hv0
  have hww : ‖w‖ = ‖w'‖ := by
    rw [hw, hw', norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, norm_norm, norm_norm, mul_comm]
  set y : sD D D' := ofP (w, w') with hy
  have hy0 : y ≠ 0 := fun h => hw0 (congrArg (fun z => (toP z).1) h)
  have hyK : KHighest ε (sE E E') (lowK ε lam) y := kHighest_sE_iff.2 ⟨kHighest_smul _ hv, kHighest_smul _ hv'⟩
  let J : Module.End ℂ (sD D D') := lift 1 (-1)
  have hJp : ∀ x, toP (J x) = ((toP x).1, -(toP x).2) := fun x => rfl
  have hJ : ∀ a b x, J (sE E E' a b x) = sE E E' a b (J x) := fun a b x => toProd_injective₂ (by
    rw [hJp, toProd_prodMap, toProd_prodMap, hJp, map_neg])
  have hJi : ∀ x, ⟪x, J x⟫_ℂ = ((‖(toP x).1‖ ^ 2 - ‖(toP x).2‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_sD, hJp, inner_neg_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  obtain ⟨⟨c, hcas⟩, hall⟩ := core hM hO hlam.1 hgl hun hF hm hy0 hyK J hJ (by
    rw [hJi]
    show ((‖w‖ ^ 2 - ‖w'‖ ^ 2 : ℝ) : ℂ) = 0
    rw [hww, sub_self, Complex.ofReal_zero])
  obtain ⟨Y, hYc, hYs, hyY, hYle⟩ := exists_closed_stable hR hD hun hF hy0 hcas
  refine equiv_of_graph hI hI' Y hYc hYs (fun z hz => ?_) hyY fun h => hy0 (Subtype.ext h)
  have hcl : IsClosed {z : WithLp 2 (H × H') | ‖(ofLp z).1‖ = ‖(ofLp z).2‖} := isClosed_eq (by fun_prop) (by fun_prop)
  refine (hcl.closure_subset_iff.2 ?_) (hYle hz)
  rintro _ ⟨x, hx, rfl⟩
  have h := hall x hx
  rw [hJi, Complex.ofReal_eq_zero, sub_eq_zero] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end GlobalTheory.CompanionTheory.DSUniq
