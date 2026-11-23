import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GamOrdNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRegroup

theorem integral_eq_vol_mul_sum {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] (ν : Measure G) [ν.IsMulLeftInvariant] (π : G →* H) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (h0 : ν (J.comap π) ≠ 0)
    (htop : ν (J.comap π) ≠ ⊤) {I : Type} [Fintype I] (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G)
    (ha : ∀ i, π (a i) = y i) (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ h, Φ (γ * h) = Φ h) (hr : ∀ k ∈ J.comap π, ∀ h, Φ (h * k) = Φ h) :
    (∀ i, Finite (Bridge.stab (π.comp Γ.subtype) J (y i))) ∧ IntegrableOn Φ 𝓖 ν ∧
      ∫ h in 𝓖, Φ h ∂ν = (ν (J.comap π)).toReal *
        ∑ i, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y i)) : ℂ))⁻¹ * Φ (a i) := by
  set c := ν (J.comap π) with hc
  have h𝓖' : IsFundamentalDomain Γ 𝓖 (c⁻¹ • ν) := h𝓖.mono (Measure.smul_absolutelyContinuous)
  have h1 : (c⁻¹ • ν) (J.comap π) = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, ← hc, ENNReal.inv_mul_cancel h0 htop]
  obtain ⟨hf, hi, he⟩ := GlobalTheory.DefiniteClassSum.integral_eq_sum (c⁻¹ • ν) π Γ h𝓖' J ho h1 y hy a ha Φ hl hr
  have hc1 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 htop
  have hc2 : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  refine ⟨hf, ?_, ?_⟩
  · unfold IntegrableOn at hi ⊢
    rw [Measure.restrict_smul] at hi
    exact (integrable_smul_measure hc1 hc2).1 hi
  · rw [← he, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv]
    have hr0 : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩
    rw [Complex.real_smul, ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hr0), one_mul]

theorem sum_regroup {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] (ν : Measure G) [ν.IsMulLeftInvariant] (π : G →* H) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) {J J'' : Subgroup H} (hle : J'' ≤ J) (ho : IsOpen (J.comap π : Set G))
    (ho'' : IsOpen (J''.comap π : Set G)) (h1 : ν (J.comap π) = 1) (h0 : ν (J''.comap π) ≠ 0)
    {I : Type} [Fintype I] (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i)
    {I'' : Type} [Fintype I''] (y'' : I'' → H) (hy'' : Bridge.IsReps (π.comp Γ.subtype) J'' y'') (a'' : I'' → G)
    (ha'' : ∀ i, π (a'' i) = y'' i)
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ h, Φ (γ * h) = Φ h) (hr : ∀ k ∈ J.comap π, ∀ h, Φ (h * k) = Φ h) :
    ∑ i, ((ν (J''.comap π)).toReal : ℂ) * ((Nat.card (Bridge.stab (π.comp Γ.subtype) J'' (y'' i)) : ℂ))⁻¹ * Φ (a'' i) =
      ∑ i, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y i)) : ℂ))⁻¹ * Φ (a i) := by
  have hle' : J''.comap π ≤ J.comap π := Subgroup.comap_mono hle
  have htop : ν (J''.comap π) ≠ ⊤ := ne_top_of_le_ne_top (h1 ▸ ENNReal.one_ne_top) (measure_mono (μ := ν) (show (J''.comap π : Set G) ⊆ J.comap π from hle'))
  have e1 := (integral_eq_vol_mul_sum ν π Γ h𝓖 J ho (by rw [h1]; exact one_ne_zero) (by rw [h1]; exact ENNReal.one_ne_top)
    y hy a ha Φ hl hr).2.2
  have e2 := (integral_eq_vol_mul_sum ν π Γ h𝓖 J'' ho'' h0 htop y'' hy'' a'' ha'' Φ hl (fun k hk => hr k (hle' hk))).2.2
  rw [h1, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1
  rw [← e1, e2, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.ClassRegroup

namespace GlobalTheory.ClassRegroup

open GlobalTheory.FunObj

variable {D : D7}

theorem gfcToGf_injective (V : HSp D) : Function.Injective (gfcToGf V) := by
  intro a b e
  apply finG_injective V
  have h : finHom V a.1 = finHom V b.1 := congrArg Subtype.val e
  show Formalism.UG.bc (Lev.swapAE D) (finHom V a.1) = Formalism.UG.bc (Lev.swapAE D) (finHom V b.1)
  rw [h]

noncomputable def finEquiv (V : HSp D) : GfC V ≃* Bridge.Gf V :=
  MulEquiv.ofBijective (gfcToGf V) ⟨gfcToGf_injective V, gfcToGf_surjective V⟩

noncomputable def finPt (V : HSp D) : GA D V →* GfC V := (finEquiv V).symm.toMonoidHom.comp (finHom V).rangeRestrict

theorem finG_finPt (V : HSp D) (g : GA D V) : finG V (finPt V g) = Lev.finE V g := by
  have h : gfcToGf V (finPt V g) = (finHom V).rangeRestrict g := (finEquiv V).apply_symm_apply _
  have h2 : finHom V (finPt V g).1 = finHom V g := congrArg Subtype.val h
  show Formalism.UG.bc (Lev.swapAE D) (finHom V (finPt V g).1) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
  rw [h2]

theorem finPt_surjective (V : HSp D) : Function.Surjective (finPt V) :=
  (finEquiv V).symm.surjective.comp (finHom V).rangeRestrict_surjective

theorem comap_finPt (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    (K.comap (finG V)).comap (finPt V) = K.comap (Lev.finE V) := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_comap, Subgroup.mem_comap, finG_finPt]

theorem eq_one_of_finPt (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) (h : finPt V γ = 1) : γ = 1 := by
  refine (GlobalTheory.DefFree.AdelCls.adelic_classes D V).2.2.2.1 γ hγ (Subtype.ext ?_)
  have := congrArg (finG V) h
  rw [finG_finPt, map_one] at this
  exact this

theorem mem_ratFin (V : HSp D) (x : GfC V) : x ∈ ratFin V ↔ ∃ γ ∈ GQ V, finPt V γ = x := by
  constructor
  · intro hx
    obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hx)
    exact ⟨γ, hγ, finG_injective V (by rw [finG_finPt, e])⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨γ, hγ, (finG_finPt V γ).symm⟩)

theorem isReps_out (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    Bridge.IsReps ((finPt V).comp (GQ V).subtype) (K.comap (finG V)) (fun c : FinCl V K => Quotient.out c) := by
  intro h
  refine ⟨DoubleCoset.mk _ _ h, ?_, ?_⟩
  · obtain ⟨r, hr, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 (DoubleCoset.out_eq' _ _ (DoubleCoset.mk (ratFin V) (K.comap (finG V)) h))
    obtain ⟨γ, hγ, rfl⟩ := (mem_ratFin V r).1 hr
    exact ⟨⟨γ, hγ⟩, ⟨k, hk⟩, e⟩
  · rintro c ⟨γ, k, e⟩
    rw [← DoubleCoset.out_eq' _ _ c]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨finPt V γ, (mem_ratFin V _).2 ⟨γ, γ.2, rfl⟩, k, k.2, e⟩

theorem card_stab (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : GfC V) :
    Nat.card (Bridge.stab ((finPt V).comp (GQ V).subtype) (K.comap (finG V)) x) = gamOrd V K x := by
  have hm : ∀ q : GQ V, q ∈ Bridge.stab ((finPt V).comp (GQ V).subtype) (K.comap (finG V)) x ↔
      finG V (x⁻¹ * finPt V q * x) ∈ K := fun q => by
    rw [Bridge.mem_stab]
    simp [MulAut.conj_apply]
  let f : Bridge.stab ((finPt V).comp (GQ V).subtype) (K.comap (finG V)) x → {γ : ratFin V // finG V (x⁻¹ * γ * x) ∈ K} :=
    fun q => ⟨⟨finPt V q.1, (mem_ratFin V _).2 ⟨q.1, q.1.2, rfl⟩⟩, (hm q.1).1 q.2⟩
  refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro q q' e
    have e1 : finPt V q.1 = finPt V q'.1 := congrArg (fun s => (s.1 : GfC V)) e
    have e2 : finPt V ((q.1 : GA D V)⁻¹ * q'.1) = 1 := by rw [map_mul, map_inv, e1, inv_mul_cancel]
    have := eq_one_of_finPt V (mul_mem (inv_mem q.1.2) q'.1.2) e2
    exact Subtype.ext (Subtype.ext (inv_mul_eq_one.1 this))
  · rintro ⟨⟨γ, hγ⟩, hk⟩
    obtain ⟨q, hq, rfl⟩ := (mem_ratFin V γ).1 hγ
    exact ⟨⟨⟨q, hq⟩, (hm _).2 hk⟩, rfl⟩

end GlobalTheory.ClassRegroup

namespace GlobalTheory.ClassRegroup

open GlobalTheory.FunObj

variable {D : D7}

theorem finCl_regroup (V : HSp D) (hV : ∀ φ : D.host.E →+* ℂ, (V.gram.map φ).PosDef)
    {K K'' : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (hK : IsCO V K) (hK'' : IsCO V K'') (hle : K'' ≤ K)
    {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : Links.IsMeasDef V K μ 𝓕) (f : GfC V → ℂ)
    (hl : ∀ γ ∈ ratFin V, ∀ x, f (γ * x) = f x) (hr : ∀ k ∈ K.comap (finG V), ∀ x, f (x * k) = f x) :
    μ (K''.comap (Lev.finE V)) ≠ 0 ∧
      ∑ᶠ c : FinCl V K'', ((μ (K''.comap (Lev.finE V))).toReal : ℂ) * ((gamOrd V K'' (Quotient.out c) : ℂ))⁻¹ * f (Quotient.out c) =
        ∑ᶠ c : FinCl V K, ((gamOrd V K (Quotient.out c) : ℂ))⁻¹ * f (Quotient.out c) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have := hμ.1.1
  have hfin := (finite_finCl_and_gamOrd V K hV hK).1
  have hfin'' := (finite_finCl_and_gamOrd V K'' hV hK'').1
  letI := Fintype.ofFinite (FinCl V K)
  letI := Fintype.ofFinite (FinCl V K'')
  have h0 : μ (K''.comap (Lev.finE V)) ≠ 0 := hK''.1.measure_ne_zero μ ⟨1, one_mem _⟩
  refine ⟨h0, ?_⟩
  choose a ha using fun c : FinCl V K => finPt_surjective V (Quotient.out c)
  choose a'' ha'' using fun c : FinCl V K'' => finPt_surjective V (Quotient.out c)
  have ho : IsOpen (((K.comap (finG V)).comap (finPt V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [comap_finPt]; exact hK.1
  have ho'' : IsOpen (((K''.comap (finG V)).comap (finPt V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [comap_finPt]; exact hK''.1
  have h1 : μ ((K.comap (finG V)).comap (finPt V)) = 1 := by
    rw [comap_finPt]; exact GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  have h0' : μ ((K''.comap (finG V)).comap (finPt V)) ≠ 0 := by rw [comap_finPt]; exact h0
  have key := ClassRegroup.sum_regroup μ (finPt V) (GQ V) hμ.2 (Subgroup.comap_mono hle : K''.comap (finG V) ≤ K.comap (finG V))
    ho ho'' h1 h0' _ (isReps_out V K) a ha _ (isReps_out V K'') a'' ha'' (fun g => f (finPt V g))
    (fun γ hγ h => by rw [map_mul]; exact hl _ ((mem_ratFin V _).2 ⟨γ, hγ, rfl⟩) _)
    (fun k hk h => by rw [map_mul]; exact hr _ hk _)
  simp only [card_stab, comap_finPt, ha, ha''] at key
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact key

end GlobalTheory.ClassRegroup

namespace GlobalTheory.ClassRegroup

theorem sum_pi_swap_one {ι : Type} [Fintype ι] [DecidableEq ι] {C : ι → Type} [∀ u, Fintype (C u)] (v : ι)
    (w w' : ∀ u, C u → ℂ) (hw : ∀ u, u ≠ v → w u = w' u) (G : (∀ u, C u) → ℂ)
    (hG : ∀ γ : ∀ u, C u, ∑ c, w v c * G (Function.update γ v c) = ∑ c, w' v c * G (Function.update γ v c)) :
    ∑ γ, (∏ u, w u (γ u)) * G γ = ∑ γ, (∏ u, w' u (γ u)) * G γ := by
  set e := Equiv.piSplitAt v C
  have hs : ∀ (c : C v) (r : ∀ u : {u // u ≠ v}, C u) (c' : C v), e.symm (c, r) = Function.update (e.symm (c', r)) v c := by
    intro c r c'
    funext u
    by_cases h : u = v
    · subst h; simp [e, Equiv.piSplitAt_symm_apply]
    · simp [e, Equiv.piSplitAt_symm_apply, h]
  have hp : ∀ (w : ∀ u, C u → ℂ) (c : C v) (r : ∀ u : {u // u ≠ v}, C u),
      ∏ u, w u (e.symm (c, r) u) = w v c * ∏ u : {u // u ≠ v}, w u (r u) := by
    intro w c r
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
    congr 1
    · simp [e, Equiv.piSplitAt_symm_apply]
    · refine Finset.prod_congr rfl fun u _ => ?_
      simp [e, Equiv.piSplitAt_symm_apply, u.2]
  rw [← Fintype.sum_equiv e.symm (fun p => (∏ u, w u (e.symm p u)) * G (e.symm p)) _ (fun _ => rfl),
    ← Fintype.sum_equiv e.symm (fun p => (∏ u, w' u (e.symm p u)) * G (e.symm p)) _ (fun _ => rfl),
    Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_comm (γ := C v)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases isEmpty_or_nonempty (C v) with hC | hne
  · simp
  obtain ⟨c1⟩ := hne
  have hR : ∏ u : {u // u ≠ v}, w u (r u) = ∏ u : {u // u ≠ v}, w' u (r u) :=
    Finset.prod_congr rfl fun u _ => by rw [hw u u.2]
  simp only [hp, hR]
  have e1 : ∀ w'' : ∀ u, C u → ℂ, ∑ c, w'' v c * (∏ u : {u // u ≠ v}, w' u (r u)) * G (e.symm (c, r)) =
      (∏ u : {u // u ≠ v}, w' u (r u)) * ∑ c, w'' v c * G (Function.update (e.symm (c1, r)) v c) := fun w'' => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [hs c r c1]; ring
  rw [e1 w, e1 w', hG]

theorem sum_pi_embed {ι : Type} [Fintype ι] [DecidableEq ι] {A C : ι → Type} [∀ u, Fintype (A u)] [∀ u, Fintype (C u)]
    [∀ u, DecidableEq (C u)] (j : ∀ u, A u → C u) (hj : ∀ u, Function.Injective (j u)) (w : ∀ u, C u → ℂ)
    (hw : ∀ u c, (∀ a, j u a ≠ c) → w u c = 0) (F : (∀ u, C u) → ℂ) :
    ∑ γ, (∏ u, w u (γ u)) * F γ = ∑ α : (∀ u, A u), (∏ u, w u (j u (α u))) * F (fun u => j u (α u)) := by
  classical
  have hinj : Function.Injective (fun α : (∀ u, A u) => fun u => j u (α u)) := fun α α' e =>
    funext fun u => hj u (congr_fun e u)
  rw [← Finset.sum_image (s := Finset.univ) (g := fun α : (∀ u, A u) => fun u => j u (α u))
    (f := fun γ => (∏ u, w u (γ u)) * F γ) (fun α _ α' _ e => hinj e)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun γ _ hγ => ?_).symm
  by_cases h : ∀ u, ∃ a, j u a = γ u
  · choose a ha using h
    exact absurd (Finset.mem_image.2 ⟨a, Finset.mem_univ _, funext ha⟩) hγ
  · push_neg at h
    obtain ⟨u, hu⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ u) (hw u _ hu), zero_mul]

theorem sum_pi_regroup {ι : Type} [Fintype ι] [DecidableEq ι] {X A B : ι → Type} [∀ v, Fintype (A v)] [∀ v, Fintype (B v)]
    (wa : ∀ v, A v → ℂ) (pa : ∀ v, A v → X v) (wb : ∀ v, B v → ℂ) (pb : ∀ v, B v → X v) (P : ∀ v, (X v → ℂ) → Prop)
    (hP : ∀ v g, P v g → ∑ a, wa v a * g (pa v a) = ∑ b, wb v b * g (pb v b)) (f : (∀ v, X v) → ℂ)
    (hf : ∀ v (x : ∀ v, X v), P v fun z => f (Function.update x v z)) :
    ∑ α : (∀ v, A v), (∏ v, wa v (α v)) * f (fun v => pa v (α v)) =
      ∑ β : (∀ v, B v), (∏ v, wb v (β v)) * f (fun v => pb v (β v)) := by
  classical
  let pt : ∀ v, A v ⊕ B v → X v := fun v => Sum.elim (pa v) (pb v)
  let W : Finset ι → ∀ v, A v ⊕ B v → ℂ := fun s v =>
    Sum.elim (fun a => if v ∈ s then 0 else wa v a) (fun b => if v ∈ s then wb v b else 0)
  let T : Finset ι → ℂ := fun s => ∑ γ : (∀ v, A v ⊕ B v), (∏ v, W s v (γ v)) * f (fun v => pt v (γ v))
  have step : ∀ s, T ∅ = T s := by
    intro s
    induction s using Finset.induction_on with
    | empty => rfl
    | insert v s hv ih =>
      rw [ih]
      refine sum_pi_swap_one v (W s) (W (insert v s)) ?_ _ ?_
      · intro u hu
        funext c
        cases c <;> simp [W, Finset.mem_insert, hu]
      · intro γ
        have hupd : ∀ c, (fun u => pt u (Function.update γ v c u)) = Function.update (fun u => pt u (γ u)) v (pt v c) :=
          fun c => funext fun u => Function.apply_update pt γ v c u
        simp only [hupd, Fintype.sum_sum_type]
        have := hP v _ (hf v fun u => pt u (γ u))
        simp only [W, pt, Sum.elim_inl, Sum.elim_inr, hv, if_false, Finset.mem_insert, true_or, if_true, zero_mul,
          Finset.sum_const_zero, add_zero, zero_add]
        exact this
  have h0 : T ∅ = ∑ α : (∀ v, A v), (∏ v, wa v (α v)) * f (fun v => pa v (α v)) := by
    show ∑ γ : (∀ v, A v ⊕ B v), (∏ v, W ∅ v (γ v)) * f (fun v => pt v (γ v)) = _
    rw [sum_pi_embed (fun v => (Sum.inl : A v → A v ⊕ B v)) (fun v => Sum.inl_injective) (W ∅)]
    · simp [W, pt]
    · intro u c hc
      cases c with
      | inl a => exact absurd rfl (hc a)
      | inr b => simp [W]
  have h1 : T Finset.univ = ∑ β : (∀ v, B v), (∏ v, wb v (β v)) * f (fun v => pb v (β v)) := by
    show ∑ γ : (∀ v, A v ⊕ B v), (∏ v, W Finset.univ v (γ v)) * f (fun v => pt v (γ v)) = _
    rw [sum_pi_embed (fun v => (Sum.inr : B v → A v ⊕ B v)) (fun v => Sum.inr_injective) (W Finset.univ)]
    · simp [W, pt]
    · intro u c hc
      cases c with
      | inl a => simp [W]
      | inr b => exact absurd rfl (hc b)
  rw [← h0, ← h1, step]

end GlobalTheory.ClassRegroup

namespace GlobalTheory.ClassRegroup

open GlobalTheory.FunObj

variable {D : D7}

def IsInvAt {ι : Type} [DecidableEq ι] (V : ι → HSp D) (K : ∀ v, Subgroup (GL (Fin (V v).rank) (Lev.EAf D)))
    (f : (∀ v, GfC (V v)) → ℂ) : Prop :=
  ∀ v (x : ∀ v, GfC (V v)), (∀ γ ∈ ratFin (V v), ∀ z, f (Function.update x v (γ * z)) = f (Function.update x v z)) ∧
    ∀ k ∈ (K v).comap (finG (V v)), ∀ z, f (Function.update x v (z * k)) = f (Function.update x v z)

example {ι : Type} [DecidableEq ι] (V : ι → HSp D) (K : ∀ v, Subgroup (GL (Fin (V v).rank) (Lev.EAf D))) :
    IsInvAt V K fun _ => 1 := fun _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem finCl_regroup_pi {ι : Type} [Fintype ι] [DecidableEq ι] (V : ι → HSp D)
    (hV : ∀ v, ∀ φ : D.host.E →+* ℂ, ((V v).gram.map φ).PosDef) {K K'' : ∀ v, Subgroup (GL (Fin (V v).rank) (Lev.EAf D))}
    (hK : ∀ v, IsCO (V v) (K v)) (hK'' : ∀ v, IsCO (V v) (K'' v)) (hle : ∀ v, K'' v ≤ K v)
    {μ : ∀ v, Measure (GA D (V v))} {𝓕 : ∀ v, Set (GA D (V v))} (hμ : ∀ v, Links.IsMeasDef (V v) (K v) (μ v) (𝓕 v))
    (f : (∀ v, GfC (V v)) → ℂ) (hf : IsInvAt V K f) :
    ∑ᶠ c : (∀ v, FinCl (V v) (K'' v)),
        (∏ v, ((μ v ((K'' v).comap (Lev.finE (V v)))).toReal : ℂ) * ((gamOrd (V v) (K'' v) (Quotient.out (c v)) : ℂ))⁻¹) *
          f (fun v => Quotient.out (c v)) =
      ∑ᶠ c : (∀ v, FinCl (V v) (K v)), (∏ v, ((gamOrd (V v) (K v) (Quotient.out (c v)) : ℂ))⁻¹) * f (fun v => Quotient.out (c v)) := by
  letI : ∀ v, Fintype (FinCl (V v) (K v)) := fun v => @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V v) (K v) (hV v) (hK v)).1
  letI : ∀ v, Fintype (FinCl (V v) (K'' v)) := fun v =>
    @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V v) (K'' v) (hV v) (hK'' v)).1
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine sum_pi_regroup (X := fun v => GfC (V v)) (A := fun v => FinCl (V v) (K'' v)) (B := fun v => FinCl (V v) (K v)) (fun v c => ((μ v ((K'' v).comap (Lev.finE (V v)))).toReal : ℂ) *
      ((gamOrd (V v) (K'' v) (Quotient.out c) : ℂ))⁻¹) (fun v c => Quotient.out c)
    (fun v c => ((gamOrd (V v) (K v) (Quotient.out c) : ℂ))⁻¹) (fun v c => Quotient.out c)
    (fun v g => (∀ γ ∈ ratFin (V v), ∀ z, g (γ * z) = g z) ∧ ∀ k ∈ (K v).comap (finG (V v)), ∀ z, g (z * k) = g z) ?_ f hf
  rintro v g ⟨hl, hr⟩
  have := (finCl_regroup (V v) (hV v) (hK v) (hK'' v) (hle v) (hμ v) g hl hr).2
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at this
  exact this

theorem finCl_regroup_prod {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (V : ι → HSp D) (V' : κ → HSp D)
    (hV : ∀ v, ∀ φ : D.host.E →+* ℂ, ((V v).gram.map φ).PosDef) (hV' : ∀ v, ∀ φ : D.host.E →+* ℂ, ((V' v).gram.map φ).PosDef)
    {K K'' : ∀ v, Subgroup (GL (Fin (V v).rank) (Lev.EAf D))} {L L'' : ∀ v, Subgroup (GL (Fin (V' v).rank) (Lev.EAf D))}
    (hK : ∀ v, IsCO (V v) (K v)) (hK'' : ∀ v, IsCO (V v) (K'' v)) (hle : ∀ v, K'' v ≤ K v)
    (hL : ∀ v, IsCO (V' v) (L v)) (hL'' : ∀ v, IsCO (V' v) (L'' v)) (hle' : ∀ v, L'' v ≤ L v)
    {μ : ∀ v, Measure (GA D (V v))} {𝓕 : ∀ v, Set (GA D (V v))} (hμ : ∀ v, Links.IsMeasDef (V v) (K v) (μ v) (𝓕 v))
    {μ' : ∀ v, Measure (GA D (V' v))} {𝓕' : ∀ v, Set (GA D (V' v))} (hμ' : ∀ v, Links.IsMeasDef (V' v) (L v) (μ' v) (𝓕' v))
    (f : (∀ v, GfC (V v)) → (∀ v, GfC (V' v)) → ℂ) (hf : ∀ y, IsInvAt V K fun x => f x y) (hf' : ∀ x, IsInvAt V' L (f x)) :
    ∑ᶠ c : (∀ v, FinCl (V v) (K'' v)) × (∀ v, FinCl (V' v) (L'' v)),
        ((∏ v, ((μ v ((K'' v).comap (Lev.finE (V v)))).toReal : ℂ) * ((gamOrd (V v) (K'' v) (Quotient.out (c.1 v)) : ℂ))⁻¹) *
          ∏ v, ((μ' v ((L'' v).comap (Lev.finE (V' v)))).toReal : ℂ) * ((gamOrd (V' v) (L'' v) (Quotient.out (c.2 v)) : ℂ))⁻¹) *
          f (fun v => Quotient.out (c.1 v)) (fun v => Quotient.out (c.2 v)) =
      ∑ᶠ c : (∀ v, FinCl (V v) (K v)) × (∀ v, FinCl (V' v) (L v)),
        ((∏ v, ((gamOrd (V v) (K v) (Quotient.out (c.1 v)) : ℂ))⁻¹) * ∏ v, ((gamOrd (V' v) (L v) (Quotient.out (c.2 v)) : ℂ))⁻¹) *
          f (fun v => Quotient.out (c.1 v)) (fun v => Quotient.out (c.2 v)) := by
  letI : ∀ v, Fintype (FinCl (V v) (K v)) := fun v => @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V v) (K v) (hV v) (hK v)).1
  letI : ∀ v, Fintype (FinCl (V v) (K'' v)) := fun v =>
    @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V v) (K'' v) (hV v) (hK'' v)).1
  letI : ∀ v, Fintype (FinCl (V' v) (L v)) := fun v => @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V' v) (L v) (hV' v) (hL v)).1
  letI : ∀ v, Fintype (FinCl (V' v) (L'' v)) := fun v =>
    @Fintype.ofFinite _ (finite_finCl_and_gamOrd (V' v) (L'' v) (hV' v) (hL'' v)).1
  have e1 := fun x => finCl_regroup_pi V' hV' hL hL'' hle' hμ' (f x) (hf' x)
  have e2 := fun y => finCl_regroup_pi V hV hK hK'' hle hμ (fun x => f x y) (hf y)
  simp only [finsum_eq_sum_of_fintype] at e1 e2 ⊢
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc _ = ∑ a : (∀ v, FinCl (V v) (K'' v)), (∏ v, ((μ v ((K'' v).comap (Lev.finE (V v)))).toReal : ℂ) *
          ((gamOrd (V v) (K'' v) (Quotient.out (a v)) : ℂ))⁻¹) * ∑ b : (∀ v, FinCl (V' v) (L v)),
          (∏ v, ((gamOrd (V' v) (L v) (Quotient.out (b v)) : ℂ))⁻¹) *
            f (fun v => Quotient.out (a v)) (fun v => Quotient.out (b v)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← e1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b : (∀ v, FinCl (V' v) (L v)), (∏ v, ((gamOrd (V' v) (L v) (Quotient.out (b v)) : ℂ))⁻¹) *
          ∑ a : (∀ v, FinCl (V v) (K'' v)), (∏ v, ((μ v ((K'' v).comap (Lev.finE (V v)))).toReal : ℂ) *
            ((gamOrd (V v) (K'' v) (Quotient.out (a v)) : ℂ))⁻¹) *
            f (fun v => Quotient.out (a v)) (fun v => Quotient.out (b v)) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by
        simp only [e2, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.ClassRegroup

namespace GlobalTheory.ClassRegroup

variable {D : D7}

end GlobalTheory.ClassRegroup
