import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.IsoFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqLine
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem nilKill_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun _ _ i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
  have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
  refine ⟨c, fun s hs i j hij => ?_⟩
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
    rcases hs with rfl | rfl
    · simpa using h1
    · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
      refine this.trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
  have hj := j.2
  have hlt' : (i : ℕ) < j := hlt
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))

private theorem nilKill_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI : Fintype (MulAction.orbit K (x : G ⧸ K')) := Set.Finite.fintype hx
  unfold dc
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ => (hf _ _).symm

private theorem nilKill_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have hinj : Function.Injective (θ' b).val := ((Module.End.isUnit_iff _).1 (θ' b).isUnit).1
  apply hinj
  have h := ha m
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h, hb]

private theorem nilKill_eig {T W : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (S0 : Submodule ℂ W) (h0 : S0 ≠ ⊥)
    (h1 : ∀ t, ∀ v ∈ S0, (θ t : Module.End ℂ W) v ∈ S0) :
    ∃ χ : T →* ℂˣ, ∃ v ∈ S0, v ≠ 0 ∧ ∀ t, (θ t : Module.End ℂ W) v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hle, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ W)).has_min
    {S | S ≠ ⊥ ∧ S ≤ S0 ∧ ∀ t, ∀ v ∈ S, (θ t : Module.End ℂ W) v ∈ S} ⟨S0, h0, le_rfl, h1⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, (θ t : Module.End ℂ W) v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((θ t : Module.End ℂ W).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : (θ t : Module.End ℂ W) w = c • (w : W) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (θ t : Module.End ℂ W) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hle, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_comm, map_mul, Units.val_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : T →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Units.val_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Units.val_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul,
          mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  refine ⟨c'.toHomUnits, v, hle hv, hv0, fun t => ?_⟩
  rw [hc t v hv]
  simp [c']

private theorem nilKill_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = θ (t a) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) 1), fun a => by simp⟩

private theorem nilKill_int {W W' κ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W) (act' : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →ₗ[ℂ] W')
    (h : ∀ a v, act' (MvPolynomial.X a) (g v) = g (act (MvPolynomial.X a) v)) (F : MvPolynomial κ ℂ) (v : W) :
    act' F (g v) = g (act F v) := by
  induction F using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
    simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp => simp [h, hp]

private theorem nilKill_nil {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W)
    (hact : ∀ a, act (MvPolynomial.X a) = θ (t a)) (F : MvPolynomial κ ℂ)
    (hF : ∀ χ : T →* ℂˣ, (⨅ s, Module.End.maxGenEigenspace (θ s : Module.End ℂ W) (χ s : ℂ)) ≠ ⊥ →
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) (N : ℕ) (hN : Module.finrank ℂ W ≤ N) :
    act (F ^ N) = 0 := by
  by_contra hne
  have h0 : LinearMap.range (act (F ^ N)) ≠ ⊥ := fun h => hne (LinearMap.range_eq_bot.1 h)
  obtain ⟨χ, v, ⟨u, rfl⟩, hv0, hv⟩ := nilKill_eig θ _ h0 (by
    rintro s _ ⟨u, rfl⟩
    refine ⟨(θ s : Module.End ℂ W) u, nilKill_int act act _ (fun a v => ?_) _ _⟩
    rw [hact, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul, ← map_mul,
      ← map_mul, mul_comm])
  have hχ := hF χ ((Submodule.ne_bot_iff _).2 ⟨_, (Submodule.mem_iInf _).2 fun s =>
    (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [pow_one, LinearMap.sub_apply, hv s]; simp⟩, hv0⟩)
  have hev : ∀ G : MvPolynomial κ ℂ, act G (act (F ^ N) u) =
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) G • act (F ^ N) u := by
    intro G
    generalize act (F ^ N) u = x at hv
    induction G using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      simp
    | add p q hp hq => simp [hp, hq, add_smul]
    | mul_X p a hp =>
      rw [map_mul, map_mul, Module.End.mul_apply, hact, hv, map_smul, hp, MvPolynomial.eval_X, smul_smul, mul_comm]
  have h1 : u ∈ LinearMap.ker (act F ^ (N + 1)) := by
    rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply, ← map_pow, hev, hχ, zero_smul]
  have h2 := Module.End.ker_pow_le_ker_pow_finrank _ _ h1
  apply hv0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [map_pow, pow_add, Module.End.mul_apply, LinearMap.mem_ker.1 h2, map_zero]

private theorem nilKill_loc (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) {κ : Type} (t : κ → Fin n → kˣ) (θY) (hY : IsTheta π C θY)
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ (fixd π (iwC k n C))) (hact : ∀ a, act (MvPolynomial.X a) = θY (t a))
    (F : MvPolynomial κ ℂ) (hF : ∀ θ, IsTheta σ.ρ C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
      (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) : act (F ^ n.factorial) = 0 := by
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := thetaEx k n C ℂ σ.V σ.ρ hq
  obtain ⟨hfd, hrk, -⟩ := jqLine hG hBZ k n C σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨actσ, hσ⟩ := nilKill_act θ t
  have hnil := nilKill_nil θ t actσ hσ F (hF θ hθ) _ hrk
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  have hle : iwC k n C ≤ iwahori k (Fin n) := fun g hg => (((memIwC k n C).1 g).1 hg).1
  have hc : IsCompact (iwC k n C : Set (GL (Fin n) k)) :=
    (IwahoriOnto.isCompact_iwahori k (Fin n)).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle
  refine LinearMap.ext fun y => ?_
  have hy := isoFix k n Y π σ _ hc hs y y.2
  have hsub : (⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ (iwC k n C)).map f.1) ≤
      (LinearMap.ker (act (F ^ n.factorial))).map (fixd π (iwC k n C)).subtype := by
    refine iSup_le ?_
    rintro ⟨f, hf⟩ _ ⟨v, hv, rfl⟩
    let g : fixd σ.ρ (iwC k n C) →ₗ[ℂ] fixd π (iwC k n C) :=
      f.restrict fun x hx u hu => by rw [← hf, hx u hu]
    have hd : ∀ s, Dom s → ∀ v, (θY s).val (g v) = g ((θ s).val v) := by
      intro s hs v
      apply Subtype.ext
      change _ = f _
      have hfin : FinOrb (iwC k n C) (iwC k n C) (diagT k (Fin n) s) := (heckePairIwC _ n C).1 _
      rw [hY s hs, hθ s hs]
      refine ((hkApply ℂ _ Y π _ _ _ hfin).1 (g v)).trans ?_
      refine (nilKill_dc σ.ρ π _ _ _ hfin f.toAddMonoidHom hf v).trans ?_
      exact congrArg f ((hkApply ℂ _ σ.V σ.ρ _ _ _ hfin).1 v).symm
    have hall : ∀ s v, (θY s).val (g v) = g ((θ s).val v) := by
      intro s v
      obtain ⟨c, hc⟩ := nilKill_split s
      refine nilKill_ext θ θY g s (fun i : Fin n => c ^ (n - (i : ℕ))) (hd _ ?_) (hd _ ?_) v
      · intro i i' hi
        simpa using hc 1 (Or.inl rfl) i i' hi
      · rw [mul_comm]
        exact hc s (Or.inr rfl)
    refine ⟨g ⟨v, hv⟩, ?_, rfl⟩
    change act _ _ = 0
    rw [nilKill_int actσ act g (fun a v => by rw [hact, hσ, hall]), hnil, LinearMap.zero_apply, map_zero]
  obtain ⟨y', hy', e⟩ := hsub hy
  obtain rfl : y' = y := Subtype.ext e
  exact hy'

theorem UpperTheory.V.Pa.Lev.nilKill :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GV n w) Y) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ π C Θ → ∀ (j : Fin q) (σ : SmIrr (GLw n (w j))), IsoSum (π.comp (atJ n w j)) ⊤ σ → ∀ (κ : Type) (t : κ → Fin n → ((w j).adicCompletion L)ˣ) (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ (fixd π (UC n w C))), (∀ a, act (MvPolynomial.X a) = Θ j (t a)) → ∀ F : MvPolynomial κ ℂ, (∀ θ, IsTheta σ.ρ (C j) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC _ n (C j)))) (χ t : ℂ)) ≠ ⊥ → MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) → act (F ^ n.factorial) = 0 := by
  intro hG hBZ L _ _ n q w Y _ _ π C Θ hΘ j σ hs κ t act hact F hF
  have hq : IsUnit (resCard ((w j).adicCompletion L) : ℂ) :=
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨θY, hY, -⟩ := thetaEx _ n (C j) ℂ Y (π.comp (atJ n w j)) hq
  obtain ⟨actY, haY⟩ := nilKill_act θY t
  have h0 := nilKill_loc hG hBZ (C j) (π.comp (atJ n w j)) σ hs t θY hY actY haY F hF
  have hle : fixd π (UC n w C) ≤ fixd (π.comp (atJ n w j)) (iwC _ n (C j)) := by
    intro x hx u hu
    refine hx (atJ n w j u) fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      simpa [atJ] using hu
    · have : atJ n w j u j' = 1 := Pi.mulSingle_eq_of_ne (M := fun j => GLw n (w j)) h u
      rw [this]
      exact (iwC _ n (C j')).one_mem
  refine LinearMap.ext fun m => Submodule.inclusion_injective hle ?_
  rw [← nilKill_int act actY (Submodule.inclusion hle) (fun a v => ?_), h0, LinearMap.zero_apply,
    LinearMap.zero_apply, map_zero]
  rw [haY, hact]
  exact Subtype.ext (thetaLoc L n q w ℂ Y π C Θ hΘ j θY hY (t a) v _ rfl)
