import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.IsoFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ThetaLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.AbsNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.ThetaFin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
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

private theorem nilKill_loc (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) {κ : Type} (t : κ ⊕ κ → Fin n → kˣ)
    (ht : ∀ a, ∃ (C' : Subgroup 𝓀[k]ˣ) (δ : kˣ) (i : Fin n), IsGenMod k C' δ ∧ t (.inr a) = Pi.mulSingle i δ) (θY) (hY : IsTheta π C θY)
    (act : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] Module.End ℂ (fixd π (iwC k n C))) (hact : ∀ a, act (MvPolynomial.X a) = θY (t a))
    (F : MvPolynomial (κ ⊕ κ) ℂ) (hF : ∀ θ, IsTheta σ.ρ C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
      (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
      ∀ (S : Type) [CommRing S] [Algebra ℂ S] (φ : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] S), (∀ a, (φ (MvPolynomial.X (.inl a)) - algebraMap ℂ S (χ (t (.inl a)) : ℂ)) ^ n.factorial = 0) → (∀ a, φ (MvPolynomial.X (.inr a)) = algebraMap ℂ S (χ (t (.inr a)) : ℂ)) → φ F = 0) : act F = 0 := by
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := thetaEx k n C ℂ σ.V σ.ρ hq
  obtain ⟨hfd, hrk, -⟩ := jqLine hG hBZ k n C σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨actσ, hσ⟩ := nilKill_act θ t
  have hnil := absNil _ _ κ θ t actσ hσ (fun a => by
    obtain ⟨C', δ, i, h1, h2⟩ := ht a
    rw [h2]
    exact thetaFin k n ℂ σ.V σ.ρ C C' θ hθ δ h1 i) _ hrk F (hF θ hθ)
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  have hle : iwC k n C ≤ iwahori k (Fin n) := fun g hg => (((memIwC k n C).1 g).1 hg).1
  have hc : IsCompact (iwC k n C : Set (GL (Fin n) k)) :=
    (IwahoriOnto.isCompact_iwahori k (Fin n)).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle
  refine LinearMap.ext fun y => ?_
  have hy := isoFix k n Y π σ _ hc hs y y.2
  have hsub : (⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ (iwC k n C)).map f.1) ≤
      (LinearMap.ker (act F)).map (fixd π (iwC k n C)).subtype := by
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

theorem UpperTheory.V.Th.nilKillX :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GV n w) Y) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ π C Θ → ∀ (j : Fin q) (σ : SmIrr (GLw n (w j))), IsoSum (π.comp (atJ n w j)) ⊤ σ → ∀ (κ : Type) (t : κ ⊕ κ → Fin n → ((w j).adicCompletion L)ˣ), (∀ a, ∃ (C' : Subgroup 𝓀[(w j).adicCompletion L]ˣ) (δ : ((w j).adicCompletion L)ˣ) (i : Fin n), IsGenMod _ C' δ ∧ t (.inr a) = Pi.mulSingle i δ) → ∀ (act : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] Module.End ℂ (fixd π (UC n w C))), (∀ a, act (MvPolynomial.X a) = Θ j (t a)) → ∀ F : MvPolynomial (κ ⊕ κ) ℂ, (∀ θ, IsTheta σ.ρ (C j) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC _ n (C j)))) (χ t : ℂ)) ≠ ⊥ → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (φ : MvPolynomial (κ ⊕ κ) ℂ →ₐ[ℂ] S), (∀ a, (φ (MvPolynomial.X (.inl a)) - algebraMap ℂ S (χ (t (.inl a)) : ℂ)) ^ n.factorial = 0) → (∀ a, φ (MvPolynomial.X (.inr a)) = algebraMap ℂ S (χ (t (.inr a)) : ℂ)) → φ F = 0) → act F = 0 := by
  intro hG hBZ L _ _ n q w Y _ _ π C Θ hΘ j σ hs κ t ht act hact F hF
  have hq : IsUnit (resCard ((w j).adicCompletion L) : ℂ) :=
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨θY, hY, -⟩ := thetaEx _ n (C j) ℂ Y (π.comp (atJ n w j)) hq
  obtain ⟨actY, haY⟩ := nilKill_act θY t
  have h0 := nilKill_loc hG hBZ (C j) (π.comp (atJ n w j)) σ hs t ht θY hY actY haY F hF
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
