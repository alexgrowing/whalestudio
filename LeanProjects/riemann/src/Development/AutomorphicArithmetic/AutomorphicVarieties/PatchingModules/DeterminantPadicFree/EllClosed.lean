import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section
variable {Γ R S : Type} [TopologicalSpace Γ] [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

private theorem ac_const (c : R) : AdicCont I fun _ : Γ => c := fun _ => IsLocallyConstant.const _

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s + g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· + ·)
  simpa [Function.comp_def, map_add] using this

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have := (hf N).comp₂ (hg N) (· * ·)
  simpa [Function.comp_def, map_mul] using this

private theorem ac_sum {ι : Type} (T : Finset ι) {f : ι → Γ → R} (hf : ∀ i, AdicCont I (f i)) :
    AdicCont I fun s => ∑ i ∈ T, f i s := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using ac_const (I := I) (Γ := Γ) 0
  | insert a T ha ih => simpa only [Finset.sum_insert ha] using ac_add (hf a) ih

private theorem ac_map (L : R → S) (hL : ∀ (N : ℕ) a b, a - b ∈ I ^ N → L a - L b ∈ J ^ N) {f : Γ → R}
    (hf : AdicCont I f) : AdicCont J fun s => L (f s) := by
  intro N
  have h : IsLocallyConstant fun s => Ideal.Quotient.mk (I ^ N) (f s) := hf N
  show IsLocallyConstant fun s => Ideal.Quotient.mk (J ^ N) (L (f s))
  rw [IsLocallyConstant.iff_eventually_eq] at h ⊢
  intro x
  filter_upwards [h x] with y hy
  rw [Ideal.Quotient.eq] at hy ⊢
  exact hL N _ _ hy

private theorem ac_hom (L : R →+* S) (t : R) {f : Γ → R}
    (hf : AdicCont (Ideal.span {t}) f) : AdicCont (Ideal.span {L t}) fun s => L (f s) := by
  refine ac_map L (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨L c, by rw [← map_pow, ← map_mul, hc, map_sub]⟩

private theorem ac_eta {g : ℕ} (t : R) {f : Γ → DD R g}
    (hf : AdicCont (Ideal.span {(DD.C t : DD R g)}) f) : AdicCont (Ideal.span {t}) fun s => (f s).eta := by
  refine ac_map (fun x : DD R g => x.eta) (fun N a b h => ?_) hf
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  obtain ⟨c, hc⟩ := h
  refine ⟨c.eta, ?_⟩
  have e : (a - b).eta = a.eta - b.eta := rfl
  rw [← e, ← hc, ← map_pow, show (DD.C (t ^ N) : DD R g) = ⟨t ^ N, 0, 0, 0⟩ from rfl]
  simp

private theorem sum_comp {g : ℕ} {ι : Type} (T : Finset ι) (f : ι → DD R g) :
    (∑ i ∈ T, f i).a = ∑ i ∈ T, (f i).a ∧ (∀ j, (∑ i ∈ T, f i).ep j = ∑ i ∈ T, (f i).ep j) ∧
      (∀ j, (∑ i ∈ T, f i).ep' j = ∑ i ∈ T, (f i).ep' j) ∧ (∑ i ∈ T, f i).eta = ∑ i ∈ T, (f i).eta := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩
  | insert i T hi ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [Finset.sum_insert hi]
    exact ⟨by rw [← h1]; rfl, fun j => by rw [← h2 j]; rfl, fun j => by rw [← h3 j]; rfl, by rw [← h4]; rfl⟩

private theorem epM_eq {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) R) (a b : Fin n) :
    DD.epM Z a b = ∑ j, DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g) := by
  classical
  have hC : ∀ c : R, (DD.C c : DD R g) = ⟨c, 0, 0, 0⟩ := fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := sum_comp Finset.univ (fun j => DD.C (Z j a b) * (⟨0, Pi.single j 1, 0, 0⟩ : DD R g))
  apply DD.ext
  · rw [h1]
    change (0 : R) = _
    simp [hC]
  · funext j
    rw [h2 j]
    change Z j a b = _
    simp [hC, Pi.single_apply]
  · funext j
    rw [h3 j]
    change (0 : R) = _
    simp [hC]
  · rw [h4]
    change (0 : R) = _
    simp [hC]

end

theorem UpperTheory.V.Pa.Det.ellClosed :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (z : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), z ∈ TwZ k x.A → IsClosed {σ : F.G₀ | ell k x.A σ z = 0} := by
  intro l _ F n x k z hz
  unfold TwZ at hz
  obtain ⟨-, hzc, -, -⟩ := hz
  have hmul : ∀ M N : F.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g),
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => M s i j) →
      (∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => N s i j) →
      ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (M s * N s) i j := by
    intro M N hM hN i j
    simp only [Matrix.mul_apply]
    exact ac_sum _ fun m => ac_mul (hM i m) (hN m j)
  have hρ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => x.ρX (DD x.A k.g) s i j := by
    intro i j
    have h := x.cont i j
    rw [PowerSeries.maximalIdeal_eq_span_X] at h
    exact ac_hom DD.C x.t h
  have hκ : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)})
      fun s => DD.epM (fun m => (k.κ m s).map ⇑(algebraMap x.A x.A)) i j := by
    intro i j
    simp only [epM_eq]
    refine ac_sum _ fun m => ac_mul ?_ (ac_const _)
    have hm := k.mem m
    unfold SelZ at hm
    obtain ⟨-, hc, -⟩ := hm
    exact ac_hom DD.C x.t (hc i j)
  have hρ1 : ∀ i j, AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => k.ρ1 x.A s i j := by
    have := hmul (fun s => 1 + DD.epM fun m => (k.κ m s).map ⇑(algebraMap x.A x.A))
      (fun s => x.ρX (DD x.A k.g) s)
      (fun i j => by simpa only [Matrix.add_apply] using ac_add (ac_const _) (hκ i j)) hρ
    intro i j
    exact this i j
  have hprod := hmul z (fun s => k.ρ1 x.A s) hzc hρ1
  have htr : AdicCont (Ideal.span {(DD.C x.t : DD x.A k.g)}) fun s => (z s * k.ρ1 x.A s).trace := by
    simp only [Matrix.trace, Matrix.diag]
    exact ac_sum _ fun i => hprod i i
  have hf : AdicCont (Ideal.span {x.t}) fun s => ell k x.A s z := ac_eta x.t htr
  have sep : ∀ a : x.A, (∀ N : ℕ, Ideal.Quotient.mk (Ideal.span {x.t} ^ N) a = 0) → a = 0 := by
    intro a ha
    refine PowerSeries.ext fun m => ?_
    have h := ha (m + 1)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
    obtain ⟨c, hc⟩ := h
    rw [show x.t = PowerSeries.X from rfl] at hc
    rw [← hc, PowerSeries.coeff_mul_X_pow']
    simp
  have hset : {σ : F.G₀ | ell k x.A σ z = 0} =
      ⋂ N : ℕ, {s | Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) = 0} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h N
      rw [h, map_zero]
    · exact sep _
  rw [hset]
  exact isClosed_iInter fun N =>
    ((show IsLocallyConstant fun s => Ideal.Quotient.mk (Ideal.span {x.t} ^ N) (ell k x.A s z) from hf N).isClopen_fiber 0).isClosed
