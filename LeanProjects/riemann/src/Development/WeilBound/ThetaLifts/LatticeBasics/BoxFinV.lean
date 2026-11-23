import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

theorem at_entry' {α β : Type} {u : Matrix α β (AE F E)} (hu : At (evI F) u) (i : α) (j : β) :
    At (evI F) (u i j) := fun c hc => by
  simpa using congrFun (congrFun (hu c hc) i) j

theorem exists_real_structure' (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    {α β : Type} {κ : Type} [Fintype κ]
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (C : InfinitePlace F → Matrix α β ℂ →ₗ[ℝ] Matrix α β ℂ) :
    ∃ (s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
          Matrix α β (AE F E))
      (Jm : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p, At (evI F) (s p)) ∧
      (∀ p, (fun i => evI F ((e (s p)).1 i)) = p.1 ∧ (fun i => evI F ((e (s p)).2 i)) = p.2) ∧
      ∀ p w, (s (Jm p)).map (piInf (emb w)) = C w ((s p).map (piInf (emb w))) := by
  let s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
      Matrix α β (AE F E) :=
    fun p => e.symm (fun i => lift (p.1 i), fun i => lift (p.2 i))
  have es : ∀ p, e (s p) = (fun i => lift (p.1 i), fun i => lift (p.2 i)) := fun p => e.apply_symm_apply _
  have sAdd : ∀ p q, s (p + q) = s p + s q := fun p q => by
    show e.symm _ = e.symm _ + e.symm _
    rw [← map_add]
    congr 1
    refine Prod.ext (funext fun i => lift_add _ _) (funext fun i => lift_add _ _)
  have sSmul : ∀ (t : ℝ) p, s (t • p) = realAd F t • s p := fun t p => by
    show e.symm _ = realAd F t • e.symm _
    rw [← map_smul]
    congr 1
    refine Prod.ext (funext fun i => lift_smul _ _) (funext fun i => lift_smul _ _)
  have sAt : ∀ p, At (evI F) (s p) := fun p c hc => by
    show c • e.symm _ = 0
    rw [← map_smul]
    have : c • ((fun i => lift (p.1 i), fun i => lift (p.2 i)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun i => at_lift _ c hc) (funext fun i => at_lift _ c hc)
    rw [this, map_zero]
  let Ψ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun p w => (s p).map (piInf (emb w))
      map_add' := fun p q => by
        funext w
        rw [sAdd]
        ext i j
        simp
      map_smul' := fun t p => by
        funext w
        rw [sSmul]
        ext i j
        simp [GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul] }
  have hΨ : ∀ p w, Ψ p w = (s p).map (piInf (emb w)) := fun _ _ => rfl
  have inj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun p hp => ?_
    have s0 : s p = 0 := by
      ext i j
      refine GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h emb _ (at_entry' (sAt p) i j) fun w => ?_
      have := congrFun (congrFun (congrFun hp w) i) j
      simpa [hΨ] using this
    have e0 := es p
    rw [s0, map_zero] at e0
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := congrFun (congrArg Prod.fst e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
    · have := congrFun (congrArg Prod.snd e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
  have surj : Function.Surjective Ψ := fun Z => by
    choose x hxA hxZ using fun (ij : α × β) => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h emb (fun w => Z w ij.1 ij.2)
    let u : Matrix α β (AE F E) := Matrix.of fun i j => x (i, j)
    have uAt : At (evI F) u := fun c hc => by
      ext i j
      exact hxA (i, j) c hc
    have hAt2 : ∀ c : AF F, evI F c = 0 → c • e u = 0 := fun c hc => by
      rw [← map_smul, uAt c hc, map_zero]
    refine ⟨(fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)), ?_⟩
    have su : s (fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)) = u := by
      show e.symm _ = u
      rw [LinearEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => lift_evI fun c hc => ?_) (funext fun i => lift_evI fun c hc => ?_)
      · exact congrFun (congrArg Prod.fst (hAt2 c hc)) i
      · exact congrFun (congrArg Prod.snd (hAt2 c hc)) i
    funext w
    rw [hΨ, su]
    ext i j
    exact hxZ (i, j) w
  let Ψe := LinearEquiv.ofBijective Ψ ⟨inj, surj⟩
  let Cp : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix α β ℂ) :=
    LinearMap.pi fun w => C w ∘ₗ LinearMap.proj w
  refine ⟨s, Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ, sAt, fun p => ?_, fun p w => ?_⟩
  · rw [es]
    exact ⟨funext fun i => evI_lift _, funext fun i => evI_lift _⟩
  · have : Ψ ((Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ) p) = Cp (Ψ p) := Ψe.apply_symm_apply _
    exact congrFun this w

def Rel (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ)
    (θ' : InfinitePlace F → Matrix β β ℂ) (u u' : Matrix (Fin m) β (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)

def dd0 (p : (κ → AF F) × (κ → AF F)) (f : SInf F κ) : SInf F κ := dop (nf p.1) (linForm (nf p.2)) f

def Gs (e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ) (θ' : InfinitePlace F → Matrix β β ℂ)
    (f : SInf F κ) : Prop :=
  ∀ u u', At (evI F) u → At (evI F) u' → Rel τ ε θ θ' u u' → dd0 (e u') f = Complex.I • dd0 (e u) f

variable {e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)} {τ : ∀ w : InfinitePlace F, EmbOver E w}
  {ε ε' : InfinitePlace F → ℤˣ} {θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ} {θ' : InfinitePlace F → Matrix β β ℂ}
  {f f' : SInf F κ}

theorem Gs.gau (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (h0 : f ≠ 0) : ∃ k, Gau f k := by
  let C : InfinitePlace F → Matrix (Fin m) β ℂ →ₗ[ℝ] Matrix (Fin m) β ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * x * (θ' w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure' σ h τ e C
  let T : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add])
      (fun t y b => by simp only [linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : linForm b (Pi.single i y) = 0 := hb _
      rw [linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f h0 fun p y => by
    have := congrArg (fun g : SInf F κ => g y) (hf (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    have e1 : ∀ q, nf (e (S q)).1 = q.1 := fun q => (sev q).1
    have e2 : ∀ q, nf (e (S q)).2 = q.2 := fun q => (sev q).2
    simp only [dd0, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, e1, e2] at this
    exact this
  exact ⟨k, gau_of h0 hk⟩

theorem exists_rel (h : IsCMExt F E σ) (ε : InfinitePlace F → ℤˣ) (u : Matrix (Fin m) β (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel τ ε θ θ' u u' := by
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ fun w =>
    ((((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)) i j
  exact ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w => Matrix.ext fun i j => hz i j w⟩

theorem Gs.same (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (hf' : Gs e τ ε' θ θ' f') (h0 : f ≠ 0) (h0' : f' ≠ 0) :
    Gs e τ ε θ θ' f' := by
  intro u u' hu hu' hr
  obtain ⟨k, g⟩ := hf.gau h h0
  obtain ⟨k', g'⟩ := hf'.gau h h0'
  obtain ⟨u'', hu'', hr'⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε' u
  have hv : At (evI F) (u' - u'') := fun c hc => by rw [smul_sub, hu' c hc, hu'' c hc, sub_zero]
  obtain ⟨v', hv', hs⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε (u' - u'')
  have hs' : Rel τ ε' θ θ' (u' - u'') (-v') := fun w => by
    rw [Matrix.map_neg _ (map_neg _), hs w, Matrix.map_sub _ (map_sub _), hr w, hr' w, ← sub_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]
    congr 1
    rcases Int.units_eq_one_or (ε w) with a | a <;> rcases Int.units_eq_one_or (ε' w) with b | b <;> simp [a, b]
  have h2 := hf' _ _ hv (fun c hc => by rw [smul_neg, hv' c hc, neg_zero]) hs'
  have en : ∀ z : κ → AF F, nf (-z) = -nf z := fun z => funext fun i =>
    map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1
  have el : ∀ b : κ → mixedEmbedding.mixedSpace F, linForm (-b) = -linForm b := fun b => by
    exact ContinuousLinearMap.ext fun y => by
      simp only [linForm_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg, ContinuousLinearMap.neg_apply]
  rw [map_neg, dd0, Prod.fst_neg, Prod.snd_neg, en, en, el] at h2
  obtain ⟨a0, l0⟩ := opp g g' (hf _ _ hv hv' hs) h2
  rw [← hf' u u'' hu hu'' hr', ← sub_add_cancel u' u'', map_add, dd0, Prod.fst_add, Prod.snd_add, nf_add, nf_add,
    linForm_add, a0, l0, zero_add, zero_add, dd0]

end GlobalTheory.ThK.Dbl.Box

end
