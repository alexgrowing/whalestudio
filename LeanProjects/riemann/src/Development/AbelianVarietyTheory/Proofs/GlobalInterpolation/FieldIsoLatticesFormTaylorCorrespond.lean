import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ZeroDimA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
open GlobalTheory.IdealTransport GlobalTheory.ThetaLatImage
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SeamTransport

section Lat

variable {D : D7} {X : Fields} (s : Seam D X) {a b : ℕ}

def matE (a b : ℕ) : HomE X.E a b ≃+ Matrix (Fin b) (Fin a) D.host.E :=
  (LinearMap.toMatrix' (R := X.E) (m := Fin b) (n := Fin a)).toAddEquiv.trans s.iE.toAddEquiv.mapMatrix

theorem matE_apply (x : HomE X.E a b) (i : Fin b) (j : Fin a) : matE s a b x i j = s.iE (x (Pi.single j 1) i) := by
  simp [matE, LinearMap.toMatrix'_apply]

theorem matE_smul (r : X.E) (x : HomE X.E a b) : matE s a b (r • x) = s.iE r • matE s a b x := by
  ext i j
  simp [matE_apply]

theorem matE_smul_int (r : 𝓞 X.E) (x : HomE X.E a b) :
    matE s a b (r • x) = RingOfIntegers.mapRingEquiv s.iE r • matE s a b x := by
  ext i j
  rw [matE_apply, Matrix.smul_apply, matE_apply, ← map_smul_int]
  rfl

theorem matE_mulVec (x : HomE X.E a b) (y : Sp X.E a) :
    (matE s a b x).mulVec (fun j => s.iE (y j)) = fun i => s.iE (x y i) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matE_apply, LinearMap.toMatrix'_apply]

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (x : Fin n → D.host.E) :
    x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N x

theorem matE_mem_homL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ TaylorLogMetric.homL D (s.lat N) (s.lat N') ↔ x ∈ homO N N' := by
  rw [mem_homL]
  constructor
  · intro H y hy
    have := H (fun j => s.iE (y j)) ((mem_lat s N _).2 (by simpa using hy))
    rw [matE_mulVec, mem_lat] at this
    simpa using this
  · intro H v hv
    have hv' : v = fun i => s.iE (s.iE.symm (v i)) := by simp
    rw [hv', matE_mulVec, mem_lat]
    simpa using H _ ((mem_lat s N _).1 hv)

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)

theorem mem_Iid (r : X.E) : s.iE r ∈ GlobalTheory.InertSign.Iid D cc ↔ r ∈ (ambOf s B χ cD).AA := by
  have : GlobalTheory.InertSign.Iid D cc = trI s.iE (ambOf s B χ cD).AA := by
    refine Eq.trans ?_ (trI_span s.iE _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext t
    constructor
    · rintro ⟨c, hc, t, ht, rfl⟩
      exact ⟨_, ⟨c, hc, t, ht, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨c, hc, t, ht, rfl⟩, rfl⟩
      exact ⟨c, hc, t, ht, by simp⟩
  rw [this, mem_trI, RingEquiv.symm_apply_apply]

theorem matE_mem_RL (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (x : HomE X.E a b) :
    matE s a b x ∈ GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') ↔ x ∈ perO (ambOf s B χ cD).AA N N' := by
  have : GlobalTheory.InertSign.RL D cc (s.lat N) (s.lat N') =
      Submodule.span (𝓞 D.host.E) (matE s a b '' (perO (ambOf s B χ cD).AA N N' : Set (HomE X.E a b))) := by
    refine Eq.trans ?_ (span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s) _).symm
    refine congrArg (Submodule.span (𝓞 D.host.E)) ?_
    ext z
    constructor
    · rintro ⟨t, ht, A, hA, rfl⟩
      obtain ⟨t, rfl⟩ := s.iE.surjective t
      obtain ⟨A, rfl⟩ := (matE s a b).surjective A
      exact ⟨_, ⟨t, (mem_Iid s B χ cD t).1 ht, A, (matE_mem_homL s N N' A).1 hA, rfl⟩, matE_smul s t A⟩
    · rintro ⟨_, ⟨t, ht, A, hA, rfl⟩, rfl⟩
      exact ⟨_, (mem_Iid s B χ cD t).2 ht, _, (matE_mem_homL s N N' A).2 hA, matE_smul s t A⟩
  rw [this, mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matE s a b) (matE_smul_int s), AddEquiv.symm_apply_apply]

theorem pt_matE (hs : s.Ok) (x : HomE X.E a b) (τ : X.Tau) :
    StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b x) (s.iT τ) = embH (X.embC s.σ₀) δ x τ := by
  funext i j
  rw [pt_apply, matE_apply, ← hs.1]
  rfl

theorem mem_La (hs : s.Ok) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b) :
    z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔
      (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N' := by
  constructor
  · intro hz
    obtain ⟨A, hA, rfl⟩ := La_sub hz
    obtain ⟨A, rfl⟩ := (matE s a b).surjective A
    exact ⟨A, (matE_mem_RL s B χ cD N N' A).1 hA, funext fun τ => (pt_matE s hs A τ).symm⟩
  · rintro ⟨A, hA, e⟩
    have hz : z = StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matE s a b A) := by
      funext τ
      obtain ⟨τ, rfl⟩ := s.iT.surjective τ
      rw [pt_matE s hs, e]
    rw [hz]
    simpa using pt_mem_La (δ := δ) ((matE_mem_RL s B χ cD N N' A).2 hA) 1

theorem sd_lat (hs : s.Ok) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (hN : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  obtain ⟨hl, hu⟩ := hN
  let f : Sp X.E n ≃+ (Fin n → D.host.E) := AddEquiv.piCongrRight fun _ : Fin n => s.iE.toAddEquiv
  rw [GlobalTheory.InertSign.sd_iff]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 hl.fg
    refine Submodule.fg_def.2 ⟨f '' S, hS.image _, ?_⟩
    exact (span_image_span (RingOfIntegers.mapRingEquiv s.iE) f
      (fun r m => funext fun i => map_smul_int s.iE r (m i)) S).symm
  · rw [eq_top_iff]
    intro v _
    have h1 := span_image_span s.iE f (fun r m => funext fun i => map_mul s.iE r (m i)) (N : Set (Sp X.E n))
    have h2 : v ∈ Submodule.span D.host.E (f '' (N : Set (Sp X.E n))) := by
      rw [← h1, hl.span_eq_top]
      exact Submodule.subset_span ⟨f.symm v, trivial, by simp⟩
    exact Submodule.span_mono (fun w hw => Submodule.subset_span hw) h2
  · have key : ∀ x y : Sp X.E n, GlobalTheory.InertSign.IntE D (GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i))) ↔
        hStd X.E n x y ∈ (1 : Submodule (𝓞 X.E) X.E) := by
      intro x y
      have e : GlobalTheory.InertSign.hE D (fun i => s.iE (y i)) (fun i => s.iE (x i)) = s.iE (hStd X.E n x y) := by
        change _ = s.iE (∑ i, star (x i) * y i)
        simp only [GlobalTheory.InertSign.hE, map_sum, map_mul, hs.2, mul_comm]
      rw [e, ← s.iE.symm_apply_apply (hStd X.E n x y), ← mem_one_iff, s.iE.symm_apply_apply, Submodule.mem_one]
      rfl
    intro y
    have hy : y = fun i => s.iE (s.iE.symm (y i)) := by simp
    rw [mem_lat, ← hu, mem_dual, hu]
    constructor
    · intro H x hx
      have hx' : x = fun i => s.iE (s.iE.symm (x i)) := by simp
      rw [hy, hx', key]
      exact H _ ((mem_lat s N x).1 hx)
    · intro H x hx
      rw [← key, ← hy]
      exact H _ ((mem_lat s N _).2 (by simpa using hx))

theorem form_eq (z w : TaylorLogMetric.VC D a b) :
    TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ)) := by
  change (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) : ℂ) =
    (((TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, z (s.iT τ) i j * (starRingEnd ℂ) (w (s.iT τ) i j)
  rw [Equiv.sum_comp s.iT fun τ => ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j), Complex.ofReal_inv, div_eq_inv_mul]

end Lat

section Taylor

variable {ι κ : Type} [Fintype ι] [Fintype κ] {a b : ℕ}

theorem deriv_transport (e : ι ≃ κ) (G : VCx κ a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 (fun z : VCx ι a b => G fun τ => z (e.symm τ)) m = derivAt0 G (m.mapDomain fun v => (e v.1, v.2)) := by
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  let L : VCx ι a b →L[ℂ] VCx κ a b := ContinuousLinearMap.pi fun τ => ContinuousLinearMap.proj (e.symm τ)
  have hL : ∀ v : DVar ι a b, L (coordX v) = coordX (e v.1, v.2) := by
    intro v
    funext τ i j
    change coordX v (e.symm τ) i j = _
    unfold coordX
    congr 1
    exact propext (and_congr_left' e.symm_apply_eq)
  have h1 : (fun z : VCx ι a b => G fun τ => z (e.symm τ)) = G ∘ L := rfl
  unfold derivAt0
  rw [h1, L.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hc : (Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).card = (Finsupp.toMultiset m).card := by
    rw [← Finsupp.toMultiset_map, Multiset.card_map]
  have p : (((Finsupp.toMultiset m).toList.map fun v => (e v.1, v.2)).map coordX).Perm
      ((Finsupp.toMultiset (m.mapDomain fun v => (e v.1, v.2))).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p (Finsupp.toMultiset m).card (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx κ a b) (w : Fin n' → VCx κ a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp [hL]
  · simp

end Taylor

theorem taylor_eq (D : D7) {a b : ℕ} (G : TaylorLogMetric.VC D a b → ℂ) (m : TaylorLogMetric.Mono D a b) :
    derivAt0 G m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G m := by
  have h : (m.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold TaylorLogMetric.taylor
  rw [mul_div_cancel₀ _ h]
  unfold derivAt0
  congr 1

theorem transport : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : TaylorLogMetric.VC D a b), z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (s.lat N) (s.lat N') ↔ (fun τ => z (s.iT τ)) ∈ LamC (X.embC s.σ₀) δ (ambOf s B χ cD).AA N N') ∧ (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Even a → Even b → IsSdLat N → IsSdLat N' → TaylorLogMetric.admitted D a b (s.lat N) (s.lat N')) ∧ (∀ z w : TaylorLogMetric.VC D a b, TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z w = HV (ambOf s B χ cD).sc (fun τ => z (s.iT τ)) (fun τ => w (s.iT τ))) ∧ ∀ G : TaylorLogMetric.VC D a b → ℂ, (∀ k : ℕ, ContDiff ℂ k G) → ∀ m : DVar X.Tau a b →₀ ℕ, derivAt0 (fun z : VCx X.Tau a b => G fun τ => z (s.iT.symm τ)) m = (m.prod fun _ n => (n.factorial : ℂ)) * TaylorLogMetric.taylor D G (m.mapDomain fun v => (s.iT v.1, v.2)) := by
  intro D X s cc δ B χ cD a b hs
  refine ⟨mem_La s B χ cD hs, fun N N' ha hb hN hN' => ⟨ha, hb, sd_lat s hs N hN, sd_lat s hs N' hN'⟩, form_eq s B χ cD,
    fun G hG m => ?_⟩
  rw [deriv_transport s.iT G hG m, taylor_eq, Finsupp.prod_mapDomain_index_inj]
  intro v w h
  exact Prod.ext (s.iT.injective (Prod.ext_iff.1 h).1) (Prod.ext_iff.1 h).2

end GlobalTheory.SeamTransport
