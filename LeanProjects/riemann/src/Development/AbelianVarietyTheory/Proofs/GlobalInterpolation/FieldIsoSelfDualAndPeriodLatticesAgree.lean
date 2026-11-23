import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree
open GlobalTheory.IdealTransport GlobalTheory.InertSign GlobalTheory.ThetaLatImage

noncomputable section

namespace GlobalTheory.PeriodTransport

section Fields

variable {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n a b : ℕ}

def vecT (n : ℕ) : (Fin n → E) ≃+ (Fin n → E') := AddEquiv.piCongrRight fun _ : Fin n => e.toAddEquiv

theorem vecT_smul (r : 𝓞 E) (x : Fin n → E) : vecT e n (r • x) = RingOfIntegers.mapRingEquiv e r • vecT e n x :=
  funext fun i => map_smul_int e r (x i)

theorem trL_fg {N : Submodule (𝓞 E) (Fin n → E)} (h : N.FG) : (trL e N).FG := by
  obtain ⟨S, hS, rfl⟩ := Submodule.fg_def.1 h
  exact Submodule.fg_def.2 ⟨_, hS.image (vecT e n),
    (span_image_span (RingOfIntegers.mapRingEquiv e) (vecT e n) (vecT_smul e) S).symm⟩

theorem trL_span {N : Submodule (𝓞 E) (Fin n → E)} (h : Submodule.span E (N : Set (Fin n → E)) = ⊤) :
    Submodule.span E' (trL e N : Set (Fin n → E')) = ⊤ := by
  have h1 := span_image_span e (vecT e n) (fun r x => funext fun i => map_mul e r (x i)) (N : Set (Fin n → E))
  rw [h, Submodule.top_coe, Set.image_univ, (vecT e n).surjective.range_eq, Submodule.span_univ] at h1
  refine top_le_iff.1 (h1.le.trans (Submodule.span_mono ?_))
  exact Submodule.subset_span

def matT (a b : ℕ) : HomE E a b ≃+ Matrix (Fin b) (Fin a) E' :=
  (LinearMap.toMatrix' (R := E) (m := Fin b) (n := Fin a)).toAddEquiv.trans e.toAddEquiv.mapMatrix

theorem matT_apply (x : HomE E a b) (i : Fin b) (j : Fin a) : matT e a b x i j = e (x (Pi.single j 1) i) := by
  change e (LinearMap.toMatrix' x i j) = _
  rw [LinearMap.toMatrix'_apply]

theorem matT_smul (r : E) (x : HomE E a b) : matT e a b (r • x) = e r • matT e a b x := by
  ext i j
  simp [matT_apply]

theorem matT_smul_int (r : 𝓞 E) (x : HomE E a b) :
    matT e a b (r • x) = RingOfIntegers.mapRingEquiv e r • matT e a b x := by
  ext i j
  rw [Matrix.smul_apply, matT_apply, matT_apply, ← map_smul_int]
  rfl

theorem matT_mulVec (x : HomE E a b) (v : Fin a → E') :
    (fun i => e.symm ((matT e a b x).mulVec v i)) = x fun j => e.symm (v j) := by
  funext i
  rw [← LinearMap.toMatrix'_mulVec]
  simp [Matrix.mulVec, dotProduct, matT_apply]

theorem matT_carries (N : Submodule (𝓞 E) (Fin a → E)) (N' : Submodule (𝓞 E) (Fin b → E)) (x : HomE E a b) :
    (∀ v ∈ trL e N, (matT e a b x).mulVec v ∈ trL e N') ↔ ∀ y ∈ N, x y ∈ N' := by
  simp only [mem_trL, matT_mulVec]
  refine ⟨fun H y hy => ?_, fun H v hv => H _ hv⟩
  simpa using H (fun i => e (y i)) (by simpa using hy)

end Fields

variable {X : Fields} {D : D7} (s : Seam D X)

theorem sd_lat (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (h : IsSdLat N) : StandardLatticesGL3.SD D (s.lat N) := by
  refine (sd_iff D _).2 ⟨trL_fg s.iE h.1.fg, trL_span s.iE h.1.span_eq_top, fun y => ?_⟩
  have key : ∀ x : Fin n → D.host.E, IntE D (hE D y x) ↔
      hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) ∈ (1 : Submodule (𝓞 X.E) X.E) := by
    intro x
    have e1 : hStd X.E n (fun i => s.iE.symm (x i)) (fun i => s.iE.symm (y i)) = s.iE.symm (hE D y x) := by
      apply s.iE.injective
      change s.iE (∑ i, star (s.iE.symm (x i)) * s.iE.symm (y i)) = _
      simp only [map_sum, map_mul, hs.2, RingEquiv.apply_symm_apply, hE, mul_comm]
    rw [e1, ← mem_one_iff, Submodule.mem_one]
    rfl
  have hm : ∀ x, x ∈ s.lat N ↔ (fun i => s.iE.symm (x i)) ∈ N := mem_trL s.iE N
  simp only [key, hm]
  conv_lhs => rw [← h.2, Formalism.L2.Col.mem_dual]
  refine ⟨fun H x hx => H _ hx, fun H x hx => ?_⟩
  simpa using H (fun i => s.iE (x i)) (by simpa using hx)

theorem mem_AA_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (t : D.host.E) : t ∈ Iid D cc ↔ s.iE.symm t ∈ (ambOf s B χ cD).AA := by
  rw [← mem_trI]
  change _ ↔ t ∈ trI s.iE (Submodule.span _ _)
  rw [trI_span, Iid]
  congr! 2
  ext u
  constructor
  · rintro ⟨c, hc, a, ha, rfl⟩
    exact ⟨_, ⟨c, hc, a, ha, rfl⟩, s.iE.apply_symm_apply _⟩
  · rintro ⟨_, ⟨c, hc, a, ha, rfl⟩, rfl⟩
    exact ⟨c, hc, a, ha, s.iE.apply_symm_apply _⟩

theorem mem_RL_iff {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (z : Matrix (Fin b) (Fin a) D.host.E) :
    z ∈ RL D cc (s.lat N) (s.lat N') ↔ (matT s.iE a b).symm z ∈ perO (ambOf s B χ cD).AA N N' := by
  rw [← mem_span_image (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), perO,
    span_image_span (RingOfIntegers.mapRingEquiv s.iE) (matT s.iE a b) (matT_smul_int s.iE), RL]
  congr! 2
  ext u
  constructor
  · rintro ⟨t, ht, A, hA, rfl⟩
    obtain ⟨x, rfl⟩ := (matT s.iE a b).surjective A
    refine ⟨_, ⟨_, (mem_AA_iff s B χ cD t).1 ht, x, (matT_carries s.iE N N' x).1 (mem_homL.1 hA), rfl⟩, ?_⟩
    rw [matT_smul, RingEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨r, hr, x, hx, rfl⟩, rfl⟩
    exact ⟨s.iE r, (mem_AA_iff s B χ cD _).2 (by simpa using hr), _,
      mem_homL.2 ((matT_carries s.iE N N' x).2 hx), matT_smul _ _ _⟩

theorem seam_lattices : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ), s.Ok → (∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), IsSdLat N → StandardLatticesGL3.SD D (s.lat N)) ∧ ∀ (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (z : VCx X.Tau a b), z ∈ lam (ambOf s B χ cD) N N' ↔ (fun τ => z (s.iT.symm τ)) ∈ TaylorLogMetric.La D B.tor (s.lat N) (s.lat N') := by
  intro X D s cc δ B χ cD hs
  refine ⟨fun n N h => sd_lat s hs h, fun a b N N' z => ?_⟩
  have hpt : ∀ (x : HomE X.E a b) (τ : X.Tau), embH (X.embC s.σ₀) δ x τ =
      StandardLatticesGL3.pt D (TaylorLogMetric.tor0 D cc δ) δ (matT s.iE a b x) (s.iT τ) := by
    intro x τ
    funext i j
    rw [pt_apply, matT_apply, ← hs.1]
    rfl
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 := pt_mem_La (δ := δ) ((mem_RL_iff s B χ cD N N' (matT s.iE a b x)).2 (by simpa using hx)) 1
    rw [one_smul] at h1
    convert h1 using 1
    funext τ
    exact (hpt x _).trans (by rw [Equiv.apply_symm_apply])
  · intro h
    obtain ⟨w, hw, e⟩ := La_sub h
    refine ⟨_, (mem_RL_iff s B χ cD N N' w).1 hw, funext fun τ => (hpt _ τ).trans ?_⟩
    rw [AddEquiv.apply_symm_apply, ← e]
    exact congrArg z (s.iT.symm_apply_apply τ)

end GlobalTheory.PeriodTransport
